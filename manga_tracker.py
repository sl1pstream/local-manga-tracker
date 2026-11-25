#!/usr/bin/env python3
"""Manga Tracker - a local manga tracker with a Tkinter GUI and a PWA web UI.

Data lives in manga_data.sqlite3 next to this script. Covers are copied into
"Manga Covers/". The web UI runs in a separate process so it can stay online
after the GUI closes.

API (used by the Komikku local tracker):
    GET    /api/manga              -> list of entries, sorted by title
    GET    /api/manga/<id>         -> one entry
    GET    /api/search?q=<query>   -> matching entries
    GET    /api/statuses           -> status values + labels
    GET    /api/cover?id=<id>      -> cover image (also ?path=<file>)
    POST   /api/manga              -> create (200 + existing entry if title exists)
    PUT    /api/manga/<id>         -> update
    DELETE /api/manga/<id>         -> delete
    POST   /api/manga/<id>/cover   -> upload/replace cover (raw image body)
    DELETE /api/manga/<id>/cover   -> remove cover
"""

import json
import ipaddress
import mimetypes
import os
import sqlite3
import shutil
import subprocess
import sys
import threading
import time
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, unquote, urlparse
from urllib.error import URLError
from urllib.request import Request, urlopen

import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from PIL import Image, ImageTk

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
LEGACY_DATA_FILE = os.path.join(SCRIPT_DIR, "manga_data.json")
DATA_FILE = os.path.join(SCRIPT_DIR, "manga_data.sqlite3")
CONFIG_FILE = os.path.join(SCRIPT_DIR, "config.json")
COVERS_DIR = os.path.join(SCRIPT_DIR, "Manga Covers")
DEFAULT_PORT = 8090

STATUSES = [
    ("reading", "Reading"),
    ("completed", "Completed"),
    ("on_hold", "On hold"),
    ("dropped", "Dropped"),
    ("plan_to_read", "Plan to read"),
]
STATUS_VALUES = [value for value, _ in STATUSES]
STATUS_LABELS = dict(STATUSES)
STATUS_VALUES_BY_LABEL = {label: value for value, label in STATUSES}


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def _now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _parse_chapter(value):
    """Accept a blank chapter or a non-negative integer."""
    if value is None:
        return None
    text = str(value).strip()
    if not text:
        return None
    if not text.isdecimal():
        raise ValueError("chapter_invalid")
    return int(text)


def _parse_score(value):
    """Scores are whole numbers 1-10; anything else is None."""
    if value is None:
        return None
    text = str(value).strip()
    if not text or text == "-":
        return None
    try:
        number = int(float(text))
    except ValueError:
        return None
    return max(1, min(10, number))


def _format_number(value):
    if value is None:
        return ""
    number = float(value)
    return str(int(number)) if number.is_integer() else str(number)


def load_config():
    try:
        with open(CONFIG_FILE, encoding="utf-8") as handle:
            return json.load(handle)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_config(data):
    with open(CONFIG_FILE, "w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=4)


# ---------------------------------------------------------------------------
# SQLite store
# ---------------------------------------------------------------------------

class Store:
    """SQLite-backed store shared safely by the GUI and server processes."""

    def __init__(self, path=DATA_FILE):
        self.path = path
        self._lock = threading.RLock()
        self.version = 0
        existed = os.path.exists(self.path)
        os.makedirs(os.path.dirname(self.path) or ".", exist_ok=True)
        self._connection = sqlite3.connect(self.path, timeout=15, check_same_thread=False)
        self._connection.row_factory = sqlite3.Row
        self._connection.execute("PRAGMA busy_timeout = 15000")
        self._connection.execute("PRAGMA journal_mode = WAL")
        self._connection.execute("""
            CREATE TABLE IF NOT EXISTS manga (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                title TEXT NOT NULL,
                title_key TEXT NOT NULL UNIQUE,
                description TEXT NOT NULL DEFAULT '',
                status TEXT NOT NULL DEFAULT 'plan_to_read',
                chapter INTEGER,
                score INTEGER,
                cover_image TEXT,
                updated_at TEXT NOT NULL
            )
        """)
        self._connection.commit()
        self._last_data_version = self._read_data_version()
        if not existed:
            self._import_legacy_json()

    def _read_data_version(self):
        return self._connection.execute("PRAGMA data_version").fetchone()[0]

    def _refresh_version(self):
        data_version = self._read_data_version()
        if data_version != self._last_data_version:
            self.version += 1
            self._last_data_version = data_version

    def check_for_changes(self):
        with self._lock:
            self._refresh_version()

    @staticmethod
    def _entry(row):
        if row is None:
            return None
        entry = dict(row)
        entry.pop("title_key", None)
        return entry

    def _import_legacy_json(self):
        try:
            with open(LEGACY_DATA_FILE, encoding="utf-8") as handle:
                legacy = json.load(handle)
        except FileNotFoundError:
            return
        except (json.JSONDecodeError, OSError) as error:
            print(f"Warning: could not import {LEGACY_DATA_FILE}: {error}")
            return

        entries = legacy.get("manga", {}) if isinstance(legacy, dict) else {}
        if not isinstance(entries, dict):
            return
        with self._lock, self._connection:
            for key, raw in entries.items():
                if not isinstance(raw, dict):
                    continue
                try:
                    manga_id = int(raw.get("id", key))
                    fields = self._normalize(raw)
                    self._connection.execute("""
                        INSERT OR IGNORE INTO manga
                            (id, title, title_key, description, status, chapter, score, cover_image, updated_at)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, (
                        manga_id,
                        fields["title"],
                        fields["title"].lower(),
                        fields["description"],
                        fields["status"],
                        fields["chapter"],
                        fields["score"],
                        fields["cover_image"],
                        raw.get("updated_at") or _now(),
                    ))
                except (TypeError, ValueError, sqlite3.IntegrityError):
                    continue
            next_id = legacy.get("next_id", 1)
            try:
                next_id = max(1, int(next_id))
            except (TypeError, ValueError):
                next_id = 1
            highest_id = self._connection.execute(
                "SELECT COALESCE(MAX(id), 0) FROM manga",
            ).fetchone()[0]
            if next_id > highest_id + 1:
                self._connection.execute(
                    "INSERT OR IGNORE INTO sqlite_sequence(name, seq) VALUES ('manga', ?)",
                    (next_id - 1,),
                )
                self._connection.execute(
                    "UPDATE sqlite_sequence SET seq = MAX(seq, ?) WHERE name = 'manga'",
                    (next_id - 1,),
                )
        self.version += 1

    def _normalize(self, fields, partial=False):
        out = {}
        if "title" in fields or not partial:
            out["title"] = str(fields.get("title", "")).strip()
        if "description" in fields or not partial:
            out["description"] = str(fields.get("description") or "")
        if "status" in fields or not partial:
            status = fields.get("status", "plan_to_read")
            out["status"] = status if status in STATUS_VALUES else "plan_to_read"
        if "chapter" in fields or not partial:
            out["chapter"] = _parse_chapter(fields.get("chapter"))
        if "score" in fields or not partial:
            out["score"] = _parse_score(fields.get("score"))
        if "cover_image" in fields or not partial:
            out["cover_image"] = fields.get("cover_image")
        return out

    def all(self):
        with self._lock:
            self._refresh_version()
            rows = self._connection.execute("SELECT * FROM manga ORDER BY title COLLATE NOCASE, id").fetchall()
            return [self._entry(row) for row in rows]

    def get(self, manga_id):
        with self._lock:
            self._refresh_version()
            row = self._connection.execute("SELECT * FROM manga WHERE id = ?", (manga_id,)).fetchone()
            return self._entry(row)

    def find_by_title(self, title):
        needle = str(title).strip().lower()
        with self._lock:
            self._refresh_version()
            row = self._connection.execute(
                "SELECT * FROM manga WHERE title_key = ?", (needle,),
            ).fetchone()
            return self._entry(row)

    def create(self, fields):
        with self._lock:
            entry = self._normalize(fields)
            try:
                self._connection.execute("BEGIN IMMEDIATE")
                row = self._connection.execute(
                    "SELECT * FROM manga WHERE title_key = ?", (entry["title"].lower(),),
                ).fetchone()
                if row is not None:
                    self._connection.commit()
                    self._refresh_version()
                    return self._entry(row), False
                cursor = self._connection.execute("""
                    INSERT INTO manga (title, title_key, description, status, chapter, score, cover_image, updated_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    entry["title"], entry["title"].lower(), entry["description"], entry["status"], entry["chapter"],
                    entry["score"], entry["cover_image"], _now(),
                ))
                manga_id = cursor.lastrowid
                self._connection.commit()
            except Exception:
                self._connection.rollback()
                raise
            self.version += 1
            self._refresh_version()
            entry["id"] = manga_id
            entry["updated_at"] = self._connection.execute(
                "SELECT updated_at FROM manga WHERE id = ?", (manga_id,),
            ).fetchone()[0]
            return entry, True

    def update(self, manga_id, fields):
        with self._lock:
            try:
                self._connection.execute("BEGIN IMMEDIATE")
                row = self._connection.execute("SELECT * FROM manga WHERE id = ?", (manga_id,)).fetchone()
                if row is None:
                    self._connection.commit()
                    self._refresh_version()
                    return None
                entry = self._entry(row)
                normalized = self._normalize(fields, partial=True)
                if "title" in normalized:
                    duplicate = self._connection.execute(
                        "SELECT id FROM manga WHERE title_key = ? AND id != ?",
                        (normalized["title"].lower(), manga_id),
                    ).fetchone()
                    if duplicate is not None:
                        self._connection.rollback()
                        raise ValueError("title_exists")
                entry.update(normalized)
                entry["updated_at"] = _now()
                self._connection.execute("""
                    UPDATE manga SET title = ?, title_key = ?, description = ?, status = ?, chapter = ?,
                        score = ?, cover_image = ?, updated_at = ? WHERE id = ?
                """, (
                    entry["title"], entry["title"].lower(), entry["description"], entry["status"], entry["chapter"],
                    entry["score"], entry["cover_image"], entry["updated_at"], manga_id,
                ))
                self._connection.commit()
            except Exception:
                self._connection.rollback()
                raise
            self.version += 1
            self._refresh_version()
            return entry

    def delete(self, manga_id):
        with self._lock:
            try:
                self._connection.execute("BEGIN IMMEDIATE")
                row = self._connection.execute("SELECT * FROM manga WHERE id = ?", (manga_id,)).fetchone()
                if row is None:
                    self._connection.commit()
                    self._refresh_version()
                    return None
                self._connection.execute("DELETE FROM manga WHERE id = ?", (manga_id,))
                self._connection.commit()
            except Exception:
                self._connection.rollback()
                raise
            self.version += 1
            self._refresh_version()
            return self._entry(row)

    def set_cover(self, manga_id, path):
        with self._lock:
            try:
                self._connection.execute("BEGIN IMMEDIATE")
                row = self._connection.execute("SELECT * FROM manga WHERE id = ?", (manga_id,)).fetchone()
                if row is None:
                    self._connection.commit()
                    self._refresh_version()
                    return None
                self._connection.execute(
                    "UPDATE manga SET cover_image = ?, updated_at = ? WHERE id = ?",
                    (path, _now(), manga_id),
                )
                self._connection.commit()
            except Exception:
                self._connection.rollback()
                raise
            self.version += 1
            self._refresh_version()
            return self.get(manga_id)

    def close(self):
        with self._lock:
            self._connection.close()


# ---------------------------------------------------------------------------
# HTTP server
# ---------------------------------------------------------------------------

class TrackerHTTPServer(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True

    def __init__(self, address, store):
        self.store = store
        super().__init__(address, TrackerRequestHandler)


class TrackerRequestHandler(BaseHTTPRequestHandler):
    server_version = "MangaTracker/1.0"

    def log_message(self, *args):
        pass

    @property
    def store(self):
        return self.server.store

    # -- response helpers ---------------------------------------------------

    def _send(self, code, body, content_type="application/json", extra_headers=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        for key, value in (extra_headers or {}).items():
            self.send_header(key, value)
        self.end_headers()
        self.wfile.write(body)

    def _json(self, code, payload):
        self._send(code, json.dumps(payload, ensure_ascii=False), "application/json; charset=utf-8")

    def _read_json(self):
        length = int(self.headers.get("Content-Length", 0) or 0)
        if length <= 0:
            return {}
        raw = self.rfile.read(length)
        try:
            return json.loads(raw.decode("utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError):
            return None

    def _serve_file(self, path):
        if not path or not os.path.isfile(path):
            self._send(404, "Not found", "text/plain; charset=utf-8")
            return
        mime = mimetypes.guess_type(path)[0] or "application/octet-stream"
        with open(path, "rb") as handle:
            data = handle.read()
        self._send(200, data, mime, {"Cache-Control": "no-cache"})

    def _serve_static(self, path):
        if path == "/":
            path = "/index.html"
        root = os.path.realpath(SCRIPT_DIR)
        file_path = os.path.realpath(os.path.join(SCRIPT_DIR, unquote(path.lstrip("/"))))
        if file_path != root and not file_path.startswith(root + os.sep):
            self._send(403, "Forbidden", "text/plain; charset=utf-8")
            return
        self._serve_file(file_path)

    # -- verbs --------------------------------------------------------------

    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path
        query = parse_qs(parsed.query)

        if path in ("/api/manga", "/api/manga/"):
            self._json(200, self.store.all())
        elif path == "/api/health":
            self._json(200, {"service": "manga-tracker", "ok": True})
        elif path.startswith("/api/manga/"):
            manga_id = path[len("/api/manga/"):].strip("/")
            entry = self.store.get(manga_id)
            self._json(200, entry) if entry else self._json(404, {"error": "not_found"})
        elif path == "/api/search":
            needle = (query.get("q", [""])[0] or "").strip().lower()
            results = [
                entry for entry in self.store.all()
                if needle in entry.get("title", "").lower()
                or needle in entry.get("description", "").lower()
            ]
            self._json(200, results)
        elif path == "/api/statuses":
            self._json(200, [{"value": value, "label": label} for value, label in STATUSES])
        elif path == "/api/cover":
            if "id" in query:
                entry = self.store.get(query["id"][0])
                self._serve_file(entry.get("cover_image") if entry else None)
            else:
                self._serve_file(unquote(query.get("path", [""])[0]))
        else:
            self._serve_static(path)

    def do_POST(self):
        path = urlparse(self.path).path

        if path == "/api/server/stop":
            try:
                is_loopback = ipaddress.ip_address(self.client_address[0]).is_loopback
            except ValueError:
                is_loopback = False
            if not is_loopback:
                self._json(403, {"error": "localhost_only"})
                return
            self._json(202, {"ok": True})
            threading.Thread(target=self.server.shutdown, daemon=True).start()

        elif path in ("/api/manga", "/api/manga/"):
            body = self._read_json()
            if not isinstance(body, dict):
                self._json(400, {"error": "invalid_json"})
                return
            title = str(body.get("title", "")).strip()
            if not title:
                self._json(400, {"error": "title_required"})
                return
            try:
                _parse_chapter(body.get("chapter"))
            except ValueError:
                self._json(400, {"error": "chapter_invalid"})
                return
            body["title"] = title
            entry, created = self.store.create(body)
            self._json(201 if created else 200, entry)

        elif path.startswith("/api/manga/") and path.endswith("/cover"):
            manga_id = path[len("/api/manga/"):-len("/cover")].strip("/")
            entry = self.store.get(manga_id)
            if entry is None:
                self._json(404, {"error": "not_found"})
                return
            length = int(self.headers.get("Content-Length", 0) or 0)
            if length <= 0:
                self._json(400, {"error": "empty_body"})
                return
            content_type = (self.headers.get("Content-Type") or "image/jpeg").split(";")[0].strip()
            extension = mimetypes.guess_extension(content_type) or ".jpg"
            if extension == ".jpe":
                extension = ".jpg"
            os.makedirs(COVERS_DIR, exist_ok=True)
            save_path = os.path.join(COVERS_DIR, f"{manga_id}{extension}")
            with open(save_path, "wb") as handle:
                handle.write(self.rfile.read(length))
            updated = self.store.set_cover(manga_id, save_path)
            old_path = entry.get("cover_image")
            if old_path and os.path.abspath(old_path) != os.path.abspath(save_path):
                try:
                    os.remove(old_path)
                except OSError:
                    pass
            self._json(200, updated)

        else:
            self._json(404, {"error": "not_found"})

    def do_PUT(self):
        path = urlparse(self.path).path
        if not path.startswith("/api/manga/"):
            self._json(404, {"error": "not_found"})
            return
        manga_id = path[len("/api/manga/"):].strip("/")
        body = self._read_json()
        if not isinstance(body, dict):
            self._json(400, {"error": "invalid_json"})
            return
        if "title" in body and not str(body["title"]).strip():
            self._json(400, {"error": "title_required"})
            return
        if "chapter" in body:
            try:
                _parse_chapter(body["chapter"])
            except ValueError:
                self._json(400, {"error": "chapter_invalid"})
                return
        try:
            entry = self.store.update(manga_id, body)
        except ValueError:
            self._json(409, {"error": "title_exists"})
            return
        if entry is None:
            self._json(404, {"error": "not_found"})
        else:
            self._json(200, entry)

    def do_DELETE(self):
        path = urlparse(self.path).path

        if path.startswith("/api/manga/") and path.endswith("/cover"):
            manga_id = path[len("/api/manga/"):-len("/cover")].strip("/")
            entry = self.store.get(manga_id)
            if entry is None:
                self._json(404, {"error": "not_found"})
                return
            old_path = entry.get("cover_image")
            if old_path and os.path.isfile(old_path):
                try:
                    os.remove(old_path)
                except OSError:
                    pass
            self._json(200, self.store.set_cover(manga_id, None))

        elif path.startswith("/api/manga/"):
            manga_id = path[len("/api/manga/"):].strip("/")
            entry = self.store.delete(manga_id)
            if entry is None:
                self._json(404, {"error": "not_found"})
                return
            cover = entry.get("cover_image")
            if cover and os.path.isfile(cover):
                try:
                    os.remove(cover)
                except OSError:
                    pass
            self._json(200, {"ok": True})

        else:
            self._json(404, {"error": "not_found"})


def _pwa_url(port):
    return f"http://127.0.0.1:{port}"


def _pwa_is_running(port, timeout=0.5):
    try:
        with urlopen(f"{_pwa_url(port)}/api/health", timeout=timeout) as response:
            body = json.loads(response.read().decode("utf-8"))
            return response.status == 200 and body.get("service") == "manga-tracker" and body.get("ok") is True
    except (OSError, URLError, ValueError, json.JSONDecodeError):
        return False


def _start_detached_server(port):
    options = {
        "cwd": SCRIPT_DIR,
        "stdin": subprocess.DEVNULL,
        "stdout": subprocess.DEVNULL,
        "stderr": subprocess.DEVNULL,
        "close_fds": True,
    }
    if os.name == "nt":
        options["creationflags"] = subprocess.DETACHED_PROCESS | subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        options["start_new_session"] = True
    return subprocess.Popen([sys.executable, os.path.abspath(__file__), "--server", str(port)], **options)


def _request_server_stop(port, timeout=2):
    request = Request(f"{_pwa_url(port)}/api/server/stop", data=b"", method="POST")
    with urlopen(request, timeout=timeout) as response:
        return response.status == 202


# ---------------------------------------------------------------------------
# Tkinter GUI
# ---------------------------------------------------------------------------

class MangaTracker:
    def __init__(self, master, store):
        self.master = master
        self.store = store
        master.title("Manga Tracker")

        self.bg_color = "#000000"      # AMOLED black background
        self.fg_color = "#D8DEE9"      # Light text color
        self.accent_color = "#88C0D0"  # Accent color for highlights

        self.cover_image = None        # path to the cover currently being edited
        self.current_id = None
        self.image_refs = {}
        self._refreshing = False
        self._active_port = None
        self._last_version = -1

        self.setup_modern_ui()
        self.create_widgets()
        self._sync_pwa_state()
        self._poll_store()

    def setup_modern_ui(self):
        style = ttk.Style()
        style.theme_use("clam")

        bg_color = self.bg_color
        fg_color = self.fg_color
        accent_color = self.accent_color

        style.configure("TFrame", background=bg_color)
        style.configure("TLabel", background=bg_color, foreground=fg_color)
        style.configure("TButton", background=accent_color, foreground=bg_color)
        style.map("TButton", background=[("active", "#81A1C1")])
        style.configure("TEntry", fieldbackground=bg_color, foreground=fg_color)
        style.configure("TSpinbox", fieldbackground=bg_color, foreground=fg_color)
        style.configure("TCombobox", fieldbackground=bg_color, foreground=fg_color, background=bg_color)
        style.map(
            "TCombobox",
            fieldbackground=[("readonly", bg_color)],
            foreground=[("readonly", fg_color)],
            selectbackground=[("readonly", bg_color)],
            selectforeground=[("readonly", fg_color)],
        )

        self.master.configure(bg=bg_color)
        self.master.option_add("*Font", "Roboto 10")
        self.master.option_add("*Background", bg_color)
        self.master.option_add("*Foreground", fg_color)

        self.master.geometry("900x650")
        self.master.grid_columnconfigure(0, weight=1)
        self.master.grid_rowconfigure(1, weight=0)
        self.master.grid_rowconfigure(2, weight=1)

    def create_widgets(self):
        style = ttk.Style()
        style.configure("Custom.TButton", background=self.accent_color, foreground=self.bg_color, padding=10)

        style.configure("Treeview", rowheight=60)
        style.configure(
            "Treeview",
            background=self.bg_color,
            fieldbackground=self.bg_color,
            foreground=self.fg_color,
            borderwidth=0,
        )
        style.layout("Treeview", [("Treeview.treearea", {"sticky": "nswe"})])

        # Add Title button
        self.add_title_button = ttk.Button(
            self.master, text="Add Title", command=self.add_new, style="Custom.TButton", width=15,
        )
        self.add_title_button.grid(row=0, column=0, columnspan=3, pady=10)

        # Status filter above the title list
        status_filter_frame = tk.Frame(self.master, bg=self.bg_color)
        status_filter_frame.grid(row=1, column=0, columnspan=3, sticky="w", padx=10, pady=(0, 4))
        ttk.Label(status_filter_frame, text="Status:").pack(side=tk.LEFT, padx=(0, 6))
        self.status_filter_var = tk.StringVar(value="All statuses")
        self.status_filter = ttk.Combobox(
            status_filter_frame,
            values=("All statuses",) + tuple(label for _, label in STATUSES),
            state="readonly",
            width=20,
            textvariable=self.status_filter_var,
        )
        self.status_filter.pack(side=tk.LEFT)
        self.status_filter.bind("<<ComboboxSelected>>", lambda _event: self.refresh_list())

        # Title list
        self.tree = ttk.Treeview(
            self.master, columns=("Title",), show="tree", selectmode="browse", style="Treeview",
        )
        self.tree.column("#0", width=100)
        self.tree.column("Title", width=200)
        self.tree.grid(row=2, column=0, rowspan=5, columnspan=3, padx=10, pady=10)
        self.tree.bind("<<TreeviewSelect>>", self.load_details)

        # Details frame
        self.details_frame = ttk.Frame(self.master)
        self.details_frame.grid(row=1, column=3, rowspan=6, padx=10, pady=10)

        # PWA toggle
        self.pwa_var = tk.BooleanVar(value=False)
        style.configure("PWA.TCheckbutton", background="#000000", foreground="#88C0D0", indicatorcolor="#88C0D0")
        style.map("PWA.TCheckbutton", background=[("active", "#000000")], foreground=[("active", "#88C0D0")])
        pwa_frame = tk.Frame(self.details_frame, bg=self.bg_color)
        pwa_frame.grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 6))
        self.pwa_check = ttk.Checkbutton(
            pwa_frame, text="Start PWA", variable=self.pwa_var, command=self.toggle_pwa, style="PWA.TCheckbutton",
        )
        self.pwa_check.pack(side=tk.LEFT)
        ttk.Label(pwa_frame, text="Port:").pack(side=tk.LEFT, padx=(10, 4))
        self.port_entry = ttk.Entry(pwa_frame, width=6)
        self.port_entry.insert(0, str(load_config().get("port", DEFAULT_PORT)))
        self.port_entry.pack(side=tk.LEFT)

        # Title
        ttk.Label(self.details_frame, text="Title:").grid(row=1, column=0, sticky="w", padx=(0, 5))
        self.title_entry = ttk.Entry(self.details_frame, width=30)
        self.title_entry.grid(row=1, column=1, sticky="w")

        # Description
        ttk.Label(self.details_frame, text="Description:").grid(row=2, column=0, sticky="w", padx=(0, 5))
        self.description_text = tk.Text(
            self.details_frame, height=5, width=30, bg=self.bg_color, fg=self.fg_color, wrap=tk.WORD,
        )
        self.description_text.grid(row=2, column=1, sticky="w")

        # Chapter
        ttk.Label(self.details_frame, text="Chapter:").grid(row=3, column=0, sticky="w", padx=(0, 5))
        self.chapter_spinbox = ttk.Spinbox(
            self.details_frame, from_=0, to=10000, increment=1, width=8,
        )
        self.chapter_spinbox.grid(row=3, column=1, sticky="w")

        # Status
        ttk.Label(self.details_frame, text="Status:").grid(row=4, column=0, sticky="w", padx=(0, 5))
        self.status_combo = ttk.Combobox(
            self.details_frame, values=[label for _, label in STATUSES], state="readonly", width=20,
        )
        self.status_combo.set(STATUS_LABELS["plan_to_read"])
        self.status_combo.grid(row=4, column=1, sticky="w")

        # Score
        ttk.Label(self.details_frame, text="Score:").grid(row=5, column=0, sticky="w", padx=(0, 5))
        self.score_combo = ttk.Combobox(
            self.details_frame, values=["-"] + [str(number) for number in range(1, 11)],
            state="readonly", width=5,
        )
        self.score_combo.set("-")
        self.score_combo.grid(row=5, column=1, sticky="w")

        # Cover image
        self.cover_image_label = ttk.Label(self.details_frame, cursor="hand2")
        self.cover_image_label.grid(row=6, column=0, columnspan=2, pady=10)
        self.cover_image_label.bind("<Button-1>", self.show_full_image)

        image_buttons_frame = tk.Frame(self.details_frame)
        image_buttons_frame.grid(row=7, column=0, columnspan=2)
        ttk.Button(
            image_buttons_frame, text="Browse Cover Image", command=self.browse_image,
            style="Custom.TButton", width=20,
        ).pack(side=tk.LEFT, padx=10)
        ttk.Button(
            image_buttons_frame, text="Remove Cover Image", command=self.remove_cover_image,
            style="Custom.TButton", width=20,
        ).pack(side=tk.LEFT, padx=10)

        # Action buttons
        action_buttons_frame = tk.Frame(self.details_frame)
        action_buttons_frame.grid(row=8, column=0, columnspan=2)
        self.delete_button = ttk.Button(
            action_buttons_frame, text="Delete", command=self.delete_entry,
            style="Custom.TButton", width=15, state="disabled",
        )
        self.delete_button.pack(side=tk.LEFT, padx=5, pady=(5, 10))
        ttk.Button(
            action_buttons_frame, text="Save/Update", command=self.save_entry,
            style="Custom.TButton", width=15,
        ).pack(side=tk.LEFT, padx=5, pady=(5, 10))
        ttk.Button(
            action_buttons_frame, text="Refresh", command=self.refresh_list,
            style="Custom.TButton", width=15,
        ).pack(side=tk.LEFT, padx=5, pady=(5, 10))

        self.refresh_list()

    # -- cover helpers ------------------------------------------------------

    def _show_cover_preview(self, path):
        self.cover_image_label.config(image="")
        self.cover_image_label.image = None
        if path and os.path.isfile(path):
            try:
                with Image.open(path) as image:
                    image.thumbnail((200, 200))
                    photo = ImageTk.PhotoImage(image)
                self.cover_image_label.config(image=photo)
                self.cover_image_label.image = photo
            except Exception as error:
                print(f"Error loading cover: {error}")

    def browse_image(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("Image files", "*.jpg *.jpeg *.png *.gif *.webp")],
        )
        if not file_path:
            return
        self.cover_image = file_path
        self._show_cover_preview(file_path)

    def remove_cover_image(self):
        self.cover_image = None
        self._show_cover_preview(None)

    def show_full_image(self, event=None):
        if not self.cover_image or not os.path.isfile(self.cover_image):
            return
        try:
            with Image.open(self.cover_image) as image:
                screen_width = self.master.winfo_screenwidth()
                screen_height = self.master.winfo_screenheight()
                image.thumbnail((int(screen_width * 0.9), int(screen_height * 0.9)))
                photo = ImageTk.PhotoImage(image)
                width, height = image.size
            window = tk.Toplevel(self.master)
            window.title("Cover Image")
            window.configure(bg=self.bg_color)
            label = tk.Label(window, image=photo, bg=self.bg_color)
            label.image = photo
            label.pack()
            window.geometry(f"{width}x{height}")
        except Exception as error:
            print(f"Error displaying full image: {error}")

    # -- list / form --------------------------------------------------------

    def refresh_list(self):
        self._refreshing = True
        try:
            for item in self.tree.get_children():
                self.tree.delete(item)
            self.image_refs.clear()

            selected_status = STATUS_VALUES_BY_LABEL.get(self.status_filter_var.get())
            for entry in self.store.all():
                if selected_status is not None and entry.get("status") != selected_status:
                    continue
                iid = str(entry["id"])
                cover = entry.get("cover_image")
                photo = None
                if cover and os.path.isfile(cover):
                    try:
                        with Image.open(cover) as image:
                            image.thumbnail((50, 50))
                            photo = ImageTk.PhotoImage(image)
                    except Exception:
                        photo = None
                if photo is not None:
                    self.image_refs[iid] = photo
                    self.tree.insert(
                        "", "end", iid=iid, text="", image=photo, values=(entry.get("title", ""),),
                    )
                else:
                    self.tree.insert("", "end", iid=iid, text="", values=(entry.get("title", ""),))

            if self.current_id is not None and self.tree.exists(str(self.current_id)):
                self.tree.selection_set(str(self.current_id))
                self.tree.see(str(self.current_id))
        finally:
            self._refreshing = False

    def load_details(self, event=None):
        if self._refreshing:
            return
        selection = self.tree.selection()
        if not selection:
            return
        self._load_entry(selection[0])

    def _load_entry(self, manga_id):
        entry = self.store.get(manga_id)
        if entry is None:
            return
        self.current_id = int(entry["id"])
        self.title_entry.delete(0, tk.END)
        self.title_entry.insert(0, entry.get("title", ""))
        self.description_text.delete("1.0", tk.END)
        self.description_text.insert("1.0", entry.get("description") or "")
        self.chapter_spinbox.delete(0, tk.END)
        if entry.get("chapter") is not None:
            self.chapter_spinbox.insert(0, _format_number(entry["chapter"]))
        self.status_combo.set(STATUS_LABELS.get(entry.get("status"), STATUS_LABELS["plan_to_read"]))
        score = entry.get("score")
        self.score_combo.set(str(score) if score is not None else "-")
        self.cover_image = entry.get("cover_image")
        self._show_cover_preview(self.cover_image)
        self.delete_button.config(state="normal")

    def add_new(self):
        self.tree.selection_remove(self.tree.selection())
        self.current_id = None
        self.title_entry.delete(0, tk.END)
        self.description_text.delete("1.0", tk.END)
        self.chapter_spinbox.delete(0, tk.END)
        self.status_combo.set(STATUS_LABELS["plan_to_read"])
        self.score_combo.set("-")
        self.cover_image = None
        self._show_cover_preview(None)
        self.delete_button.config(state="disabled")

    def save_entry(self):
        title = self.title_entry.get().strip()
        if not title:
            messagebox.showwarning("Manga Tracker", "Title is required.")
            return

        try:
            chapter = _parse_chapter(self.chapter_spinbox.get())
        except ValueError:
            messagebox.showwarning("Manga Tracker", "Chapter must be a whole number of 0 or more.")
            return

        fields = {
            "title": title,
            "description": self.description_text.get("1.0", tk.END).strip(),
            "status": STATUS_VALUES_BY_LABEL.get(self.status_combo.get(), "plan_to_read"),
            "chapter": chapter,
            "score": _parse_score(self.score_combo.get()),
        }

        try:
            if self.current_id is None:
                entry, created = self.store.create(fields)
                self.current_id = int(entry["id"])
                if not created:
                    self.refresh_list()
                    self._load_entry(self.current_id)
                    messagebox.showinfo(
                        "Manga Tracker",
                        "A title with that name already exists; opened it instead.",
                    )
                    return
            else:
                entry = self.store.update(self.current_id, fields)
                if entry is None:
                    messagebox.showerror("Manga Tracker", "This title no longer exists.")
                    self.add_new()
                    self.refresh_list()
                    return
        except ValueError:
            messagebox.showerror("Manga Tracker", "Another title already uses that name.")
            return

        entry = self._apply_cover(self.current_id, entry)
        self.refresh_list()
        self._load_entry(self.current_id)

    def _apply_cover(self, manga_id, entry):
        current = entry.get("cover_image")

        if self.cover_image is None:
            if current:
                try:
                    os.remove(current)
                except OSError:
                    pass
                entry = self.store.set_cover(manga_id, None)
            return entry

        source = os.path.abspath(self.cover_image)
        if current and os.path.abspath(current) == source:
            return entry

        os.makedirs(COVERS_DIR, exist_ok=True)
        extension = os.path.splitext(source)[1].lower() or ".jpg"
        destination = os.path.join(COVERS_DIR, f"{manga_id}{extension}")
        try:
            if source != os.path.abspath(destination):
                shutil.copyfile(source, destination)
        except OSError as error:
            messagebox.showerror("Manga Tracker", f"Could not copy cover image:\n{error}")
            return entry

        if current and os.path.abspath(current) != os.path.abspath(destination):
            try:
                os.remove(current)
            except OSError:
                pass

        self.cover_image = destination
        return self.store.set_cover(manga_id, destination)

    def delete_entry(self):
        if self.current_id is None:
            return
        deleted = self.store.delete(self.current_id)
        if deleted:
            cover = deleted.get("cover_image")
            if cover and os.path.isfile(cover):
                try:
                    os.remove(cover)
                except OSError:
                    pass
        self.add_new()
        self.refresh_list()

    # -- PWA ----------------------------------------------------------------

    def _configured_port(self):
        try:
            port = int(self.port_entry.get().strip())
        except ValueError:
            port = DEFAULT_PORT
            self.port_entry.delete(0, tk.END)
            self.port_entry.insert(0, str(port))
        if not 1 <= port <= 65535:
            raise ValueError("Port must be between 1 and 65535.")
        return port

    def _set_pwa_active(self, active, port=None):
        self.pwa_var.set(active)
        self._active_port = port if active else None
        self.port_entry.config(state="disabled" if active else "normal")
        if active:
            self.pwa_check.config(text=f"PWA: {_pwa_url(port)}")
        else:
            self.pwa_check.config(text="Start PWA")

    def _sync_pwa_state(self):
        try:
            port = self._configured_port()
        except ValueError:
            port = DEFAULT_PORT
        if _pwa_is_running(port):
            self._set_pwa_active(True, port)
        else:
            self._set_pwa_active(False)

    def toggle_pwa(self):
        if self.pwa_var.get():
            try:
                port = self._configured_port()
            except ValueError as error:
                messagebox.showerror("Manga Tracker", str(error))
                self._set_pwa_active(False)
                return
            save_config({"port": port})

            if not _pwa_is_running(port):
                try:
                    _start_detached_server(port)
                except OSError as error:
                    messagebox.showerror("Manga Tracker", f"Could not start the server on port {port}:\n{error}")
                    self._set_pwa_active(False)
                    return

                deadline = time.monotonic() + 6
                while time.monotonic() < deadline and not _pwa_is_running(port, timeout=0.25):
                    time.sleep(0.1)

            if not _pwa_is_running(port):
                messagebox.showerror(
                    "Manga Tracker",
                    f"Could not start the PWA server on port {port}. The port may already be in use.",
                )
                self._set_pwa_active(False)
                return
            self._set_pwa_active(True, port)
        else:
            port = self._active_port
            if port is None:
                try:
                    port = self._configured_port()
                except ValueError:
                    port = DEFAULT_PORT
            if _pwa_is_running(port):
                try:
                    _request_server_stop(port)
                except (OSError, URLError) as error:
                    messagebox.showerror("Manga Tracker", f"Could not stop the PWA server:\n{error}")
                    self._set_pwa_active(True, port)
                    return
                deadline = time.monotonic() + 4
                while time.monotonic() < deadline and _pwa_is_running(port, timeout=0.25):
                    time.sleep(0.1)
                if _pwa_is_running(port):
                    messagebox.showerror("Manga Tracker", "The PWA server did not stop.")
                    self._set_pwa_active(True, port)
                    return
            self._set_pwa_active(False)

    # -- polling ------------------------------------------------------------

    def _poll_store(self):
        self.store.check_for_changes()
        if self.store.version != self._last_version:
            self._last_version = self.store.version
            self.refresh_list()
            if self.current_id is not None and self.store.get(self.current_id) is None:
                self.add_new()
        self.master.after(2000, self._poll_store)


# ---------------------------------------------------------------------------
# entry point
# ---------------------------------------------------------------------------

def run_server(port):
    os.makedirs(COVERS_DIR, exist_ok=True)
    store = Store()
    server = None
    try:
        # Bind all interfaces so the PWA remains reachable over Tailscale.
        server = TrackerHTTPServer(("0.0.0.0", port), store)
        server.serve_forever()
    finally:
        if server is not None:
            server.server_close()
        store.close()


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--server":
        try:
            port = int(sys.argv[2])
            if not 1 <= port <= 65535:
                raise ValueError
        except ValueError:
            raise SystemExit("Server port must be an integer between 1 and 65535.")
        run_server(port)
        return

    os.makedirs(COVERS_DIR, exist_ok=True)
    store = Store()
    root = tk.Tk()
    MangaTracker(root, store)
    try:
        root.mainloop()
    finally:
        store.close()


if __name__ == "__main__":
    main()
