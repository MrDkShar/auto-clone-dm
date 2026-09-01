import asyncio
import csv
import hashlib
import hmac
import io
import json
import logging
import os
import re
import secrets
import shutil
import sqlite3
import threading
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Optional

from dotenv import load_dotenv
from aiohttp import web
from telegram import (
    BotCommand,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputFile,
    MessageEntity,
    Update,
)
from telegram.error import (
    BadRequest,
    Forbidden,
    NetworkError,
    RetryAfter,
    TelegramError,
    TimedOut,
)
from telegram.ext import (
    Application,
    ApplicationBuilder,
    CallbackQueryHandler,
    ChatJoinRequestHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ============================================================
# CONFIG
# ============================================================

load_dotenv()

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
OWNER_ID_RAW = os.getenv("OWNER_ID", "").strip()
DATABASE_URL = os.getenv("DATABASE_URL", "sqlite:///bot_data.db").strip()

if not BOT_TOKEN:
    raise RuntimeError("BOT_TOKEN is missing.")

try:
    OWNER_ID = int(OWNER_ID_RAW)
except (TypeError, ValueError):
    raise RuntimeError("OWNER_ID must be a numeric Telegram user ID.")

if DATABASE_URL.startswith("sqlite:///"):
    DB_PATH = Path(DATABASE_URL[len("sqlite:///"):])
elif DATABASE_URL.startswith("sqlite://"):
    DB_PATH = Path(DATABASE_URL[len("sqlite://"):])
else:
    raise RuntimeError(
        "This build supports SQLite only. Set DATABASE_URL=sqlite:///bot_data.db"
    )

DB_PATH.parent.mkdir(parents=True, exist_ok=True)
BACKUP_DIR = DB_PATH.parent / "backups"
BACKUP_DIR.mkdir(parents=True, exist_ok=True)

# Directory holding every child bot's isolated SQLite file.
CHILD_DB_DIR = DB_PATH.parent / "child_data"
CHILD_DB_DIR.mkdir(parents=True, exist_ok=True)

RENDER_EXTERNAL_URL = os.getenv("RENDER_EXTERNAL_URL", "").strip().rstrip("/")
try:
    RENDER_PORT = int(os.getenv("PORT", "10000"))
except (TypeError, ValueError):
    RENDER_PORT = 10000
WEBHOOK_PATH = os.getenv("WEBHOOK_PATH", f"telegram-{BOT_TOKEN.split(':', 1)[0]}").strip("/")
WEBHOOK_SECRET = os.getenv("WEBHOOK_SECRET", "").strip()

try:
    HEALTH_PORT = int(os.getenv("HEALTH_PORT", str(RENDER_PORT + 1)))
except (TypeError, ValueError):
    HEALTH_PORT = RENDER_PORT + 1

MAX_RETRIES = 3
BROADCAST_DELAY = 0.08
JOIN_REQUEST_ACTION_DELAY = 0.08
MAX_BUTTONS = 100
MAX_TEXT_LENGTH = 4096
MAX_CAPTION_LENGTH = 1024

AUTO_BACKUP_INTERVAL_SECONDS_DEFAULT = 6 * 60 * 60
AUTO_BACKUP_LOCAL_RETENTION = 10

BACKUP_INTERVAL_CHOICES = {
    "1h": 1 * 60 * 60,
    "6h": 6 * 60 * 60,
    "12h": 12 * 60 * 60,
    "24h": 24 * 60 * 60,
    "off": 0,
}

CUSTOM_EMOJI_ENTITY_TYPE = "custom_emoji"
BUTTON_STYLES = ("primary", "success", "danger")

# Multi-bot limits and master encryption secret.
try:
    MAX_CHILD_BOTS = int(os.getenv("MAX_CHILD_BOTS", "20"))
except (TypeError, ValueError):
    MAX_CHILD_BOTS = 20
MULTIBOT_SECRET = os.getenv("MULTIBOT_SECRET", "").strip()

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
logger = logging.getLogger("multi_bot_manager")
# httpx/httpcore can log request URLs at INFO; Telegram bot tokens may appear in
# those URLs, so keep transport request logging above INFO in production.
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("httpcore").setLevel(logging.WARNING)


# ============================================================
# HEALTH ENDPOINT (polling-mode fallback only)
# ============================================================
# In webhook mode the MultiBotWebhookServer below serves /health on the SAME
# public port as every bot webhook. This threaded server is only used in
# polling mode (no RENDER_EXTERNAL_URL), where PTB binds no port at all.

class _HealthHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path in ("/", "/health"):
            body = b"ok"
            self.send_response(200)
            self.send_header("Content-Type", "text/plain")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        else:
            self.send_response(404)
            self.end_headers()

    def log_message(self, format, *args):  # noqa: A002
        pass


def start_health_server() -> Optional[ThreadingHTTPServer]:
    try:
        server = ThreadingHTTPServer(("0.0.0.0", HEALTH_PORT), _HealthHandler)
    except OSError as exc:
        logger.warning("Health server could not bind port %s: %s", HEALTH_PORT, exc)
        return None
    thread = threading.Thread(target=server.serve_forever, name="health-server", daemon=True)
    thread.start()
    logger.info("Health endpoint listening on 0.0.0.0:%s (GET /health)", HEALTH_PORT)
    return server


# ============================================================
# HELPERS
# ============================================================

def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def safe_int(value, default=0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def valid_http_url(url: str) -> bool:
    return bool(
        re.fullmatch(
            r"https?://[^\s]+",
            url.strip(),
            flags=re.IGNORECASE,
        )
    )


def parse_json(value, fallback):
    try:
        return json.loads(value)
    except (TypeError, ValueError, json.JSONDecodeError):
        return fallback


_TOKEN_RE = re.compile(r"\b\d{6,12}:[A-Za-z0-9_-]{30,}\b")

def clean_error(exc: Exception) -> str:
    """Return an exception string with Telegram bot tokens redacted."""
    text = str(exc)
    if BOT_TOKEN:
        text = text.replace(BOT_TOKEN, "[REDACTED_TOKEN]")
    text = _TOKEN_RE.sub("[REDACTED_TOKEN]", text)
    return text[:4000]


def normalize_button_style(style: Optional[str]) -> str:
    style = (style or "primary").strip().lower()
    return style if style in BUTTON_STYLES else "primary"


# ============================================================
# TOKEN ENCRYPTION (at-rest, dependency-free)
# ============================================================
# Child bot tokens are NEVER stored in plaintext. We derive a 32-byte key from
# the master secret (env MULTIBOT_SECRET, or BOT_TOKEN as a last resort) using
# PBKDF2-HMAC-SHA256, then encrypt with an HMAC-keystream stream cipher
# (encrypt-then-MAC). The salt is stored alongside each ciphertext so rekeys
# remain possible. Tokens are NEVER logged, NEVER shown in the UI, NEVER
# included in exports or audit logs, NEVER sent in webhook URLs.

def _master_key_material() -> bytes:
    base = MULTIBOT_SECRET or BOT_TOKEN
    return (base + "|multibot-token-vault").encode("utf-8")


def _derive_key(salt: bytes) -> bytes:
    return hashlib.pbkdf2_hmac("sha256", _master_key_material(), salt, 200_000, dklen=32)


def encrypt_token(plaintext: str) -> str:
    """Return a self-contained 'salt$ciphertext$mac' string."""
    if not plaintext:
        return ""
    salt = secrets.token_bytes(16)
    key = _derive_key(salt)
    data = plaintext.encode("utf-8")
    # Keystream: chained HMAC-SHA256 over a counter, XORed with data.
    out = bytearray()
    counter = 0
    block = b""
    pos = 0
    while pos < len(data):
        if not block:
            block = hmac.new(key, counter.to_bytes(8, "big"), hashlib.sha256).digest()
            counter += 1
        out.append(data[pos] ^ block[0])
        block = block[1:]
        pos += 1
    mac = hmac.new(key, bytes(out), hashlib.sha256).hexdigest()
    return f"{salt.hex()}${bytes(out).hex()}${mac}"


def decrypt_token(blob: str) -> str:
    if not blob:
        return ""
    try:
        salt_hex, ct_hex, mac = blob.split("$")
        salt = bytes.fromhex(salt_hex)
        ct = bytes.fromhex(ct_hex)
    except (ValueError, AttributeError):
        return ""
    key = _derive_key(salt)
    expected_mac = hmac.new(key, ct, hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected_mac, mac):
        logger.warning("Token decryption failed (MAC mismatch); token may have been rekeyed.")
        return ""
    out = bytearray()
    counter = 0
    block = b""
    pos = 0
    while pos < len(ct):
        if not block:
            block = hmac.new(key, counter.to_bytes(8, "big"), hashlib.sha256).digest()
            counter += 1
        out.append(ct[pos] ^ block[0])
        block = block[1:]
        pos += 1
    return out.decode("utf-8", errors="ignore")


# ============================================================
# DATABASE  (reusable per BotInstance)
# ============================================================
# Each BotInstance owns a Database(path). The schema is identical for the main
# bot and every child bot, so all existing functionality works unchanged on a
# child bot's own database. The MAIN bot's database additionally carries the
# child_bots + master_audit tables (created only on the main instance).

MAIN_BOT_ID = 1  # Logical id used for the main bot's own records.

class Database:
    def __init__(self, path: Path, is_main: bool = False):
        self.path = path
        self.is_main = is_main
        self.conn: Optional[sqlite3.Connection] = None
        self.connect_lock = asyncio.Lock()

    def connect(self):
        if self.conn is not None:
            return
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(self.path), timeout=30, check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA synchronous=NORMAL")
        self.conn.execute("PRAGMA foreign_keys=ON")
        self.conn.execute("PRAGMA busy_timeout=30000")
        self.create_schema()
        self.seed_defaults()

    def close(self):
        if self.conn is not None:
            try:
                self.conn.commit()
            except Exception:
                pass
            try:
                self.conn.close()
            except Exception:
                logger.exception("Database close failed")
            finally:
                self.conn = None

    def execute(self, query, params=(), commit=False):
        self.connect()
        cursor = self.conn.execute(query, params)
        if commit:
            self.conn.commit()
        return cursor

    def executemany(self, query, rows, commit=False):
        self.connect()
        cursor = self.conn.executemany(query, rows)
        if commit:
            self.conn.commit()
        return cursor

    def fetchone(self, query, params=()):
        return self.execute(query, params).fetchone()

    def fetchall(self, query, params=()):
        return self.execute(query, params).fetchall()

    def create_schema(self):
        self.conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                username TEXT,
                first_name TEXT,
                last_name TEXT,
                language_code TEXT,
                is_bot INTEGER NOT NULL DEFAULT 0,
                is_blocked INTEGER NOT NULL DEFAULT 0,
                first_seen TEXT NOT NULL,
                last_seen TEXT NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_users_last_seen ON users(last_seen);

            CREATE TABLE IF NOT EXISTS admins (
                user_id INTEGER PRIMARY KEY,
                role TEXT NOT NULL DEFAULT 'admin',
                permissions TEXT NOT NULL DEFAULT '{}',
                created_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS channels (
                channel_id INTEGER PRIMARY KEY,
                username TEXT,
                title TEXT,
                type TEXT,
                enabled INTEGER NOT NULL DEFAULT 1,
                required INTEGER NOT NULL DEFAULT 1,
                auto_approve INTEGER NOT NULL DEFAULT 0,
                sort_order INTEGER NOT NULL DEFAULT 0,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS bot_settings (
                key TEXT PRIMARY KEY,
                value TEXT
            );

            CREATE TABLE IF NOT EXISTS messages (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL UNIQUE,
                media_type TEXT NOT NULL DEFAULT 'none',
                file_id TEXT,
                caption TEXT NOT NULL DEFAULT '',
                parse_mode TEXT NOT NULL DEFAULT 'HTML',
                enabled INTEGER NOT NULL DEFAULT 1,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS message_buttons (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                message_id INTEGER NOT NULL,
                text TEXT NOT NULL,
                url TEXT NOT NULL,
                style TEXT NOT NULL DEFAULT 'primary',
                icon_custom_emoji_id TEXT,
                row_number INTEGER NOT NULL DEFAULT 0,
                position INTEGER NOT NULL DEFAULT 0,
                enabled INTEGER NOT NULL DEFAULT 1,
                FOREIGN KEY(message_id) REFERENCES messages(id) ON DELETE CASCADE
            );
            CREATE INDEX IF NOT EXISTS idx_message_buttons_message ON message_buttons(message_id);

            CREATE TABLE IF NOT EXISTS join_requests (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                channel_id INTEGER NOT NULL,
                requested_at TEXT NOT NULL,
                message_sent INTEGER NOT NULL DEFAULT 0,
                message_sent_at TEXT,
                error TEXT,
                status TEXT NOT NULL DEFAULT 'received',
                event_key TEXT UNIQUE,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            );
            CREATE INDEX IF NOT EXISTS idx_join_requests_user ON join_requests(user_id);
            CREATE INDEX IF NOT EXISTS idx_join_requests_channel ON join_requests(channel_id);
            CREATE INDEX IF NOT EXISTS idx_join_requests_requested ON join_requests(requested_at);

            CREATE TABLE IF NOT EXISTS broadcasts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                admin_id INTEGER NOT NULL,
                text TEXT,
                media_type TEXT NOT NULL DEFAULT 'none',
                file_id TEXT,
                caption TEXT,
                parse_mode TEXT NOT NULL DEFAULT 'HTML',
                source_chat_id INTEGER,
                source_message_id INTEGER,
                entities_json TEXT NOT NULL DEFAULT '[]',
                buttons_json TEXT NOT NULL DEFAULT '[]',
                staged_media_path TEXT,
                status TEXT NOT NULL DEFAULT 'pending',
                total INTEGER NOT NULL DEFAULT 0,
                sent INTEGER NOT NULL DEFAULT 0,
                failed INTEGER NOT NULL DEFAULT 0,
                blocked INTEGER NOT NULL DEFAULT 0,
                next_user_id INTEGER,
                created_at TEXT NOT NULL,
                started_at TEXT,
                finished_at TEXT
            );

            CREATE TABLE IF NOT EXISTS broadcast_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                broadcast_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                status TEXT,
                error TEXT,
                created_at TEXT NOT NULL,
                UNIQUE(broadcast_id, user_id),
                FOREIGN KEY(broadcast_id) REFERENCES broadcasts(id) ON DELETE CASCADE
            );
            CREATE INDEX IF NOT EXISTS idx_broadcast_logs_broadcast ON broadcast_logs(broadcast_id);

            CREATE TABLE IF NOT EXISTS bot_events (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                event_type TEXT,
                user_id INTEGER,
                channel_id INTEGER,
                details TEXT,
                created_at TEXT NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_bot_events_created ON bot_events(created_at);

            CREATE TABLE IF NOT EXISTS error_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                level TEXT,
                module TEXT,
                event TEXT,
                exception TEXT,
                created_at TEXT NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_error_logs_created ON error_logs(created_at);

            CREATE TABLE IF NOT EXISTS backups (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                filename TEXT,
                created_at TEXT NOT NULL,
                created_by INTEGER,
                size INTEGER
            );
            """
        )
        # Schema upgrades (preserved from original).
        for stmt in (
            "ALTER TABLE message_buttons ADD COLUMN style TEXT NOT NULL DEFAULT 'primary'",
            "ALTER TABLE message_buttons ADD COLUMN icon_custom_emoji_id TEXT",
            "ALTER TABLE channels ADD COLUMN auto_approve INTEGER NOT NULL DEFAULT 0",
        ):
            try:
                self.conn.execute(stmt)
                self.conn.commit()
            except sqlite3.OperationalError:
                pass
        for col in (
            "source_chat_id INTEGER",
            "source_message_id INTEGER",
            "entities_json TEXT NOT NULL DEFAULT '[]'",
        ):
            try:
                self.conn.execute(f"ALTER TABLE broadcasts ADD COLUMN {col}")
                self.conn.commit()
            except sqlite3.OperationalError:
                pass

        if self.is_main:
            try:
                self.conn.execute("ALTER TABLE child_bots ADD COLUMN created_by INTEGER")
                self.conn.commit()
            except sqlite3.OperationalError:
                pass

        # Multi-bot registry tables — main bot only.
        if self.is_main:
            self.conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS child_bots (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    bot_id INTEGER UNIQUE NOT NULL,
                    username TEXT,
                    display_name TEXT,
                    encrypted_token TEXT NOT NULL,
                    admin_id INTEGER NOT NULL,
                    status TEXT NOT NULL DEFAULT 'stopped',
                    enabled INTEGER NOT NULL DEFAULT 1,
                    webhook_path TEXT NOT NULL,
                    webhook_secret TEXT,
                    last_seen TEXT,
                    last_error TEXT,
                    created_at TEXT NOT NULL,
                    created_by INTEGER,
                    deleted INTEGER NOT NULL DEFAULT 0
                );
                CREATE INDEX IF NOT EXISTS idx_child_bots_status ON child_bots(status);

                CREATE TABLE IF NOT EXISTS bot_creators (
                    user_id INTEGER PRIMARY KEY,
                    granted_by INTEGER NOT NULL,
                    created_at TEXT NOT NULL,
                    max_bots INTEGER NOT NULL DEFAULT 1
                );
                CREATE INDEX IF NOT EXISTS idx_bot_creators_created_at ON bot_creators(created_at);

                CREATE TABLE IF NOT EXISTS master_audit (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    main_admin_id INTEGER,
                    child_bot_id INTEGER,
                    action TEXT NOT NULL,
                    result TEXT,
                    error TEXT,
                    created_at TEXT NOT NULL
                );
                CREATE INDEX IF NOT EXISTS idx_master_audit_created ON master_audit(created_at);
                """
            )
            try:
                self.conn.execute("ALTER TABLE bot_creators ADD COLUMN max_bots INTEGER NOT NULL DEFAULT 1")
                self.conn.commit()
            except sqlite3.OperationalError:
                pass
            try:
                self.conn.execute("ALTER TABLE broadcasts ADD COLUMN staged_media_path TEXT")
                self.conn.commit()
            except sqlite3.OperationalError:
                pass

        self.conn.commit()

    def seed_defaults(self):
        now = utc_now()
        defaults = {
            "maintenance_mode": "0",
            "auto_message_enabled": "1",
            # New additive feature. Disabled by default so existing behavior
            # remains unchanged after deployment.
            "auto_member_enabled": "0",
            "start_message": "Please join our channel to continue.",
            "start_button_text": "JOIN NOW",
            "start_button_style": "primary",
            "check_join_enabled": "0",
            "bot_name": "Join Request Bot",
            "join_msg_source_entities": "[]",
            "backup_channel_id": "",
            "backup_channel_username": "",
            "backup_channel_title": "",
            "backup_channel_enabled": "0",
            "backup_interval_seconds": str(AUTO_BACKUP_INTERVAL_SECONDS_DEFAULT),
        }
        for key, value in defaults.items():
            self.execute(
                "INSERT OR IGNORE INTO bot_settings(key, value) VALUES (?, ?)",
                (key, value),
            )
        # The main bot seeds OWNER_ID as owner; a child bot seeds its own
        # admin_id as owner. main_admin_id is supplied by BotInstance.
        owner_id = OWNER_ID if self.is_main else getattr(self, "_seed_admin_id", 0)
        if owner_id:
            self.execute(
                """
                INSERT OR IGNORE INTO admins(user_id, role, permissions, created_at)
                VALUES (?, 'owner', ?, ?)
                """,
                (owner_id, json.dumps({"all": True}), now),
            )
        self.conn.commit()

    # ---- settings ----
    def get_setting(self, key, default=""):
        row = self.fetchone("SELECT value FROM bot_settings WHERE key=?", (key,))
        return row["value"] if row else default

    def set_setting(self, key, value):
        self.execute(
            """
            INSERT INTO bot_settings(key,value) VALUES(?,?)
            ON CONFLICT(key) DO UPDATE SET value=excluded.value
            """,
            (key, str(value)),
            commit=True,
        )

    # ---- users ----
    def upsert_user(self, user):
        now = utc_now()
        self.execute(
            """
            INSERT INTO users(
                user_id, username, first_name, last_name,
                language_code, is_bot, first_seen, last_seen
            ) VALUES(?,?,?,?,?,?,?,?)
            ON CONFLICT(user_id) DO UPDATE SET
                username=excluded.username,
                first_name=excluded.first_name,
                last_name=excluded.last_name,
                language_code=excluded.language_code,
                is_bot=excluded.is_bot,
                last_seen=excluded.last_seen
            """,
            (
                user.id, user.username, user.first_name, user.last_name,
                user.language_code, int(bool(user.is_bot)), now, now,
            ),
            commit=True,
        )

    # ---- join requests ----
    def save_join_request(self, user_id, channel_id, event_key, requested_at):
        try:
            cursor = self.execute(
                """
                INSERT INTO join_requests(user_id, channel_id, requested_at, event_key)
                VALUES(?,?,?,?)
                """,
                (user_id, channel_id, requested_at, event_key),
                commit=True,
            )
            return cursor.lastrowid
        except sqlite3.IntegrityError:
            return None

    def update_join_request(self, row_id, sent, status, error=None):
        self.execute(
            """
            UPDATE join_requests
            SET message_sent=?, message_sent_at=?, status=?, error=?
            WHERE id=?
            """,
            (int(bool(sent)), utc_now() if sent else None, status, error, row_id),
            commit=True,
        )

    # ---- events / errors ----
    def log_event(self, event_type, user_id=None, channel_id=None, details=""):
        self.execute(
            """
            INSERT INTO bot_events(event_type,user_id,channel_id,details,created_at)
            VALUES(?,?,?,?,?)
            """,
            (event_type, user_id, channel_id, str(details)[:4000], utc_now()),
            commit=True,
        )

    def log_error(self, level, module, event, exception):
        try:
            self.execute(
                """
                INSERT INTO error_logs(level,module,event,exception,created_at)
                VALUES(?,?,?,?,?)
                """,
                (level, module, event, str(exception)[:4000], utc_now()),
                commit=True,
            )
        except Exception:
            logger.exception("Could not save error log")

    # ---- messages ----
    def ensure_message_row(self, name: str):
        now = utc_now()
        self.execute(
            """
            INSERT OR IGNORE INTO messages(
                name,media_type,file_id,caption,parse_mode,enabled,created_at,updated_at
            ) VALUES(?,'none','','','HTML',1,?,?)
            """,
            (name, now, now),
            commit=True,
        )

    def get_message_by_name(self, name: str):
        self.ensure_message_row(name)
        return self.fetchone("SELECT * FROM messages WHERE name=?", (name,))

    def ensure_join_message(self):
        self.ensure_message_row("join_request")

    def get_join_message(self):
        return self.get_message_by_name("join_request")

    def get_start_message(self):
        return self.get_message_by_name("start")

    def get_message_buttons(self, message_id):
        return self.fetchall(
            """
            SELECT * FROM message_buttons
            WHERE message_id=? AND enabled=1
            ORDER BY row_number, position, id
            """,
            (message_id,),
        )

    def clear_message_buttons(self, message_id):
        self.execute("DELETE FROM message_buttons WHERE message_id=?", (message_id,), commit=True)

    def add_message_button(self, message_id, text, url, row_number, position,
                           style="primary", icon_custom_emoji_id=None):
        self.execute(
            """
            INSERT INTO message_buttons(
                message_id,text,url,style,icon_custom_emoji_id,row_number,position,enabled
            ) VALUES(?,?,?,?,?,?,?,1)
            """,
            (
                message_id, text, url,
                style if style in BUTTON_STYLES else "primary",
                str(icon_custom_emoji_id) if icon_custom_emoji_id else None,
                row_number, position,
            ),
            commit=True,
        )

    # ---- channels ----
    def get_channels(self, enabled_only=False):
        if enabled_only:
            return self.fetchall(
                "SELECT * FROM channels WHERE enabled=1 ORDER BY sort_order, title"
            )
        return self.fetchall("SELECT * FROM channels ORDER BY sort_order, title")

    # ---- stats ----
    def stats(self):
        queries = {
            "users": "SELECT COUNT(*) c FROM users",
            "active": "SELECT COUNT(*) c FROM users WHERE is_blocked=0",
            "blocked": "SELECT COUNT(*) c FROM users WHERE is_blocked=1",
            "requests": "SELECT COUNT(*) c FROM join_requests",
            "today": "SELECT COUNT(*) c FROM join_requests WHERE date(requested_at)=date('now')",
            "week": "SELECT COUNT(*) c FROM join_requests WHERE requested_at >= datetime('now','-7 days')",
            "month": "SELECT COUNT(*) c FROM join_requests WHERE requested_at >= datetime('now','-30 days')",
            "sent": "SELECT COUNT(*) c FROM join_requests WHERE message_sent=1",
            "failed": "SELECT COUNT(*) c FROM join_requests WHERE status='failed'",
            "channels": "SELECT COUNT(*) c FROM channels",
            "broadcasts": "SELECT COUNT(*) c FROM broadcasts",
        }
        result = {}
        for key, query in queries.items():
            row = self.fetchone(query)
            result[key] = int(row["c"]) if row else 0
        return result

    # ---- master audit (main bot only) ----
    def log_master_audit(self, main_admin_id, child_bot_id, action, result="ok", error=""):
        if not self.is_main:
            return
        self.execute(
            """
            INSERT INTO master_audit(main_admin_id,child_bot_id,action,result,error,created_at)
            VALUES(?,?,?,?,?,?)
            """,
            (main_admin_id, child_bot_id, action, result, str(error)[:4000], utc_now()),
            commit=True,
        )

    # ---- child bot registry (main bot only) ----
    def list_child_bots(self, include_deleted=False):
        if not self.is_main:
            return []
        if include_deleted:
            return self.fetchall("SELECT * FROM child_bots ORDER BY id")
        return self.fetchall("SELECT * FROM child_bots WHERE deleted=0 ORDER BY id")

    def get_child_bot(self, bot_id):
        if not self.is_main:
            return None
        return self.fetchone("SELECT * FROM child_bots WHERE bot_id=? AND deleted=0", (bot_id,))

    def upsert_child_bot(self, bot_id, username, display_name, encrypted_token,
                         admin_id, webhook_path, webhook_secret, status="stopped",
                         created_by: Optional[int] = None):
        now = utc_now()
        self.execute(
            """
            INSERT INTO child_bots(
                bot_id, username, display_name, encrypted_token, admin_id,
                status, enabled, webhook_path, webhook_secret, created_at, last_seen, created_by
            ) VALUES(?,?,?,?,?,?,1,?,?,?,?,?)
            ON CONFLICT(bot_id) DO UPDATE SET
                username=excluded.username, display_name=excluded.display_name,
                encrypted_token=excluded.encrypted_token, admin_id=excluded.admin_id,
                webhook_path=excluded.webhook_path, webhook_secret=excluded.webhook_secret,
                created_by=COALESCE(child_bots.created_by, excluded.created_by), deleted=0
            """,
            (bot_id, username, display_name, encrypted_token, admin_id, status,
             webhook_path, webhook_secret, now, now, created_by), commit=True,
        )

    def set_child_bot_status(self, bot_id, status, last_error=""):
        self.execute(
            "UPDATE child_bots SET status=?, last_error=?, last_seen=? WHERE bot_id=?",
            (status, str(last_error)[:1000], utc_now(), bot_id), commit=True,
        )

    def add_bot_creator(self, user_id: int, granted_by: int, max_bots: int = 1):
        max_bots = max(1, int(max_bots or 1))
        self.execute(
            "INSERT INTO bot_creators(user_id,granted_by,created_at,max_bots) VALUES(?,?,?,?) "
            "ON CONFLICT(user_id) DO UPDATE SET granted_by=excluded.granted_by,max_bots=excluded.max_bots",
            (user_id, granted_by, utc_now(), max_bots), commit=True,
        )

    def remove_bot_creator(self, user_id: int):
        self.execute("DELETE FROM bot_creators WHERE user_id=?", (user_id,), commit=True)

    def set_bot_creator_limit(self, user_id: int, max_bots: int):
        max_bots = max(1, int(max_bots or 1))
        self.execute("UPDATE bot_creators SET max_bots=? WHERE user_id=?", (max_bots, user_id), commit=True)

    def get_bot_creator(self, user_id: Optional[int]):
        if not self.is_main or not user_id:
            return None
        return self.fetchone(
            "SELECT user_id,granted_by,created_at,max_bots FROM bot_creators WHERE user_id=?",
            (user_id,),
        )

    def get_bot_creator_limit(self, user_id: Optional[int], default: int = 1) -> int:
        row = self.get_bot_creator(user_id)
        return max(1, safe_int(row["max_bots"], default)) if row else default

    def count_bots_created_by(self, user_id: Optional[int]) -> int:
        if not self.is_main or not user_id:
            return 0
        row = self.fetchone(
            "SELECT COUNT(*) AS c FROM child_bots WHERE created_by=? AND deleted=0",
            (user_id,),
        )
        return int(row["c"]) if row else 0

    def is_bot_creator(self, user_id: Optional[int]) -> bool:
        return bool(self.get_bot_creator(user_id))

    def list_bot_creators(self):
        if not self.is_main:
            return []
        return self.fetchall(
            "SELECT user_id,granted_by,created_at,max_bots FROM bot_creators ORDER BY created_at,user_id"
        )

    def set_child_bot_admin(self, bot_id, admin_id):
        self.execute(
            "UPDATE child_bots SET admin_id=? WHERE bot_id=? AND deleted=0",
            (admin_id, bot_id),
            commit=True,
        )

    def reset_bot_owner_admin(self, owner_id: int):
        # Revoke only prior owner rows; preserve any explicitly configured
        # non-owner admin accounts and their permissions.
        self.execute("DELETE FROM admins WHERE role='owner' AND user_id!=?", (owner_id,), commit=True)
        self.execute(
            """INSERT INTO admins(user_id,role,permissions,created_at)
               VALUES(?, 'owner', ?, ?)
               ON CONFLICT(user_id) DO UPDATE SET role='owner', permissions=excluded.permissions""",
            (owner_id, json.dumps({"all": True}), utc_now()), commit=True,
        )

    def soft_delete_child_bot(self, bot_id):
        self.execute(
            "UPDATE child_bots SET deleted=1, status='deleted', enabled=0 WHERE bot_id=?",
            (bot_id,),
            commit=True,
        )

    def count_child_bots(self):
        row = self.fetchone("SELECT COUNT(*) c FROM child_bots WHERE deleted=0")
        return int(row["c"]) if row else 0



# ============================================================
# ACCESS CONTROL  (per-BotInstance)
# ============================================================

def is_admin_for(db: Database, user_id: Optional[int]) -> bool:
    if not user_id:
        return False
    row = db.fetchone("SELECT role,permissions FROM admins WHERE user_id=?", (user_id,))
    if not row:
        return False
    if row["role"] == "owner":
        return True
    permissions = parse_json(row["permissions"], {})
    return bool(permissions.get("all") or any(bool(v) for v in permissions.values()))


def is_owner_for(db: Database, user_id: Optional[int], owner_id: int) -> bool:
    return bool(user_id and user_id == owner_id)


# ============================================================
# KEYBOARDS
# ============================================================

def _make_inline_button(text: str, url: str, style: Optional[str] = None,
                        icon_custom_emoji_id: Optional[str] = None) -> InlineKeyboardButton:
    kwargs = {"text": text[:64], "url": url, "style": normalize_button_style(style)}
    if icon_custom_emoji_id:
        kwargs["icon_custom_emoji_id"] = str(icon_custom_emoji_id)
    return InlineKeyboardButton(**kwargs)


def _make_callback_button(text: str, callback_data: str, style: Optional[str] = None,
                          icon_custom_emoji_id: Optional[str] = None) -> InlineKeyboardButton:
    kwargs = {"text": text[:64], "callback_data": callback_data, "style": normalize_button_style(style)}
    if icon_custom_emoji_id:
        kwargs["icon_custom_emoji_id"] = str(icon_custom_emoji_id)
    return InlineKeyboardButton(**kwargs)


def build_keyboard(buttons):
    if not isinstance(buttons, list):
        return None
    rows = {}
    for index, button in enumerate(buttons[:MAX_BUTTONS]):
        if not isinstance(button, dict):
            continue
        text = str(button.get("text", "")).strip()
        url = str(button.get("url", "")).strip()
        if not text or not valid_http_url(url):
            continue
        style = normalize_button_style(button.get("style", "primary"))
        icon_id = str(button.get("icon_custom_emoji_id", "") or "").strip() or None
        row = max(0, safe_int(button.get("row", 0), 0))
        position = max(0, safe_int(button.get("position", index), index))
        rows.setdefault(row, []).append((position, _make_inline_button(text, url, style, icon_id)))
    keyboard_rows = []
    for row_number in sorted(rows):
        keyboard_rows.append([b for _, b in sorted(rows[row_number], key=lambda i: i[0])])
    return InlineKeyboardMarkup(keyboard_rows) if keyboard_rows else None


def start_keyboard(db: Database):
    rows = []
    button_text = db.get_setting("start_button_text", "JOIN NOW")
    button_style = db.get_setting("start_button_style", "primary")
    for channel in db.get_channels(enabled_only=True):
        username = (channel["username"] or "").lstrip("@")
        if username:
            url = f"https://t.me/{username}"
        else:
            url = db.get_setting(f"channel_url_{channel['channel_id']}", "")
        if url and valid_http_url(url):
            rows.append([_make_inline_button(button_text[:64], url, button_style)])
    if db.get_setting("check_join_enabled", "0") == "1":
        rows.append([_make_callback_button("I HAVE JOINED", "check_join", "success")])
    return InlineKeyboardMarkup(rows) if rows else None


def admin_menu(is_main: bool = False):
    rows = [
        [_make_callback_button("📊 Dashboard", "admin_dashboard", "primary"),
         _make_callback_button("⚙️ Settings", "admin_settings", "primary")],
        [_make_callback_button("📩 Join Request", "admin_join", "primary"),
         _make_callback_button("💬 Message Builder", "admin_message", "primary")],
        [_make_callback_button("🚀 Start Message", "admin_start_msg", "primary")],
        [_make_callback_button("📢 Channels", "admin_channels", "primary"),
         _make_callback_button("👥 Users", "admin_users", "primary")],
        [_make_callback_button("📢 Broadcast", "admin_broadcast", "primary"),
         _make_callback_button("📈 Statistics", "admin_stats", "primary")],
        [_make_callback_button("💾 Backup", "admin_backup", "primary"),
         _make_callback_button("📤 Export", "admin_export", "primary")],
        [_make_callback_button("☁️ Backup Channel", "admin_backup_channel", "primary")],
        [_make_callback_button("🧪 Test Message", "admin_test", "success"),
         _make_callback_button("📝 Logs", "admin_logs", "danger")],
        [_make_callback_button("🔐 Admins", "admin_admins", "primary")],
    ]
    if is_main:
        rows.append([_make_callback_button("👤 Bot Creators", "bot_creators", "primary")])
    # Only the MAIN bot's owner sees the Bot Manager entry.
    if is_main:
        rows.append([_make_callback_button("🤖 Bot Manager", "bot_manager", "primary")])
    return InlineKeyboardMarkup(rows)


def back_keyboard():
    return InlineKeyboardMarkup([[_make_callback_button("⬅️ Back", "admin_home", "primary")]])


# ============================================================
# TEMPLATE + ENTITY HELPERS
# ============================================================

USERNAME_PLACEHOLDERS = ("{Username}", "{username}", "{UserName}", "{USERNAME}")


def display_name_for_user(user) -> str:
    first_name = (getattr(user, "first_name", None) or "").strip()
    if first_name:
        return first_name
    username = (getattr(user, "username", None) or "").strip().lstrip("@")
    if username:
        return f"@{username}"
    return "there"


def serialize_message_entities(entities) -> str:
    result = []
    for entity in entities or ():
        try:
            entity_type = getattr(entity, "type", None)
            offset = int(getattr(entity, "offset", 0))
            length = int(getattr(entity, "length", 0))
        except (TypeError, ValueError):
            continue
        if not entity_type or length <= 0:
            continue
        data = {"type": entity_type, "offset": offset, "length": length}
        for key in ("url", "language", "custom_emoji_id", "date_time_format"):
            value = getattr(entity, key, None)
            if value is not None:
                data[key] = value
        entity_user = getattr(entity, "user", None)
        if entity_user is not None:
            try:
                data["user"] = entity_user.to_dict()
            except Exception:
                pass
        unix_time = getattr(entity, "unix_time", None)
        if unix_time is not None:
            try:
                data["unix_time"] = unix_time.isoformat()
            except AttributeError:
                pass
        result.append(data)
    return json.dumps(result, ensure_ascii=False, separators=(",", ":"))


def count_custom_emoji(entities) -> int:
    return sum(1 for e in (entities or ()) if getattr(e, "type", "") == CUSTOM_EMOJI_ENTITY_TYPE)


def deserialize_message_entities(value: str, bot=None):
    raw = parse_json(value, [])
    if not isinstance(raw, list):
        return []
    entities = []
    for data in raw:
        if not isinstance(data, dict):
            continue
        try:
            entity_type = str(data.get("type", ""))
            offset = int(data.get("offset", 0))
            length = int(data.get("length", 0))
            if not entity_type or length <= 0 or offset < 0:
                continue
            kwargs = {"type": entity_type, "offset": offset, "length": length}
            for key in ("url", "language", "custom_emoji_id", "date_time_format"):
                if data.get(key) is not None:
                    kwargs[key] = data[key]
            try:
                entity = MessageEntity(**kwargs)
            except TypeError:
                kwargs.pop("date_time_format", None)
                try:
                    entity = MessageEntity(**kwargs)
                except TypeError:
                    minimal = {"type": entity_type, "offset": offset, "length": length}
                    if entity_type == CUSTOM_EMOJI_ENTITY_TYPE and data.get("custom_emoji_id") is not None:
                        minimal["custom_emoji_id"] = str(data["custom_emoji_id"])
                    for key in ("url", "language"):
                        if data.get(key) is not None:
                            minimal[key] = data[key]
                    entity = MessageEntity(**minimal)
            if entity_type == CUSTOM_EMOJI_ENTITY_TYPE:
                custom_id = getattr(entity, "custom_emoji_id", None)
                if not custom_id:
                    logger.warning("Skipping custom_emoji entity without custom_emoji_id: %r", data)
                    continue
            entities.append(entity)
        except Exception:
            logger.exception("Could not restore message entity: %r", data)
    return entities


def _utf16_len(value: str) -> int:
    return len(value.encode("utf-16-le")) // 2


def render_template_with_entities(text: str, entities, user):
    if not text:
        return text, list(entities or [])
    replacement = display_name_for_user(user)
    matches = []
    for placeholder in USERNAME_PLACEHOLDERS:
        start = 0
        while True:
            pos = text.find(placeholder, start)
            if pos < 0:
                break
            matches.append((pos, pos + len(placeholder), replacement))
            start = pos + len(placeholder)
    if not matches:
        return text, list(entities or [])
    matches.sort(key=lambda i: i[0])
    pieces = []
    cursor = 0
    for start, end, value in matches:
        pieces.append(text[cursor:start])
        pieces.append(value)
        cursor = end
    pieces.append(text[cursor:])
    rendered = "".join(pieces)
    replacements_utf16 = []
    for start, end, value in matches:
        replacements_utf16.append((_utf16_len(text[:start]), _utf16_len(text[:end]), _utf16_len(value)))

    def map_offset(old_offset: int) -> int:
        delta = 0
        for old_start, old_end, new_len in replacements_utf16:
            old_len = old_end - old_start
            if old_offset >= old_end:
                delta += new_len - old_len
            elif old_offset > old_start:
                return old_start + delta + new_len
            else:
                break
        return old_offset + delta

    shifted = []
    for entity in entities or []:
        old_start = int(entity.offset)
        old_end = old_start + int(entity.length)
        new_start = map_offset(old_start)
        new_end = map_offset(old_end)
        if new_end < new_start:
            continue
        try:
            entity_kwargs = {
                "type": getattr(entity, "type", ""),
                "offset": new_start,
                "length": new_end - new_start,
            }
            for key in ("url", "user", "language", "custom_emoji_id", "date_time_format", "unix_time"):
                value = getattr(entity, key, None)
                if value is not None:
                    entity_kwargs[key] = value
            try:
                shifted.append(MessageEntity(**entity_kwargs))
            except TypeError:
                entity_kwargs.pop("date_time_format", None)
                entity_kwargs.pop("unix_time", None)
                shifted.append(MessageEntity(**entity_kwargs))
        except (TypeError, ValueError):
            logger.warning("Could not shift message entity safely: %r", entity)
    return rendered, shifted


# ============================================================
# TELEGRAM SEND HELPERS  (operate against any bot + its Database)
# ============================================================

async def send_media_content(bot, chat_id: int, media_type: str, file_id: str,
                              caption: str, entities, parse_mode: Optional[str], keyboard=None):
    media_type = (media_type or "none").lower()
    caption = caption or ""
    entities = list(entities or [])
    valid_entities = []
    for entity in entities:
        if getattr(entity, "type", None) == CUSTOM_EMOJI_ENTITY_TYPE and not getattr(entity, "custom_emoji_id", None):
            logger.warning("Ignoring custom_emoji entity without custom_emoji_id during send")
            continue
        valid_entities.append(entity)
    entities = valid_entities

    def _media_kwargs(extra_send_field):
        kw = {"chat_id": chat_id, extra_send_field: file_id, "reply_markup": keyboard}
        if caption:
            kw["caption"] = caption[:MAX_CAPTION_LENGTH]
            if entities:
                kw["caption_entities"] = entities
            elif parse_mode:
                kw["parse_mode"] = parse_mode
        return kw

    if media_type == "photo" and file_id:
        return await bot.send_photo(**_media_kwargs("photo"))
    if media_type == "video" and file_id:
        return await bot.send_video(**_media_kwargs("video"))
    if media_type == "document" and file_id:
        return await bot.send_document(**_media_kwargs("document"))
    if media_type == "animation" and file_id:
        return await bot.send_animation(**_media_kwargs("animation"))
    if media_type == "audio" and file_id:
        return await bot.send_audio(**_media_kwargs("audio"))
    if media_type == "voice" and file_id:
        return await bot.send_voice(**_media_kwargs("voice"))

    text = caption[:MAX_TEXT_LENGTH].strip("\u0000")
    if not text.strip():
        raise ValueError("Text must be non-empty. Add text/caption before previewing or broadcasting.")
    kwargs = {
        "chat_id": chat_id, "text": text, "reply_markup": keyboard,
        "disable_web_page_preview": True,
    }
    if entities:
        kwargs["entities"] = entities
    elif parse_mode:
        kwargs["parse_mode"] = parse_mode
    return await bot.send_message(**kwargs)


def _source_setting_keys(name: str):
    if name == "join_request":
        return ("join_msg_source_entities", "join_msg_source_chat",
                "join_msg_source_id", "join_msg_source_exact")
    return (f"{name}_msg_source_entities", f"{name}_msg_source_chat",
            f"{name}_msg_source_id", f"{name}_msg_source_exact")


async def send_named_message(bot, db: Database, chat_id: int, name: str, user=None, extra_keyboard=None):
    message = db.get_message_by_name(name)
    if not message or not message["enabled"]:
        return None
    caption = message["caption"] or ""
    parse_mode = message["parse_mode"] or None
    media_type = message["media_type"] or "none"
    file_id = message["file_id"] or ""
    entities_key, chat_key, id_key, exact_key = _source_setting_keys(name)

    buttons = []
    for row in db.get_message_buttons(message["id"]):
        buttons.append({
            "text": row["text"],
            "url": row["url"],
            "style": normalize_button_style(row["style"] if "style" in row.keys() else "primary"),
            "icon_custom_emoji_id": row["icon_custom_emoji_id"] if "icon_custom_emoji_id" in row.keys() else None,
            "row": row["row_number"],
            "position": row["position"],
        })
    keyboard = build_keyboard(buttons) or extra_keyboard
    stored_entities = deserialize_message_entities(db.get_setting(entities_key, "[]"), bot)
    rendered_caption, rendered_entities = render_template_with_entities(caption, stored_entities, user)

    has_template = any(token in caption for token in USERNAME_PLACEHOLDERS)
    source_chat = safe_int(db.get_setting(chat_key, "0"), 0)
    source_msg = safe_int(db.get_setting(id_key, "0"), 0)
    source_is_exact = db.get_setting(exact_key, "0") == "1"

    for attempt in range(MAX_RETRIES):
        try:
            if source_chat and source_msg and source_is_exact and not has_template:
                try:
                    return await bot.copy_message(
                        chat_id=chat_id, from_chat_id=source_chat,
                        message_id=source_msg, reply_markup=keyboard,
                    )
                except TelegramError as copy_exc:
                    logger.warning("Configured copy_message fallback: %s", clean_error(copy_exc)[:500])
            return await send_media_content(
                bot, chat_id, media_type, file_id, rendered_caption,
                rendered_entities, parse_mode, keyboard,
            )
        except RetryAfter as exc:
            await asyncio.sleep(float(exc.retry_after) + 1)
        except (NetworkError, TimedOut):
            if attempt >= MAX_RETRIES - 1:
                raise
            await asyncio.sleep(2 ** attempt)
        except BadRequest:
            raise
    raise RuntimeError("Telegram send retry limit reached.")


async def send_configured_message(bot, db: Database, chat_id: int, user=None):
    return await send_named_message(bot, db, chat_id, "join_request", user=user)



# ============================================================
# BOT INSTANCE  (one per bot — main + each child)
# ============================================================
# A BotInstance bundles everything the original single-bot code held in
# module globals: its Database, Application, owner_id, webhook path/secret,
# broadcast/backup task handles, and runtime status. Every handler reads
# state through the instance it belongs to, so two bots in the same process
# never touch each other's data.

class BotInstance:
    def __init__(
        self,
        bot_id: int,
        token: str,
        owner_id: int,
        db_path: Path,
        is_main: bool = False,
        display_name: str = "",
        webhook_path: str = "",
        webhook_secret: str = "",
    ):
        self.bot_id = bot_id
        self.token = token
        self.owner_id = owner_id
        self.is_main = is_main
        self.display_name = display_name
        self.webhook_path = webhook_path.strip("/") or f"telegram-{token.split(':', 1)[0]}"
        self.webhook_secret = webhook_secret

        self.db = Database(db_path, is_main=is_main)
        # Seed the per-bot owner row using this instance's owner_id.
        self.db._seed_admin_id = owner_id

        self.application: Optional[Application] = None
        self.status: str = "stopped"  # stopped | starting | live | error | offline
        self.last_error: str = ""
        self.last_seen: str = ""
        self.broadcast_tasks: set = set()
        self.backup_task: Optional[asyncio.Task] = None
        self.start_lock = asyncio.Lock()
        self.stop_lock = asyncio.Lock()
        self._initialized = False

    def _set_status(self, status: str, error: str = "", persist_registry: bool = True):
        self.status = status
        self.last_error = error or ""
        if persist_registry and not self.is_main and BOT_MANAGER is not None:
            try:
                BOT_MANAGER.main.db.set_child_bot_status(self.bot_id, status, self.last_error)
            except Exception:
                logger.exception("Could not persist child status (bot_id=%s)", self.bot_id)

    # ---- access convenience ----
    def is_bot_creator(self, user_id: Optional[int]) -> bool:
        return self.db.is_bot_creator(user_id)

    async def _pending_join_requests_for_channel(self, channel_id: int, approve: bool):
        processed = failed = 0
        while True:
            requests = await self.application.bot.get_chat_join_requests(chat_id=channel_id, limit=100)
            if not requests:
                break
            page_progress = False
            for req in requests:
                try:
                    if approve:
                        await self.application.bot.approve_chat_join_request(
                            chat_id=channel_id, user_id=req.user.id
                        )
                        action = "approved_all"
                    else:
                        await self.application.bot.decline_chat_join_request(
                            chat_id=channel_id, user_id=req.user.id
                        )
                        action = "rejected_all"
                    processed += 1
                    page_progress = True
                    self.db.execute(
                        "UPDATE join_requests SET status=?,error=NULL "
                        "WHERE id=(SELECT id FROM join_requests WHERE user_id=? AND channel_id=? "
                        "ORDER BY id DESC LIMIT 1)",
                        (action, req.user.id, channel_id), commit=True,
                    )
                except RetryAfter as exc:
                    await asyncio.sleep(float(exc.retry_after) + 1)
                    try:
                        if approve:
                            await self.application.bot.approve_chat_join_request(
                                chat_id=channel_id, user_id=req.user.id
                            )
                            action = "approved_all"
                        else:
                            await self.application.bot.decline_chat_join_request(
                                chat_id=channel_id, user_id=req.user.id
                            )
                            action = "rejected_all"
                        processed += 1
                        page_progress = True
                        self.db.execute(
                            "UPDATE join_requests SET status=?,error=NULL "
                            "WHERE id=(SELECT id FROM join_requests WHERE user_id=? AND channel_id=? "
                            "ORDER BY id DESC LIMIT 1)",
                            (action, req.user.id, channel_id), commit=True,
                        )
                    except Exception as retry_exc:
                        failed += 1
                        self.db.log_error("ERROR", "join_requests", "bulk_action", clean_error(retry_exc))
                except TelegramError as exc:
                    failed += 1
                    self.db.log_error("ERROR", "join_requests", "bulk_action", clean_error(exc))
                await asyncio.sleep(JOIN_REQUEST_ACTION_DELAY)
            if len(requests) < 100 or not page_progress:
                break
        return processed, failed

    async def process_all_join_requests(self, approve: bool):
        if not self.application:
            raise RuntimeError("Bot is not running")
        total = failed = channel_failures = 0
        for channel in self.db.get_channels(enabled_only=False):
            channel_id = safe_int(channel["channel_id"], 0)
            if not channel_id:
                continue
            try:
                member = await self.application.bot.get_chat_member(
                    channel_id, self.application.bot.id
                )
                status = str(getattr(member, "status", ""))
                can_invite = getattr(member, "can_invite_users", None)
                if status not in ("administrator", "creator"):
                    continue
                if status != "creator" and can_invite is not True:
                    continue
                done, bad = await self._pending_join_requests_for_channel(channel_id, approve)
                total += done
                failed += bad
            except TelegramError as exc:
                channel_failures += 1
                self.db.log_error("ERROR", "join_requests", "bulk_channel", clean_error(exc))
            except Exception as exc:
                channel_failures += 1
                self.db.log_error("EXCEPTION", "join_requests", "bulk_channel", repr(exc))
        return total, failed, channel_failures

    # ---- lifecycle ----
    def _build_application(self) -> Application:
        """Build once, attach handlers, and assign self.application immediately."""
        application = (
            ApplicationBuilder()
            .token(self.token)
            .concurrent_updates(False)
            .connect_timeout(20.0)
            .read_timeout(20.0)
            .write_timeout(20.0)
            .pool_timeout(20.0)
            .get_updates_connect_timeout(20.0)
            .get_updates_read_timeout(20.0)
            .build()
        )
        self._register_handlers(application)
        application.bot_data["instance"] = self
        # CRITICAL: the live Application is visible through the instance before
        # any webhook can be registered or an update can be dispatched.
        self.application = application
        return application

    async def prepare(self) -> bool:
        """Initialize the PTB Application and run one-time runtime checks."""
        if self.application is not None and getattr(self, "_initialized", False):
            return True
        self.db.connect()
        if self.application is None:
            self._build_application()
        try:
            await self.application.initialize()
            await self._post_init(self.application)
            self._initialized = True
            return True
        except Exception as exc:
            self.last_error = clean_error(exc)
            self._set_status("error", self.last_error)
            logger.exception("BotInstance prepare failed (bot_id=%s): %s", self.bot_id, self.last_error)
            await self._cleanup_application(delete_webhook=False)
            return False

    async def _start_runtime_tasks(self) -> None:
        """Start resumable work only after Application.start()."""
        if not self.application:
            return
        pending = self.db.fetchall(
            "SELECT id FROM broadcasts WHERE status IN ('running','paused') ORDER BY id"
        )
        for row in pending:
            self.db.execute(
                "UPDATE broadcasts SET status='running' WHERE id=?",
                (row["id"],), commit=True,
            )
            task = self.application.create_task(self.run_broadcast(int(row["id"])))
            self.broadcast_tasks.add(task)
            task.add_done_callback(self.broadcast_tasks.discard)
        if self.backup_task is None or self.backup_task.done():
            self.backup_task = self.application.create_task(self.automatic_backup_loop())

    async def start(self, webhook_base_url: str = "", polling: bool = False) -> bool:
        async with self.start_lock:
            if self.application is not None and self.status == "live":
                return True
            self._set_status("starting", "")
            logger.info("%s bot_id=%s starting…", "Main" if self.is_main else "Child", self.bot_id)
            try:
                if not await self.prepare():
                    error = self.last_error or "Application preparation failed"
                    self._set_status("error", error)
                    return False
                app = self.application
                if app is None:
                    raise RuntimeError("Application was not assigned during prepare")
                if not getattr(app, "running", False):
                    await app.start()
                    logger.info("Application started for bot_id=%s", self.bot_id)
                if webhook_base_url:
                    if not WEBHOOK_SERVER or not WEBHOOK_SERVER.is_running:
                        raise RuntimeError("Shared webhook server is not running")
                    webhook_url = f"{webhook_base_url.rstrip('/')}/{self.webhook_path.strip('/')}"
                    await app.bot.set_webhook(
                        url=webhook_url,
                        allowed_updates=["message", "callback_query", "chat_join_request"],
                        drop_pending_updates=False, secret_token=self.webhook_secret or None,
                    )
                    info = await app.bot.get_webhook_info()
                    actual = (getattr(info, "url", "") or "").rstrip("/")
                    if actual != webhook_url.rstrip("/"):
                        raise RuntimeError("Telegram webhook verification failed")
                    logger.info("set_webhook OK for bot_id=%s", self.bot_id)
                else:
                    await app.bot.delete_webhook(drop_pending_updates=False)
                    if polling:
                        await app.updater.start_polling(
                            allowed_updates=["message", "callback_query", "chat_join_request"],
                            drop_pending_updates=False)
                await self._start_runtime_tasks()
                self.last_seen = utc_now()
                self._set_status("live", "")
                self.db.log_event("live", details=f"bot_id={self.bot_id}")
                logger.info("Application live: bot_id=%s role=%s", self.bot_id, "main" if self.is_main else "child")
                return True
            except Exception as exc:
                error = clean_error(exc)
                self._set_status("error", error)
                try:
                    self.db.log_error("ERROR", "lifecycle", "start", error)
                except Exception:
                    pass
                logger.exception("BotInstance start failed (bot_id=%s): %s", self.bot_id, error)
                await self._cleanup_application(delete_webhook=True)
                self._set_status("error", error)
                return False

    async def _cleanup_application(self, delete_webhook: bool = True) -> None:
        app = self.application
        if app is None:
            self.db.close()
            self._initialized = False
            return
        try:
            if self.backup_task:
                self.backup_task.cancel()
                try:
                    await self.backup_task
                except BaseException:
                    pass
                self.backup_task = None
            for task in list(self.broadcast_tasks):
                task.cancel()
            for task in list(self.broadcast_tasks):
                try:
                    await task
                except BaseException:
                    pass
            self.broadcast_tasks.clear()
            if getattr(app, "updater", None) and app.updater.running:
                await app.updater.stop()
        except Exception:
            logger.exception("Application worker cleanup failed (bot_id=%s)", self.bot_id)
        if delete_webhook:
            try:
                await app.bot.delete_webhook(drop_pending_updates=False)
            except Exception:
                logger.warning("Could not delete webhook during cleanup (bot_id=%s)", self.bot_id)
        try:
            if getattr(app, "running", False):
                await app.stop()
        except Exception:
            logger.exception("Application stop failed during cleanup (bot_id=%s)", self.bot_id)
        try:
            await app.shutdown()
        except Exception:
            logger.exception("Application shutdown failed during cleanup (bot_id=%s)", self.bot_id)
        self.application = None
        self._initialized = False
        self.db.close()

    async def stop(self) -> bool:
        async with self.stop_lock:
            if self.application is None:
                self.status = "stopped"
                self.db.close()
                return True
            try:
                self.status = "stopping"
                await self._cleanup_application(delete_webhook=True)
                self._set_status("stopped", "")
                logger.info("Bot stopped: bot_id=%s", self.bot_id)
                return True
            except Exception as exc:
                self.status = "error"
                self.last_error = clean_error(exc)
                logger.exception("BotInstance stop failed (bot_id=%s)", self.bot_id)
                self.application = None
                self.db.close()
                return False

    async def _post_init(self, application: Application):
        """One-time initialization hook retained for backward compatibility."""
        try:
            integrity = self.db.fetchone("PRAGMA integrity_check")
            if not integrity or integrity[0] != "ok":
                raise RuntimeError(f"SQLite integrity check failed: {integrity}")
            me = None
            last_exc: Optional[Exception] = None
            for attempt in range(1, 6):
                try:
                    me = await application.bot.get_me()
                    break
                except (TimedOut, NetworkError) as exc:
                    last_exc = exc
                    await asyncio.sleep(attempt * 2)
            if me is None:
                raise RuntimeError(f"Could not reach Telegram after 5 attempts: {clean_error(last_exc or RuntimeError('unknown error'))}")
            self.last_seen = utc_now()
            await application.bot.set_my_commands([BotCommand("start", "Start")])
            self.db.log_event("startup", details=f"bot_id={me.id};username={me.username}")
        except Exception:
            logger.exception("BotInstance post_init failed (bot_id=%s)", self.bot_id)
            raise

    async def _post_shutdown(self, application: Application):
        # Kept as a compatibility method for callers that used the old hook.
        try:
            self.db.log_event("shutdown")
        except Exception:
            pass

    # ---- handlers ----
    def _register_handlers(self, application: Application):
        application.add_handler(CommandHandler("start", self.handle_start))
        application.add_handler(CommandHandler("admin", self.handle_admin_command))
        application.add_handler(CommandHandler("cancel", self.handle_cancel_command))
        application.add_handler(CommandHandler("broadcast_confirm", self.handle_broadcast_confirm))
        # Main-only commands for bot management.
        if self.is_main:
            application.add_handler(CommandHandler("create", self.handle_create_command))
            application.add_handler(CommandHandler("bots", self.handle_bots_command))

        application.add_handler(ChatJoinRequestHandler(self.handle_join_request))
        application.add_handler(
            CallbackQueryHandler(self.btn_add_style_callback, pattern=r"^btn_add_style:")
        )
        application.add_handler(CallbackQueryHandler(self.admin_callback))
        application.add_handler(
            MessageHandler(
                (
                    filters.ChatType.PRIVATE
                    & (
                        filters.TEXT | filters.PHOTO | filters.VIDEO | filters.ANIMATION
                        | filters.AUDIO | filters.VOICE | filters.Document.ALL
                    )
                    & ~filters.COMMAND
                ),
                self.private_message_router,
            )
        )
        application.add_error_handler(self.global_error_handler)

    # ---- access helpers ----
    def is_admin(self, user_id):
        return is_admin_for(self.db, user_id)

    def is_owner(self, user_id):
        return is_owner_for(self.db, user_id, self.owner_id)

    # ============================================================
    # START
    # ============================================================
    async def handle_start(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        user = update.effective_user
        if not user or not update.message:
            return
        try:
            self.db.upsert_user(user)
            if (self.db.get_setting("maintenance_mode", "0") == "1"
                    and not self.is_admin(user.id)):
                return
            join_keyboard = start_keyboard(self.db)
            start_msg = self.db.get_start_message()
            has_own_buttons = bool(self.db.get_message_buttons(start_msg["id"])) if start_msg else False
            is_configured = bool(
                start_msg and start_msg["enabled"] and (
                    (start_msg["caption"] or "").strip()
                    or (start_msg["media_type"] or "none") != "none"
                    or has_own_buttons
                )
            )
            if is_configured:
                try:
                    sent = await send_named_message(
                        context.bot, self.db, update.effective_chat.id, "start",
                        user=user, extra_keyboard=join_keyboard,
                    )
                    if sent is not None:
                        return
                except Exception as exc:
                    logger.exception("Configured /start message failed, falling back")
                    self.db.log_error("ERROR", "start", "send_named_message", repr(exc))
            if join_keyboard:
                await update.message.reply_text(
                    self.db.get_setting("start_message", "Please join our channel to continue.")[:MAX_TEXT_LENGTH],
                    reply_markup=join_keyboard,
                )
            elif self.is_admin(user.id):
                await update.message.reply_text(
                    "No channel is configured.",
                    reply_markup=admin_menu(self.is_main),
                )
        except Exception as exc:
            logger.exception("/start failed")
            self.db.log_error("ERROR", "start", "handler", repr(exc))

    # ============================================================
    # JOIN REQUEST
    # ============================================================
    async def handle_join_request(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        request = update.chat_join_request
        if not request:
            return
        user = request.from_user
        chat = request.chat
        try:
            self.db.upsert_user(user)
            channel = self.db.fetchone(
                "SELECT * FROM channels WHERE channel_id=? AND enabled=1", (chat.id,)
            )
            if not channel:
                self.db.log_event("join_request_ignored", user.id, chat.id, "Channel not configured or disabled")
                return
            request_time = request.date.strftime("%Y-%m-%d %H:%M:%S") if request.date else utc_now()
            event_key = f"join:{chat.id}:{user.id}:{getattr(update, 'update_id', 0)}"
            row_id = self.db.save_join_request(user.id, chat.id, event_key, request_time)
            if row_id is None:
                self.db.log_event("duplicate_join_request", user.id, chat.id)
                return
            self.db.log_event("join_request_received", user.id, chat.id)
            dm_sent = False
            if self.db.get_setting("auto_message_enabled", "1") == "1":
                try:
                    dm_chat_id = getattr(request, "user_chat_id", None) or user.id
                    await send_configured_message(context.bot, self.db, dm_chat_id, user)
                    dm_sent = True
                    self.db.log_event("join_request_message_sent", user.id, chat.id)
                except Forbidden as exc:
                    error = clean_error(exc)
                    self.db.execute("UPDATE users SET is_blocked=1 WHERE user_id=?", (user.id,), commit=True)
                    self.db.log_error("WARNING", "join_request", "forbidden", error)
                    self.db.update_join_request(row_id, sent=False, status="blocked", error=error)
                except Exception as exc:
                    error = clean_error(exc)
                    self.db.log_error("ERROR", "join_request", "send_failed", error)
                    self.db.update_join_request(row_id, sent=False, status="failed", error=error)
            # New Auto Member switch is global to this bot instance. The
            # existing per-channel Auto Approve feature remains supported.
            auto_member_enabled = self.db.get_setting("auto_member_enabled", "0") == "1"
            if auto_member_enabled or bool(channel["auto_approve"]):
                try:
                    await context.bot.approve_chat_join_request(chat_id=chat.id, user_id=user.id)
                    self.db.log_event("join_request_auto_approved", user.id, chat.id)
                    final_status = "auto_approved" if dm_sent else "auto_approved_dm_failed"
                    self.db.update_join_request(row_id, sent=dm_sent, status=final_status)
                except TelegramError as exc:
                    error = clean_error(exc)
                    self.db.update_join_request(row_id, sent=dm_sent, status="approve_failed", error=error)
                    self.db.log_error("ERROR", "join_request", "approve_failed", error)
            elif dm_sent:
                self.db.update_join_request(row_id, sent=True, status="sent")
        except Exception as exc:
            logger.exception("Join request handler failed")
            self.db.log_error("EXCEPTION", "join_request", "handler", repr(exc))

    # ============================================================
    # ADMIN COMMANDS
    # ============================================================
    async def handle_admin_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not update.message:
            return
        user = update.effective_user
        if not user:
            return
        if not self.is_admin(user.id):
            if self.is_main and self.is_bot_creator(user.id):
                await update.message.reply_text(
                    "🤖 BOT CREATOR\n\nYou can create and manage the bots you create through the main create flow.",
                    reply_markup=InlineKeyboardMarkup([[
                        _make_callback_button("➕ Create My Bot", "bm:create", "success")
                    ]]),
                )
            else:
                await update.message.reply_text("Access Denied")
            return
        self.db.upsert_user(user)
        await update.message.reply_text("🔐 Admin Panel", reply_markup=admin_menu(self.is_main))

    async def handle_cancel_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not update.message:
            return
        user = update.effective_user
        if not user or not (self.is_admin(user.id) or (self.is_main and self.is_bot_creator(user.id))):
            return
        context.user_data.clear()
        await update.message.reply_text("Cancelled.", reply_markup=admin_menu(self.is_main))

    async def handle_broadcast_confirm(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not update.message:
            return
        user = update.effective_user
        if not user or not self.is_admin(user.id):
            await update.message.reply_text("Access Denied")
            return
        broadcast_id = context.user_data.get("pending_broadcast_id")
        if not broadcast_id:
            await update.message.reply_text("No pending broadcast.")
            return
        await self.start_broadcast_send(update.message, context, broadcast_id)

    async def handle_create_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Main-only /create — opens the create-bot flow."""
        if not update.message:
            return
        user = update.effective_user
        if not user or not (self.is_admin(user.id) or (self.is_main and self.is_bot_creator(user.id))):
            await update.message.reply_text("❌ You are not authorized to use this command.")
            return
        context.user_data["awaiting"] = "create_bot_token"
        await update.message.reply_text(
            "🤖 CREATE NEW BOT\n\nSend your Telegram Bot Token.\n"
            "Create your bot using @BotFather and send the token here.\n\nUse /cancel to cancel.",
            reply_markup=InlineKeyboardMarkup(
                [[_make_callback_button("❌ Cancel", "create_bot_cancel", "danger")]]
            ),
        )

    async def handle_bots_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not update.message:
            return
        user = update.effective_user
        if not user or not self.is_admin(user.id):
            await update.message.reply_text("❌ You are not authorized to use this command.")
            return
        await show_bot_manager(update.message)

    # ============================================================
    # USER MESSAGE -> CONFIGURED JOIN MESSAGE
    # ============================================================
    async def handle_user_message(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        user = update.effective_user
        message = update.message
        if not user or not message or self.is_admin(user.id):
            return
        try:
            self.db.upsert_user(user)
            if self.db.get_setting("maintenance_mode", "0") == "1":
                return
            await send_configured_message(context.bot, self.db, user.id, user)
        except Forbidden:
            self.db.execute("UPDATE users SET is_blocked=1 WHERE user_id=?", (user.id,), commit=True)
        except Exception as exc:
            logger.exception("User message handler failed")
            self.db.log_error("ERROR", "user_message", "send_configured", repr(exc))

    async def private_message_router(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        user = update.effective_user
        if not user:
            return
        if self.is_admin(user.id) or (self.is_main and self.is_bot_creator(user.id)):
            await self.admin_input(update, context)
        else:
            await self.handle_user_message(update, context)

    # ============================================================
    # GLOBAL ERROR HANDLER
    # ============================================================
    async def global_error_handler(self, update: object, context: ContextTypes.DEFAULT_TYPE):
        error = context.error
        if isinstance(error, RetryAfter):
            logger.warning("Telegram rate limit: %s seconds", error.retry_after)
            return
        if isinstance(error, Forbidden):
            logger.warning("Telegram forbidden error: %s", error)
            return
        if isinstance(error, (NetworkError, TimedOut)):
            logger.warning("Telegram network error: %s", error)
            return
        logger.exception("Unhandled application error", exc_info=error)
        try:
            self.db.log_error("EXCEPTION", "application", "global_error", repr(error))
        except Exception:
            logger.exception("Could not save global error")


    # ============================================================
    # ADMIN PAGES
    # ============================================================
    async def show_dashboard(self, query):
        s = self.db.stats()
        try:
            db_size = self.db.path.stat().st_size
        except OSError:
            db_size = 0
        text = (
            "📊 BOT DASHBOARD\n\n"
            f"👥 Total Users: {s['users']}\n"
            f"🟢 Active: {s['active']}\n"
            f"🚫 Blocked: {s['blocked']}\n\n"
            f"📩 Join Requests: {s['requests']}\n"
            f"📅 Today: {s['today']}\n"
            f"📆 Week: {s['week']}\n"
            f"🗓 Month: {s['month']}\n\n"
            f"📤 Sent: {s['sent']}\n"
            f"❌ Failed: {s['failed']}\n"
            f"📢 Channels: {s['channels']}\n"
            f"📢 Broadcasts: {s['broadcasts']}\n\n"
            f"🗄 DB: {self.db.path.name}\n"
            f"📦 Size: {db_size:,} bytes"
        )
        await query.edit_message_text(
            text,
            reply_markup=InlineKeyboardMarkup([
                [_make_callback_button("🔄 Refresh", "admin_dashboard", "primary")],
                [_make_callback_button("⬅️ Back", "admin_home", "primary")],
            ]),
        )

    async def show_statistics(self, query):
        s = self.db.stats()
        total = s["sent"] + s["failed"]
        success_rate = (s["sent"] / total) * 100 if total else 0
        await query.edit_message_text(
            (
                "📈 STATISTICS\n\n"
                f"Users: {s['users']}\nActive: {s['active']}\nBlocked: {s['blocked']}\n\n"
                f"Requests Today: {s['today']}\nRequests 7 Days: {s['week']}\nRequests 30 Days: {s['month']}\n\n"
                f"Messages Sent: {s['sent']}\nMessages Failed: {s['failed']}\nSuccess Rate: {success_rate:.2f}%"
            ),
            reply_markup=back_keyboard(),
        )

    async def show_settings(self, query):
        maintenance = self.db.get_setting("maintenance_mode", "0")
        check = self.db.get_setting("check_join_enabled", "0")
        style = self.db.get_setting("start_button_style", "primary")
        await query.edit_message_text(
            (
                "⚙️ BOT SETTINGS\n\n"
                f"Bot Name: {self.db.get_setting('bot_name','Join Request Bot')}\n"
                f"Maintenance: {'ON' if maintenance == '1' else 'OFF'}\n"
                f"Check Join Button: {'ON' if check == '1' else 'OFF'}\n"
                f"Join Button Style: {style.upper()}"
            ),
            reply_markup=InlineKeyboardMarkup([
                [_make_callback_button("Toggle Maintenance", "toggle_maintenance", "primary")],
                [_make_callback_button("Toggle Check Join", "toggle_check", "primary")],
                [
                    _make_callback_button("🔵 Primary", "btn_style:primary", "primary"),
                    _make_callback_button("🟢 Success", "btn_style:success", "success"),
                    _make_callback_button("🔴 Danger", "btn_style:danger", "danger"),
                ],
                [_make_callback_button("⬅️ Back", "admin_home", "primary")],
            ]),
        )

    async def show_join_settings(self, query):
        enabled = self.db.get_setting("auto_message_enabled", "1")
        await query.edit_message_text(
            (
                "📩 JOIN REQUEST SETTINGS\n\n"
                f"Auto Message: {'ON' if enabled == '1' else 'OFF'}\n"
                f"Auto Member: {'ON' if self.db.get_setting('auto_member_enabled', '0') == '1' else 'OFF'}\n\n"
                "When Auto Member is ON, incoming join requests for every enabled configured channel are accepted automatically.\n"
                "Existing per-channel Auto Approve remains available in Channel Manager."
            ),
            reply_markup=InlineKeyboardMarkup([
                [_make_callback_button(
                    ("👥 Auto Member: ON" if self.db.get_setting("auto_member_enabled", "0") == "1" else "👥 Auto Member: OFF"),
                    "toggle_auto_member",
                    "success" if self.db.get_setting("auto_member_enabled", "0") == "1" else "danger",
                )],
                [_make_callback_button("Toggle Auto Message", "toggle_auto", "primary")],
                [_make_callback_button("✅ Approve All Pending", "join_approve_all", "success"),
                 _make_callback_button("❌ Reject All Pending", "join_reject_all", "danger")],
                [_make_callback_button("⬅️ Back", "admin_home", "primary")],
            ]),
        )

    async def show_named_message_builder(self, query, name: str):
        spec = _MESSAGE_BUILDER_TARGETS[name]
        message = self.db.get_message_by_name(name)
        buttons = self.db.get_message_buttons(message["id"])
        media = message["media_type"] or "none"
        parse_mode = message["parse_mode"] or "HTML"
        caption = message["caption"] or "(empty)"
        btn_lines = []
        for b in buttons:
            style = b["style"] if "style" in b.keys() else "primary"
            icon = " ⭐" if ("icon_custom_emoji_id" in b.keys() and b["icon_custom_emoji_id"]) else ""
            btn_lines.append(f"  [{style}]{icon} {b['text']} → {b['url']}")
        btn_preview = "\n".join(btn_lines) if btn_lines else "None"
        extra_note = ""
        if name == "start":
            extra_note = (
                "\nIf left empty (no caption/media/buttons), /start falls back "
                "to the classic default welcome + channel-join button.\n"
            )
        await query.edit_message_text(
            (
                f"{spec['title']}\n\nMedia: {media}\nParse Mode: {parse_mode}\n"
                f"Buttons: {len(buttons)}\n{btn_preview}\n{extra_note}\nCaption:\n{caption[:800]}"
            )[:4000],
            reply_markup=InlineKeyboardMarkup([
                [
                    _make_callback_button("📝 Caption", spec["set_caption"], "primary"),
                    _make_callback_button("🔤 Parse", spec["toggle_parse"], "primary"),
                ],
                [
                    _make_callback_button("🖼/🎥 Media", spec["set_media"], "primary"),
                    _make_callback_button("🗑 Remove Media", spec["remove_media"], "danger"),
                ],
                [
                    _make_callback_button("➕ Add Button", spec["add_button"], "success"),
                    _make_callback_button("🗑 Clear Buttons", spec["clear_buttons"], "danger"),
                ],
                [
                    _make_callback_button("👁 Preview", spec["preview"], "primary"),
                    _make_callback_button("🧪 Test", spec["test"], "success"),
                ],
                [_make_callback_button("⬅️ Back", spec["back"], "primary")],
            ]),
        )

    async def show_message_builder(self, query):
        await self.show_named_message_builder(query, "join_request")

    async def show_start_message_builder(self, query):
        await self.show_named_message_builder(query, "start")

    async def show_channels(self, query):
        channels = self.db.get_channels()
        lines = ["📢 CHANNEL MANAGER\n"]
        if not channels:
            lines.append("No channels configured.")
        else:
            for channel in channels:
                status = "ON" if channel["enabled"] else "OFF"
                title = channel["title"] or channel["username"] or str(channel["channel_id"])
                auto = "ON" if channel["auto_approve"] else "OFF"
                lines.append(f"• {title}\n  ID: {channel['channel_id']}\n  Status: {status}\n  Auto Approve: {auto}\n")
        rows = [
            [_make_callback_button("➕ Add Channel", "add_channel", "success")],
            [_make_callback_button("✅ Approve All Pending", "join_approve_all", "success"),
             _make_callback_button("❌ Reject All Pending", "join_reject_all", "danger")],
        ]
        for channel in channels:
            rows.append([
                _make_callback_button(
                    ("Disable " if channel["enabled"] else "Enable ") + str(channel["channel_id"]),
                    f"channel_toggle:{channel['channel_id']}", "primary",
                ),
                _make_callback_button(
                    ("✅ Auto Approve" if channel["auto_approve"] else "⏸ Auto Approve"),
                    f"channel_auto:{channel['channel_id']}",
                    "success" if channel["auto_approve"] else "danger",
                ),
            ])
            rows.append([_make_callback_button("🗑 Remove Channel", f"remove_channel:{channel['channel_id']}", "danger")])
        rows.append([_make_callback_button("⬅️ Back", "admin_home", "primary")])
        await query.edit_message_text("\n".join(lines)[:4000], reply_markup=InlineKeyboardMarkup(rows))

    async def show_users(self, query):
        s = self.db.stats()
        latest = self.db.fetchall(
            "SELECT user_id,username,first_name,last_seen FROM users ORDER BY last_seen DESC LIMIT 10"
        )
        lines = ["👥 USERS", "", f"Total: {s['users']}", f"Active: {s['active']}", f"Blocked: {s['blocked']}", "", "Latest:"]
        for row in latest:
            name = row["username"] or row["first_name"] or str(row["user_id"])
            lines.append(f"• {name} — {row['user_id']}")
        await query.edit_message_text(
            "\n".join(lines)[:4000],
            reply_markup=InlineKeyboardMarkup([
                [_make_callback_button("📤 Export CSV", "export_users", "primary")],
                [_make_callback_button("⬅️ Back", "admin_home", "primary")],
            ]),
        )

    async def show_broadcast_menu(self, query):
        recent = self.db.fetchall(
            "SELECT id,status,total,sent,failed,blocked,created_at FROM broadcasts ORDER BY id DESC LIMIT 5"
        )
        lines = [
            "📢 BROADCAST CENTER", "",
            "Supports text, photo, video, document, animation, audio and voice.",
            "Premium/custom emoji are kept from the original Telegram message.",
            "Buttons support blue/green/red styles and optional custom-emoji icons.", "",
            "Recent:",
        ]
        if recent:
            for row in recent:
                lines.append(
                    f"#{row['id']} — {row['status']} — {row['sent']}/{row['total']} sent, "
                    f"{row['failed']} failed, {row['blocked']} blocked"
                )
        else:
            lines.append("No broadcasts yet.")
        await query.edit_message_text(
            "\n".join(lines)[:4000],
            reply_markup=InlineKeyboardMarkup([
                [_make_callback_button("➕ New Broadcast", "broadcast_start", "success")],
                [_make_callback_button("⬅️ Back", "admin_home", "primary")],
            ]),
        )

    async def show_backup_menu(self, query):
        backups = self.db.fetchall("SELECT filename,created_at,size FROM backups ORDER BY id DESC LIMIT 5")
        channel_id = self.db.get_setting("backup_channel_id", "")
        channel_title = self.db.get_setting("backup_channel_title", "")
        channel_username = self.db.get_setting("backup_channel_username", "")
        channel_enabled = self.db.get_setting("backup_channel_enabled", "0") == "1"
        last_backup = self.db.fetchone("SELECT created_at, size FROM backups ORDER BY id DESC LIMIT 1")
        lines = ["💾 BACKUP\n"]
        if channel_enabled and channel_id:
            channel_line = channel_title or channel_id
            if channel_username:
                channel_line += f" (@{channel_username})"
            lines.extend([
                "☁️ Auto Backup: ON",
                f"📢 Backup Channel: {channel_line}",
                f"🆔 ID: {channel_id}",
                f"⏱ Interval: {_format_interval_label(self.get_backup_interval_seconds())}",
                (f"🕐 Last backup: {last_backup['created_at']} ({last_backup['size']:,} bytes)"
                 if last_backup else "🕐 Last backup: none yet"), "",
            ])
        else:
            lines.extend([
                "☁️ Auto Backup: OFF", "📢 Backup Channel: Not configured", "",
                "⚠️ WARNING: On Render's free tier (and after most restarts/deploys "
                "on any tier), the local SQLite file is NOT persistent — it is "
                "wiped whenever the instance sleeps, restarts, or redeploys. "
                "Without a backup channel configured, ALL bot data can be permanently lost.", "",
            ])
        if backups:
            lines.append("Recent local backups:")
            for row in backups:
                lines.append(f"• {row['filename']}\n  {row['size']:,} bytes\n  {row['created_at']}")
        else:
            lines.append("No local backups yet.")
        lines.append("\n📥 RESTORE: Send a .db/.sqlite/.sqlite3 backup file directly here.")
        rows = [
            [_make_callback_button("💾 Create Backup", "backup_create", "success")],
            [_make_callback_button("☁️ Backup Channel Settings", "admin_backup_channel", "primary")],
            [_make_callback_button("⬅️ Back", "admin_home", "primary")],
        ]
        await query.edit_message_text("\n".join(lines)[:4000], reply_markup=InlineKeyboardMarkup(rows))

    async def show_export_menu(self, query):
        await query.edit_message_text(
            "📤 DATABASE EXPORT",
            reply_markup=InlineKeyboardMarkup([
                [_make_callback_button("👥 Users CSV", "export_users", "primary")],
                [_make_callback_button("📩 Join Requests CSV", "export_requests", "primary")],
                [_make_callback_button("📢 Broadcast Logs CSV", "export_broadcasts", "primary")],
                [_make_callback_button("⬅️ Back", "admin_home", "primary")],
            ]),
        )

    async def show_logs(self, query):
        rows = self.db.fetchall(
            "SELECT level,module,event,exception,created_at FROM error_logs ORDER BY id DESC LIMIT 15"
        )
        if not rows:
            text = "📝 LOGS\n\nNo error records."
        else:
            parts = ["📝 LOGS\n"]
            for row in rows:
                parts.append(
                    f"[{row['created_at']}] {row['level']} {row['module']}\n"
                    f"{row['event']}\n{(row['exception'] or '')[:300]}\n"
                )
            text = "\n".join(parts)
        await query.edit_message_text(text[:4000], reply_markup=back_keyboard())

    async def show_admins(self, query):
        rows = self.db.fetchall("SELECT user_id,role,created_at FROM admins ORDER BY role,user_id")
        lines = ["🔐 ADMINS\n"]
        for row in rows:
            mark = " 👑" if row["role"] == "owner" else ""
            lines.append(f"{row['user_id']} — {row['role']}{mark}")
        lines.append("\nOwner is controlled by this bot's owner id.")
        await query.edit_message_text("\n".join(lines)[:4000], reply_markup=back_keyboard())

    async def show_backup_channel(self, query):
        channel_id = self.db.get_setting("backup_channel_id", "")
        username = self.db.get_setting("backup_channel_username", "")
        title = self.db.get_setting("backup_channel_title", "")
        enabled = self.db.get_setting("backup_channel_enabled", "0") == "1"
        interval_label = _format_interval_label(self.get_backup_interval_seconds())
        if enabled and channel_id:
            status_lines = ["🟢 ENABLED", f"Channel: {title or '-'}", f"ID: {channel_id}"]
            if username:
                status_lines.append(f"Username: @{username}")
            status = "\n".join(status_lines)
        else:
            status = ("🔴 NOT CONFIGURED\n\n⚠️ Without this, local data is at risk: Render's free tier "
                      "(and restarts/redeploys generally) wipe the local SQLite file.")
        last_backup = self.db.fetchone("SELECT created_at, size FROM backups ORDER BY id DESC LIMIT 1")
        last_backup_line = (f"Last backup: {last_backup['created_at']} ({last_backup['size']:,} bytes)"
                            if last_backup else "Last backup: none yet")
        await query.edit_message_text(
            "☁️ BACKUP CHANNEL\n\n"
            f"{status}\n\nAutomatic backup: {interval_label}\n{last_backup_line}\n"
            "Each backup is a complete SQLite database snapshot, taken on a background thread.\n"
            "Set the backup interval:",
            reply_markup=InlineKeyboardMarkup([
                *self.backup_interval_keyboard(),
                [_make_callback_button("➕ Set / Change Channel", "set_backup_channel", "success")],
                [_make_callback_button("⏸ Disable Auto Backup", "disable_backup_channel", "danger")],
                [_make_callback_button("⬅️ Back", "admin_home", "primary")],
            ]),
        )

    def backup_interval_keyboard(self):
        current = self.get_backup_interval_seconds()
        rows = []
        row = []
        for label, seconds in BACKUP_INTERVAL_CHOICES.items():
            marker = "✅ " if seconds == current else ""
            style = "success" if seconds == current else "primary"
            row.append(_make_callback_button(f"{marker}{label.upper()}", f"set_backup_interval:{label}", style))
            if len(row) == 3:
                rows.append(row)
                row = []
        if row:
            rows.append(row)
        return rows

    def get_backup_interval_seconds(self) -> int:
        return max(0, safe_int(self.db.get_setting("backup_interval_seconds", ""),
                               AUTO_BACKUP_INTERVAL_SECONDS_DEFAULT))

    # ============================================================
    # ADMIN CALLBACK ROUTER
    # ============================================================
    async def admin_callback(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        query = update.callback_query
        if not query:
            return
        user = query.from_user
        data = query.data or ""
        creator_allowed = bool(user and self.is_main and self.is_bot_creator(user.id))
        admin_allowed = bool(user and self.is_admin(user.id))
        if not admin_allowed and not creator_allowed:
            try:
                await query.answer("Access Denied", show_alert=True)
            except TelegramError:
                pass
            return
        if creator_allowed and not data.startswith(("create_bot_", "bm:create")):
            try:
                await query.answer("Bot Creator access is limited to Create Bot.", show_alert=True)
            except TelegramError:
                pass
            return
        # Main-only Bot Manager / create-flow callbacks are dispatched first.
        if self.is_main:
            try:
                if await main_admin_callback_extension(self, update, context):
                    return
            except Exception as exc:
                logger.exception("Main admin callback extension failed: %s", data)
                self.db.log_error("EXCEPTION", "admin_callback", data, repr(exc))
        try:
            await query.answer()
            if data == "admin_home":
                await query.edit_message_text("🔐 Admin Panel", reply_markup=admin_menu(self.is_main))
                return
            if data == "admin_dashboard":
                await self.show_dashboard(query); return
            if data == "admin_stats":
                await self.show_statistics(query); return
            if data == "admin_settings":
                await self.show_settings(query); return
            if data == "admin_join":
                await self.show_join_settings(query); return
            if data == "admin_message":
                await self.show_message_builder(query); return
            if data == "admin_start_msg":
                await self.show_start_message_builder(query); return
            if data == "admin_channels":
                await self.show_channels(query); return
            if data == "admin_users":
                await self.show_users(query); return
            if data == "admin_broadcast":
                await self.show_broadcast_menu(query); return
            if data == "admin_backup":
                await self.show_backup_menu(query); return
            if data == "admin_backup_channel":
                await self.show_backup_channel(query); return
            if data == "set_backup_channel":
                context.user_data["awaiting"] = "backup_channel"
                await query.message.reply_text(
                    "Send the backup channel ID, @username, or link.\n\n"
                    "Private channel: send its numeric ID (for example -1001234567890).\n"
                    "Public channel: @MyBackupChannel or https://t.me/MyBackupChannel\n\n"
                    "The bot must already be an administrator with permission to post messages.\n"
                    "Use /cancel to cancel."
                )
                return
            if data == "disable_backup_channel":
                self.db.set_setting("backup_channel_enabled", "0")
                await self.show_backup_channel(query); return
            if data.startswith("set_backup_interval:"):
                label = data.split(":", 1)[1]
                seconds = BACKUP_INTERVAL_CHOICES.get(label)
                if seconds is None:
                    await answer_query(query, "Unknown interval.", show_alert=True); return
                self.db.set_setting("backup_interval_seconds", str(seconds))
                self.db.log_event("backup_interval_changed", user_id=query.from_user.id,
                                  details=f"interval={label}({seconds}s)")
                await answer_query(query, f"Backup interval set to {label.upper()}.")
                await self.show_backup_channel(query); return
            if data == "admin_export":
                await self.show_export_menu(query); return
            if data == "admin_logs":
                await self.show_logs(query); return
            if data == "admin_admins":
                await self.show_admins(query); return
            if data == "admin_test":
                await self.test_message(query, context); return

            if data == "toggle_auto_member":
                current = self.db.get_setting("auto_member_enabled", "0")
                new_value = "0" if current == "1" else "1"
                if new_value == "1":
                    channels = self.db.get_channels(enabled_only=True)
                    if not channels:
                        await query.answer("Add and enable a channel first.", show_alert=True)
                        return
                    permission_ok = False
                    for channel in channels:
                        try:
                            member = await context.bot.get_chat_member(
                                chat_id=channel["channel_id"], user_id=context.bot.id
                            )
                            status = str(getattr(member, "status", ""))
                            can_invite = getattr(member, "can_invite_users", None)
                            if status == "creator" or (status == "administrator" and can_invite is True):
                                permission_ok = True
                                break
                        except TelegramError:
                            continue
                    if not permission_ok:
                        await query.answer(
                            "Bot needs admin + Invite Users permission in at least one enabled channel.",
                            show_alert=True,
                        )
                        return
                self.db.set_setting("auto_member_enabled", new_value)
                self.db.log_event("auto_member_toggled", user_id=query.from_user.id, details=f"enabled={new_value}")
                await self.show_join_settings(query); return
            if data == "toggle_auto":
                current = self.db.get_setting("auto_message_enabled", "1")
                self.db.set_setting("auto_message_enabled", "0" if current == "1" else "1")
                await self.show_join_settings(query); return
            if data == "toggle_maintenance":
                current = self.db.get_setting("maintenance_mode", "0")
                self.db.set_setting("maintenance_mode", "0" if current == "1" else "1")
                await self.show_settings(query); return
            if data == "toggle_check":
                current = self.db.get_setting("check_join_enabled", "0")
                self.db.set_setting("check_join_enabled", "0" if current == "1" else "1")
                await self.show_settings(query); return
            if data.startswith("btn_style:"):
                style = data.split(":", 1)[1]
                if style in BUTTON_STYLES:
                    self.db.set_setting("start_button_style", style)
                await self.show_settings(query); return

            # Caption / media / button builders.
            if data == "set_caption":
                context.user_data["awaiting"] = "caption"
                context.user_data["message_target"] = "join_request"
                await query.message.reply_text(
                    "Send the caption/text now.\n\nUse Telegram's Custom Emoji picker for Premium Emoji. "
                    "The bot stores Telegram entities.\n\nUse /cancel to cancel."
                ); return
            if data == "set_caption_start":
                context.user_data["awaiting"] = "caption"
                context.user_data["message_target"] = "start"
                await query.message.reply_text(
                    "Send the /start message text now.\n\nUse Telegram's Custom Emoji picker for Premium Emoji.\n\n"
                    "Use /cancel to cancel."
                ); return
            if data == "toggle_parse":
                message = self.db.get_join_message()
                current = message["parse_mode"] or "HTML"
                new_mode = "MarkdownV2" if current == "HTML" else "HTML"
                self.db.execute("UPDATE messages SET parse_mode=?,updated_at=? WHERE id=?",
                                (new_mode, utc_now(), message["id"]), commit=True)
                await self.show_message_builder(query); return
            if data == "toggle_parse_start":
                message = self.db.get_start_message()
                current = message["parse_mode"] or "HTML"
                new_mode = "MarkdownV2" if current == "HTML" else "HTML"
                self.db.execute("UPDATE messages SET parse_mode=?,updated_at=? WHERE id=?",
                                (new_mode, utc_now(), message["id"]), commit=True)
                await self.show_start_message_builder(query); return
            if data in ("set_photo", "set_media"):
                context.user_data["awaiting"] = "media"
                context.user_data["message_target"] = "join_request"
                await query.message.reply_text(
                    "Send photo, video, document, animation, audio or voice now.\n"
                    "You may include a Premium/custom-emoji caption.\n\nUse /cancel to cancel."
                ); return
            if data == "set_media_start":
                context.user_data["awaiting"] = "media"
                context.user_data["message_target"] = "start"
                await query.message.reply_text(
                    "Send the /start photo, video, document, animation, audio or voice now.\n"
                    "You may include a Premium/custom-emoji caption.\n\nUse /cancel to cancel."
                ); return
            if data == "remove_media":
                message = self.db.get_join_message()
                self.db.execute("UPDATE messages SET media_type='none',file_id='',updated_at=? WHERE id=?",
                                (utc_now(), message["id"]), commit=True)
                for key in ("join_msg_source_chat", "join_msg_source_id", "join_msg_source_exact", "join_msg_source_entities"):
                    self.db.set_setting(key, "0" if key != "join_msg_source_entities" else "[]")
                await self.show_message_builder(query); return
            if data == "remove_media_start":
                message = self.db.get_start_message()
                self.db.execute("UPDATE messages SET media_type='none',file_id='',updated_at=? WHERE id=?",
                                (utc_now(), message["id"]), commit=True)
                entities_key, chat_key, id_key, exact_key = _source_setting_keys("start")
                self.db.set_setting(chat_key, "0")
                self.db.set_setting(id_key, "0")
                self.db.set_setting(exact_key, "0")
                self.db.set_setting(entities_key, "[]")
                await self.show_start_message_builder(query); return
            if data == "add_button":
                context.user_data["button_target"] = "join"
                context.user_data["awaiting"] = "btn_link"
                await query.message.reply_text(
                    "Step 1/4 — Send the button URL.\nExample: https://t.me/yourchannel\n\nUse /cancel to cancel."
                ); return
            if data == "add_button_start":
                context.user_data["button_target"] = "start"
                context.user_data["awaiting"] = "btn_link"
                await query.message.reply_text(
                    "Step 1/4 — Send the button URL.\nExample: https://t.me/yourchannel\n\nUse /cancel to cancel."
                ); return
            if data == "clear_buttons":
                message = self.db.get_join_message()
                self.db.clear_message_buttons(message["id"])
                await self.show_message_builder(query); return
            if data == "clear_buttons_start":
                message = self.db.get_start_message()
                self.db.clear_message_buttons(message["id"])
                await self.show_start_message_builder(query); return
            if data == "preview":
                await self.preview_message(query, context); return
            if data == "preview_start":
                await self.preview_start_message(query, context); return
            if data == "test_start":
                await self.test_start_message(query, context); return

            if data in ("join_approve_all", "join_reject_all"):
                if not self.is_owner(user.id):
                    await query.message.reply_text("❌ Only the Owner can run bulk join-request actions.")
                    return
                approve = data == "join_approve_all"
                await query.answer("Processing pending requests…")
                try:
                    done, failed, channel_failures = await self.process_all_join_requests(approve)
                    verb = "approved" if approve else "rejected"
                    await query.message.reply_text(
                        f"{'✅' if approve else '❌'} Bulk action complete.\\n\\n"
                        f"{verb.title()}: {done}\\nFailed: {failed}\\n"
                        f"Channels skipped/failed: {channel_failures}",
                        reply_markup=admin_menu(self.is_main),
                    )
                except Exception as exc:
                    logger.exception("Bulk join-request action failed")
                    self.db.log_error("EXCEPTION", "join_requests", data, repr(exc))
                    await query.message.reply_text(
                        f"⚠️ Bulk action failed safely: {clean_error(exc)[:700]}",
                        reply_markup=admin_menu(self.is_main),
                    )
                return

            if data.startswith("channel_toggle:"):
                channel_id = safe_int(data.split(":", 1)[1], None)
                if channel_id is None:
                    await query.message.reply_text("Invalid channel action."); return
                self.db.execute(
                    "UPDATE channels SET enabled=CASE enabled WHEN 1 THEN 0 ELSE 1 END, updated_at=? WHERE channel_id=?",
                    (utc_now(), channel_id), commit=True,
                )
                await self.show_channels(query); return
            if data.startswith("channel_auto:"):
                channel_id = safe_int(data.split(":", 1)[1], None)
                if channel_id is None:
                    await query.message.reply_text("Invalid channel action."); return
                row = self.db.fetchone("SELECT * FROM channels WHERE channel_id=?", (channel_id,))
                if not row:
                    await query.message.reply_text("Channel not found."); return
                if not row["auto_approve"]:
                    try:
                        member = await context.bot.get_chat_member(chat_id=channel_id, user_id=context.bot.id)
                        status = str(getattr(member, "status", ""))
                        can_invite = getattr(member, "can_invite_users", None)
                        has_invite_right = status == "creator" or can_invite is True
                        if status not in ("administrator", "creator") or not has_invite_right:
                            await query.answer(
                                "Bot needs channel admin + Invite Users permission for auto-approve.",
                                show_alert=True,
                            )
                            return
                    except TelegramError as exc:
                        await query.answer(f"Cannot verify channel permissions: {clean_error(exc)[:120]}",
                                           show_alert=True)
                        return
                self.db.execute(
                    "UPDATE channels SET auto_approve=CASE auto_approve WHEN 1 THEN 0 ELSE 1 END, updated_at=? WHERE channel_id=?",
                    (utc_now(), channel_id), commit=True,
                )
                await self.show_channels(query); return
            if data.startswith("remove_channel:"):
                channel_id = safe_int(data.split(":", 1)[1], None)
                if channel_id is None:
                    await query.message.reply_text("Invalid channel action."); return
                if not self.is_owner(user.id):
                    await query.message.reply_text("Only Owner can remove channels."); return
                self.db.execute("DELETE FROM channels WHERE channel_id=?", (channel_id,), commit=True)
                await self.show_channels(query); return
            if data == "add_channel":
                context.user_data["awaiting"] = "channel"
                await query.message.reply_text(
                    "Send the channel @username or numeric channel ID.\n\n"
                    "Public: @MyChannel\nPrivate: -1001234567890\n"
                    "Telegram Bot API cannot resolve a private invite link by itself; "
                    "for private channels send the numeric -100... channel ID.\n\n"
                    "The bot must be an admin in the channel.\nUse /cancel to cancel."
                ); return

            # Broadcast flow.
            if data == "broadcast_start":
                context.user_data["awaiting"] = "broadcast"
                context.user_data["pending_broadcast_buttons"] = []
                await query.message.reply_text(
                    "Send the broadcast content now.\n\nText, photo, video, document, animation, audio or voice are supported. "
                    "Premium/custom emoji are preserved from Telegram entities.\n\nUse /cancel to cancel."
                ); return
            if data == "broadcast_add_button":
                if not context.user_data.get("pending_broadcast_id"):
                    await query.message.reply_text("No pending broadcast draft."); return
                context.user_data["button_target"] = "broadcast"
                context.user_data["awaiting"] = "btn_link"
                await query.message.reply_text(
                    "Step 1/4 — Send the button URL.\nExample: https://t.me/yourchannel\n\nUse /cancel to cancel."
                ); return
            if data == "broadcast_clear_buttons":
                broadcast_id = context.user_data.get("pending_broadcast_id")
                if broadcast_id:
                    context.user_data["pending_broadcast_buttons"] = []
                    self.db.execute("UPDATE broadcasts SET buttons_json='[]' WHERE id=? AND status='pending'",
                                    (broadcast_id,), commit=True)
                await query.message.reply_text("🗑 Broadcast buttons cleared.", reply_markup=broadcast_draft_keyboard())
                return
            if data == "broadcast_preview":
                broadcast_id = context.user_data.get("pending_broadcast_id")
                if not broadcast_id:
                    await query.message.reply_text("No pending broadcast draft."); return
                try:
                    row = self.db.fetchone("SELECT * FROM broadcasts WHERE id=? AND status='pending'", (broadcast_id,))
                    if not row:
                        await query.message.reply_text("Broadcast draft not found."); return
                    await send_broadcast_to_user(context.bot, row, query.from_user.id)
                    await query.message.reply_text("👁 Broadcast preview sent.", reply_markup=broadcast_draft_keyboard())
                except Exception as exc:
                    await query.message.reply_text(f"Preview failed: {clean_error(exc)[:700]}",
                                                   reply_markup=broadcast_draft_keyboard())
                return
            if data == "broadcast_send":
                broadcast_id = context.user_data.get("pending_broadcast_id")
                if not broadcast_id:
                    await query.message.reply_text("No pending broadcast draft."); return
                await self.start_broadcast_send(query.message, context, broadcast_id); return

            if data == "backup_create":
                await self.create_backup(query); return
            if data == "export_users":
                await self.export_csv(query, "users"); return
            if data == "export_requests":
                await self.export_csv(query, "join_requests"); return
            if data == "export_broadcasts":
                await self.export_csv(query, "broadcast_logs"); return
            if data == "check_join":
                await answer_query(query, "Verification requires the user to join the configured channel(s).")
                return

            await answer_query(query, "Unknown or expired action.", True)
        except Exception as exc:
            logger.exception("Admin callback failed: %s", data)
            self.db.log_error("EXCEPTION", "admin_callback", data, repr(exc))
            try:
                await query.message.reply_text("⚠️ Operation failed safely.\nCheck Admin → Logs.")
            except Exception:
                pass

    async def btn_add_style_callback(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        query = update.callback_query
        if not query:
            return
        user = query.from_user
        if not user or not self.is_admin(user.id):
            await query.answer("Access Denied", show_alert=True)
            return
        data = query.data or ""
        if not data.startswith("btn_add_style:"):
            return
        style = normalize_button_style(data.split(":", 1)[1])
        url = context.user_data.pop("btn_pending_url", None)
        name = context.user_data.pop("btn_pending_name", None)
        icon_id = context.user_data.pop("btn_pending_icon", None)
        target = context.user_data.get("button_target", "join")
        context.user_data.pop("awaiting", None)
        await query.answer()
        if not url or not name:
            await query.message.reply_text("Button data expired. Start Add Button again."); return
        button = {"text": name[:64], "url": url, "style": style,
                  "icon_custom_emoji_id": icon_id, "row": 0, "position": 0}
        if target in ("broadcast", "master_broadcast"):
            buttons = context.user_data.setdefault("pending_broadcast_buttons", [])
            button["row"] = len(buttons)
            buttons.append(button)
            broadcast_id = context.user_data.get("pending_broadcast_id")
            target_db = self.db
            if target == "master_broadcast" and self.is_main and BOT_MANAGER is not None:
                target_inst = BOT_MANAGER.children.get(context.user_data.get("master_broadcast_target"))
                if target_inst:
                    target_db = target_inst.db
            if broadcast_id:
                target_db.execute("UPDATE broadcasts SET buttons_json=? WHERE id=? AND status='pending'",
                                  (json.dumps(buttons, ensure_ascii=False), broadcast_id), commit=True)
            await query.message.reply_text(
                f"✅ Broadcast button added: [{style.upper()}] {name}\n"
                + ("⭐ Premium button icon saved." if icon_id else ""),
                reply_markup=broadcast_draft_keyboard(),
            )
            return
        target_name = "start" if target == "start" else "join_request"
        target_msg = self.db.get_message_by_name(target_name)
        existing = self.db.get_message_buttons(target_msg["id"])
        next_row = len(existing)
        self.db.add_message_button(target_msg["id"], name, url, row_number=next_row,
                                   position=0, style=style, icon_custom_emoji_id=icon_id)
        prefix = "/start " if target_name == "start" else ""
        await query.message.reply_text(
            f"✅ {prefix}Button added: [{style.upper()}] {name}\n"
            + ("⭐ Premium button icon saved." if icon_id else ""),
            reply_markup=admin_menu(self.is_main),
        )

    # ============================================================
    # PREVIEW / TEST
    # ============================================================
    async def preview_message(self, query, context):
        try:
            await send_configured_message(context.bot, self.db, query.from_user.id, query.from_user)
            await query.message.reply_text("👁 Preview sent.")
        except Exception as exc:
            await query.message.reply_text(f"Preview failed: {clean_error(exc)[:700]}")

    async def test_message(self, query, context):
        try:
            await send_configured_message(context.bot, self.db, query.from_user.id, query.from_user)
            await query.message.reply_text("🧪 Test message sent.")
        except Exception as exc:
            await query.message.reply_text(f"Test failed: {clean_error(exc)[:700]}")

    async def preview_start_message(self, query, context):
        try:
            sent = await send_named_message(context.bot, self.db, query.from_user.id, "start",
                                            user=query.from_user, extra_keyboard=start_keyboard(self.db))
            if sent is None:
                await query.message.reply_text("Nothing configured yet for /start -- the classic default welcome would be used instead.")
            else:
                await query.message.reply_text("👁 Start message preview sent.")
        except Exception as exc:
            await query.message.reply_text(f"Preview failed: {clean_error(exc)[:700]}")

    async def test_start_message(self, query, context):
        try:
            sent = await send_named_message(context.bot, self.db, query.from_user.id, "start",
                                            user=query.from_user, extra_keyboard=start_keyboard(self.db))
            if sent is None:
                await query.message.reply_text("Nothing configured yet for /start -- the classic default welcome would be used instead.")
            else:
                await query.message.reply_text("🧪 Start message test sent.")
        except Exception as exc:
            await query.message.reply_text(f"Test failed: {clean_error(exc)[:700]}")

    # ============================================================
    # ADMIN INPUT
    # ============================================================
    async def admin_input(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        user = update.effective_user
        message = update.message
        if not user or not message:
            return
        creator_allowed = self.is_main and self.is_bot_creator(user.id)
        if not self.is_admin(user.id) and not creator_allowed:
            return
        # Main-only Bot Manager input states (create-bot / edit-admin /
        # master-broadcast-through-child) are dispatched before the generic
        # admin input router below.
        if self.is_main:
            try:
                if await main_admin_input_extension(self, update, context):
                    return
            except Exception as exc:
                state = context.user_data.get("awaiting")
                logger.exception("Main admin input extension failed: %s", state)
                self.db.log_error("EXCEPTION", "admin_input", state or "main_ext", repr(exc))
                await message.reply_text(f"Operation failed safely:\n{clean_error(exc)[:700]}")
                return
        state = context.user_data.get("awaiting")

        # Owner-only backup restore.
        if (message.document and message.document.file_name
                and Path(message.document.file_name).suffix.lower() in {".db", ".sqlite", ".sqlite3"}):
            if self.is_owner(user.id):
                await self.restore_backup_from_document(message, context)
            else:
                await message.reply_text("Only the owner can restore backups.")
            return

        if not state:
            return
        try:
            if state == "caption":
                target_name = context.user_data.get("message_target", "join_request")
                entities_key, chat_key, id_key, exact_key = _source_setting_keys(target_name)
                text = message.text if message.text is not None else (message.caption or "")
                if len(text) > MAX_TEXT_LENGTH:
                    await message.reply_text("Caption is too long (maximum 4096 characters)."); return
                target_msg = self.db.get_message_by_name(target_name)
                self.db.execute("UPDATE messages SET caption=?,updated_at=? WHERE id=?",
                                (text, utc_now(), target_msg["id"]), commit=True)
                entities = (message.entities if message.text is not None else message.caption_entities) or ()
                self.db.set_setting(entities_key, serialize_message_entities(entities))
                if (target_msg["media_type"] or "none") != "none" or message.caption:
                    self.db.set_setting(chat_key, "0")
                    self.db.set_setting(id_key, "0")
                    self.db.set_setting(exact_key, "0")
                else:
                    self.db.set_setting(chat_key, str(message.chat_id))
                    self.db.set_setting(id_key, str(message.message_id))
                    self.db.set_setting(exact_key, "1")
                custom_count = count_custom_emoji(entities)
                context.user_data.pop("awaiting", None)
                context.user_data.pop("message_target", None)
                label = "/start message" if target_name == "start" else "Caption"
                await message.reply_text(
                    f"✅ {label} saved. {custom_count} Premium/custom emoji entity(ies) detected.\n"
                    "Preview/Test will use Telegram entities directly.",
                    reply_markup=admin_menu(self.is_main),
                )
                return

            if state in ("media", "photo"):
                target_name = context.user_data.get("message_target", "join_request")
                entities_key, chat_key, id_key, exact_key = _source_setting_keys(target_name)
                media_type = None
                file_id = None
                caption = message.caption or ""
                entities = message.caption_entities or ()
                if message.photo:
                    media_type, file_id = "photo", message.photo[-1].file_id
                elif message.video:
                    media_type, file_id = "video", message.video.file_id
                elif message.animation:
                    media_type, file_id = "animation", message.animation.file_id
                elif message.document:
                    media_type, file_id = "document", message.document.file_id
                elif message.audio:
                    media_type, file_id = "audio", message.audio.file_id
                elif message.voice:
                    media_type, file_id = "voice", message.voice.file_id
                if not media_type or not file_id:
                    await message.reply_text("Send a photo, video, document, animation, audio or voice message."); return
                if len(caption) > MAX_CAPTION_LENGTH:
                    await message.reply_text(f"Media caption is too long. Telegram allows up to {MAX_CAPTION_LENGTH} characters."); return
                target_msg = self.db.get_message_by_name(target_name)
                self.db.execute("UPDATE messages SET media_type=?,file_id=?,caption=?,updated_at=? WHERE id=?",
                                (media_type, file_id, caption, utc_now(), target_msg["id"]), commit=True)
                self.db.set_setting(entities_key, serialize_message_entities(entities))
                if caption:
                    self.db.set_setting(chat_key, str(message.chat_id))
                    self.db.set_setting(id_key, str(message.message_id))
                    self.db.set_setting(exact_key, "1")
                else:
                    self.db.set_setting(chat_key, "0")
                    self.db.set_setting(id_key, "0")
                    self.db.set_setting(exact_key, "0")
                context.user_data.pop("awaiting", None)
                context.user_data.pop("message_target", None)
                prefix = "/start " if target_name == "start" else ""
                await message.reply_text(
                    f"✅ {prefix}{media_type.title()} saved. {count_custom_emoji(entities)} Premium/custom emoji entity(ies) detected.",
                    reply_markup=admin_menu(self.is_main),
                )
                return

            if state == "btn_link":
                raw = (message.text or "").strip()
                if raw.startswith("@"):
                    raw = f"https://t.me/{raw.lstrip('@')}"
                elif raw.startswith("t.me/"):
                    raw = "https://" + raw
                if not valid_http_url(raw):
                    await message.reply_text("Invalid URL. Send a full http(s) URL, e.g. https://t.me/yourchannel"); return
                context.user_data["btn_pending_url"] = raw
                context.user_data["awaiting"] = "btn_name"
                await message.reply_text(
                    "Step 2/4 — Send the button label.\n\nYou can include one Premium/custom emoji. It will be used as the button icon.\nUse /cancel to cancel."
                ); return

            if state == "btn_name":
                name = (message.text or message.caption or "").strip()
                if not name:
                    await message.reply_text("Button label cannot be empty."); return
                icon_id = None
                entities = message.entities or message.caption_entities or ()
                for entity in entities:
                    if getattr(entity, "type", None) == MessageEntity.CUSTOM_EMOJI:
                        icon_id = getattr(entity, "custom_emoji_id", None)
                        break
                context.user_data["btn_pending_name"] = name[:64]
                context.user_data["btn_pending_icon"] = icon_id
                context.user_data["awaiting"] = "btn_style_choice"
                await message.reply_text(
                    "Step 3/4 — Choose button color:",
                    reply_markup=InlineKeyboardMarkup([[
                        _make_callback_button("🔵 Primary", "btn_add_style:primary", "primary"),
                        _make_callback_button("🟢 Success", "btn_add_style:success", "success"),
                        _make_callback_button("🔴 Danger", "btn_add_style:danger", "danger"),
                    ]]),
                ); return

            if state == "btn_style_choice":
                await message.reply_text(
                    "Please tap a color button above.",
                    reply_markup=InlineKeyboardMarkup([[
                        _make_callback_button("🔵 Primary", "btn_add_style:primary", "primary"),
                        _make_callback_button("🟢 Success", "btn_add_style:success", "success"),
                        _make_callback_button("🔴 Danger", "btn_add_style:danger", "danger"),
                    ]]),
                ); return

            if state == "broadcast_buttons":
                await message.reply_text(
                    "Broadcast draft is ready. Use the buttons below to add buttons or send it.",
                    reply_markup=broadcast_draft_keyboard(),
                ); return

            if state == "backup_channel":
                raw = (message.text or "").strip()
                if not raw:
                    await message.reply_text("Send the private/public backup channel ID, @username, or t.me link."); return
                if raw.startswith("@"):
                    lookup = raw
                elif "t.me/" in raw:
                    tail = raw.split("t.me/", 1)[1].split("/", 1)[0].strip()
                    lookup = f"@{tail}"
                else:
                    try:
                        lookup = int(raw)
                    except ValueError:
                        lookup = f"@{raw.lstrip('@')}"
                try:
                    chat = await context.bot.get_chat(lookup)
                    if chat.type != "channel":
                        await message.reply_text("That is not a Telegram channel."); return
                    member = await context.bot.get_chat_member(chat.id, context.bot.id)
                    status = str(getattr(member, "status", ""))
                    if status not in ("administrator", "creator"):
                        await message.reply_text("❌ Bot is not an administrator in this channel."); return
                    if getattr(member, "can_post_messages", None) is False:
                        await message.reply_text("❌ Bot is admin, but it does not have permission to post messages."); return
                    username = getattr(chat, "username", None) or ""
                    self.db.set_setting("backup_channel_id", str(chat.id))
                    self.db.set_setting("backup_channel_username", username)
                    self.db.set_setting("backup_channel_title", chat.title or "")
                    self.db.set_setting("backup_channel_enabled", "1")
                    context.user_data.pop("awaiting", None)
                    current_interval_label = _format_interval_label(self.get_backup_interval_seconds())
                    await message.reply_text(
                        "✅ Private backup channel configured.\n\n"
                        f"📢 {chat.title or 'Private Backup Vault'}\n🆔 {chat.id}\n\n"
                        "🔒 This backup channel is admin-only and is never shown to normal users.\n"
                        "☁️ Automatic full backup is now ON.\n"
                        f"⏱ Current interval: {current_interval_label}\n\n"
                        "⚠️ On Render's free tier, the local SQLite file is wiped on every sleep/restart. "
                        "This backup channel is what protects your data.",
                        reply_markup=admin_menu(self.is_main),
                    )
                    try:
                        await message.reply_text("🧪 Sending a test backup to the channel...")
                        await self.automatic_backup_once(context.bot)
                        await message.reply_text("✅ Test backup uploaded successfully.")
                    except Exception as exc:
                        self.db.log_error("ERROR", "backup", "channel_test", repr(exc))
                        await message.reply_text(
                            f"⚠️ Channel saved, but the test upload failed:\n{clean_error(exc)[:500]}\n\nCheck that the bot can post in the channel."
                        )
                except TelegramError as exc:
                    await message.reply_text(f"❌ Could not access the backup channel:\n{clean_error(exc)[:700]}")
                return

            if state == "channel":
                raw = (message.text or "").strip()
                if raw.startswith("@"):
                    raw = raw.lstrip("@")
                elif "t.me/" in raw:
                    raw = raw.split("t.me/", 1)[1].split("/", 1)[0]
                try:
                    try:
                        channel_id_or_username = int(raw)
                    except ValueError:
                        channel_id_or_username = f"@{raw}"
                    chat = await context.bot.get_chat(channel_id_or_username)
                    if chat.type != "channel":
                        await message.reply_text("Please provide a Telegram channel username/link or numeric ID."); return
                    member = await context.bot.get_chat_member(chat.id, context.bot.id)
                    if str(getattr(member, "status", "")) not in ("administrator", "creator"):
                        await message.reply_text("Bot is not an administrator in this channel."); return
                    now = utc_now()
                    self.db.execute(
                        """
                        INSERT INTO channels(channel_id,username,title,type,enabled,required,auto_approve,sort_order,created_at,updated_at)
                        VALUES(?,?,?,?,1,1,0,0,?,?)
                        ON CONFLICT(channel_id) DO UPDATE SET
                            username=excluded.username,title=excluded.title,type=excluded.type,updated_at=excluded.updated_at
                        """,
                        (chat.id, chat.username, chat.title or "", chat.type, now, now), commit=True,
                    )
                    context.user_data.pop("awaiting", None)
                    await message.reply_text(
                        f"✅ Channel configured.\n\nTitle: {chat.title or '-'}\nID: {chat.id}\n"
                        + (f"Username: @{chat.username}" if chat.username else ""),
                        reply_markup=admin_menu(self.is_main),
                    )
                except TelegramError as exc:
                    await message.reply_text(f"Could not access the channel.\n\n{clean_error(exc)[:700]}")
                return

            if state == "broadcast":
                await self.create_broadcast(update, context); return

        except Exception as exc:
            logger.exception("Admin input failed: %s", state)
            self.db.log_error("EXCEPTION", "admin_input", state, repr(exc))
            await message.reply_text(f"Operation failed safely:\n{clean_error(exc)[:700]}")


    # ============================================================
    # BROADCAST
    # ============================================================
    def _broadcast_draft_keyboard(self):
        return broadcast_draft_keyboard()

    async def create_broadcast(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        user = update.effective_user
        message = update.message
        if not user or not message:
            return
        media_type = "none"
        file_id = None
        text = ""
        caption = ""
        source_entities = message.entities or ()
        if message.photo:
            media_type, file_id = "photo", message.photo[-1].file_id
            caption = message.caption or ""
            source_entities = message.caption_entities or ()
        elif message.video:
            media_type, file_id = "video", message.video.file_id
            caption = message.caption or ""; source_entities = message.caption_entities or ()
        elif message.animation:
            media_type, file_id = "animation", message.animation.file_id
            caption = message.caption or ""; source_entities = message.caption_entities or ()
        elif message.document:
            media_type, file_id = "document", message.document.file_id
            caption = message.caption or ""; source_entities = message.caption_entities or ()
        elif message.audio:
            media_type, file_id = "audio", message.audio.file_id
            caption = message.caption or ""; source_entities = message.caption_entities or ()
        elif message.voice:
            media_type, file_id = "voice", message.voice.file_id
            caption = message.caption or ""; source_entities = message.caption_entities or ()
        else:
            text = message.text or ""
            caption = text
            source_entities = message.entities or ()
        content = caption if media_type != "none" else text
        max_len = 1024 if media_type != "none" else MAX_TEXT_LENGTH
        if not content and media_type == "none":
            await message.reply_text("Broadcast content cannot be empty."); return
        if len(content) > max_len:
            await message.reply_text(f"Broadcast content is too long. Maximum: {max_len} characters."); return
        buttons = context.user_data.get("pending_broadcast_buttons", [])
        entities_json = serialize_message_entities(source_entities)
        cursor = self.db.execute(
            """
            INSERT INTO broadcasts(
                admin_id,text,media_type,file_id,caption,parse_mode,
                source_chat_id,source_message_id,entities_json,buttons_json,status,created_at
            ) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
            """,
            (user.id, text, media_type, file_id, caption,
             self.db.get_join_message()["parse_mode"] or "HTML",
             message.chat_id, message.message_id, entities_json,
             json.dumps(buttons, ensure_ascii=False), "pending", utc_now()),
            commit=True,
        )
        broadcast_id = cursor.lastrowid
        context.user_data["pending_broadcast_id"] = broadcast_id
        context.user_data["awaiting"] = "broadcast_buttons"
        custom_count = count_custom_emoji(source_entities)
        await message.reply_text(
            f"📢 Broadcast #{broadcast_id} ready.\n\nType: {media_type}\n"
            f"Premium/custom emoji: {custom_count}\nButtons: {len(buttons)}\n\n"
            "Add buttons or tap Send Now. The original Telegram message is copied when possible, preserving its entities exactly.",
            reply_markup=broadcast_draft_keyboard(),
        )

    async def start_broadcast_send(self, message, context, broadcast_id):
        row = self.db.fetchone("SELECT * FROM broadcasts WHERE id=? AND status='pending'", (broadcast_id,))
        if not row:
            await message.reply_text("Pending broadcast not found or already sent."); return
        self.db.execute("UPDATE broadcasts SET status='running',started_at=? WHERE id=?",
                        (utc_now(), broadcast_id), commit=True)
        context.user_data.pop("pending_broadcast_id", None)
        context.user_data.pop("pending_broadcast_buttons", None)
        context.user_data.pop("button_target", None)
        context.user_data.pop("awaiting", None)
        await message.reply_text(f"📢 Broadcast #{broadcast_id} started.")
        task = self.application.create_task(self.run_broadcast(broadcast_id))
        self.broadcast_tasks.add(task)
        task.add_done_callback(self.broadcast_tasks.discard)

    async def run_broadcast(self, broadcast_id: int):
        try:
            row = self.db.fetchone("SELECT * FROM broadcasts WHERE id=?", (broadcast_id,))
            if not row:
                return
            users = self.db.fetchall("SELECT user_id FROM users WHERE is_blocked=0 ORDER BY user_id")
            total_row = self.db.fetchone("SELECT COUNT(*) AS c FROM users")
            total = int(total_row["c"]) if total_row else len(users)
            self.db.execute("UPDATE broadcasts SET total=? WHERE id=?", (total, broadcast_id), commit=True)
            count_rows = self.db.fetchall(
                "SELECT status,COUNT(*) AS c FROM broadcast_logs WHERE broadcast_id=? GROUP BY status",
                (broadcast_id,),
            )
            counts = {r["status"]: int(r["c"]) for r in count_rows}
            sent = counts.get("sent", 0)
            failed = counts.get("failed", 0)
            blocked = counts.get("blocked", 0)
            for item in users:
                user_id = item["user_id"]
                existing = self.db.fetchone(
                    "SELECT status FROM broadcast_logs WHERE broadcast_id=? AND user_id=?",
                    (broadcast_id, user_id),
                )
                if existing and existing["status"] in ("sent", "blocked"):
                    continue
                try:
                    await send_broadcast_to_user(self.application.bot, row, user_id)
                    sent += 1
                    status, error = "sent", None
                except Forbidden as exc:
                    blocked += 1
                    status, error = "blocked", clean_error(exc)
                    self.db.execute("UPDATE users SET is_blocked=1 WHERE user_id=?", (user_id,), commit=True)
                except RetryAfter as exc:
                    await asyncio.sleep(float(exc.retry_after) + 1)
                    try:
                        await send_broadcast_to_user(self.application.bot, row, user_id)
                        sent += 1
                        status, error = "sent", None
                    except Forbidden as retry_exc:
                        blocked += 1
                        status, error = "blocked", clean_error(retry_exc)
                        self.db.execute("UPDATE users SET is_blocked=1 WHERE user_id=?", (user_id,), commit=True)
                    except Exception as retry_exc:
                        failed += 1
                        status, error = "failed", clean_error(retry_exc)
                except (NetworkError, TimedOut) as exc:
                    retry_ok = False
                    last_error = exc
                    for retry_index in range(2):
                        try:
                            await asyncio.sleep(2 ** retry_index)
                            await send_broadcast_to_user(self.application.bot, row, user_id)
                            sent += 1
                            status, error = "sent", None
                            retry_ok = True
                            break
                        except Forbidden as retry_exc:
                            blocked += 1
                            status, error = "blocked", clean_error(retry_exc)
                            self.db.execute("UPDATE users SET is_blocked=1 WHERE user_id=?", (user_id,), commit=True)
                            retry_ok = True
                            break
                        except Exception as retry_exc:
                            last_error = retry_exc
                    if not retry_ok:
                        failed += 1
                        status, error = "failed", clean_error(last_error)
                except Exception as exc:
                    failed += 1
                    status, error = "failed", clean_error(exc)
                self.db.execute(
                    """
                    INSERT INTO broadcast_logs(broadcast_id,user_id,status,error,created_at)
                    VALUES(?,?,?,?,?)
                    ON CONFLICT(broadcast_id,user_id) DO UPDATE SET
                        status=excluded.status,error=excluded.error,created_at=excluded.created_at
                    """,
                    (broadcast_id, user_id, status, error, utc_now()),
                    commit=True,
                )
                self.db.execute(
                    "UPDATE broadcasts SET sent=?,failed=?,blocked=?,next_user_id=? WHERE id=?",
                    (sent, failed, blocked, user_id, broadcast_id),
                    commit=True,
                )
                await asyncio.sleep(BROADCAST_DELAY)
            self.db.execute(
                """
                UPDATE broadcasts SET status='completed',sent=?,failed=?,blocked=?,next_user_id=NULL,finished_at=?
                WHERE id=?
                """,
                (sent, failed, blocked, utc_now(), broadcast_id),
                commit=True,
            )
            staged = row["staged_media_path"] if "staged_media_path" in row.keys() else ""
            if staged:
                try:
                    Path(staged).unlink(missing_ok=True)
                    self.db.execute("UPDATE broadcasts SET staged_media_path=NULL WHERE id=?", (broadcast_id,), commit=True)
                except Exception:
                    logger.warning("Could not remove staged broadcast media for id=%s", broadcast_id)
            self.db.log_event("broadcast_completed",
                              details=f"id={broadcast_id};sent={sent};failed={failed};blocked={blocked}")
        except Exception as exc:
            logger.exception("Broadcast crashed safely")
            self.db.execute("UPDATE broadcasts SET status='paused' WHERE id=? AND status='running'",
                            (broadcast_id,), commit=True)
            self.db.log_error("EXCEPTION", "broadcast", "worker", repr(exc))

    # ============================================================
    # BACKUP / DISASTER RECOVERY
    # ============================================================
    def backup_channel_id(self) -> Optional[int]:
        if self.db.get_setting("backup_channel_enabled", "0") != "1":
            return None
        raw = self.db.get_setting("backup_channel_id", "").strip()
        if not raw:
            return None
        try:
            return int(raw)
        except (TypeError, ValueError):
            return None

    def prune_local_backups(self) -> None:
        try:
            files = sorted(
                (f for f in self.db.path.parent.glob("backup_*.db") if f.is_file()),
                key=lambda f: f.stat().st_mtime, reverse=True,
            )
            for old_file in files[AUTO_BACKUP_LOCAL_RETENTION:]:
                try:
                    old_file.unlink()
                except OSError:
                    logger.warning("Could not prune local backup: %s", old_file)
        except Exception:
            logger.exception("Local backup pruning failed")

    def create_backup_file(self, created_by: Optional[int] = None):
        if not self.db.path.exists():
            raise FileNotFoundError("Database file does not exist.")
        filename = "backup_" + datetime.now(timezone.utc).strftime("%Y_%m_%d_%H%M%S_%f") + ".db"
        destination = self.db.path.parent / filename
        source = None
        target = None
        try:
            source = sqlite3.connect(str(self.db.path), timeout=30)
            target = sqlite3.connect(str(destination), timeout=30)
            source.backup(target)
            target.commit()
            integrity = target.execute("PRAGMA integrity_check").fetchone()[0]
            if integrity != "ok":
                raise RuntimeError(f"Backup integrity check failed: {integrity}")
            size = destination.stat().st_size
            self.db.execute(
                "INSERT INTO backups(filename,created_at,created_by,size) VALUES(?,?,?,?)",
                (filename, utc_now(), created_by, size), commit=True,
            )
            self.prune_local_backups()
            return destination, filename, size
        finally:
            if source: source.close()
            if target: target.close()

    async def send_backup_to_channel(self, bot, destination: Path, filename: str, size: int, automatic: bool):
        channel_id = self.backup_channel_id()
        if not channel_id:
            return False
        caption = ("🔐 AUTOMATIC BOT BACKUP\n" if automatic else "💾 MANUAL BOT BACKUP\n")
        caption += (f"📁 {filename}\n📦 Size: {size:,} bytes\n🕐 UTC: {utc_now()}\n\n"
                    "This .db file contains the bot's persisted database state and can be "
                    "uploaded to the bot by the owner to restore it.")
        with destination.open("rb") as file:
            await bot.send_document(chat_id=channel_id, document=InputFile(file, filename=filename),
                                    caption=caption[:1024])
        return True

    async def create_backup(self, query):
        if not self.db.path.exists():
            await query.message.reply_text("Database file does not exist."); return
        try:
            destination, filename, size = await asyncio.to_thread(self.create_backup_file, query.from_user.id)
            with destination.open("rb") as file:
                await query.message.reply_document(
                    document=InputFile(file, filename=filename),
                    caption=f"💾 Backup created successfully.\nSize: {size:,} bytes\n\nTo restore: send this .db file to me.",
                )
            channel_id = self.backup_channel_id()
            if channel_id:
                try:
                    await self.send_backup_to_channel(query.get_bot(), destination, filename, size, automatic=False)
                    await query.message.reply_text("☁️ A copy was also uploaded to the configured backup channel.")
                except Exception as channel_exc:
                    logger.exception("Manual backup channel upload failed")
                    self.db.log_error("ERROR", "backup", "manual_channel_upload", repr(channel_exc))
                    await query.message.reply_text(
                        f"⚠️ Local/manual backup succeeded, but channel upload failed:\n{clean_error(channel_exc)[:500]}"
                    )
        except Exception as exc:
            logger.exception("Backup creation failed")
            self.db.log_error("ERROR", "backup", "create", repr(exc))
            await query.message.reply_text(f"Backup failed:\n{clean_error(exc)[:700]}")

    async def automatic_backup_once(self, bot) -> bool:
        channel_id = self.backup_channel_id()
        if not channel_id:
            return False
        try:
            destination, filename, size = await asyncio.to_thread(self.create_backup_file, None)
            await self.send_backup_to_channel(bot, destination, filename, size, automatic=True)
            self.db.log_event("automatic_backup_sent",
                              details=f"filename={filename};size={size}")
            return True
        except Exception as exc:
            logger.exception("Automatic backup failed")
            self.db.log_error("ERROR", "backup", "automatic", repr(exc))
            return False

    async def automatic_backup_loop(self):
        logger.info("Automatic backup worker started (bot_id=%s, interval=%ss)",
                    self.bot_id, self.get_backup_interval_seconds())
        await asyncio.sleep(5)
        while True:
            interval = self.get_backup_interval_seconds()
            if interval <= 0:
                try:
                    await asyncio.sleep(300)
                except asyncio.CancelledError:
                    logger.info("Automatic backup worker stopped."); raise
                continue
            try:
                await self.automatic_backup_once(self.application.bot)
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                logger.exception("Automatic backup loop iteration failed")
                self.db.log_error("ERROR", "backup", "loop", repr(exc))
            try:
                await asyncio.sleep(self.get_backup_interval_seconds() or 300)
            except asyncio.CancelledError:
                logger.info("Automatic backup worker stopped."); raise

    async def restore_backup_from_document(self, message, context):
        try:
            await message.reply_text("⏳ Validating backup file...")
            tg_file = await context.bot.get_file(message.document.file_id)
            suffix = Path(message.document.file_name or ".db").suffix.lower()
            if suffix not in {".db", ".sqlite", ".sqlite3"}:
                await message.reply_text("❌ Unsupported backup file. Send a .db, .sqlite or .sqlite3 file."); return
            tmp_path = self.db.path.parent / (
                f"restore_tmp_{datetime.now(timezone.utc).strftime('%Y%m%d%H%M%S_%f')}.db"
            )
            await tg_file.download_to_drive(str(tmp_path))
            db_path = self.db.path

            def _validate_uploaded_db():
                check_conn = sqlite3.connect(str(tmp_path), timeout=10)
                try:
                    integrity_result = check_conn.execute("PRAGMA integrity_check").fetchone()[0]
                    found_tables = {row[0] for row in check_conn.execute(
                        "SELECT name FROM sqlite_master WHERE type='table'").fetchall()}
                finally:
                    check_conn.close()
                return integrity_result, found_tables

            try:
                integrity, tables = await asyncio.to_thread(_validate_uploaded_db)
            except Exception as exc:
                tmp_path.unlink(missing_ok=True)
                await message.reply_text(f"❌ Invalid backup file:\n{clean_error(exc)[:500]}"); return
            if integrity != "ok":
                tmp_path.unlink(missing_ok=True)
                await message.reply_text(f"❌ Backup integrity check failed: {integrity}"); return
            required_tables = {"users", "admins", "channels", "bot_settings", "messages"}
            missing = required_tables - tables
            if missing:
                tmp_path.unlink(missing_ok=True)
                await message.reply_text(
                    "❌ This is a valid SQLite file, but it is not a compatible bot backup.\n"
                    f"Missing tables: {', '.join(sorted(missing))}"
                ); return

            emergency = None
            try:
                emergency, emergency_name, emergency_size = await asyncio.to_thread(
                    self.create_backup_file, message.from_user.id)
                logger.info("Pre-restore emergency backup created: %s", emergency_name)
            except Exception:
                logger.exception("Could not create pre-restore emergency backup")

            def _wal_sidecars(db_file: Path):
                return [Path(str(db_file) + "-wal"), Path(str(db_file) + "-shm")]

            def _purge_wal_sidecars(db_file: Path):
                for sidecar in _wal_sidecars(db_file):
                    try:
                        sidecar.unlink(missing_ok=True)
                    except Exception:
                        logger.exception("Could not remove stale sidecar file: %s", sidecar)

            try:
                if self.db.conn is not None:
                    self.db.conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
            except Exception:
                logger.exception("Pre-restore WAL checkpoint failed (continuing)")
            self.db.close()
            _purge_wal_sidecars(db_path)
            _purge_wal_sidecars(tmp_path)
            os.replace(str(tmp_path), str(db_path))
            _purge_wal_sidecars(db_path)
            self.db.connect()
            try:
                self.db.conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
            except Exception:
                logger.exception("Post-restore WAL checkpoint failed (continuing)")

            restored_user_count = await asyncio.to_thread(
                lambda: self.db.fetchone("SELECT COUNT(*) AS c FROM users")["c"])
            restored_active_count = await asyncio.to_thread(
                lambda: self.db.fetchone("SELECT COUNT(*) AS c FROM users WHERE is_blocked=0")["c"])

            self.db.log_event(
                "backup_restored", user_id=message.from_user.id,
                details=(f"filename={message.document.file_name};pre_restore={bool(emergency)};"
                         f"restored_users={restored_user_count}"),
            )
            if restored_user_count > 0:
                status_line = (f"👥 Restored {restored_user_count:,} users "
                               f"({restored_active_count:,} not blocked, ready for broadcast).")
            else:
                status_line = ("⚠️ Restore completed, but the users table is EMPTY in this backup file. "
                               "Broadcast will have nothing to send to.")
            await message.reply_text(
                "✅ FULL BACKUP RESTORED SUCCESSFULLY.\n\n"
                f"{status_line}\n\n"
                "All persisted settings, channels, messages, buttons, join requests, broadcasts and logs "
                "from that backup are now active -- no restart needed.\n\n"
                "Automatic backup will continue using the restored backup-channel setting.",
                reply_markup=admin_menu(self.is_main),
            )
        except Exception as exc:
            logger.exception("Backup restore failed")
            try:
                self.db.connect()
            except Exception:
                pass
            await message.reply_text(f"❌ Restore failed:\n{clean_error(exc)[:700]}")

    # ============================================================
    # CSV EXPORT
    # ============================================================
    async def export_csv(self, query, export_type):
        if export_type == "users":
            rows = self.db.fetchall("SELECT * FROM users ORDER BY user_id")
            filename = "users.csv"
        elif export_type == "join_requests":
            rows = self.db.fetchall("SELECT * FROM join_requests ORDER BY id")
            filename = "join_requests.csv"
        elif export_type == "broadcast_logs":
            rows = self.db.fetchall("SELECT * FROM broadcast_logs ORDER BY id")
            filename = "broadcast_logs.csv"
        else:
            await query.message.reply_text("Invalid export."); return
        output = io.StringIO()
        writer = csv.writer(output)
        if rows:
            writer.writerow(rows[0].keys())
            for row in rows:
                writer.writerow([row[key] for key in row.keys()])
        else:
            writer.writerow(["No records"])
        data = io.BytesIO(output.getvalue().encode("utf-8-sig"))
        data.name = filename
        await query.message.reply_document(document=InputFile(data, filename=filename),
                                           caption=f"📤 {filename}")



# ============================================================
# MODULE-LEVEL HELPERS  (referenced by BotInstance methods above)
# ============================================================

def broadcast_draft_keyboard():
    return InlineKeyboardMarkup([
        [_make_callback_button("➕ Add Button", "broadcast_add_button", "success")],
        [
            _make_callback_button("👁 Preview", "broadcast_preview", "primary"),
            _make_callback_button("🚀 Send Now", "broadcast_send", "success"),
        ],
        [_make_callback_button("🗑 Clear Buttons", "broadcast_clear_buttons", "danger")],
        [_make_callback_button("⬅️ Broadcast Center", "admin_broadcast", "primary")],
    ])


_MESSAGE_BUILDER_TARGETS = {
    "join_request": {
        "title": "💬 MESSAGE BUILDER",
        "set_caption": "set_caption",
        "toggle_parse": "toggle_parse",
        "set_media": "set_media",
        "remove_media": "remove_media",
        "add_button": "add_button",
        "clear_buttons": "clear_buttons",
        "preview": "preview",
        "test": "admin_test",
        "back": "admin_home",
    },
    "start": {
        "title": "🚀 START MESSAGE BUILDER",
        "set_caption": "set_caption_start",
        "toggle_parse": "toggle_parse_start",
        "set_media": "set_media_start",
        "remove_media": "remove_media_start",
        "add_button": "add_button_start",
        "clear_buttons": "clear_buttons_start",
        "preview": "preview_start",
        "test": "test_start",
        "back": "admin_home",
    },
}


async def answer_query(query, text="", show_alert=False):
    try:
        await query.answer(text=text[:200], show_alert=show_alert)
    except TelegramError:
        pass


def _format_interval_label(seconds: int) -> str:
    if seconds <= 0:
        return "OFF"
    hours = seconds // 3600
    return f"EVERY {hours} HOUR{'S' if hours != 1 else ''}"


# ============================================================
# SEND BROADCAST TO USER  (module-level; reads row only)
# ============================================================

async def send_broadcast_to_user(bot, row, user_id: int):
    """Send a broadcast row. Same-bot source messages are copied first;
    master-broadcast media uses a staged upload so the CHILD bot token sends it."""
    source_chat = safe_int(row["source_chat_id"] if "source_chat_id" in row.keys() else 0, 0)
    source_msg = safe_int(row["source_message_id"] if "source_message_id" in row.keys() else 0, 0)
    buttons = parse_json(row["buttons_json"], [])
    keyboard = build_keyboard(buttons)
    staged_path = (row["staged_media_path"] or "") if "staged_media_path" in row.keys() else ""

    if not staged_path and source_chat and source_msg:
        try:
            return await bot.copy_message(
                chat_id=user_id, from_chat_id=source_chat,
                message_id=source_msg, reply_markup=keyboard,
            )
        except TelegramError as copy_exc:
            logger.warning(
                "Broadcast copy_message fallback for user %s: %s",
                user_id, clean_error(copy_exc)[:500]
            )

    entities = deserialize_message_entities(
        row["entities_json"] if "entities_json" in row.keys() else "[]", bot
    )

    if staged_path and Path(staged_path).is_file() and (row["media_type"] or "none") != "none":
        media_type = row["media_type"] or "none"
        caption = row["caption"] or ""
        parse_mode = row["parse_mode"] or None
        field = {
            "photo": "photo", "video": "video", "document": "document",
            "animation": "animation", "audio": "audio", "voice": "voice",
        }.get(media_type)
        if field:
            kwargs = {"chat_id": user_id, "reply_markup": keyboard}
            if caption:
                kwargs["caption"] = caption[:MAX_CAPTION_LENGTH]
                if entities:
                    kwargs["caption_entities"] = entities
                elif parse_mode:
                    kwargs["parse_mode"] = parse_mode
            with open(staged_path, "rb") as fh:
                kwargs[field] = InputFile(fh, filename=Path(staged_path).name)
                return await getattr(bot, f"send_{field}")(**kwargs)

    return await send_media_content(
        bot, user_id,
        row["media_type"] or "none",
        row["file_id"] or "",
        row["caption"] if row["media_type"] != "none"
        else (row["text"] or row["caption"] or ""),
        entities, row["parse_mode"] or None, keyboard,
    )


# ============================================================
# BOT MANAGER  (master controller — lives on the main bot)
# ============================================================
# The BotManager owns the registry of child BotInstance objects, drives their
# start/stop, and routes main-admin actions (create / list / broadcast-through
# / delete) to the right child. Child bots' tokens are decrypted only in
# memory at start time; the BotManager never logs or displays them.

class BotManager:
    def __init__(self, main_instance: "BotInstance"):
        self.main = main_instance
        self.children: dict[int, "BotInstance"] = {}
        self.lock = asyncio.Lock()

    # ---- registry ----
    def _child_db_path(self, bot_id: int) -> Path:
        return CHILD_DB_DIR / f"child_{bot_id}.db"

    def _webhook_path_for(self, bot_id: int) -> str:
        return f"telegram-bot-{bot_id}"

    def _webhook_secret_for(self, bot_id: int) -> str:
        # Stable per-bot webhook secret derived from the master vault material,
        # so redeploys regenerate the same secret and Telegram webhook auth still
        # passes after restart recovery. Never contains the bot token.
        return hmac.new(
            _master_key_material(),
            f"webhook-secret|{bot_id}".encode("utf-8"),
            hashlib.sha256,
        ).hexdigest()

    async def load_persisted_children(self):
        """On startup, rebuild BotInstance objects for every enabled child bot
        stored in the main DB (without starting them yet)."""
        for row in self.main.db.list_child_bots():
            if not row["enabled"]:
                continue
            token = decrypt_token(row["encrypted_token"])
            if not token:
                self.main.db.set_child_bot_status(row["bot_id"], "error", "token decryption failed")
                continue
            inst = BotInstance(
                bot_id=row["bot_id"],
                token=token,
                owner_id=row["admin_id"],
                db_path=self._child_db_path(row["bot_id"]),
                is_main=False,
                display_name=row["display_name"] or row["username"] or "",
                webhook_path=row["webhook_path"] or self._webhook_path_for(row["bot_id"]),
                webhook_secret=row["webhook_secret"] or self._webhook_secret_for(row["bot_id"]),
            )
            inst.status = "stopped"
            inst.last_error = ""
            self.main.db.set_child_bot_status(row["bot_id"], "stopped", "")
            self.children[row["bot_id"]] = inst

    async def start_all_enabled_children(self, webhook_base_url: str):
        tasks = [asyncio.create_task(self._safe_start(inst, webhook_base_url),
                                     name=f"child-start-{inst.bot_id}")
                 for inst in list(self.children.values())]
        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)

    async def _safe_start(self, inst: "BotInstance", webhook_base_url: str) -> bool:
        try:
            return await self.start_child(inst.bot_id, webhook_base_url)
        except Exception as exc:
            error = clean_error(exc)
            inst._set_status("error", error)
            self.main.db.set_child_bot_status(inst.bot_id, "error", error)
            self.main.db.log_master_audit(self.main.owner_id, inst.bot_id,
                                          "child_bot_started", "error", error)
            logger.exception("Safe child startup failed (bot_id=%s): %s", inst.bot_id, error)
            return False

    # ---- token validation ----
    async def validate_token(self, token: str):
        """Return (bot_id, username, first_name) or raise ValueError."""
        from telegram import Bot
        if not re.fullmatch(r"\d{6,12}:[A-Za-z0-9_-]{30,}", token or ""):
            raise ValueError("Invalid token format.")
        try:
            bot = Bot(token=token)
            await bot.initialize()
            try:
                me = await bot.get_me()
            finally:
                await bot.shutdown()
        except (TimedOut, NetworkError) as exc:
            raise ValueError(f"Telegram unreachable: {clean_error(exc)[:200]}")
        except TelegramError as exc:
            raise ValueError(f"Token rejected by Telegram: {clean_error(exc)[:200]}")
        if not me or not me.username or not me.is_bot:
            raise ValueError("That token does not belong to a bot.")
        return me.id, me.username, (me.first_name or me.username)

    # ---- create flow ----
    async def create_child_bot(self, main_admin_id: int, token: str, admin_id: int,
                                display_name: str = "") -> "BotInstance":
        async with self.lock:
            if self.main.db.count_child_bots() >= MAX_CHILD_BOTS:
                raise ValueError(f"Maximum bot limit reached ({MAX_CHILD_BOTS}).")
            if main_admin_id != self.main.owner_id:
                creator = self.main.db.get_bot_creator(main_admin_id)
                if not creator:
                    raise ValueError("❌ You do not have Bot Creator permission.")
                used = self.main.db.count_bots_created_by(main_admin_id)
                limit = max(1, safe_int(creator["max_bots"], 1))
                if used >= limit:
                    raise ValueError(f"❌ Bot Creator limit reached: {used}/{limit} bots already created.")
            bot_id, username, first_name = await self.validate_token(token)
            if self.main.db.get_child_bot(bot_id):
                raise ValueError("⚠️ This bot is already registered.")
            if not admin_id or admin_id <= 0:
                raise ValueError("❌ Invalid Telegram Admin ID.")

            encrypted = encrypt_token(token)
            webhook_path = self._webhook_path_for(bot_id)
            webhook_secret = self._webhook_secret_for(bot_id)
            self.main.db.upsert_child_bot(
                bot_id=bot_id, username=username,
                display_name=display_name or first_name,
                encrypted_token=encrypted, admin_id=admin_id,
                webhook_path=webhook_path, webhook_secret=webhook_secret,
                status="stopped", created_by=main_admin_id,
            )
            self.main.db.log_master_audit(main_admin_id, bot_id, "bot_created", "ok", "")

            inst = BotInstance(
                bot_id=bot_id, token=token, owner_id=admin_id,
                db_path=self._child_db_path(bot_id), is_main=False,
                display_name=display_name or first_name,
                webhook_path=webhook_path, webhook_secret=webhook_secret,
            )
            self.children[bot_id] = inst
            return inst

    async def start_child(self, bot_id: int, webhook_base_url: str) -> bool:
        inst = self.children.get(bot_id)
        if not inst:
            error = "Child bot is not loaded in memory"
            self.main.db.set_child_bot_status(bot_id, "error", error)
            return False
        if webhook_base_url and (not WEBHOOK_SERVER or not WEBHOOK_SERVER.is_running):
            error = "Shared webhook server is not running"
            inst._set_status("error", error)
            self.main.db.set_child_bot_status(bot_id, "error", error)
            return False
        self.main.db.set_child_bot_status(bot_id, "starting", "")
        try:
            ok = await inst.start(webhook_base_url=webhook_base_url)
            self.main.db.set_child_bot_status(bot_id, "live" if ok else "error", inst.last_error)
            self.main.db.log_master_audit(self.main.owner_id, bot_id,
                                          "bot_started", "ok" if ok else "error", inst.last_error)
            logger.info("Child bot_id=%s start result=%s status=%s", bot_id, ok, inst.status)
            return ok
        except Exception as exc:
            error = clean_error(exc)
            inst._set_status("error", error)
            self.main.db.set_child_bot_status(bot_id, "error", error)
            self.main.db.log_master_audit(self.main.owner_id, bot_id, "bot_started", "error", error)
            logger.exception("start_child failed (bot_id=%s): %s", bot_id, error)
            return False

    async def stop_child(self, bot_id: int) -> bool:
        inst = self.children.get(bot_id)
        if not inst:
            return False
        ok = await inst.stop()
        self.main.db.set_child_bot_status(bot_id, "stopped" if ok else "error", inst.last_error)
        self.main.db.log_master_audit(self.main.owner_id, bot_id,
                                      "bot_stopped", "ok" if ok else "error", inst.last_error)
        return ok

    async def delete_child(self, bot_id: int) -> bool:
        async with self.lock:
            inst = self.children.get(bot_id)
            if inst:
                await inst.stop()
            self.main.db.soft_delete_child_bot(bot_id)
            self.children.pop(bot_id, None)
            self.main.db.log_master_audit(self.main.owner_id, bot_id, "bot_deleted", "ok", "")
            return True

    def status_label(self, inst: "BotInstance") -> str:
        return {
            "live": "🟢 LIVE", "starting": "🟡 STARTING", "stopped": "⏸ STOPPED",
            "error": "⚠️ ERROR", "offline": "🔴 OFFLINE",
        }.get(inst.status, "🔴 OFFLINE")

    def instance_for_callback(self, callback_data: str) -> Optional["BotInstance"]:
        """Extract a child BotInstance from a 'bm:<bot_id>:...' callback string."""
        if not callback_data.startswith("bm:"):
            return None
        try:
            bot_id = int(callback_data.split(":", 2)[1])
        except (IndexError, ValueError):
            return None
        return self.children.get(bot_id)


# ============================================================
# BOT MANAGER UI  (rendered inside the main bot's admin panel)
# ============================================================

def bot_manager_keyboard(bm: BotManager):
    rows = []
    children = list(bm.children.values())
    for inst in children[:20]:  # Telegram inline keyboard cap safety.
        label = f"{bm.status_label(inst)} @{inst.display_name or inst.bot_id}"
        rows.append([_make_callback_button(label, f"bm:{inst.bot_id}:manage", "primary")])
    rows.append([_make_callback_button("➕ Create Bot", "bm:create", "success")])
    rows.append([_make_callback_button("🔄 Refresh", "bot_manager", "primary")])
    rows.append([_make_callback_button("⬅️ Admin Panel", "admin_home", "primary")])
    return InlineKeyboardMarkup(rows)


async def show_bot_creators(query, main_inst: "BotInstance"):
    if not main_inst.is_owner(query.from_user.id):
        await answer_query(query, "Only the Main Owner can manage Bot Creators.", show_alert=True)
        return
    creators = main_inst.db.list_bot_creators()
    lines = ["👤 BOT CREATORS", ""]
    if not creators:
        lines.append("No Bot Creators have been granted permission yet.")
    else:
        lines.append("User ID | Max Bots | Created")
        for row in creators:
            used = main_inst.db.count_bots_created_by(row["user_id"])
            lines.append(
                f"• {row['user_id']} | {row['max_bots']} | {row['created_at']} | Used: {used}"
            )
    rows = [[_make_callback_button("➕ Add Bot Creator", "bot_creator_add", "success")]]
    for row in creators[:30]:
        rows.append([
            _make_callback_button(
                f"✏️ Edit Limit {row['user_id']}",
                f"bot_creator_edit:{row['user_id']}", "primary"
            ),
            _make_callback_button(
                f"❌ Revoke {row['user_id']}",
                f"bot_creator_revoke:{row['user_id']}", "danger"
            ),
        ])
    rows.append([_make_callback_button("⬅️ Admin Panel", "admin_home", "primary")])
    await query.edit_message_text(
        "\n".join(lines)[:4000],
        reply_markup=InlineKeyboardMarkup(rows)
    )


async def show_bot_manager(message_or_query, query=None):
    """Render the Bot Manager overview. Accepts a Message (from /bots command)
    or a CallbackQuery (passed via query)."""
    bm: BotManager = BOT_MANAGER
    children = list(bm.children.values())
    live = sum(1 for c in children if c.status == "live")
    offline = len(children) - live
    text = (
        "🤖 BOT MANAGER\n\n"
        f"Total Bots: {len(children)}\n"
        f"🟢 Live: {live}\n"
        f"🔴 Offline: {offline}\n"
    )
    for inst in children[:20]:
        s = inst.db.stats()
        row = bm.main.db.fetchone("SELECT created_by,last_error FROM child_bots WHERE bot_id=?", (inst.bot_id,))
        created_by = row["created_by"] if row and row["created_by"] else "unknown"
        error_line = f"\n⚠️ Error: {row['last_error'][:220]}" if row and row["last_error"] and inst.status == "error" else ""
        text += (f"\n{bm.status_label(inst)} @{inst.display_name or inst.bot_id}\n"
                 f"👥 Users: {s['users']}\n👤 Admin: {inst.owner_id}\n👤 Created by: {created_by}{error_line}\n")
    keyboard = bot_manager_keyboard(bm)
    if query is not None:
        await query.edit_message_text(text[:4000], reply_markup=keyboard)
    else:
        await message_or_query.reply_text(text[:4000], reply_markup=keyboard)


async def show_bot_manage_page(query, inst: "BotInstance"):
    s = inst.db.stats()
    row = inst.db.fetchone  # not used; placeholder
    text = (
        f"🤖 @{inst.display_name or inst.bot_id}\n\n"
        f"🆔 Bot ID: {inst.bot_id}\n"
        f"👤 Admin ID: {inst.owner_id}\n"
        f"📊 Status: {BOT_MANAGER.status_label(inst)}\n"
        f"👥 Users: {s['users']}  |  🟢 Active: {s['active']}  |  🚫 Blocked: {s['blocked']}\n"
        f"📩 Join Requests: {s['requests']}\n"
        f"📢 Broadcasts: {s['broadcasts']}\n"
        f"📅 Channels: {s['channels']}\n"
        f"👥 Auto Member: {'ON' if inst.db.get_setting('auto_member_enabled', '0') == '1' else 'OFF'}\n\n"
        "Token is never displayed."
    )
    keyboard = InlineKeyboardMarkup([
        [_make_callback_button("📊 Stats", f"bm:{inst.bot_id}:stats", "primary"),
         _make_callback_button("📢 Broadcast", f"bm:{inst.bot_id}:broadcast", "primary")],
        [_make_callback_button("⚙️ Manage (open child admin)", f"bm:{inst.bot_id}:open", "primary")],
        [_make_callback_button(
            ("👥 Auto Member: ON" if inst.db.get_setting("auto_member_enabled", "0") == "1" else "👥 Auto Member: OFF"),
            f"bm:{inst.bot_id}:auto_member",
            "success" if inst.db.get_setting("auto_member_enabled", "0") == "1" else "danger",
        )],
        [
            _make_callback_button("⏸ Stop", f"bm:{inst.bot_id}:stop", "danger") if inst.status == "live"
            else _make_callback_button("▶️ Start", f"bm:{inst.bot_id}:start", "success"),
            _make_callback_button("🗑 Delete", f"bm:{inst.bot_id}:delete", "danger"),
        ],
        [_make_callback_button("✏️ Edit Admin ID", f"bm:{inst.bot_id}:edit_admin", "primary")],
        [_make_callback_button("⬅️ Bot Manager", "bot_manager", "primary")],
    ])
    await query.edit_message_text(text[:4000], reply_markup=keyboard)


async def show_bot_stats_page(query, inst: "BotInstance"):
    s = inst.db.stats()
    total = s["sent"] + s["failed"]
    success_rate = (s["sent"] / total) * 100 if total else 0
    await query.edit_message_text(
        f"📈 STATS — @{inst.display_name or inst.bot_id}\n\n"
        f"Users: {s['users']}\nActive: {s['active']}\nBlocked: {s['blocked']}\n\n"
        f"Join Requests Today: {s['today']}\n7 Days: {s['week']}\n30 Days: {s['month']}\n\n"
        f"Messages Sent: {s['sent']}\nFailed: {s['failed']}\nSuccess Rate: {success_rate:.2f}%\n"
        f"Broadcasts: {s['broadcasts']}",
        reply_markup=InlineKeyboardMarkup([
            [_make_callback_button("⬅️ Back", f"bm:{inst.bot_id}:manage", "primary")],
        ]),
    )


# ============================================================
# MULTI-BOT WEBHOOK SERVER  (single Render port, N routes)
# ============================================================
# Render forwards ONE public port. We bind it once with aiohttp and register a
# POST route per bot webhook path (/{path}) plus GET /health. Each route feeds
# its incoming Update into the corresponding BotInstance's update_queue. Child
# bot failures cannot take the server down: every dispatch is wrapped.

class MultiBotWebhookServer:
    def __init__(self, port: int, base_url: str):
        self.port = port
        self.base_url = base_url.rstrip("/")
        self.runner: Optional[web.AppRunner] = None
        self.site: Optional[web.TCPSite] = None
        self.web_app = web.Application()
        self.web_app.router.add_get("/health", self._health)
        self.web_app.router.add_get("/", self._health)
        self.web_app.router.add_post("/{tail:.*}", self._dispatch)

    @property
    def is_running(self) -> bool:
        return self.runner is not None and self.site is not None


    def _instance_for_path(self, path: str) -> Optional["BotInstance"]:
        path = path.strip("/")
        main = MAIN_INSTANCE
        if main and main.webhook_path == path:
            return main
        if BOT_MANAGER:
            for inst in BOT_MANAGER.children.values():
                if inst.webhook_path == path:
                    return inst
        return None

    async def _health(self, request: web.Request) -> web.Response:
        return web.Response(status=200, text="ok")

    async def _dispatch(self, request: web.Request) -> web.Response:
        inst = self._instance_for_path(request.path)
        if inst is None or inst.application is None:
            return web.Response(status=404, text="unknown webhook")
        if inst.webhook_secret:
            header_secret = request.headers.get("X-Telegram-Bot-Api-Secret-Token", "")
            if header_secret != inst.webhook_secret:
                return web.Response(status=401, text="unauthorized")
        try:
            data = await request.json()
        except Exception:
            return web.Response(status=400, text="bad request")
        try:
            update = Update.de_json(data, inst.application.bot)
        except Exception:
            logger.exception("Failed to parse incoming Telegram update (path=%s)", request.path)
            return web.Response(status=400, text="bad update")
        if update is not None:
            try:
                await inst.application.update_queue.put(update)
            except Exception as exc:
                logger.exception("Failed to enqueue update for bot_id=%s: %s", inst.bot_id, exc)
                return web.Response(status=500, text="enqueue failed")
        return web.Response(status=200, text="ok")

    def register_bot(self, inst: "BotInstance"):
        logger.info("Webhook endpoint ready for bot_id=%s path=/%s",
                    inst.bot_id, inst.webhook_path.strip('/'))

    async def start(self):
        self.runner = web.AppRunner(self.web_app)
        await self.runner.setup()
        self.site = web.TCPSite(self.runner, "0.0.0.0", self.port)
        await self.site.start()
        logger.info("Multi-bot webhook + /health listening on 0.0.0.0:%s", self.port)

    async def stop(self):
        if self.site:
            await self.site.stop()
        if self.runner:
            await self.runner.cleanup()
        self.site = None
        self.runner = None


# ============================================================
# MAIN-BOT ADMIN_INPUT EXTENSION  (create-bot / admin-id / edit-admin flows)
# ============================================================
# These states are MAIN-bot only and are dispatched BEFORE the generic admin
# input router. They live at module level so the main BotInstance can call
# them without polluting the per-instance class with main-only logic.

async def main_admin_input_extension(main_inst: "BotInstance", update: Update,
                                     context: ContextTypes.DEFAULT_TYPE) -> bool:
    """Return True if the message was handled here (main-only states)."""
    user = update.effective_user
    message = update.message
    if not user or not message:
        return False
    state = context.user_data.get("awaiting")
    bm = BOT_MANAGER

    if state == "bot_creator_add_id":
        if not main_inst.is_owner(user.id):
            context.user_data.pop("awaiting", None)
            await message.reply_text("❌ Only the Main Owner can grant Bot Creator permission.")
            return True
        raw = (message.text or "").strip()
        try:
            target_id = int(raw)
            if target_id <= 0:
                raise ValueError
        except (TypeError, ValueError):
            await message.reply_text("❌ Invalid Telegram User ID. Send a numeric ID.")
            return True
        if target_id == OWNER_ID:
            await message.reply_text("The Main Owner already has full control.")
            return True
        context.user_data["bot_creator_add_target"] = target_id
        context.user_data["awaiting"] = "bot_creator_add_limit"
        await message.reply_text("Step 2/2 — Send Max Bots for this Creator.\nExample: 1, 3, 5, 10")
        return True

    if state == "bot_creator_add_limit":
        if not main_inst.is_owner(user.id):
            context.user_data.pop("awaiting", None)
            return True
        target_id = safe_int(context.user_data.get("bot_creator_add_target"), 0)
        limit = safe_int((message.text or "").strip(), 0)
        if target_id <= 0 or limit <= 0:
            await message.reply_text("❌ Invalid Max Bots. Send a positive number such as 1 or 5.")
            return True
        main_inst.db.add_bot_creator(target_id, user.id, limit)
        main_inst.db.log_master_audit(
            user.id, 0, "bot_creator_granted", "ok",
            f"user_id={target_id};max_bots={limit}"
        )
        context.user_data.pop("awaiting", None)
        context.user_data.pop("bot_creator_add_target", None)
        await message.reply_text(
            f"✅ Bot Creator permission granted to {target_id}. Max Bots: {limit}.",
            reply_markup=admin_menu(True),
        )
        return True

    if state == "bot_creator_edit_limit":
        if not main_inst.is_owner(user.id):
            context.user_data.pop("awaiting", None)
            return True
        target_id = safe_int(context.user_data.get("bot_creator_edit_target"), 0)
        limit = safe_int((message.text or "").strip(), 0)
        if target_id <= 0 or limit <= 0 or not main_inst.db.is_bot_creator(target_id):
            await message.reply_text("❌ Invalid limit or Bot Creator no longer exists.")
            return True
        used = main_inst.db.count_bots_created_by(target_id)
        if limit < used:
            await message.reply_text(
                f"❌ New limit cannot be below already-created bots ({used})."
            )
            return True
        main_inst.db.set_bot_creator_limit(target_id, limit)
        main_inst.db.log_master_audit(
            user.id, 0, "bot_creator_limit_changed", "ok",
            f"user_id={target_id};max_bots={limit}"
        )
        context.user_data.pop("awaiting", None)
        context.user_data.pop("bot_creator_edit_target", None)
        await message.reply_text(
            f"✅ Max Bots updated for {target_id}: {limit}.",
            reply_markup=admin_menu(True),
        )
        return True

    # /create flow — step 1: token.
    if state == "create_bot_token":
        token = (message.text or "").strip()
        if not token:
            await message.reply_text("Send a valid bot token, or /cancel."); return True
        try:
            bot_id, username, first_name = await bm.validate_token(token)
        except ValueError as exc:
            main_inst.db.log_master_audit(user.id, 0, "bot_token_validation_failed", "error", str(exc))
            await message.reply_text(f"❌ {exc}\n\nSend a valid token, or /cancel."); return True
        # Stash the validated token in memory only (never persisted in plaintext).
        context.user_data["create_bot_id"] = bot_id
        context.user_data["create_bot_username"] = username
        context.user_data["create_bot_first_name"] = first_name
        context.user_data["create_bot_token"] = token
        context.user_data["awaiting"] = "create_bot_admin_id"
        await message.reply_text(
            f"✅ Bot token verified\n🤖 Bot: @{username}\n🆔 Bot ID: {bot_id}\n\n"
            "👤 SEND ADMIN ID\n\nSend the Telegram numeric User ID that should have full admin access to this bot.",
            reply_markup=InlineKeyboardMarkup(
                [[_make_callback_button("❌ Cancel", "create_bot_cancel", "danger")]]
            ),
        )
        return True

    # /create flow — step 2: admin id.
    if state == "create_bot_admin_id":
        raw = (message.text or "").strip()
        try:
            admin_id = int(raw)
            if admin_id <= 0:
                raise ValueError
        except (TypeError, ValueError):
            await message.reply_text("❌ Invalid Telegram Admin ID. Send a numeric user ID."); return True
        context.user_data["create_bot_admin_id"] = admin_id
        context.user_data["awaiting"] = "create_bot_confirm"
        bot_id = context.user_data.get("create_bot_id")
        username = context.user_data.get("create_bot_username")
        first_name = context.user_data.get("create_bot_first_name")
        await message.reply_text(
            f"✅ Admin ID verified\n🤖 Bot: @{username}\n👤 Admin ID: {admin_id}\n\nCreate this bot?",
            reply_markup=InlineKeyboardMarkup([
                [_make_callback_button("✅ Create Bot", "create_bot_confirm", "success"),
                 _make_callback_button("❌ Cancel", "create_bot_cancel", "danger")],
            ]),
        )
        return True

    # Edit child admin id flow.
    if state == "edit_child_admin_id":
        raw = (message.text or "").strip()
        target_bot_id = context.user_data.pop("edit_child_target", None)
        context.user_data.pop("awaiting", None)
        try:
            admin_id = int(raw)
            if admin_id <= 0:
                raise ValueError
        except (TypeError, ValueError):
            await message.reply_text("❌ Invalid Telegram Admin ID."); return True
        if target_bot_id is None:
            await message.reply_text("Expired."); return True
        main_inst.db.set_child_bot_admin(target_bot_id, admin_id)
        inst = bm.children.get(target_bot_id)
        if inst:
            inst.owner_id = admin_id
            inst.db.connect()
            inst.db._seed_admin_id = admin_id
            inst.db.reset_bot_owner_admin(admin_id)
        main_inst.db.log_master_audit(user.id, target_bot_id, "bot_admin_changed", "ok", "")
        await message.reply_text(
            f"✅ Admin ID updated for bot {target_bot_id}.\nThe new admin now has full access; the previous admin no longer does.",
            reply_markup=admin_menu(is_main=True),
        )
        return True

    # Master broadcast through a child bot — compose message.
    if state == "master_broadcast_compose":
        target_bot_id = context.user_data.get("master_broadcast_target")
        inst = bm.children.get(target_bot_id) if target_bot_id else None
        if not inst or inst.application is None:
            await message.reply_text("Target child bot is not running."); return True
        # Build a broadcast row in the CHILD bot's database using the admin's
        # message, then start that child's own broadcast pipeline. This
        # guarantees the broadcast is sent FROM the child bot's token to the
        # child bot's user list.
        await _create_and_send_master_broadcast(inst, update, context, user.id)
        return True

    return False


async def _create_and_send_master_broadcast(inst: "BotInstance", update: Update,
                                            context: ContextTypes.DEFAULT_TYPE, main_admin_id: int):
    """Create a pending broadcast in the CHILD DB. Media received by MAIN is
    staged locally because the child bot cannot use the main bot's file_id."""
    message = update.message
    media_type = "none"
    file_id = None
    text = ""
    caption = ""
    source_entities = message.entities or ()
    media_obj = None

    if message.photo:
        media_type, file_id, media_obj = "photo", message.photo[-1].file_id, message.photo[-1]
        caption = message.caption or ""
        source_entities = message.caption_entities or ()
    elif message.video:
        media_type, file_id, media_obj = "video", message.video.file_id, message.video
        caption = message.caption or ""
        source_entities = message.caption_entities or ()
    elif message.animation:
        media_type, file_id, media_obj = "animation", message.animation.file_id, message.animation
        caption = message.caption or ""
        source_entities = message.caption_entities or ()
    elif message.document:
        media_type, file_id, media_obj = "document", message.document.file_id, message.document
        caption = message.caption or ""
        source_entities = message.caption_entities or ()
    elif message.audio:
        media_type, file_id, media_obj = "audio", message.audio.file_id, message.audio
        caption = message.caption or ""
        source_entities = message.caption_entities or ()
    elif message.voice:
        media_type, file_id, media_obj = "voice", message.voice.file_id, message.voice
        caption = message.caption or ""
        source_entities = message.caption_entities or ()
    else:
        text = message.text or ""
        caption = text
        source_entities = message.entities or ()

    content = caption if media_type != "none" else text
    max_len = MAX_CAPTION_LENGTH if media_type != "none" else MAX_TEXT_LENGTH
    if not content and media_type == "none":
        await message.reply_text("Broadcast content cannot be empty.")
        return
    if len(content) > max_len:
        await message.reply_text(f"Broadcast content is too long. Maximum: {max_len} characters.")
        return

    staged_path = ""
    if media_obj and file_id:
        try:
            staging_dir = DB_PATH.parent / "master_broadcast_media"
            staging_dir.mkdir(parents=True, exist_ok=True)
            suffix = {
                "photo": ".jpg", "video": ".mp4", "animation": ".mp4",
                "document": ".bin", "audio": ".mp3", "voice": ".ogg",
            }.get(media_type, ".bin")
            path = staging_dir / (
                f"broadcast_{inst.bot_id}_{message.message_id}_{secrets.token_hex(6)}{suffix}"
            )
            tg_file = await context.bot.get_file(file_id)
            await tg_file.download_to_drive(custom_path=str(path))
            staged_path = str(path)
        except Exception as exc:
            logger.exception("Could not stage master broadcast media")
            await message.reply_text(
                f"❌ Could not prepare the media for the child bot: {clean_error(exc)[:700]}"
            )
            return

    buttons = context.user_data.get("pending_broadcast_buttons", [])
    entities_json = serialize_message_entities(source_entities)
    cursor = inst.db.execute(
        """INSERT INTO broadcasts(
            admin_id,text,media_type,file_id,caption,parse_mode,
            source_chat_id,source_message_id,entities_json,buttons_json,staged_media_path,status,created_at
        ) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)""",
        (
            main_admin_id, text, media_type, file_id, caption,
            inst.db.get_join_message()["parse_mode"] or "HTML",
            0, 0, entities_json, json.dumps(buttons, ensure_ascii=False),
            staged_path, "pending", utc_now()
        ),
        commit=True,
    )
    broadcast_id = cursor.lastrowid
    context.user_data["pending_broadcast_id"] = broadcast_id
    context.user_data["awaiting"] = "broadcast_buttons"
    context.user_data["button_target"] = "master_broadcast"
    custom_count = count_custom_emoji(source_entities)
    await message.reply_text(
        f"📢 Child Broadcast #{broadcast_id} ready.\n\n"
        f"Target: @{inst.display_name}\nType: {media_type}\n"
        f"Premium/custom emoji: {custom_count}\nButtons: {len(buttons)}\n\n"
        "Add buttons, Preview, Clear Buttons, or Send Now.",
        reply_markup=broadcast_draft_keyboard(),
    )


# ============================================================
# MAIN-BOT CALLBACK EXTENSION  (Bot Manager callbacks + create flow)
# ============================================================

async def main_admin_callback_extension(main_inst: "BotInstance", update: Update,
                                        context: ContextTypes.DEFAULT_TYPE) -> bool:
    query = update.callback_query
    if not query:
        return False
    user = query.from_user
    data = query.data or ""
    bm = BOT_MANAGER
    if not user or not bm:
        return False

    # Creator management is Main Owner only.
    if data == "bot_creators":
        await query.answer()
        if not main_inst.is_owner(user.id):
            await query.message.reply_text("❌ Only the Main Owner can manage Bot Creators.")
            return True
        await show_bot_creators(query, main_inst)
        return True
    if data == "bot_creator_add":
        await query.answer()
        if not main_inst.is_owner(user.id):
            await query.message.reply_text("❌ Only the Main Owner can grant Bot Creator permission.")
            return True
        context.user_data["awaiting"] = "bot_creator_add_id"
        await query.message.reply_text("Step 1/2 — Send the numeric Telegram User ID.\n\nUse /cancel to cancel.")
        return True
    if data.startswith("bot_creator_edit:"):
        await query.answer()
        if not main_inst.is_owner(user.id):
            await query.message.reply_text("❌ Only the Main Owner can edit Bot Creator limits.")
            return True
        target = safe_int(data.split(":", 1)[1], 0)
        if not target or not main_inst.db.is_bot_creator(target):
            await query.message.reply_text("Bot Creator not found.")
            return True
        context.user_data["bot_creator_edit_target"] = target
        context.user_data["awaiting"] = "bot_creator_edit_limit"
        current = main_inst.db.get_bot_creator_limit(target, 1)
        await query.message.reply_text(
            f"Send the new Max Bots limit for {target}. Current: {current}.\nExample: 5"
        )
        return True
    if data.startswith("bot_creator_revoke:"):
        await query.answer()
        if not main_inst.is_owner(user.id):
            await query.message.reply_text("❌ Only the Main Owner can revoke Bot Creator permission.")
            return True
        target = safe_int(data.split(":", 1)[1], 0)
        if target == OWNER_ID:
            await query.message.reply_text("The Main Owner cannot be revoked.")
            return True
        main_inst.db.remove_bot_creator(target)
        main_inst.db.log_master_audit(user.id, 0, "bot_creator_revoked", "ok", f"user_id={target}")
        await show_bot_creators(query, main_inst)
        return True

    if data == "bot_manager":
        await query.answer()
        if not main_inst.is_owner(user.id):
            await query.message.reply_text("❌ Bot Manager is available only to the Main Owner.")
            return True
        await show_bot_manager(query, query=query)
        return True

    # Master-broadcast draft callbacks are handled on MAIN while the draft
    # itself lives in the selected CHILD database.
    if data in ("broadcast_add_button", "broadcast_clear_buttons", "broadcast_preview", "broadcast_send")             and context.user_data.get("master_broadcast_target"):
        await query.answer()
        target_bot_id = context.user_data.get("master_broadcast_target")
        inst = bm.children.get(target_bot_id)
        broadcast_id = context.user_data.get("pending_broadcast_id")
        if not inst or not broadcast_id:
            await query.message.reply_text("Master broadcast draft expired. Start the child broadcast again.")
            return True
        try:
            row = inst.db.fetchone(
                "SELECT * FROM broadcasts WHERE id=? AND status='pending'", (broadcast_id,)
            )
            if not row:
                await query.message.reply_text("Master broadcast draft not found or already sent.")
                return True
            if data == "broadcast_add_button":
                context.user_data["button_target"] = "master_broadcast"
                context.user_data["awaiting"] = "btn_link"
                await query.message.reply_text(
                    "Step 1/4 — Send the button URL.\nExample: https://t.me/yourchannel\n\nUse /cancel to cancel."
                )
                return True
            if data == "broadcast_clear_buttons":
                context.user_data["pending_broadcast_buttons"] = []
                inst.db.execute(
                    "UPDATE broadcasts SET buttons_json='[]' WHERE id=? AND status='pending'",
                    (broadcast_id,), commit=True
                )
                await query.message.reply_text(
                    "🗑 Child broadcast buttons cleared.",
                    reply_markup=broadcast_draft_keyboard()
                )
                return True
            if data == "broadcast_preview":
                try:
                    await send_broadcast_to_user(inst.application.bot, row, query.from_user.id)
                    preview_source = "child"
                except Exception as child_preview_exc:
                    # A child bot cannot initiate a private chat with a user who
                    # has never opened it. Preview is therefore allowed to fall
                    # back to MAIN; the real broadcast is always sent by CHILD.
                    logger.warning(
                        "Child preview unavailable; using main-bot preview: %s",
                        clean_error(child_preview_exc)[:500],
                    )
                    await send_broadcast_to_user(main_inst.application.bot, row, query.from_user.id)
                    preview_source = "main fallback"
                await query.message.reply_text(
                    f"👁 Child broadcast preview sent ({preview_source}).",
                    reply_markup=broadcast_draft_keyboard()
                )
                return True
            if data == "broadcast_send":
                await inst.start_broadcast_send(query.message, context, broadcast_id)
                context.user_data.pop("master_broadcast_target", None)
                return True
        except Exception as exc:
            logger.exception("Master broadcast callback failed")
            main_inst.db.log_error("EXCEPTION", "master_broadcast", data, repr(exc))
            await query.message.reply_text(
                f"⚠️ Operation failed safely: {clean_error(exc)[:700]}",
                reply_markup=broadcast_draft_keyboard()
            )
        return True

    if data == "bm:create":
        await query.answer()
        if not (main_inst.is_owner(user.id) or main_inst.is_bot_creator(user.id)):
            await query.message.reply_text("❌ You are not authorized to create bots.")
            return True
        if not main_inst.is_owner(user.id):
            used = main_inst.db.count_bots_created_by(user.id)
            limit = main_inst.db.get_bot_creator_limit(user.id, 1)
            if used >= limit:
                await query.message.reply_text(
                    f"❌ Bot Creator limit reached: {used}/{limit} bots already created."
                )
                return True
        context.user_data["awaiting"] = "create_bot_token"
        await query.message.reply_text(
            "🤖 CREATE NEW BOT\n\nSend your Telegram Bot Token.\n"
            "Create your bot using @BotFather and send the token here.\n\nUse /cancel to cancel.",
            reply_markup=InlineKeyboardMarkup([[
                _make_callback_button("❌ Cancel", "create_bot_cancel", "danger")
            ]]),
        )
        return True

    if data == "create_bot_cancel":
        await query.answer()
        for k in ("awaiting", "create_bot_id", "create_bot_username", "create_bot_first_name",
                  "create_bot_token", "create_bot_admin_id"):
            context.user_data.pop(k, None)
        await query.message.reply_text("❌ Create-bot flow cancelled.",
                                       reply_markup=admin_menu(main_inst.is_main) if main_inst.is_owner(user.id) else InlineKeyboardMarkup([[
                                           _make_callback_button("➕ Create My Bot", "bm:create", "success")
                                       ]]))
        return True

    if data == "create_bot_confirm":
        await query.answer()
        token = context.user_data.get("create_bot_token")
        admin_id = context.user_data.get("create_bot_admin_id")
        bot_id = context.user_data.get("create_bot_id")
        username = context.user_data.get("create_bot_username") or "bot"
        if not token or not admin_id or not bot_id:
            await query.message.reply_text("Create-bot data expired. Start again.")
            return True
        try:
            inst = await bm.create_child_bot(user.id, token, admin_id, display_name=context.user_data.get("create_bot_first_name") or "")
            # Do not keep plaintext token in user_data after persistence.
            for k in ("awaiting", "create_bot_id", "create_bot_username", "create_bot_first_name",
                      "create_bot_token", "create_bot_admin_id"):
                context.user_data.pop(k, None)
            ok = await bm.start_child(inst.bot_id, RENDER_EXTERNAL_URL)
            if ok:
                await query.message.reply_text(
                    f"✅ Bot created and LIVE: @{inst.display_name} (id {inst.bot_id})\n"
                    f"Admin ID: {admin_id}\n\nThe child bot's admin panel is available with /admin in that bot.",
                )
                if main_inst.is_owner(user.id):
                    await show_bot_manager(query, query=query)
            else:
                await query.message.reply_text(
                    f"⚠️ Bot @{inst.display_name} was created but could not start.\n\n"
                    f"Status: ERROR\nReason: {inst.last_error[:1200]}",
                    reply_markup=admin_menu(True) if main_inst.is_owner(user.id) else InlineKeyboardMarkup([[
                        _make_callback_button("➕ Create My Bot", "bm:create", "success")
                    ]]),
                )
                if main_inst.is_owner(user.id):
                    await show_bot_manager(query, query=query)
            return True
        except ValueError as exc:
            main_inst.db.log_master_audit(user.id, 0, "bot_created", "error", str(exc))
            await query.message.reply_text(f"❌ {exc}")
            return True
        except Exception as exc:
            error = clean_error(exc)
            main_inst.db.log_master_audit(user.id, bot_id or 0, "bot_created", "error", error)
            logger.exception("Create bot flow failed: %s", error)
            await query.message.reply_text(f"❌ Bot creation failed safely.\nReason: {error[:1200]}")
            return True

    if not main_inst.is_owner(user.id):
        return False

    if data.startswith("bm:"):
        await query.answer()
        try:
            _, bot_id_str, action = data.split(":", 2)
            bot_id = int(bot_id_str)
        except (ValueError, IndexError):
            await query.message.reply_text("Invalid bot action.")
            return True
        inst = bm.children.get(bot_id)
        if action == "auto_member":
            if not inst:
                await query.message.reply_text("Bot not found.")
                return True
            if inst.application is None:
                await query.answer("Child bot is not running.", show_alert=True)
                return True
            current = inst.db.get_setting("auto_member_enabled", "0")
            new_value = "0" if current == "1" else "1"
            if new_value == "1":
                channels = inst.db.get_channels(enabled_only=True)
                if not channels:
                    await query.answer("This child bot has no enabled channels.", show_alert=True)
                    return True
                permission_ok = False
                for channel in channels:
                    try:
                        member = await inst.application.bot.get_chat_member(
                            chat_id=channel["channel_id"], user_id=inst.application.bot.id
                        )
                        status = str(getattr(member, "status", ""))
                        can_invite = getattr(member, "can_invite_users", None)
                        if status == "creator" or (status == "administrator" and can_invite is True):
                            permission_ok = True
                            break
                    except TelegramError:
                        continue
                if not permission_ok:
                    await query.answer(
                        "Child bot needs admin + Invite Users permission in an enabled channel.",
                        show_alert=True,
                    )
                    return True
            inst.db.set_setting("auto_member_enabled", new_value)
            inst.db.log_event("auto_member_toggled_by_main_owner", user.id, details=f"enabled={new_value}")
            main_inst.db.log_master_audit(user.id, bot_id, "auto_member_toggled", "ok", f"enabled={new_value}")
            await query.answer(f"Auto Member {'ON' if new_value == '1' else 'OFF'}")
            await show_bot_manage_page(query, inst)
            return True
        if action == "manage":
            if not inst:
                await query.message.reply_text("Bot not found.")
                return True
            await show_bot_manage_page(query, inst); return True
        if action == "stats":
            if not inst:
                await query.message.reply_text("Bot not found.")
                return True
            await show_bot_stats_page(query, inst); return True
        if action == "broadcast":
            if not inst or inst.application is None or inst.status != "live":
                await query.message.reply_text("That child bot is not live. Start it first.")
                return True
            context.user_data["master_broadcast_target"] = bot_id
            context.user_data.pop("pending_broadcast_id", None)
            context.user_data["pending_broadcast_buttons"] = []
            context.user_data["button_target"] = None
            context.user_data["awaiting"] = "master_broadcast_compose"
            await query.message.reply_text(
                f"📢 SEND BROADCAST FOR @{inst.display_name}\n\n"
                "Send the broadcast content now (text/photo/video/document/animation/audio/voice).\n"
                "It will be sent FROM this child bot to ITS user list.\n\nUse /cancel to cancel.")
            return True
        if action == "open":
            if not inst:
                await query.message.reply_text("Bot not found."); return True
            await query.message.reply_text(
                f"👉 Open @{inst.display_name} in Telegram and send /admin there. "
                f"That bot's admin (id {inst.owner_id}) gets the full admin panel for it.")
            return True
        if action == "start":
            if not inst:
                await query.message.reply_text("Bot not found."); return True
            ok = await bm.start_child(bot_id, RENDER_EXTERNAL_URL)
            if ok:
                await query.message.reply_text(f"🟢 @{inst.display_name} is LIVE.")
            else:
                await query.message.reply_text(f"⚠️ @{inst.display_name} failed to start.\nReason: {inst.last_error[:1200]}")
            await show_bot_manage_page(query, inst)
            return True
        if action == "stop":
            if not inst:
                await query.message.reply_text("Bot not found."); return True
            ok = await bm.stop_child(bot_id)
            await query.message.reply_text(f"{'⏸' if ok else '⚠️'} @{inst.display_name} status: {inst.status}.")
            await show_bot_manage_page(query, inst)
            return True
        if action == "delete":
            if not inst:
                await query.message.reply_text("Bot not found."); return True
            await query.message.reply_text(
                f"⚠️ Are you sure you want to delete @{inst.display_name}?",
                reply_markup=InlineKeyboardMarkup([[
                    _make_callback_button("🗑 Yes, Delete", f"bm:{bot_id}:delete_yes", "danger"),
                    _make_callback_button("❌ Cancel", f"bm:{bot_id}:manage", "primary")
                ]]))
            return True
        if action == "delete_yes":
            if not inst:
                await query.message.reply_text("Bot not found."); return True
            name = inst.display_name
            await bm.delete_child(bot_id)
            await query.message.reply_text(f"🗑 @{name} stopped, webhook removed, and removed from Bot Manager. Historical data preserved (soft-delete).",
                                           reply_markup=admin_menu(True))
            return True
        if action == "edit_admin":
            if not inst:
                await query.message.reply_text("Bot not found."); return True
            context.user_data["edit_child_target"] = bot_id
            context.user_data["awaiting"] = "edit_child_admin_id"
            await query.message.reply_text(f"Send the new Admin ID for @{inst.display_name}. The previous admin will lose access immediately.")
            return True
    return False


# ============================================================
# GLOBAL INSTANCES + MAIN ENTRYPOINT
# ============================================================

MAIN_INSTANCE: Optional[BotInstance] = None
BOT_MANAGER: Optional[BotManager] = None
WEBHOOK_SERVER: Optional[MultiBotWebhookServer] = None


def _build_main_instance() -> BotInstance:
    global MAIN_INSTANCE, BOT_MANAGER
    MAIN_INSTANCE = BotInstance(
        bot_id=MAIN_BOT_ID, token=BOT_TOKEN, owner_id=OWNER_ID, db_path=DB_PATH,
        is_main=True, display_name="Main Control Bot",
        webhook_path=WEBHOOK_PATH, webhook_secret=WEBHOOK_SECRET,
    )
    BOT_MANAGER = BotManager(MAIN_INSTANCE)
    return MAIN_INSTANCE


async def run_webhook_mode() -> None:
    """Run the shared single-port webhook server and every enabled bot."""
    global WEBHOOK_SERVER
    main_inst = MAIN_INSTANCE
    if main_inst is None or BOT_MANAGER is None:
        raise RuntimeError("Main instance was not built")

    logger.info("Starting Render webhook mode on port %s", RENDER_PORT)
    # 1. Prepare MAIN first. This assigns MAIN_INSTANCE.application reliably.
    if not await main_inst.prepare():
        raise RuntimeError(f"Main bot preparation failed: {main_inst.last_error}")

    # 2. Load persisted children before exposing webhook endpoints.
    await BOT_MANAGER.load_persisted_children()

    # 3. Start the ONE public aiohttp server and register every known route.
    WEBHOOK_SERVER = MultiBotWebhookServer(RENDER_PORT, RENDER_EXTERNAL_URL)
    WEBHOOK_SERVER.register_bot(main_inst)
    for inst in list(BOT_MANAGER.children.values()):
        WEBHOOK_SERVER.register_bot(inst)
    await WEBHOOK_SERVER.start()

    try:
        # 4. Start MAIN first; its Application is already initialized and the
        # route is already live. Telegram webhook registration happens only
        # after Application.start() is consuming update_queue.
        if not await main_inst.start(webhook_base_url=RENDER_EXTERNAL_URL):
            raise RuntimeError(f"Main bot start failed: {main_inst.last_error}")

        logger.info("Webhook URL (main): %s/%s", RENDER_EXTERNAL_URL, main_inst.webhook_path)
        logger.info("Health check: %s/health", RENDER_EXTERNAL_URL)

        # 5. Start children independently; one failure never aborts MAIN.
        await BOT_MANAGER.start_all_enabled_children(RENDER_EXTERNAL_URL)

        await asyncio.Event().wait()
    except asyncio.CancelledError:
        pass
    finally:
        logger.info("Shutting down multi-bot webhook server...")
        if BOT_MANAGER:
            for inst in list(BOT_MANAGER.children.values()):
                try:
                    await inst.stop()
                except Exception:
                    logger.exception("Child stop failed during shutdown (bot_id=%s)", inst.bot_id)
        if main_inst:
            try:
                await main_inst.stop()
            except Exception:
                logger.exception("Main stop failed during shutdown (bot_id=%s)", main_inst.bot_id)
        if WEBHOOK_SERVER:
            await WEBHOOK_SERVER.stop()
            WEBHOOK_SERVER = None


async def run_polling_mode() -> None:
    """Local development mode: main bot polls; children remain stopped."""
    main_inst = MAIN_INSTANCE
    if main_inst is None or BOT_MANAGER is None:
        raise RuntimeError("Main instance was not built")
    await BOT_MANAGER.load_persisted_children()
    if not await main_inst.start(polling=True):
        raise RuntimeError(f"Main bot start failed: {main_inst.last_error}")
    try:
        await asyncio.Event().wait()
    except asyncio.CancelledError:
        pass
    finally:
        await main_inst.stop()


def main() -> None:
    logger.info("Initializing main database at: %s", DB_PATH.resolve())
    _build_main_instance()
    MAIN_INSTANCE.db.connect()

    if RENDER_EXTERNAL_URL:
        logger.info("Detected Render deployment (RENDER_EXTERNAL_URL set).")
        logger.info("Single-port webhook mode: all bot webhooks + /health on 0.0.0.0:%s", RENDER_PORT)
        try:
            asyncio.run(run_webhook_mode())
        except KeyboardInterrupt:
            pass
    else:
        start_health_server()
        logger.info("Local polling mode. Main bot only; child bots remain stopped.")
        try:
            asyncio.run(run_polling_mode())
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()
