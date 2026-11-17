#!/usr/bin/env python3
"""
MinorUPI — Private Personal UPI Payment Gateway
A self-hosted, single-admin UPI payment gateway with automated FamApp email
verification, unique-amount paise offset, order lifecycle management, webhooks,
and AI integration prompt generator.
"""

import os
import sys
import re
import time
import hmac
import hashlib
import secrets
import sqlite3
import threading
import imaplib
import email
from email.header import decode_header
import base64
import io
import json
import urllib.parse
import urllib.request
from datetime import datetime, timezone, timedelta
from decimal import Decimal, ROUND_HALF_UP
from collections import defaultdict

from flask import (
    Flask, request, jsonify, session, redirect, send_file,
    Response, make_response
)
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.middleware.proxy_fix import ProxyFix
from itsdangerous import URLSafeTimedSerializer, BadSignature, SignatureExpired
from cryptography.fernet import Fernet
import qrcode
from qrcode.constants import ERROR_CORRECT_M

# ==============================================================================
# CONFIGURATION CONSTANTS (Plain constants at top of file)
# ==============================================================================
PORT = int(os.environ.get("PORT", 3000))
HOST = "0.0.0.0"
BASE_URL = os.environ.get("APP_URL", "").rstrip("/")
DB_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gateway.db")
ALLOWED_EMAIL_DOMAINS = ["famapp.in"]
API_DEFAULT_EXPIRY_MINUTES = 5
WORKER_POLL_INTERVAL_SECONDS = 6
CHECKOUT_POLL_INTERVAL_SECONDS = 3
MAX_PAISE_OFFSET = 100
MAX_LOGIN_ATTEMPTS = 5
LOGIN_LOCKOUT_SECONDS = 60
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

# ==============================================================================
# FLASK APPLICATION & IN-MEMORY RATE LIMITERS
# ==============================================================================
app = Flask(__name__)
# Add ProxyFix so HTTPS and client IP behind proxy (Cloud Run, Render, nginx) are properly recognized
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1, x_prefix=1)
app.config["SESSION_COOKIE_HTTPONLY"] = True
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
app.config["SESSION_COOKIE_SECURE"] = False  # Set dynamically for HTTPS in after_request
app.config["PERMANENT_SESSION_LIFETIME"] = timedelta(days=7)

@app.after_request
def dynamic_cookie_security(response):
    is_https = request.is_secure or request.headers.get("X-Forwarded-Proto") == "https"
    if is_https:
        cookies = response.headers.getlist("Set-Cookie")
        if cookies:
            response.headers.remove("Set-Cookie")
            for c in cookies:
                if "session=" in c and "Secure" not in c:
                    c = c + "; Secure"
                response.headers.add("Set-Cookie", c)
    return response

# In-memory tracking for brute-force login protection and API rate limits
login_failed_attempts = defaultdict(list)  # ip -> [timestamps]
api_rate_tracking = defaultdict(list)      # api_key_hash -> [timestamps]
db_lock = threading.Lock()

# Global encryption & webhook secrets (loaded from DB settings table)
FERNET_KEY = None
WEBHOOK_SECRET = None
_fernet_instance = None
_worker_started = False

# ==============================================================================
# DATABASE MANAGEMENT (SQLite)
# ==============================================================================
def get_db():
    conn = sqlite3.connect(DB_FILE, timeout=10.0, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL;")
    conn.execute("PRAGMA busy_timeout=5000;")
    return conn

def init_db():
    global FERNET_KEY, WEBHOOK_SECRET, _fernet_instance
    with get_db() as db:
        # Settings table for auto-generated secrets
        db.execute("""
            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );
        """)

        # Admin table (Single admin, no public signups)
        db.execute("""
            CREATE TABLE IF NOT EXISTS admin (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                email TEXT UNIQUE NOT NULL,
                password_hash TEXT NOT NULL,
                created_at TEXT NOT NULL
            );
        """)

        # Connection table (UPI ID + Encrypted Google App Password)
        db.execute("""
            CREATE TABLE IF NOT EXISTS connection (
                id INTEGER PRIMARY KEY CHECK (id = 1),
                upi_id TEXT NOT NULL,
                gmail TEXT NOT NULL,
                encrypted_app_password TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'disconnected',
                last_checked TEXT,
                last_error TEXT
            );
        """)

        # Orders table
        db.execute("""
            CREATE TABLE IF NOT EXISTS orders (
                id TEXT PRIMARY KEY,
                source TEXT NOT NULL, -- 'api' or 'link'
                base_amount REAL NOT NULL,
                payable_amount REAL NOT NULL,
                status TEXT NOT NULL DEFAULT 'pending', -- pending, paid, expired, cancelled, failed
                fail_reason TEXT,
                utr TEXT UNIQUE,
                txn_id TEXT,
                created_at TEXT NOT NULL,
                expires_at TEXT NOT NULL,
                paid_at TEXT,
                callback_url TEXT,
                redirect_url TEXT,
                note TEXT
            );
        """)

        # API Keys table (Store SHA-256 hash, display key only once)
        db.execute("""
            CREATE TABLE IF NOT EXISTS api_keys (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                key_hash TEXT UNIQUE NOT NULL,
                prefix TEXT NOT NULL,
                name TEXT NOT NULL,
                created_at TEXT NOT NULL,
                revoked INTEGER DEFAULT 0
            );
        """)

        # Processed emails (Idempotency check so one email never verifies twice)
        db.execute("""
            CREATE TABLE IF NOT EXISTS processed_emails (
                message_id TEXT PRIMARY KEY,
                sender TEXT,
                subject TEXT,
                received_at TEXT,
                matched_order_id TEXT,
                amount REAL,
                utr TEXT
            );
        """)

        # Webhook logs
        db.execute("""
            CREATE TABLE IF NOT EXISTS webhook_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                order_id TEXT NOT NULL,
                url TEXT NOT NULL,
                payload TEXT NOT NULL,
                signature TEXT NOT NULL,
                attempt INTEGER DEFAULT 1,
                response_code INTEGER,
                response_body TEXT,
                success INTEGER DEFAULT 0,
                created_at TEXT NOT NULL
            );
        """)

        # Unmatched payments
        db.execute("""
            CREATE TABLE IF NOT EXISTS unmatched_payments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                amount REAL NOT NULL,
                sender_name TEXT,
                utr TEXT UNIQUE,
                txn_id TEXT,
                email_date TEXT,
                message_id TEXT,
                raw_snippet TEXT,
                reason TEXT NOT NULL,
                received_at TEXT NOT NULL
            );
        """)
        db.commit()

        # Initialize or load secrets
        cur = db.cursor()
        cur.execute("SELECT value FROM settings WHERE key = 'SECRET_KEY'")
        row = cur.fetchone()
        if not row:
            secret_key = secrets.token_hex(32)
            cur.execute("INSERT INTO settings (key, value) VALUES ('SECRET_KEY', ?)", (secret_key,))
        else:
            secret_key = row["value"]
        app.secret_key = secret_key

        cur.execute("SELECT value FROM settings WHERE key = 'FERNET_KEY'")
        row = cur.fetchone()
        if not row:
            fernet_key_bytes = Fernet.generate_key().decode()
            cur.execute("INSERT INTO settings (key, value) VALUES ('FERNET_KEY', ?)", (fernet_key_bytes,))
            FERNET_KEY = fernet_key_bytes
        else:
            FERNET_KEY = row["value"]
        _fernet_instance = Fernet(FERNET_KEY.encode())

        cur.execute("SELECT value FROM settings WHERE key = 'WEBHOOK_SECRET'")
        row = cur.fetchone()
        if not row:
            webhook_secret = secrets.token_hex(24)
            cur.execute("INSERT INTO settings (key, value) VALUES ('WEBHOOK_SECRET', ?)", (webhook_secret,))
            WEBHOOK_SECRET = webhook_secret
        else:
            WEBHOOK_SECRET = row["value"]
        db.commit()

def encrypt_secret(plain_text: str) -> str:
    global _fernet_instance
    if not plain_text:
        return ""
    return _fernet_instance.encrypt(plain_text.encode()).decode()

def decrypt_secret(cipher_text: str) -> str:
    global _fernet_instance
    if not cipher_text:
        return ""
    try:
        return _fernet_instance.decrypt(cipher_text.encode()).decode()
    except Exception:
        return ""

def get_base_url():
    if BASE_URL:
        return BASE_URL
    return request.host_url.rstrip("/")

def iso_now():
    return datetime.now(timezone.utc).isoformat()

# ==============================================================================
# STATELESS SIGNED CSRF & CONFIGURATION HELPERS
# ==============================================================================
CSRF_SALT = "minorupi-csrf-token-salt"
CSRF_MAX_AGE_SECONDS = 43200  # 12 hours valid

def get_csrf_serializer():
    # Use app.secret_key (guaranteed persisted in database settings table)
    key = app.secret_key or "minorupi-fallback-secret-key"
    return URLSafeTimedSerializer(key, salt=CSRF_SALT)

def generate_csrf_token():
    s = get_csrf_serializer()
    nonce = secrets.token_hex(16)
    return s.dumps({"nonce": nonce, "ts": int(time.time())})

def verify_csrf_token(token: str) -> bool:
    if not token or not isinstance(token, str):
        return False
    s = get_csrf_serializer()
    try:
        data = s.loads(token, max_age=CSRF_MAX_AGE_SECONDS)
        return isinstance(data, dict) and "nonce" in data
    except (BadSignature, SignatureExpired, Exception):
        return False

def verify_csrf():
    # 1. Origin / Referer validation if present
    origin = request.headers.get("Origin") or request.headers.get("Referer")
    if origin:
        try:
            parsed_origin = urllib.parse.urlparse(origin).netloc.lower()
            req_host = request.host.lower()
            if parsed_origin and req_host and parsed_origin != req_host:
                is_local = (parsed_origin.startswith("localhost") or parsed_origin.startswith("127.0.0.1")) and \
                           (req_host.startswith("localhost") or req_host.startswith("127.0.0.1"))
                if not is_local:
                    return False
        except Exception:
            return False

    # 2. Extract token from Header X-CSRF-Token, Form, or JSON body
    token = request.headers.get("X-CSRF-Token")
    if not token and request.form:
        token = request.form.get("csrf_token")
    if not token and request.is_json:
        try:
            json_body = request.get_json(silent=True)
            if isinstance(json_body, dict):
                token = json_body.get("csrf_token")
        except Exception:
            pass

    return verify_csrf_token(token)

def csrf_error_response():
    return jsonify({
        "success": False,
        "error": {
            "code": "CSRF_INVALID",
            "message": "Invalid or expired CSRF token. Please refresh and try again."
        }
    }), 403

def is_gateway_configured() -> bool:
    """
    Checks if FamApp UPI ID + Gmail + App Password have been connected
    and the IMAP verification test succeeded (status == 'connected').
    """
    with get_db() as db:
        row = db.execute("SELECT upi_id, gmail, encrypted_app_password, status FROM connection WHERE id = 1").fetchone()
        if not row:
            return False
        if not (row["upi_id"] and row["gmail"] and row["encrypted_app_password"]):
            return False
        if row["status"] != "connected":
            return False
        return True

def is_ip_rate_limited(ip_address: str) -> bool:
    now = time.time()
    recent = [t for t in login_failed_attempts[ip_address] if now - t < LOGIN_LOCKOUT_SECONDS]
    login_failed_attempts[ip_address] = recent
    return len(recent) >= MAX_LOGIN_ATTEMPTS

def record_failed_login(ip_address: str):
    login_failed_attempts[ip_address].append(time.time())

def reset_failed_login(ip_address: str):
    if ip_address in login_failed_attempts:
        del login_failed_attempts[ip_address]

# ==============================================================================
# UNIQUE-AMOUNT PAISE OFFSET ALLOCATION (Section 7.1)
# ==============================================================================
def allocate_unique_payable_amount(base_amount: float) -> float:
    """
    Finds the first available paise offset (0.00 to 0.99) for a base amount
    such that no other pending order has the exact same payable amount.
    """
    base_dec = Decimal(str(base_amount)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    with get_db() as db:
        rows = db.execute("SELECT payable_amount FROM orders WHERE status = 'pending'").fetchall()
        busy_amounts = {round(row["payable_amount"], 2) for row in rows}

        for offset in range(MAX_PAISE_OFFSET):
            offset_dec = Decimal(offset) / Decimal(100)
            candidate = float(base_dec + offset_dec)
            candidate_rounded = round(candidate, 2)
            if candidate_rounded not in busy_amounts:
                return candidate_rounded

    raise ValueError(f"No unique payable amount slot available for ₹{base_amount:.2f}. All {MAX_PAISE_OFFSET} paise slots are currently pending. Retry shortly.")

# ==============================================================================
# QR CODE & UPI LINK GENERATION (Section 6)
# ==============================================================================
def generate_upi_payment_data(order_id: str, payable_amount: float):
    with get_db() as db:
        conn_row = db.execute("SELECT upi_id FROM connection WHERE id = 1").fetchone()
        admin_row = db.execute("SELECT name FROM admin LIMIT 1").fetchone()

    upi_id = conn_row["upi_id"] if conn_row and conn_row["upi_id"] else ""
    merchant_name = admin_row["name"] if admin_row and admin_row["name"] else "MinorUPI Merchant"
    
    # Standard UPI URI schema
    query = urllib.parse.urlencode({
        "pa": upi_id or "pay@minorupi",
        "pn": merchant_name,
        "am": f"{payable_amount:.2f}",
        "cu": "INR",
        "tn": order_id
    })
    upi_link = f"upi://pay?{query}"

    # Generate QR PNG
    qr = qrcode.QRCode(
        version=1,
        error_correction=ERROR_CORRECT_M,
        box_size=10,
        border=2,
    )
    qr.add_data(upi_link)
    qr.make(fit=True)
    img = qr.make_image(fill_color="#0f172a", back_color="#ffffff")
    
    buf = io.BytesIO()
    img.save(buf, format="PNG")
    qr_bytes = buf.getvalue()
    qr_base64 = "data:image/png;base64," + base64.b64encode(qr_bytes).decode("ascii")

    return {
        "upi_id": upi_id,
        "merchant_name": merchant_name,
        "upi_link": upi_link,
        "qr_base64": qr_base64,
        "qr_bytes": qr_bytes
    }

# ==============================================================================
# EMAIL PARSER REGISTRY (Section 7.2)
# ==============================================================================
def clean_html_to_text(html_content: str) -> str:
    text = re.sub(r"<style.*?>.*?</style>", "", html_content, flags=re.DOTALL | re.IGNORECASE)
    text = re.sub(r"<script.*?>.*?</script>", "", text, flags=re.DOTALL | re.IGNORECASE)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"&nbsp;", " ", text)
    text = re.sub(r"&amp;", "&", text)
    return re.sub(r"\s+", " ", text).strip()

def parse_famapp_email(subject: str, body_text: str, headers: dict):
    """
    Parses FamApp credit notification emails.
    Sample:
    Hey Customer Name,
    You have successfully received
    ₹33.0
    from SENDER NAME
    Transaction ID :
    TXN_7819203841
    Date :
    04:22 PM IST, 02 November 2026
    Updated Balance :
    ₹34.01
    UTR :
    006523947230
    """
    normalized = body_text.replace("\r", "")
    
    # Must contain credit confirmation
    if "successfully received" not in normalized.lower():
        return None

    # Amount: number right after 'received', before 'from' (MUST NOT match 'Updated Balance')
    amount_match = re.search(
        r"(?:successfully\s+received|received)[\s\n\r]*[₹Rs\.]*\s*([0-9,]+(?:\.[0-9]{1,2})?)",
        normalized,
        re.IGNORECASE
    )
    if not amount_match:
        return None

    raw_amount = amount_match.group(1).replace(",", "")
    try:
        amount = float(Decimal(raw_amount).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))
    except Exception:
        return None

    # Sender Name
    sender_match = re.search(r"from\s+([A-Za-z0-9\s\.\-_]+?)(?:\n|Transaction ID|\Z)", normalized, re.IGNORECASE)
    sender_name = sender_match.group(1).strip() if sender_match else "UPI Customer"

    # Transaction ID
    txn_match = re.search(r"Transaction ID\s*:\s*([A-Za-z0-9_\-]+)", normalized, re.IGNORECASE)
    txn_id = txn_match.group(1).strip() if txn_match else None

    # UTR
    utr_match = re.search(r"UTR\s*:\s*([A-Za-z0-9_\-]+)", normalized, re.IGNORECASE)
    utr = utr_match.group(1).strip() if utr_match else None
    if not utr and txn_id:
        utr = txn_id  # Fallback if UTR missing

    # Date
    date_match = re.search(r"Date\s*:\s*([^\n\r]+)", normalized, re.IGNORECASE)
    date_str = date_match.group(1).strip() if date_match else iso_now()

    return {
        "amount": amount,
        "sender_name": sender_name,
        "txn_id": txn_id or f"TXN_{secrets.token_hex(6).upper()}",
        "utr": utr or f"UTR_{secrets.token_hex(6).upper()}",
        "date_str": date_str,
        "raw_snippet": normalized[:250]
    }

# Registry for multi-provider extension
EMAIL_PARSER_REGISTRY = [
    parse_famapp_email
]

# ==============================================================================
# WEBHOOK DISPATCHER WITH EXPONENTIAL BACKOFF (Section 8.1)
# ==============================================================================
def dispatch_webhook_async(order_id: str, status: str, amount: float, base_amount: float, utr: str, txn_id: str, paid_at: str, note: str, callback_url: str):
    if not callback_url:
        return

    def _worker():
        payload_dict = {
            "order_id": order_id,
            "status": status,
            "amount": amount,
            "base_amount": base_amount,
            "utr": utr,
            "txn_id": txn_id,
            "paid_at": paid_at,
            "created_at": iso_now(),
            "note": note or ""
        }
        raw_body = json.dumps(payload_dict, separators=(",", ":"))
        signature = hmac.new(WEBHOOK_SECRET.encode("utf-8"), raw_body.encode("utf-8"), hashlib.sha256).hexdigest()

        delays = [0, 2, 6]  # 3 attempts with backoff
        for attempt_idx, delay in enumerate(delays, start=1):
            if delay > 0:
                time.sleep(delay)

            try:
                req = urllib.request.Request(
                    callback_url,
                    data=raw_body.encode("utf-8"),
                    headers={
                        "Content-Type": "application/json",
                        "X-Signature": signature,
                        "User-Agent": "Personal-UPI-Gateway-Webhook/1.0"
                    },
                    method="POST"
                )
                with urllib.request.urlopen(req, timeout=10) as resp:
                    resp_code = resp.status
                    resp_body = resp.read().decode("utf-8", errors="replace")[:500]
                    success = 1 if 200 <= resp_code < 300 else 0

                with get_db() as db:
                    db.execute("""
                        INSERT INTO webhook_logs (order_id, url, payload, signature, attempt, response_code, response_body, success, created_at)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, (order_id, callback_url, raw_body, signature, attempt_idx, resp_code, resp_body, success, iso_now()))
                    db.commit()

                if success:
                    break
            except Exception as e:
                with get_db() as db:
                    db.execute("""
                        INSERT INTO webhook_logs (order_id, url, payload, signature, attempt, response_code, response_body, success, created_at)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, (order_id, callback_url, raw_body, signature, attempt_idx, 0, str(e)[:500], 0, iso_now()))
                    db.commit()

    t = threading.Thread(target=_worker, daemon=True)
    t.start()

# ==============================================================================
# BACKGROUND IMAP WORKER & EXPIRY SCHEDULER (Section 5 & 7.1)
# ==============================================================================
def check_order_expiries():
    """Marks pending orders that have passed expires_at as expired."""
    now_str = iso_now()
    with get_db() as db:
        expired_orders = db.execute("""
            SELECT * FROM orders WHERE status = 'pending' AND expires_at <= ?
        """, (now_str,)).fetchall()

        for o in expired_orders:
            db.execute("UPDATE orders SET status = 'expired' WHERE id = ?", (o["id"],))
            db.commit()
            if o["callback_url"]:
                dispatch_webhook_async(
                    order_id=o["id"],
                    status="expired",
                    amount=o["payable_amount"],
                    base_amount=o["base_amount"],
                    utr=None,
                    txn_id=None,
                    paid_at=None,
                    note=o["note"],
                    callback_url=o["callback_url"]
                )

def poll_gmail_imap():
    """Connects to Gmail via IMAP, searches recent emails, and verifies pending orders."""
    with get_db() as db:
        pending_orders = db.execute("SELECT * FROM orders WHERE status = 'pending'").fetchall()
        if not pending_orders:
            return  # Idle if no pending orders

        conn_row = db.execute("SELECT * FROM connection WHERE id = 1").fetchone()
        if not conn_row or conn_row["status"] != "connected":
            return

        gmail = conn_row["gmail"]
        app_password = decrypt_secret(conn_row["encrypted_app_password"])

    if not gmail or not app_password:
        return

    mail = None
    try:
        mail = imaplib.IMAP4_SSL("imap.gmail.com", 993, timeout=12)
        mail.login(gmail, app_password)
        mail.select("INBOX")

        # Search for recent unread or recent 15 minutes of messages
        status, search_data = mail.search(None, "UNSEEN")
        msg_ids = search_data[0].split()

        # If no unseen, check latest 15 messages in inbox
        if not msg_ids:
            status, all_data = mail.search(None, "ALL")
            all_ids = all_data[0].split()
            msg_ids = all_ids[-15:] if len(all_ids) > 15 else all_ids

        for num in reversed(msg_ids):
            status, data = mail.fetch(num, "(RFC822)")
            if status != "OK" or not data or not data[0]:
                continue

            raw_email = data[0][1]
            msg = email.message_from_bytes(raw_email)

            msg_id = msg.get("Message-ID") or f"MSG_{hashlib.sha256(raw_email).hexdigest()[:20]}"
            
            # Idempotency check: have we already processed this message?
            with get_db() as db:
                if db.execute("SELECT message_id FROM processed_emails WHERE message_id = ?", (msg_id,)).fetchone():
                    continue

            # Check Sender Domain for anti-spoofing
            from_hdr = msg.get("From", "")
            from_domain = from_hdr.split("@")[-1].replace(">", "").strip().lower()
            if not any(from_domain.endswith(allowed) for allowed in ALLOWED_EMAIL_DOMAINS):
                # Non-allowed sender, ignore
                continue

            # Check SPF/DKIM authentication header if present
            auth_results = msg.get("Authentication-Results", "").lower()
            if "dkim=fail" in auth_results or "spf=fail" in auth_results:
                # Rejected spoofed email
                continue

            # Extract subject and body
            subject = ""
            raw_sub = msg.get("Subject", "")
            for part, enc in decode_header(raw_sub):
                if isinstance(part, bytes):
                    subject += part.decode(enc or "utf-8", errors="replace")
                else:
                    subject += str(part)

            body_text = ""
            if msg.is_multipart():
                for part in msg.walk():
                    ctype = part.get_content_type()
                    cdisp = str(part.get("Content-Disposition"))
                    if "attachment" in cdisp:
                        continue
                    payload = part.get_payload(decode=True)
                    if not payload:
                        continue
                    text_chunk = payload.decode(part.get_content_charset() or "utf-8", errors="replace")
                    if ctype == "text/plain":
                        body_text += " " + text_chunk
                    elif ctype == "text/html":
                        body_text += " " + clean_html_to_text(text_chunk)
            else:
                payload = msg.get_payload(decode=True)
                if payload:
                    body_text = clean_html_to_text(payload.decode(msg.get_content_charset() or "utf-8", errors="replace"))

            # Run through email parser registry
            parsed = None
            for parser_func in EMAIL_PARSER_REGISTRY:
                parsed = parser_func(subject, body_text, dict(msg.items()))
                if parsed:
                    break

            if not parsed:
                continue

            parsed_amount = parsed["amount"]
            parsed_utr = parsed["utr"]
            parsed_txnid = parsed["txn_id"]
            parsed_sender = parsed["sender_name"]
            parsed_date = parsed["date_str"]

            with get_db() as db:
                # Find matching pending order
                # Condition: payable_amount matches parsed amount exactly
                matched_order = db.execute("""
                    SELECT * FROM orders 
                    WHERE status = 'pending' AND ABS(payable_amount - ?) < 0.005
                    ORDER BY created_at ASC
                    LIMIT 1
                """, (parsed_amount,)).fetchone()

                now_time_iso = iso_now()

                if matched_order:
                    # Check if UTR is already used by another order
                    existing_utr = db.execute("SELECT id FROM orders WHERE utr = ?", (parsed_utr,)).fetchone()
                    if existing_utr and existing_utr["id"] != matched_order["id"]:
                        # Duplicate payment or conflicting UTR
                        db.execute("""
                            INSERT INTO unmatched_payments (amount, sender_name, utr, txn_id, email_date, message_id, raw_snippet, reason, received_at)
                            VALUES (?, ?, ?, ?, ?, ?, ?, 'Duplicate UTR already recorded', ?)
                        """, (parsed_amount, parsed_sender, parsed_utr, parsed_txnid, parsed_date, msg_id, parsed["raw_snippet"], now_time_iso))
                    else:
                        # Success! Mark order as paid
                        db.execute("""
                            UPDATE orders 
                            SET status = 'paid', utr = ?, txn_id = ?, paid_at = ?
                            WHERE id = ?
                        """, (parsed_utr, parsed_txnid, now_time_iso, matched_order["id"]))

                        db.execute("""
                            INSERT INTO processed_emails (message_id, sender, subject, received_at, matched_order_id, amount, utr)
                            VALUES (?, ?, ?, ?, ?, ?, ?)
                        """, (msg_id, from_hdr, subject, now_time_iso, matched_order["id"], parsed_amount, parsed_utr))
                        db.commit()

                        if matched_order["callback_url"]:
                            dispatch_webhook_async(
                                order_id=matched_order["id"],
                                status="paid",
                                amount=matched_order["payable_amount"],
                                base_amount=matched_order["base_amount"],
                                utr=parsed_utr,
                                txn_id=parsed_txnid,
                                paid_at=now_time_iso,
                                note=matched_order["note"],
                                callback_url=matched_order["callback_url"]
                            )
                else:
                    # No pending order matched (arrived late, wrong amount, etc.)
                    db.execute("""
                        INSERT INTO unmatched_payments (amount, sender_name, utr, txn_id, email_date, message_id, raw_snippet, reason, received_at)
                        VALUES (?, ?, ?, ?, ?, ?, ?, 'No pending order matching amount', ?)
                    """, (parsed_amount, parsed_sender, parsed_utr, parsed_txnid, parsed_date, msg_id, parsed["raw_snippet"], now_time_iso))

                    db.execute("""
                        INSERT INTO processed_emails (message_id, sender, subject, received_at, matched_order_id, amount, utr)
                        VALUES (?, ?, ?, ?, NULL, ?, ?)
                    """, (msg_id, from_hdr, subject, now_time_iso, parsed_amount, parsed_utr))
                    db.commit()

        # Update last connection health
        with get_db() as db:
            db.execute("UPDATE connection SET status = 'connected', last_checked = ?, last_error = NULL WHERE id = 1", (iso_now(),))
            db.commit()

    except Exception as e:
        with get_db() as db:
            db.execute("UPDATE connection SET status = 'disconnected', last_error = ?, last_checked = ? WHERE id = 1", (str(e), iso_now()))
            db.commit()
    finally:
        if mail:
            try:
                mail.close()
            except Exception:
                pass
            try:
                mail.logout()
            except Exception:
                pass

def background_worker_loop():
    while True:
        try:
            check_order_expiries()
            poll_gmail_imap()
        except Exception:
            pass
        time.sleep(WORKER_POLL_INTERVAL_SECONDS)

def start_background_worker_once():
    global _worker_started
    if not _worker_started:
        _worker_started = True
        worker_thread = threading.Thread(target=background_worker_loop, daemon=True)
        worker_thread.start()

# ==============================================================================
# AUTHENTICATION & API KEY VERIFICATION
# ==============================================================================
def require_admin(f):
    def wrapper(*args, **kwargs):
        if "admin_id" not in session:
            if request.path.startswith("/api/"):
                return jsonify({"success": False, "error": {"code": "UNAUTHORIZED", "message": "Admin session required"}}), 401
            return redirect("/login")
        return f(*args, **kwargs)
    wrapper.__name__ = f.__name__
    return wrapper

def verify_api_key_auth():
    auth_header = request.headers.get("Authorization", "")
    api_key = None
    if auth_header.startswith("Bearer "):
        api_key = auth_header[7:].strip()
    elif "X-API-Key" in request.headers:
        api_key = request.headers.get("X-API-Key").strip()

    if not api_key:
        return False, {"code": "MISSING_KEY", "message": "API key required in Authorization: Bearer <KEY> or X-API-Key"}

    key_hash = hashlib.sha256(api_key.encode()).hexdigest()
    
    # Rate limit per API key (60 req/min)
    now = time.time()
    recent = [t for t in api_rate_tracking[key_hash] if now - t < 60]
    api_rate_tracking[key_hash] = recent
    if len(recent) >= 60:
        return False, {"code": "RATE_LIMIT_EXCEEDED", "message": "API rate limit of 60 requests/minute exceeded"}
    api_rate_tracking[key_hash].append(now)

    with get_db() as db:
        key_row = db.execute("SELECT * FROM api_keys WHERE key_hash = ? AND revoked = 0", (key_hash,)).fetchone()
        if not key_row:
            return False, {"code": "INVALID_KEY", "message": "Invalid or revoked API key"}

    return True, key_row

# ==============================================================================
# AI INTEGRATION PROMPT GENERATOR (Section 8.3)
# ==============================================================================
def generate_ai_prompt_text(stack: str = "python", api_key: str = None, webhook_secret: str = None) -> str:
    base = get_base_url()
    key_val = api_key if api_key else "YOUR_API_KEY"
    secret_val = webhook_secret if webhook_secret else "YOUR_WEBHOOK_SECRET"

    stack_guidelines = {
        "python": """### Python (Flask / FastAPI) Implementation Notes:
1. Use `requests` or `httpx` to create orders:
   ```python
   import requests
   resp = requests.post(
       f"{GATEWAY_BASE_URL}/api/v1/orders",
       headers={"Authorization": f"Bearer {GATEWAY_API_KEY}"},
       json={"amount": 99.00, "note": "Subscription #101", "callback_url": "https://yourapp.com/api/webhook"}
   )
   data = resp.json()["data"]
   payment_url = data["payment_url"]
   ```
2. Webhook verification in Flask:
   ```python
   import hmac, hashlib
   @app.route('/api/webhook', methods=['POST'])
   def handle_webhook():
       sig = request.headers.get('X-Signature')
       raw_body = request.get_data()
       expected = hmac.new(WEBHOOK_SECRET.encode(), raw_body, hashlib.sha256).hexdigest()
       if not hmac.compare_digest(sig, expected):
           return ("Invalid signature", 400)
       event = request.json
       if event.get("status") == "paid":
           # Idempotently mark order as completed in your database
           fulfill_order(event["order_id"], event["utr"])
       return ("OK", 200)
   ```""",
        "node": """### Node.js (Express) Implementation Notes:
1. Create order:
   ```javascript
   const res = await fetch(`${GATEWAY_BASE_URL}/api/v1/orders`, {
     method: 'POST',
     headers: {
       'Content-Type': 'application/json',
       'Authorization': `Bearer ${GATEWAY_API_KEY}`
     },
     body: JSON.stringify({
       amount: 149.00,
       note: 'Order #402',
       callback_url: 'https://yourapp.com/api/webhook'
     })
   });
   const { data } = await res.json();
   // Redirect customer to data.payment_url
   ```
2. Webhook verification in Express (Requires raw body):
   ```javascript
   const crypto = require('crypto');
   app.post('/api/webhook', express.raw({ type: 'application/json' }), (req, res) => {
     const signature = req.headers['x-signature'];
     const hmac = crypto.createHmac('sha256', WEBHOOK_SECRET);
     const expected = hmac.update(req.body).digest('hex');
     if (signature !== expected) return res.status(400).send('Invalid signature');
     const event = JSON.parse(req.body.toString());
     if (event.status === 'paid') {
       fulfillOrder(event.order_id, event.utr);
     }
     res.sendStatus(200);
   });
   ```""",
        "php": """### PHP Implementation Notes:
1. Create order with cURL:
   ```php
   $ch = curl_init("$GATEWAY_BASE_URL/api/v1/orders");
   curl_setopt($ch, CURLOPT_HTTPHEADER, [
       "Content-Type: application/json",
       "Authorization: Bearer $GATEWAY_API_KEY"
   ]);
   curl_setopt($ch, CURLOPT_POSTFIELDS, json_encode([
       "amount" => 50.00,
       "note" => "Order #123",
       "callback_url" => "https://yourapp.com/webhook.php"
   ]));
   curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
   $response = json_decode(curl_exec($ch), true);
   $payment_url = $response['data']['payment_url'];
   ```
2. Webhook verification in PHP:
   ```php
   $raw_body = file_get_contents('php://input');
   $signature = $_SERVER['HTTP_X_SIGNATURE'] ?? '';
   $expected = hash_hmac('sha256', $raw_body, $WEBHOOK_SECRET);
   if (!hash_equals($expected, $signature)) {
       http_response_code(400);
       exit('Invalid signature');
   }
   $event = json_decode($raw_body, true);
   if ($event['status'] === 'paid') {
       fulfill_order($event['order_id'], $event['utr']);
   }
   http_response_code(200);
   ```""",
        "frontend": """### HTML + JavaScript Frontend Notes:
1. Call your own backend to create the order securely so your API key is never exposed in browser source code!
2. Your backend creates the order via `POST /api/v1/orders` and returns `data.payment_url` and `data.qr_base64`.
3. You can display the payment QR in a modal or redirect the customer to `data.payment_url`.
4. Poll status or await redirect to complete the purchase.""",
        "telegram_python": """### Telegram Bot (Python - python-telegram-bot / aiogram) Notes:
1. When user asks to purchase:
   - Ask for amount or item selection.
   - Send `POST /api/v1/orders` with `amount`, `note=f"TG_{user_id}"`, and optional callback URL.
   - Gateway returns `qr_base64`, `payment_url`, and `upi_link`.
2. Send the QR image to the user in Telegram:
   - Decode `qr_base64` and send with `bot.send_photo`.
   - Add inline keyboard with a button "Pay via UPI App" pointing to `upi_link` or `payment_url`.
3. Polling or Webhook:
   - Start an async task polling `GET /api/v1/orders/{order_id}` every 5 seconds until `status == 'paid'` or `expired`.
   - When paid: notify user in Telegram "Payment Received! UTR: {utr}" and deliver digital goods!""",
        "telegram_node": """### Telegram Bot (Node.js - Telegraf) Notes:
1. In bot handler:
   - Request order from gateway `POST /api/v1/orders`.
   - Send QR buffer with `ctx.replyWithPhoto({ source: Buffer.from(qrBase64, 'base64') })`.
   - Add inline button with link `data.payment_url`.
2. Monitor status:
   - Poll `GET /api/v1/orders/<order_id>` every 4-5s or set up Express webhook receiver.
   - On success: send celebration message with UTR and activate perks.""",
        "generic": """### General Guidelines:
- Base URL: {GATEWAY_BASE_URL}
- Auth: Authorization: Bearer {GATEWAY_API_KEY}
- Always verify the HMAC-SHA256 signature on the raw request body for webhooks.
- Store the gateway `order_id` in your local database.""".replace("{GATEWAY_BASE_URL}", base).replace("{GATEWAY_API_KEY}", key_val)
    }

    selected_guide = stack_guidelines.get(stack, stack_guidelines["generic"])

    prompt = f"""You are a senior full-stack developer. Integrate the following private personal UPI payment gateway into my project.

### Gateway Credentials & Endpoints:
- Base URL: {base}
- API Key: {key_val}
- Webhook Secret: {secret_val}
- Authentication Header: Authorization: Bearer <API_KEY> (or X-API-Key: <API_KEY>)

### Core Payment Flow:
1. Create Order:
   Send `POST {base}/api/v1/orders`
   Body:
   {{
     "amount": 99.00,
     "order_id": "optional-custom-id",
     "expiry_minutes": 5,
     "callback_url": "https://yourdomain.com/webhook",
     "redirect_url": "https://yourdomain.com/checkout/success",
     "note": "Product Purchase #101"
   }}
   Response:
   {{
     "success": true,
     "data": {{
       "order_id": "ORD-12345678",
       "base_amount": 99.00,
       "payable_amount": 99.01,
       "payment_url": "{base}/pay/ORD-12345678",
       "qr_base64": "data:image/png;base64,...",
       "upi_link": "upi://pay?pa=...",
       "expires_at": "2026-11-17T03:55:00Z",
       "status": "pending"
     }}
   }}

2. Customer Checkout:
   Direct the customer to `payment_url` OR display the provided `qr_base64` and `upi_link` in your custom UI.

3. Receive Webhook & Verify Signature:
   When payment is verified, the gateway sends a POST request to your `callback_url`:
   Headers:
     Content-Type: application/json
     X-Signature: <hex HMAC-SHA256 of raw body using Webhook Secret>
   Body:
   {{
     "order_id": "ORD-12345678",
     "status": "paid",
     "amount": 99.01,
     "base_amount": 99.00,
     "utr": "006523947230",
     "txn_id": "TXN_78192038",
     "paid_at": "2026-11-17T03:52:10Z"
   }}
   CRITICAL: Verify the HMAC-SHA256 signature on the raw body before fulfilling any order!

4. Double-Check Verification (Idempotent):
   You can also fetch `GET {base}/api/v1/orders/<order_id>` to verify status independently.

5. Order Lifecycle:
   Statuses: `pending`, `paid`, `expired`, `cancelled`, `failed`.
   Only fulfill product or digital service when status is strictly `paid`.

{selected_guide}

### Safety & Architecture Rules:
- Never store the Gateway API Key in client-side code. Keep it strictly in server-side configuration.
- Implement idempotency: multiple webhooks for the same order must not grant duplicate items.
- Always handle order expiry and cancellation gracefully.

Ask me for project details (framework, where to place the pay button, what to do after payment) only if something is missing, otherwise write complete working code with file names.
"""
    return prompt.strip()

# ==============================================================================
# PUBLIC ROUTING & FRONTEND TEMPLATES (Section 3 & 4)
# ==============================================================================
@app.route("/")
def route_root():
    with get_db() as db:
        admin_row = db.execute("SELECT id FROM admin LIMIT 1").fetchone()
        if not admin_row:
            return redirect("/setup")
    if "admin_id" in session:
        return redirect("/dashboard")
    return redirect("/login")

@app.route("/setup")
def route_setup():
    with get_db() as db:
        if db.execute("SELECT id FROM admin LIMIT 1").fetchone():
            return redirect("/login")
    return send_file(os.path.join(BASE_DIR, "index.html"))

@app.route("/login")
def route_login():
    return send_file(os.path.join(BASE_DIR, "index.html"))

@app.route("/docs")
def route_docs():
    return send_file(os.path.join(BASE_DIR, "index.html"))

@app.route("/pay/<order_id>")
def route_checkout(order_id):
    return send_file(os.path.join(BASE_DIR, "index.html"))

@app.route("/dashboard")
def route_dashboard():
    if "admin_id" not in session:
        return redirect("/login")
    return send_file(os.path.join(BASE_DIR, "dashboard.html"))

@app.route("/ai-prompt.txt")
def route_ai_prompt_txt():
    stack = request.args.get("stack", "python")
    include_key = request.args.get("include_key", "0") == "1"
    include_secret = request.args.get("include_secret", "0") == "1"
    
    api_key_str = None
    if include_key and "admin_id" in session:
        # Check if there is an active key prefix or pass placeholder
        with get_db() as db:
            k = db.execute("SELECT prefix FROM api_keys WHERE revoked = 0 ORDER BY id DESC LIMIT 1").fetchone()
            if k:
                api_key_str = f"{k['prefix']}... (use full key generated)"
    
    sec_str = WEBHOOK_SECRET if include_secret and "admin_id" in session else "YOUR_WEBHOOK_SECRET"
    prompt = generate_ai_prompt_text(stack, api_key_str, sec_str)
    return Response(prompt, mimetype="text/plain; charset=utf-8")

# ==============================================================================
# CSRF TOKEN ENDPOINT & PUBLIC API / CHECKOUT ENDPOINTS (Section 5, 6, 8.1)
# ==============================================================================
@app.route("/api/csrf", methods=["GET"])
def api_get_csrf():
    return jsonify({
        "success": True,
        "token": generate_csrf_token()
    })

@app.route("/api/public/order/<order_id>")
def api_public_order(order_id):
    with get_db() as db:
        order = db.execute("SELECT * FROM orders WHERE id = ?", (order_id,)).fetchone()
        if not order:
            return jsonify({"success": False, "error": {"code": "ORDER_NOT_FOUND", "message": "Order not found"}}), 404

        # Block checkout if merchant has not configured UPI & Gmail (Bug 2)
        if order["status"] == "pending" and not is_gateway_configured():
            return jsonify({
                "success": False,
                "error": {
                    "code": "NOT_CONFIGURED",
                    "message": "Merchant is not configured or temporarily unavailable. Payments are currently paused."
                }
            }), 503
        
        # Calculate seconds remaining until expiry
        try:
            exp_dt = datetime.fromisoformat(order["expires_at"].replace("Z", "+00:00"))
            now_dt = datetime.now(timezone.utc)
            seconds_left = max(0, int((exp_dt - now_dt).total_seconds()))
        except Exception:
            seconds_left = 0

        # Auto-expire if time has passed
        if seconds_left == 0 and order["status"] == "pending":
            db.execute("UPDATE orders SET status = 'expired' WHERE id = ?", (order_id,))
            db.commit()
            order = db.execute("SELECT * FROM orders WHERE id = ?", (order_id,)).fetchone()

    pay_data = generate_upi_payment_data(order_id, order["payable_amount"])
    return jsonify({
        "success": True,
        "order": {
            "order_id": order["id"],
            "base_amount": order["base_amount"],
            "payable_amount": order["payable_amount"],
            "status": order["status"],
            "fail_reason": order["fail_reason"],
            "utr": order["utr"],
            "txn_id": order["txn_id"],
            "created_at": order["created_at"],
            "expires_at": order["expires_at"],
            "seconds_left": seconds_left,
            "redirect_url": order["redirect_url"],
            "note": order["note"],
            "merchant_name": pay_data["merchant_name"],
            "upi_id": pay_data["upi_id"],
            "upi_link": pay_data["upi_link"],
            "qr_base64": pay_data["qr_base64"]
        }
    })

@app.route("/api/public/status/<order_id>")
def api_public_status(order_id):
    with get_db() as db:
        order = db.execute("SELECT id, status, payable_amount, utr, redirect_url, expires_at, fail_reason FROM orders WHERE id = ?", (order_id,)).fetchone()
        if not order:
            return jsonify({"success": False, "error": {"code": "ORDER_NOT_FOUND", "message": "Order not found"}}), 404

        if order["status"] == "pending" and not is_gateway_configured():
            return jsonify({
                "success": False,
                "error": {
                    "code": "NOT_CONFIGURED",
                    "message": "Merchant is not configured or temporarily unavailable."
                }
            }), 503

        try:
            exp_dt = datetime.fromisoformat(order["expires_at"].replace("Z", "+00:00"))
            now_dt = datetime.now(timezone.utc)
            seconds_left = max(0, int((exp_dt - now_dt).total_seconds()))
        except Exception:
            seconds_left = 0

        # Auto-expire
        if seconds_left == 0 and order["status"] == "pending":
            db.execute("UPDATE orders SET status = 'expired' WHERE id = ?", (order_id,))
            db.commit()
            order_status = "expired"
        else:
            order_status = order["status"]

    return jsonify({
        "success": True,
        "order_id": order["id"],
        "status": order_status,
        "payable_amount": order["payable_amount"],
        "utr": order["utr"],
        "redirect_url": order["redirect_url"],
        "seconds_left": seconds_left,
        "fail_reason": order["fail_reason"]
    })

@app.route("/api/public/qr/<order_id>.png")
def api_public_qr_png(order_id):
    with get_db() as db:
        order = db.execute("SELECT payable_amount FROM orders WHERE id = ?", (order_id,)).fetchone()
        if not order:
            return "Order not found", 404
        pay_data = generate_upi_payment_data(order_id, order["payable_amount"])

    resp = make_response(pay_data["qr_bytes"])
    resp.headers.set("Content-Type", "image/png")
    resp.headers.set("Content-Disposition", f'attachment; filename="qr-{order_id}.png"')
    return resp

# ==============================================================================
# PUBLIC REST API V1 (Section 8.1)
# ==============================================================================
@app.route("/api/v1/orders", methods=["POST"])
def api_v1_create_order():
    is_authed, auth_res = verify_api_key_auth()
    if not is_authed:
        return jsonify({"success": False, "error": auth_res}), 401

    if not is_gateway_configured():
        return jsonify({
            "success": False,
            "error": {
                "code": "NOT_CONFIGURED",
                "message": "Gateway is not configured. Connect your UPI ID and Gmail first."
            }
        }), 409

    data = request.get_json(silent=True) or {}
    amount_raw = data.get("amount")
    if amount_raw is None:
        return jsonify({"success": False, "error": {"code": "INVALID_PARAM", "message": "amount is required"}}), 400

    try:
        base_amount = float(Decimal(str(amount_raw)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))
        if base_amount <= 0:
            raise ValueError()
    except Exception:
        return jsonify({"success": False, "error": {"code": "INVALID_PARAM", "message": "amount must be a positive number"}}), 400

    # Expiry in minutes (default 5 for API)
    expiry_minutes = data.get("expiry_minutes", API_DEFAULT_EXPIRY_MINUTES)
    try:
        expiry_minutes = max(1, int(expiry_minutes))
    except Exception:
        expiry_minutes = API_DEFAULT_EXPIRY_MINUTES

    custom_id = data.get("order_id")
    callback_url = data.get("callback_url", "").strip() or None
    redirect_url = data.get("redirect_url", "").strip() or None
    note = data.get("note", "").strip() or None

    try:
        payable_amount = allocate_unique_payable_amount(base_amount)
    except ValueError as e:
        return jsonify({"success": False, "error": {"code": "NO_SLOT_AVAILABLE", "message": str(e)}}), 409

    order_id = custom_id if custom_id else f"ORD-{secrets.token_hex(4).upper()}"
    now_dt = datetime.now(timezone.utc)
    created_at = now_dt.isoformat()
    expires_at = (now_dt + timedelta(minutes=expiry_minutes)).isoformat()

    with get_db() as db:
        # Check uniqueness of order_id
        if db.execute("SELECT id FROM orders WHERE id = ?", (order_id,)).fetchone():
            return jsonify({"success": False, "error": {"code": "DUPLICATE_ID", "message": "order_id already exists"}}), 409

        db.execute("""
            INSERT INTO orders (id, source, base_amount, payable_amount, status, created_at, expires_at, callback_url, redirect_url, note)
            VALUES (?, 'api', ?, ?, 'pending', ?, ?, ?, ?, ?)
        """, (order_id, base_amount, payable_amount, created_at, expires_at, callback_url, redirect_url, note))
        db.commit()

    pay_data = generate_upi_payment_data(order_id, payable_amount)
    payment_url = f"{get_base_url()}/pay/{order_id}"

    return jsonify({
        "success": True,
        "data": {
            "order_id": order_id,
            "base_amount": base_amount,
            "payable_amount": payable_amount,
            "payment_url": payment_url,
            "qr_base64": pay_data["qr_base64"],
            "upi_link": pay_data["upi_link"],
            "expires_at": expires_at,
            "status": "pending",
            "note": note
        }
    }), 201

@app.route("/api/v1/orders/<order_id>", methods=["GET"])
def api_v1_get_order(order_id):
    is_authed, auth_res = verify_api_key_auth()
    if not is_authed:
        return jsonify({"success": False, "error": auth_res}), 401

    with get_db() as db:
        order = db.execute("SELECT * FROM orders WHERE id = ?", (order_id,)).fetchone()
        if not order:
            return jsonify({"success": False, "error": {"code": "ORDER_NOT_FOUND", "message": "Order not found"}}), 404

    return jsonify({
        "success": True,
        "data": {
            "order_id": order["id"],
            "source": order["source"],
            "base_amount": order["base_amount"],
            "payable_amount": order["payable_amount"],
            "status": order["status"],
            "fail_reason": order["fail_reason"],
            "utr": order["utr"],
            "txn_id": order["txn_id"],
            "created_at": order["created_at"],
            "expires_at": order["expires_at"],
            "paid_at": order["paid_at"],
            "callback_url": order["callback_url"],
            "redirect_url": order["redirect_url"],
            "note": order["note"]
        }
    })

@app.route("/api/v1/orders/<order_id>/cancel", methods=["POST"])
def api_v1_cancel_order(order_id):
    is_authed, auth_res = verify_api_key_auth()
    if not is_authed:
        return jsonify({"success": False, "error": auth_res}), 401

    with get_db() as db:
        order = db.execute("SELECT * FROM orders WHERE id = ?", (order_id,)).fetchone()
        if not order:
            return jsonify({"success": False, "error": {"code": "ORDER_NOT_FOUND", "message": "Order not found"}}), 404

        if order["status"] != "pending":
            return jsonify({"success": False, "error": {"code": "INVALID_STATE", "message": f"Cannot cancel order with status '{order['status']}'"}}), 400

        db.execute("UPDATE orders SET status = 'cancelled' WHERE id = ?", (order_id,))
        db.commit()

        if order["callback_url"]:
            dispatch_webhook_async(
                order_id=order["id"],
                status="cancelled",
                amount=order["payable_amount"],
                base_amount=order["base_amount"],
                utr=None,
                txn_id=None,
                paid_at=None,
                note=order["note"],
                callback_url=order["callback_url"]
            )

    return jsonify({"success": True, "message": "Order cancelled successfully"})

@app.route("/api/v1/orders", methods=["GET"])
def api_v1_list_orders():
    is_authed, auth_res = verify_api_key_auth()
    if not is_authed:
        return jsonify({"success": False, "error": auth_res}), 401

    status_filter = request.args.get("status")
    page = max(1, int(request.args.get("page", 1)))
    limit = min(100, max(1, int(request.args.get("limit", 20))))
    offset = (page - 1) * limit

    with get_db() as db:
        if status_filter:
            orders = db.execute("SELECT * FROM orders WHERE status = ? ORDER BY created_at DESC LIMIT ? OFFSET ?", (status_filter, limit, offset)).fetchall()
            total = db.execute("SELECT COUNT(*) as c FROM orders WHERE status = ?", (status_filter,)).fetchone()["c"]
        else:
            orders = db.execute("SELECT * FROM orders ORDER BY created_at DESC LIMIT ? OFFSET ?", (limit, offset)).fetchall()
            total = db.execute("SELECT COUNT(*) as c FROM orders").fetchone()["c"]

    items = []
    for o in orders:
        items.append({
            "order_id": o["id"],
            "source": o["source"],
            "base_amount": o["base_amount"],
            "payable_amount": o["payable_amount"],
            "status": o["status"],
            "utr": o["utr"],
            "created_at": o["created_at"],
            "expires_at": o["expires_at"],
            "paid_at": o["paid_at"]
        })

    return jsonify({
        "success": True,
        "data": {
            "orders": items,
            "total": total,
            "page": page,
            "limit": limit
        }
    })

# ==============================================================================
# ADMIN AUTH & PROFILE ENDPOINTS (Section 3)
# ==============================================================================
@app.route("/api/setup", methods=["POST"])
def api_setup():
    if not verify_csrf():
        return csrf_error_response()

    with get_db() as db:
        if db.execute("SELECT id FROM admin LIMIT 1").fetchone():
            return jsonify({"success": False, "error": {"code": "FORBIDDEN", "message": "Setup is permanently disabled. Admin already exists."}}), 403

        data = request.get_json(silent=True) or {}
        name = data.get("name", "").strip()
        email_addr = data.get("email", "").strip().lower()
        password = data.get("password", "")
        confirm_password = data.get("confirm_password", "")

        if not name or not email_addr or not password:
            return jsonify({"success": False, "error": {"code": "MISSING_FIELDS", "message": "Name, email, and password are required"}}), 400

        if password != confirm_password:
            return jsonify({"success": False, "error": {"code": "PASSWORD_MISMATCH", "message": "Passwords do not match"}}), 400

        if len(password) < 6:
            return jsonify({"success": False, "error": {"code": "WEAK_PASSWORD", "message": "Password must be at least 6 characters"}}), 400

        pwd_hash = generate_password_hash(password)
        cur = db.cursor()
        cur.execute("INSERT INTO admin (name, email, password_hash, created_at) VALUES (?, ?, ?, ?)", (name, email_addr, pwd_hash, iso_now()))
        db.commit()
        admin_id = cur.lastrowid

    session.permanent = True
    session["admin_id"] = admin_id
    return jsonify({
        "success": True,
        "message": "Admin account created successfully",
        "csrf_token": generate_csrf_token()
    })

@app.route("/api/login", methods=["POST"])
def api_login():
    if not verify_csrf():
        return csrf_error_response()

    ip = request.remote_addr or "127.0.0.1"
    if is_ip_rate_limited(ip):
        return jsonify({"success": False, "error": {"code": "TOO_MANY_REQUESTS", "message": "Too many failed attempts. Try again in 1 minute."}}), 429

    data = request.get_json(silent=True) or {}
    email_addr = data.get("email", "").strip().lower()
    password = data.get("password", "")

    with get_db() as db:
        admin_row = db.execute("SELECT * FROM admin WHERE email = ?", (email_addr,)).fetchone()
        if not admin_row or not check_password_hash(admin_row["password_hash"], password):
            record_failed_login(ip)
            return jsonify({"success": False, "error": {"code": "INVALID_CREDENTIALS", "message": "Invalid email or password"}}), 401

    reset_failed_login(ip)
    session.permanent = True
    session["admin_id"] = admin_row["id"]
    return jsonify({
        "success": True,
        "message": "Logged in successfully",
        "csrf_token": generate_csrf_token()
    })

@app.route("/api/logout", methods=["POST"])
def api_logout():
    if not verify_csrf():
        return csrf_error_response()
    session.clear()
    return jsonify({
        "success": True,
        "csrf_token": generate_csrf_token()
    })

@app.route("/api/me")
def api_me():
    with get_db() as db:
        admin_exists = bool(db.execute("SELECT id FROM admin LIMIT 1").fetchone())
        admin_info = None
        if "admin_id" in session:
            admin_row = db.execute("SELECT id, name, email FROM admin WHERE id = ?", (session["admin_id"],)).fetchone()
            if admin_row:
                admin_info = {"id": admin_row["id"], "name": admin_row["name"], "email": admin_row["email"]}

    return jsonify({
        "admin_exists": admin_exists,
        "logged_in": admin_info is not None,
        "admin": admin_info,
        "is_configured": is_gateway_configured(),
        "csrf_token": generate_csrf_token()
    })

@app.route("/api/admin/profile", methods=["POST"])
@require_admin
def api_admin_profile():
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    data = request.get_json(silent=True) or {}
    name = data.get("name", "").strip()
    email_addr = data.get("email", "").strip().lower()
    current_password = data.get("current_password", "")
    new_password = data.get("new_password", "")

    with get_db() as db:
        admin_row = db.execute("SELECT * FROM admin WHERE id = ?", (session["admin_id"],)).fetchone()
        if not admin_row:
            return jsonify({"success": False, "error": {"code": "NOT_FOUND", "message": "Admin not found"}}), 404

        if new_password:
            if not current_password or not check_password_hash(admin_row["password_hash"], current_password):
                return jsonify({"success": False, "error": {"code": "INVALID_CURRENT_PASSWORD", "message": "Current password is required and must match"}}), 400
            if len(new_password) < 6:
                return jsonify({"success": False, "error": {"code": "WEAK_PASSWORD", "message": "New password must be at least 6 characters"}}), 400
            new_hash = generate_password_hash(new_password)
            db.execute("UPDATE admin SET name = ?, email = ?, password_hash = ? WHERE id = ?", (name or admin_row["name"], email_addr or admin_row["email"], new_hash, admin_row["id"]))
        else:
            db.execute("UPDATE admin SET name = ?, email = ? WHERE id = ?", (name or admin_row["name"], email_addr or admin_row["email"], admin_row["id"]))
        db.commit()

    return jsonify({"success": True, "message": "Profile updated successfully"})

# ==============================================================================
# DASHBOARD CONNECTION MANAGEMENT (Section 4.2)
# ==============================================================================
@app.route("/api/admin/connection", methods=["GET"])
@require_admin
def api_admin_get_connection():
    with get_db() as db:
        row = db.execute("SELECT upi_id, gmail, status, last_checked, last_error FROM connection WHERE id = 1").fetchone()
        if not row:
            return jsonify({
                "configured": False,
                "upi_id": "",
                "gmail": "",
                "status": "disconnected",
                "last_checked": None,
                "last_error": None
            })
        return jsonify({
            "configured": True,
            "upi_id": row["upi_id"],
            "gmail": row["gmail"],
            "status": row["status"],
            "last_checked": row["last_checked"],
            "last_error": row["last_error"],
            "has_password": True
        })

@app.route("/api/admin/connection", methods=["POST"])
@require_admin
def api_admin_save_connection():
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    data = request.get_json(silent=True) or {}
    upi_id = data.get("upi_id", "").strip()
    gmail = data.get("gmail", "").strip().lower()
    app_password = data.get("app_password", "").strip().replace(" ", "")

    if not upi_id or not gmail or not app_password:
        return jsonify({"success": False, "error": {"code": "MISSING_FIELDS", "message": "UPI ID, Gmail address, and App Password are required"}}), 400

    # Test IMAP connection actively before saving
    try:
        test_mail = imaplib.IMAP4_SSL("imap.gmail.com", 993, timeout=10)
        test_mail.login(gmail, app_password)
        test_mail.logout()
    except Exception as e:
        return jsonify({
            "success": False,
            "error": {
                "code": "IMAP_FAILED",
                "message": f"Connection failed: wrong email or app password ({str(e)})"
            }
        }), 400

    enc_pwd = encrypt_secret(app_password)
    with get_db() as db:
        db.execute("""
            INSERT INTO connection (id, upi_id, gmail, encrypted_app_password, status, last_checked, last_error)
            VALUES (1, ?, ?, ?, 'connected', ?, NULL)
            ON CONFLICT(id) DO UPDATE SET
                upi_id = excluded.upi_id,
                gmail = excluded.gmail,
                encrypted_app_password = excluded.encrypted_app_password,
                status = 'connected',
                last_checked = excluded.last_checked,
                last_error = NULL
        """, (upi_id, gmail, enc_pwd, iso_now()))
        db.commit()

    return jsonify({"success": True, "message": "Gmail IMAP & UPI connection verified and saved successfully"})

@app.route("/api/admin/connection/disconnect", methods=["POST"])
@require_admin
def api_admin_disconnect():
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    with get_db() as db:
        db.execute("UPDATE connection SET status = 'disconnected', last_error = 'Manually disconnected' WHERE id = 1")
        db.commit()
    return jsonify({"success": True, "message": "Disconnected"})

# ==============================================================================
# DASHBOARD STATS, ORDERS & PAYMENT LINKS (Section 4.1, 4.3, 4.4)
# ==============================================================================
@app.route("/api/admin/stats")
@require_admin
def api_admin_stats():
    with get_db() as db:
        # Aggregate order counters
        status_counts = dict(db.execute("SELECT status, COUNT(*) as c FROM orders GROUP BY status").fetchall())
        total_payments = sum(status_counts.values())

        # Today's stats (UTC)
        today_prefix = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        today_row = db.execute("""
            SELECT COUNT(*) as count, COALESCE(SUM(payable_amount), 0) as amount
            FROM orders
            WHERE status = 'paid' AND created_at LIKE ?
        """, (f"{today_prefix}%",)).fetchone()

        total_received_row = db.execute("""
            SELECT COALESCE(SUM(payable_amount), 0) as total FROM orders WHERE status = 'paid'
        """).fetchone()

        # Last 30 days time series for Chart.js
        time_series = []
        for i in range(29, -1, -1):
            day_str = (datetime.now(timezone.utc) - timedelta(days=i)).strftime("%Y-%m-%d")
            day_stat = db.execute("""
                SELECT COUNT(*) as cnt, COALESCE(SUM(payable_amount), 0) as amt
                FROM orders WHERE status = 'paid' AND created_at LIKE ?
            """, (f"{day_str}%",)).fetchone()
            time_series.append({
                "date": day_str,
                "count": day_stat["cnt"],
                "amount": round(day_stat["amt"], 2)
            })

        # Recent 10 transactions
        recent_txns = db.execute("SELECT * FROM orders ORDER BY created_at DESC LIMIT 10").fetchall()
        recent = [dict(r) for r in recent_txns]

    return jsonify({
        "success": True,
        "stats": {
            "total_payments": total_payments,
            "paid": status_counts.get("paid", 0),
            "pending": status_counts.get("pending", 0),
            "expired": status_counts.get("expired", 0),
            "cancelled": status_counts.get("cancelled", 0),
            "failed": status_counts.get("failed", 0),
            "today_count": today_row["count"],
            "today_amount": round(today_row["amount"], 2),
            "total_received": round(total_received_row["total"], 2)
        },
        "time_series": time_series,
        "recent_transactions": recent
    })

@app.route("/api/admin/orders", methods=["GET"])
@require_admin
def api_admin_get_orders():
    status = request.args.get("status")
    source = request.args.get("source")
    search = request.args.get("search", "").strip()
    page = max(1, int(request.args.get("page", 1)))
    limit = max(1, min(100, int(request.args.get("limit", 20))))
    offset = (page - 1) * limit

    query = "SELECT * FROM orders WHERE 1=1"
    params = []
    if status and status != "all":
        query += " AND status = ?"
        params.append(status)
    if source and source != "all":
        query += " AND source = ?"
        params.append(source)
    if search:
        query += " AND (id LIKE ? OR utr LIKE ? OR note LIKE ?)"
        s_param = f"%{search}%"
        params.extend([s_param, s_param, s_param])

    count_query = query.replace("SELECT *", "SELECT COUNT(*) as c")
    query += " ORDER BY created_at DESC LIMIT ? OFFSET ?"
    params_for_list = list(params) + [limit, offset]

    with get_db() as db:
        total = db.execute(count_query, params).fetchone()["c"]
        rows = db.execute(query, params_for_list).fetchall()

    return jsonify({
        "success": True,
        "orders": [dict(r) for r in rows],
        "total": total,
        "page": page,
        "limit": limit
    })

@app.route("/api/admin/orders", methods=["POST"])
@require_admin
def api_admin_create_payment_link():
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    data = request.get_json(silent=True) or {}
    try:
        base_amount = float(Decimal(str(data.get("amount"))).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))
        if base_amount <= 0:
            raise ValueError()
    except Exception:
        return jsonify({"success": False, "error": {"code": "INVALID_AMOUNT", "message": "Amount must be a positive number"}}), 400

    try:
        expiry_minutes = int(data.get("expiry_minutes", 10))
        if expiry_minutes < 1:
            expiry_minutes = 10
    except Exception:
        expiry_minutes = 10

    note = data.get("note", "").strip() or None
    redirect_url = data.get("redirect_url", "").strip() or None

    try:
        payable_amount = allocate_unique_payable_amount(base_amount)
    except ValueError as e:
        return jsonify({"success": False, "error": {"code": "NO_SLOT", "message": str(e)}}), 409

    order_id = f"PL-{secrets.token_hex(4).upper()}"
    now_dt = datetime.now(timezone.utc)
    created_at = now_dt.isoformat()
    expires_at = (now_dt + timedelta(minutes=expiry_minutes)).isoformat()

    with get_db() as db:
        db.execute("""
            INSERT INTO orders (id, source, base_amount, payable_amount, status, created_at, expires_at, redirect_url, note)
            VALUES (?, 'link', ?, ?, 'pending', ?, ?, ?, ?)
        """, (order_id, base_amount, payable_amount, created_at, expires_at, redirect_url, note))
        db.commit()

    payment_url = f"{get_base_url()}/pay/{order_id}"
    return jsonify({
        "success": True,
        "order_id": order_id,
        "payment_url": payment_url,
        "base_amount": base_amount,
        "payable_amount": payable_amount,
        "expires_at": expires_at
    })

@app.route("/api/admin/orders/<order_id>/cancel", methods=["POST"])
@require_admin
def api_admin_cancel_order(order_id):
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    with get_db() as db:
        order = db.execute("SELECT * FROM orders WHERE id = ?", (order_id,)).fetchone()
        if not order:
            return jsonify({"success": False, "error": {"code": "NOT_FOUND", "message": "Order not found"}}), 404
        if order["status"] != "pending":
            return jsonify({"success": False, "error": {"code": "INVALID_STATE", "message": f"Order is already {order['status']}"}}), 400

        db.execute("UPDATE orders SET status = 'cancelled' WHERE id = ?", (order_id,))
        db.commit()

        if order["callback_url"]:
            dispatch_webhook_async(order_id, "cancelled", order["payable_amount"], order["base_amount"], None, None, None, order["note"], order["callback_url"])

    return jsonify({"success": True, "message": "Order cancelled"})

@app.route("/api/admin/orders/<order_id>", methods=["DELETE"])
@require_admin
def api_admin_delete_order(order_id):
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    with get_db() as db:
        db.execute("DELETE FROM orders WHERE id = ?", (order_id,))
        db.commit()
    return jsonify({"success": True, "message": "Order deleted"})

@app.route("/api/admin/orders/export")
@require_admin
def api_admin_export_csv():
    with get_db() as db:
        rows = db.execute("SELECT id, source, base_amount, payable_amount, status, utr, txn_id, created_at, paid_at, note FROM orders ORDER BY created_at DESC").fetchall()

    csv_lines = ["Order ID,Source,Base Amount,Payable Amount,Status,UTR,Transaction ID,Created At,Paid At,Note"]
    for r in rows:
        note_clean = (r["note"] or "").replace('"', '""')
        csv_lines.append(f'"{r["id"]}","{r["source"]}","{r["base_amount"]}","{r["payable_amount"]}","{r["status"]}","{r["utr"] or ""}","{r["txn_id"] or ""}","{r["created_at"]}","{r["paid_at"] or ""}","{note_clean}"')

    output = "\n".join(csv_lines)
    resp = make_response(output)
    resp.headers.set("Content-Type", "text/csv")
    resp.headers.set("Content-Disposition", f'attachment; filename="orders-{datetime.now().strftime("%Y%m%d%H%M%S")}.csv"')
    return resp

@app.route("/api/admin/unmatched")
@require_admin
def api_admin_unmatched():
    with get_db() as db:
        rows = db.execute("SELECT * FROM unmatched_payments ORDER BY received_at DESC LIMIT 50").fetchall()
    return jsonify({"success": True, "unmatched": [dict(r) for r in rows]})

# ==============================================================================
# DASHBOARD API KEYS & WEBHOOK SETTINGS (Section 4.5)
# ==============================================================================
@app.route("/api/admin/keys", methods=["GET"])
@require_admin
def api_admin_list_keys():
    with get_db() as db:
        rows = db.execute("SELECT id, prefix, name, created_at, revoked FROM api_keys ORDER BY created_at DESC").fetchall()
    return jsonify({"success": True, "keys": [dict(r) for r in rows]})

@app.route("/api/admin/keys", methods=["POST"])
@require_admin
def api_admin_create_key():
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    data = request.get_json(silent=True) or {}
    key_name = data.get("name", "").strip() or "Default Key"

    # Generate key format: upi_live_<32 hex chars>
    secret_part = secrets.token_hex(20)
    plain_key = f"upi_live_{secret_part}"
    prefix = plain_key[:12] + "..."
    key_hash = hashlib.sha256(plain_key.encode()).hexdigest()

    with get_db() as db:
        cur = db.cursor()
        cur.execute("""
            INSERT INTO api_keys (key_hash, prefix, name, created_at, revoked)
            VALUES (?, ?, ?, ?, 0)
        """, (key_hash, prefix, key_name, iso_now()))
        db.commit()
        key_id = cur.lastrowid

    # The raw key is returned ONCE
    return jsonify({
        "success": True,
        "key": {
            "id": key_id,
            "name": key_name,
            "prefix": prefix,
            "plain_key": plain_key
        }
    })

@app.route("/api/admin/keys/<int:key_id>/revoke", methods=["POST"])
@require_admin
def api_admin_revoke_key(key_id):
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    with get_db() as db:
        db.execute("UPDATE api_keys SET revoked = 1 WHERE id = ?", (key_id,))
        db.commit()
    return jsonify({"success": True, "message": "API key revoked"})

@app.route("/api/admin/webhook-secret", methods=["GET"])
@require_admin
def api_admin_get_webhook_secret():
    return jsonify({"success": True, "webhook_secret": WEBHOOK_SECRET})

@app.route("/api/admin/webhook-secret/regenerate", methods=["POST"])
@require_admin
def api_admin_regenerate_webhook_secret():
    global WEBHOOK_SECRET
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    new_secret = secrets.token_hex(24)
    with get_db() as db:
        db.execute("UPDATE settings SET value = ? WHERE key = 'WEBHOOK_SECRET'", (new_secret,))
        db.commit()
    WEBHOOK_SECRET = new_secret
    return jsonify({"success": True, "webhook_secret": new_secret})

@app.route("/api/admin/webhook-logs")
@require_admin
def api_admin_webhook_logs():
    with get_db() as db:
        rows = db.execute("SELECT * FROM webhook_logs ORDER BY created_at DESC LIMIT 50").fetchall()
    return jsonify({"success": True, "logs": [dict(r) for r in rows]})

@app.route("/api/admin/ai-prompt")
@require_admin
def api_admin_ai_prompt():
    stack = request.args.get("stack", "python")
    include_key = request.args.get("include_key", "0") == "1"
    include_secret = request.args.get("include_secret", "0") == "1"

    key_str = None
    if include_key:
        with get_db() as db:
            k = db.execute("SELECT prefix FROM api_keys WHERE revoked = 0 ORDER BY id DESC LIMIT 1").fetchone()
            if k:
                key_str = f"{k['prefix']} (insert full key)"

    sec_str = WEBHOOK_SECRET if include_secret else "YOUR_WEBHOOK_SECRET"
    prompt = generate_ai_prompt_text(stack, key_str, sec_str)
    return jsonify({"success": True, "prompt": prompt})

# ==============================================================================
# TEST / SIMULATION ENDPOINT (Section 4 & 7)
# ==============================================================================
@app.route("/api/admin/simulate-email", methods=["POST"])
@require_admin
def api_admin_simulate_email():
    """
    Allows the admin to simulate an incoming bank/FamApp email notification
    to test matching, status transitions, QR animations, and webhooks live.
    """
    if not verify_csrf():
        return jsonify({"success": False, "error": {"code": "CSRF_ERROR", "message": "Invalid CSRF token"}}), 403

    data = request.get_json(silent=True) or {}
    email_text = data.get("email_text", "").strip()

    if email_text:
        parsed = parse_famapp_email("Payment Received", email_text, {})
        if not parsed:
            return jsonify({"success": False, "error": {"code": "PARSE_FAILED", "message": "Could not parse email text. Check format."}}), 400
        amount = parsed["amount"]
        utr = parsed["utr"]
        txn_id = parsed["txn_id"]
        sender_name = parsed["sender_name"]
    else:
        try:
            amount = float(Decimal(str(data.get("amount", 0))).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))
            utr = data.get("utr", f"SIM_{secrets.token_hex(6).upper()}")
            txn_id = data.get("txn_id", f"FMP_{secrets.token_hex(5).upper()}")
            sender_name = data.get("sender_name", "Test Customer")
        except Exception:
            return jsonify({"success": False, "error": {"code": "INVALID_PARAM", "message": "Invalid amount"}}), 400

    now_time = iso_now()
    with get_db() as db:
        matched_order = db.execute("""
            SELECT * FROM orders 
            WHERE status = 'pending' AND ABS(payable_amount - ?) < 0.005
            ORDER BY created_at ASC
            LIMIT 1
        """, (amount,)).fetchone()

        if matched_order:
            db.execute("""
                UPDATE orders 
                SET status = 'paid', utr = ?, txn_id = ?, paid_at = ?
                WHERE id = ?
            """, (utr, txn_id, now_time, matched_order["id"]))

            db.execute("""
                INSERT INTO processed_emails (message_id, sender, subject, received_at, matched_order_id, amount, utr)
                VALUES (?, 'simulate@famapp.in', 'Simulated Email', ?, ?, ?, ?)
            """, (f"SIM_{secrets.token_hex(12)}", now_time, matched_order["id"], amount, utr))
            db.commit()

            if matched_order["callback_url"]:
                dispatch_webhook_async(
                    order_id=matched_order["id"],
                    status="paid",
                    amount=matched_order["payable_amount"],
                    base_amount=matched_order["base_amount"],
                    utr=utr,
                    txn_id=txn_id,
                    paid_at=now_time,
                    note=matched_order["note"],
                    callback_url=matched_order["callback_url"]
                )

            return jsonify({
                "success": True,
                "matched": True,
                "order_id": matched_order["id"],
                "amount": amount,
                "utr": utr,
                "message": f"Successfully verified order {matched_order['id']} for ₹{amount:.2f}"
            })
        else:
            db.execute("""
                INSERT INTO unmatched_payments (amount, sender_name, utr, txn_id, email_date, message_id, raw_snippet, reason, received_at)
                VALUES (?, ?, ?, ?, ?, ?, 'Simulated unmatched email', 'No pending order matching amount', ?)
            """, (amount, sender_name, utr, txn_id, now_time, f"SIM_{secrets.token_hex(12)}", now_time))
            db.commit()

            return jsonify({
                "success": True,
                "matched": False,
                "amount": amount,
                "utr": utr,
                "message": f"Recorded as unmatched payment: No pending order found with payable amount ₹{amount:.2f}"
            })

# ==============================================================================
# APPLICATION INITIALIZATION ON IMPORT & RUN
# ==============================================================================
init_db()
start_background_worker_once()

if __name__ == "__main__":
    print(f"[*] Personal UPI Gateway running on http://{HOST}:{PORT}")
    app.run(host=HOST, port=PORT, debug=False)
