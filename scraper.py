import csv
import json
import logging
import os
import random
import re
import sqlite3
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from html import unescape
from urllib.parse import quote, urljoin, urlparse

import requests
from bs4 import BeautifulSoup
from email_validator import EmailNotValidError, validate_email

try:
    from playwright.sync_api import sync_playwright
except Exception:
    sync_playwright = None


INPUT_FILE = "input.csv"
OUTPUT_FILE = "output.csv"
DEBUG_LOG_FILE = "debug.log"
DB_FILE = "scraper_state_1m.db"

# =========================
# ENV KEYS
# =========================

MILLIONVERIFIER_API_KEY = "rV0Bi3dyIuwUXgfOPk9DncKpF"
INSTANTLY_API_KEY = "ZTM5ZDFlN2YtMTZlMC00N2Q3LTkwMjgtNzc1OTdkNTI4ODZlOktJRURvT0lWREhuUA=="
INSTANTLY_CAMPAIGN_ID = "3b913e3c-44a1-4e3f-93da-37eda6bfbb92"

# =========================
# REQUEST CONFIG
# =========================
HEADERS_LIST = [
    {"User-Agent": "Mozilla/5.0"},
    {"User-Agent": "Chrome/120"},
    {"User-Agent": "Safari/537.36"},
]

# =========================
# SCALE CONFIG
# =========================
FAST_MAX_THREADS = 80
FAST_REQUEST_TIMEOUT = 5
FAST_MAX_INTERNAL_LINKS = 8
FAST_MAX_DEPTH = 1
FAST_BATCH_SIZE = 4000

RETRY_MAX_THREADS = 25
RETRY_REQUEST_TIMEOUT = 8
RETRY_MAX_INTERNAL_LINKS = 18
RETRY_MAX_DEPTH = 2
RETRY_BATCH_SIZE = 1200

USE_PLAYWRIGHT_ON_RETRY = False
PLAYWRIGHT_MAX_PAGES = 4
PLAYWRIGHT_WAIT_MS = 1200
PLAYWRIGHT_TIMEOUT_MS = 8000

MAX_VALID_EMAILS_PER_WEBSITE = 3

VERIFY_ONLY_OK = True
VERIFIER_MAX_THREADS = 20
SLEEP_BETWEEN_VERIFY_CALLS = 0.02

INSTANTLY_BATCH_SIZE = 100
SLEEP_BETWEEN_INSTANTLY_BATCHES = 0.20

CHECKPOINT_EVERY_N_SITES = 5000

LIKELY_CONTACT_PATHS = [
    "/contact", "/contact-us", "/contactus", "/about", "/about-us",
    "/support", "/team", "/company", "/help", "/privacy-policy",
    "/get-in-touch", "/reach-us", "/locations", "/default.aspx",
    "/portal", "/our-team"
]

KNOWN_HARD_SITES = {
    "taxsolutionscorp.com",
    "taxsmart.io",
    "taxsidekick.com",
    "taxsolutionsgroup.net",
}

RAW_EMAIL_REGEX = re.compile(
    r"[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}",
    re.IGNORECASE
)
STRICT_TEXT_EMAIL_REGEX = re.compile(
    r"\b[a-zA-Z0-9._%+\-]{1,64}@[a-zA-Z0-9.\-]{1,255}\.[A-Za-z]{2,24}\b",
    re.IGNORECASE
)

FAKE_LOCAL_PARTS = {
    "react", "react-dom", "lodash", "core-js-bundle", "rspack",
    "intl-segmenter", "focus-within-polyfill", "main-tracking-script-javatar",
    "onepagefunnelpaymentcomponent", "bootstrap"
}

BLACKLIST_KEYWORDS = [
    "example", "sample", "dummy", "placeholder",
    "noreply", "no-reply", "donotreply",
    "your@", "email@", "name@", "john@example.com"
]

BLACKLIST_DOMAINS = [
    "example.com",
    "sentry.io",
    "sentry-next.wixpress.com",
    "sentry.wixpress.com",
]

JS_APP_HINTS = [
    "enable javascript to run this app",
    "__next",
    "webpack",
    "chunk.js",
    'id="root"',
    "id='root'",
    'id="__next"',
    "id='__next'"
]

logging.basicConfig(
    level=logging.INFO,
    format="%(message)s",
    handlers=[
        logging.FileHandler(DEBUG_LOG_FILE, mode="w", encoding="utf-8"),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

_thread_local = threading.local()
_session_local = threading.local()


# ============================================================
# DB
# ============================================================
def get_db():
    conn = getattr(_thread_local, "db_conn", None)
    if conn is None:
        conn = sqlite3.connect(DB_FILE, timeout=30, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("PRAGMA temp_store=MEMORY")
        _thread_local.db_conn = conn
    return conn


def init_db():
    conn = sqlite3.connect(DB_FILE, timeout=30, check_same_thread=False)
    cur = conn.cursor()
    cur.execute("PRAGMA journal_mode=WAL")
    cur.execute("PRAGMA synchronous=NORMAL")

    cur.execute("""
        CREATE TABLE IF NOT EXISTS websites (
            website TEXT PRIMARY KEY,
            normalized_website TEXT,
            domain TEXT,
            phase TEXT DEFAULT 'pending',
            scrape_status TEXT,
            scrape_error TEXT,
            emails_found_count INTEGER DEFAULT 0,
            retry_needed INTEGER DEFAULT 0,
            used_playwright INTEGER DEFAULT 0,
            processed_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    """)

    cur.execute("""
        CREATE TABLE IF NOT EXISTS emails (
            email TEXT PRIMARY KEY,
            mv_status TEXT,
            mv_result_raw TEXT,
            verified_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    """)

    cur.execute("""
        CREATE TABLE IF NOT EXISTS website_emails (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            website TEXT,
            email TEXT,
            instantly_status TEXT DEFAULT 'not_sent',
            instantly_message TEXT,
            instantly_created_at TEXT,
            UNIQUE(website, email)
        )
    """)

    cur.execute("CREATE INDEX IF NOT EXISTS idx_websites_phase_status ON websites(phase, scrape_status)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_websites_retry_needed ON websites(retry_needed)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_website_emails_website ON website_emails(website)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_website_emails_email ON website_emails(email)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_emails_mv_status ON emails(mv_status)")

    conn.commit()
    conn.close()


# ============================================================
# SESSION
# ============================================================
def get_session():
    session = getattr(_session_local, "session", None)
    if session is None:
        session = requests.Session()
        adapter = requests.adapters.HTTPAdapter(
            pool_connections=300,
            pool_maxsize=300,
            max_retries=0,
        )
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        _session_local.session = session
    return session


# ============================================================
# URL HELPERS
# ============================================================
def normalize_url(url: str) -> str:
    url = (url or "").strip()
    if not url:
        return ""
    if not url.startswith("http://") and not url.startswith("https://"):
        url = "https://" + url
    return url.rstrip("/")


def safe_domain(url: str) -> str:
    try:
        return urlparse(url).netloc.replace("www.", "").lower()
    except Exception:
        return ""


def canonical_website(url: str) -> str:
    url = normalize_url(url)
    parsed = urlparse(url)
    scheme = "https"
    netloc = parsed.netloc.replace("www.", "").lower()
    path = parsed.path.rstrip("/")
    return f"{scheme}://{netloc}{path}"


def swap_www_variant(url: str) -> str:
    url = normalize_url(url)
    parsed = urlparse(url)
    netloc = parsed.netloc.lower()
    if netloc.startswith("www."):
        netloc = netloc[4:]
    else:
        netloc = "www." + netloc
    return f"{parsed.scheme or 'https'}://{netloc}{parsed.path}".rstrip("/")


def build_site_variants(site: str) -> list[str]:
    site = normalize_url(site)
    variants = []
    for candidate in [site, canonical_website(site), swap_www_variant(site), swap_www_variant(canonical_website(site))]:
        c = normalize_url(candidate)
        if c and c not in variants:
            variants.append(c)
    return variants


def is_contactish_url(url: str) -> bool:
    low = (url or "").lower()
    return any(x in low for x in [
        "contact", "about", "privacy", "support", "team",
        "help", "reach", "location", "portal", "default.aspx"
    ])


def get_candidate_links(base_url: str, soup: BeautifulSoup, max_links: int) -> list[str]:
    base_domain = safe_domain(base_url)
    links = set()

    for a in soup.find_all("a", href=True):
        href = urljoin(base_url, a["href"])
        href = href.split("#")[0].strip()
        if href and safe_domain(href) == base_domain:
            links.add(href.rstrip("/"))

    for path in LIKELY_CONTACT_PATHS:
        links.add(urljoin(base_url + "/", path).rstrip("/"))

    priority = []
    normal = []
    for link in links:
        if is_contactish_url(link):
            priority.append(link)
        else:
            normal.append(link)

    ordered = []
    seen = set()
    for link in priority + normal:
        if link not in seen:
            seen.add(link)
            ordered.append(link)

    return ordered[:max_links]


# ============================================================
# EMAIL FILTERS
# ============================================================
def clean_email(email: str) -> str:
    email = unescape((email or "").strip().lower())
    email = email.replace("mailto:", "").strip()
    return email.strip(" \t\r\n\"'<>[](){}.,;:!")


def is_blacklisted(email: str) -> bool:
    e = (email or "").strip().lower()
    if any(k in e for k in BLACKLIST_KEYWORDS):
        return True
    domain = e.split("@")[-1] if "@" in e else ""
    return domain in BLACKLIST_DOMAINS or any(bad in domain for bad in BLACKLIST_DOMAINS)


def is_probably_fake_asset_email(email: str) -> bool:
    e = clean_email(email)
    if "@" not in e:
        return True

    local, domain = e.split("@", 1)

    if local in FAKE_LOCAL_PARTS:
        return True

    if domain.endswith((".js", ".css", ".map", ".png", ".jpg", ".jpeg", ".svg", ".webp")):
        return True

    if re.search(r"\b\d+\.\d+\.\d+\b", domain):
        return True

    if re.fullmatch(r"\d+(\.\d+)+", domain):
        return True

    return False


def custom_email_guard(email: str) -> bool:
    e = clean_email(email)
    if not e or "@" not in e:
        return False

    if is_blacklisted(e) or is_probably_fake_asset_email(e):
        return False

    local = e.split("@")[0]
    if len(local) > 64:
        return False

    if re.fullmatch(r"[a-f0-9]{20,}", local):
        return False

    return True


def decode_cloudflare_email(hex_string: str) -> str:
    try:
        if not hex_string or len(hex_string) < 2:
            return ""
        r = int(hex_string[:2], 16)
        out = ""
        for i in range(2, len(hex_string), 2):
            out += chr(int(hex_string[i:i + 2], 16) ^ r)
        return out
    except Exception:
        return ""


def is_probably_js_app(html: str) -> bool:
    low = (html or "").lower()
    return any(hint in low for hint in JS_APP_HINTS)


def score_email(email: str, site_domain: str) -> int:
    """
    Higher score = better email.
    Prioritizes domain-match and business-looking emails.
    """
    e = clean_email(email)
    if "@" not in e:
        return -999

    local, domain = e.split("@", 1)
    score = 0

    if domain == site_domain:
        score += 100
    elif domain.endswith("." + site_domain):
        score += 80

    preferred_locals = {
        "info", "contact", "hello", "support", "sales",
        "admin", "team", "office", "accounts", "billing"
    }
    if local in preferred_locals:
        score += 30

    generic_penalty = {"test", "demo", "sample", "temp"}
    if local in generic_penalty:
        score -= 20

    if any(ch.isdigit() for ch in local):
        score -= 5

    if len(local) <= 3:
        score -= 3

    return score


# ============================================================
# INPUT
# ============================================================
def stream_input_websites(file_path: str):
    with open(file_path, "r", encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        if "website" not in (reader.fieldnames or []):
            raise ValueError(f"'website' column not found in {file_path}. Found: {reader.fieldnames}")

        for row in reader:
            website = (row.get("website") or "").strip()
            if website:
                yield website


def seed_websites_from_input():
    conn = get_db()
    cur = conn.cursor()
    inserted = 0
    seen = 0

    for website in stream_input_websites(INPUT_FILE):
        seen += 1
        normalized = canonical_website(website)
        domain = safe_domain(normalized)

        cur.execute("""
            INSERT OR IGNORE INTO websites (
                website, normalized_website, domain, phase, scrape_status,
                scrape_error, emails_found_count, retry_needed, used_playwright
            ) VALUES (?, ?, ?, 'pending', NULL, '', 0, 0, 0)
        """, (website, normalized, domain))

        if cur.rowcount:
            inserted += 1

        if seen % 10000 == 0:
            conn.commit()
            logger.info(f"Seeded {seen} rows from input")

    conn.commit()
    logger.info(f"Input seed complete | Seen: {seen} | Newly inserted: {inserted}")


def iter_pending_websites_for_phase(phase_name: str):
    conn = get_db()
    cur = conn.cursor()

    if phase_name == "fast":
        cur.execute("""
            SELECT website, normalized_website
            FROM websites
            WHERE (phase = 'pending' OR phase IS NULL)
            ORDER BY website
        """)
    elif phase_name == "retry":
        cur.execute("""
            SELECT website, normalized_website
            FROM websites
            WHERE retry_needed = 1
            ORDER BY website
        """)
    else:
        raise ValueError("Unsupported phase")

    for row in cur.fetchall():
        yield row["website"], row["normalized_website"]


# ============================================================
# HTML FETCH
# ============================================================
def get_html(url: str, timeout: int) -> tuple[str, str]:
    try:
        response = get_session().get(
            url,
            headers=random.choice(HEADERS_LIST),
            timeout=timeout,
            allow_redirects=True,
        )
        if response.status_code != 200:
            return "", ""
        return response.text or "", response.url or url
    except Exception:
        return "", ""


# ============================================================
# EMAIL EXTRACTION
# ============================================================
def extract_from_text_blob(text: str) -> set[str]:
    if not text:
        return set()

    candidates = set()
    temp = unescape(text)
    temp = temp.replace("[at]", "@").replace("(at)", "@").replace(" at ", "@")
    temp = temp.replace("[dot]", ".").replace("(dot)", ".").replace(" dot ", ".")

    for e in RAW_EMAIL_REGEX.findall(temp):
        candidates.add(clean_email(e))

    for e in STRICT_TEXT_EMAIL_REGEX.findall(temp):
        candidates.add(clean_email(e))

    return {e for e in candidates if custom_email_guard(e)}


def extract_emails_from_html(html: str) -> set[str]:
    emails = set()
    if not html:
        return emails

    soup = BeautifulSoup(html, "html.parser")

    emails.update(extract_from_text_blob(html))
    emails.update(extract_from_text_blob(soup.get_text(" ", strip=True)))

    for a in soup.select("a[href^='mailto:']"):
        emails.add(clean_email(a.get("href", "")))

    for tag in soup.select("a.__cf_email__, [data-cfemail]"):
        decoded = decode_cloudflare_email(tag.get("data-cfemail"))
        if decoded:
            emails.add(clean_email(decoded))

    for script in soup.find_all("script"):
        text = script.get_text(" ", strip=False) or ""
        if text:
            emails.update(extract_from_text_blob(text))

    for tag in soup.find_all(attrs=True):
        for _, value in tag.attrs.items():
            if isinstance(value, str):
                emails.update(extract_from_text_blob(value))
            elif isinstance(value, list):
                for item in value:
                    if isinstance(item, str):
                        emails.update(extract_from_text_blob(item))

    return {clean_email(e) for e in emails if custom_email_guard(e)}


def pick_best_3_emails(found_emails: set[str], site_domain: str) -> list[str]:
    ranked = sorted(
        found_emails,
        key=lambda x: (-score_email(x, site_domain), x)
    )
    return ranked[:MAX_VALID_EMAILS_PER_WEBSITE]


# ============================================================
# CRAWL
# ============================================================
def crawl_site(site: str, depth_limit: int, link_limit: int, request_timeout: int):
    variants = build_site_variants(site)
    visited = set()
    found_emails = set()
    js_hint_seen = False

    def crawl(url: str, depth: int):
        nonlocal js_hint_seen

        if not url or url in visited or depth > depth_limit:
            return

        visited.add(url)

        html, final_url = get_html(url, request_timeout)
        if not html:
            return

        active_url = final_url or url

        if is_probably_js_app(html):
            js_hint_seen = True

        found_emails.update(extract_emails_from_html(html))
        if len(found_emails) >= 12:
            # collect a few more, then rank later
            return

        try:
            soup = BeautifulSoup(html, "html.parser")
            for link in get_candidate_links(active_url, soup, link_limit):
                if depth == 0 or is_contactish_url(link):
                    crawl(link, depth + 1)

                if len(found_emails) >= 12:
                    return
        except Exception:
            pass

    for variant in variants:
        crawl(variant, 0)
        if found_emails:
            break

    return found_emails, js_hint_seen


def scrape_with_playwright_retry_only(site: str) -> set[str]:
    if not USE_PLAYWRIGHT_ON_RETRY or sync_playwright is None:
        return set()

    emails = set()
    variants = build_site_variants(site)

    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            context = browser.new_context(ignore_https_errors=True)

            candidate_urls = []
            for variant in variants:
                candidate_urls.append(variant)
                for path in LIKELY_CONTACT_PATHS:
                    candidate_urls.append(urljoin(variant + "/", path).rstrip("/"))

            seen = set()
            ordered = []
            for url in candidate_urls:
                if url and url not in seen:
                    seen.add(url)
                    ordered.append(url)

            for target_url in ordered[:PLAYWRIGHT_MAX_PAGES]:
                page = context.new_page()
                try:
                    page.goto(target_url, timeout=PLAYWRIGHT_TIMEOUT_MS, wait_until="domcontentloaded")
                    try:
                        page.wait_for_load_state("networkidle", timeout=2500)
                    except Exception:
                        pass

                    page.wait_for_timeout(PLAYWRIGHT_WAIT_MS)
                    html = page.content()
                    emails.update(extract_emails_from_html(html))

                    if len(emails) >= 12:
                        break
                except Exception:
                    pass
                finally:
                    page.close()

            browser.close()
    except Exception:
        pass

    return {e for e in emails if custom_email_guard(e)}


# ============================================================
# SCRAPE WORKERS
# ============================================================
def scrape_site_fast(site: str) -> dict:
    domain = safe_domain(site)

    found_emails, js_hint_seen = crawl_site(
        site,
        depth_limit=FAST_MAX_DEPTH,
        link_limit=FAST_MAX_INTERNAL_LINKS,
        request_timeout=FAST_REQUEST_TIMEOUT,
    )

    valid_emails = set()
    format_invalid = set()

    for email in found_emails:
        try:
            validated = validate_email(email, check_deliverability=False).email
            if custom_email_guard(validated):
                valid_emails.add(validated)
        except EmailNotValidError:
            format_invalid.add(email)

    best_3 = pick_best_3_emails(valid_emails, domain)
    retry_needed = 1 if (not best_3 and (js_hint_seen or domain in KNOWN_HARD_SITES)) else 0

    return {
        "website": site,
        "normalized_website": canonical_website(site),
        "domain": domain,
        "valid_emails": best_3,
        "format_invalid_emails": sorted(format_invalid),
        "emails_found_count": len(best_3),
        "retry_needed": retry_needed,
        "used_playwright": 0,
        "phase": "fast_done",
    }


def scrape_site_retry(site: str) -> dict:
    domain = safe_domain(site)

    found_emails, js_hint_seen = crawl_site(
        site,
        depth_limit=RETRY_MAX_DEPTH,
        link_limit=RETRY_MAX_INTERNAL_LINKS,
        request_timeout=RETRY_REQUEST_TIMEOUT,
    )

    used_playwright = 0
    if not found_emails and (js_hint_seen or domain in KNOWN_HARD_SITES):
        pw_emails = scrape_with_playwright_retry_only(site)
        if pw_emails:
            used_playwright = 1
        found_emails.update(pw_emails)

    valid_emails = set()
    format_invalid = set()

    for email in found_emails:
        try:
            validated = validate_email(email, check_deliverability=False).email
            if custom_email_guard(validated):
                valid_emails.add(validated)
        except EmailNotValidError:
            format_invalid.add(email)

    best_3 = pick_best_3_emails(valid_emails, domain)

    return {
        "website": site,
        "normalized_website": canonical_website(site),
        "domain": domain,
        "valid_emails": best_3,
        "format_invalid_emails": sorted(format_invalid),
        "emails_found_count": len(best_3),
        "retry_needed": 0,
        "used_playwright": used_playwright,
        "phase": "retry_done",
    }


# ============================================================
# DB UPDATES
# ============================================================
def upsert_site_result(site_result: dict, scrape_status="done", scrape_error=""):
    conn = get_db()
    cur = conn.cursor()

    website = site_result["website"]
    normalized = site_result["normalized_website"]
    domain = site_result["domain"]
    phase = site_result.get("phase", "done")
    emails_found_count = int(site_result.get("emails_found_count", 0))
    retry_needed = int(site_result.get("retry_needed", 0))
    used_playwright = int(site_result.get("used_playwright", 0))

    cur.execute("""
        INSERT INTO websites (
            website, normalized_website, domain, phase, scrape_status, scrape_error,
            emails_found_count, retry_needed, used_playwright
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(website) DO UPDATE SET
            normalized_website = excluded.normalized_website,
            domain = excluded.domain,
            phase = excluded.phase,
            scrape_status = excluded.scrape_status,
            scrape_error = excluded.scrape_error,
            emails_found_count = excluded.emails_found_count,
            retry_needed = excluded.retry_needed,
            used_playwright = CASE WHEN excluded.used_playwright = 1 THEN 1 ELSE websites.used_playwright END,
            processed_at = CURRENT_TIMESTAMP
    """, (
        website, normalized, domain, phase, scrape_status,
        scrape_error, emails_found_count, retry_needed, used_playwright
    ))

    # ensure max 3 emails stored per website
    emails_to_store = site_result.get("valid_emails", [])[:MAX_VALID_EMAILS_PER_WEBSITE]
    for email in emails_to_store:
        cur.execute("""
            INSERT OR IGNORE INTO website_emails (website, email, instantly_status)
            VALUES (?, ?, 'not_sent')
        """, (website, email))

    conn.commit()


def mark_site_failed(website: str, normalized: str, phase: str, error: str, retry_needed: int = 1):
    conn = get_db()
    cur = conn.cursor()

    cur.execute("""
        INSERT INTO websites (
            website, normalized_website, domain, phase, scrape_status, scrape_error, retry_needed
        ) VALUES (?, ?, ?, ?, 'failed', ?, ?)
        ON CONFLICT(website) DO UPDATE SET
            phase = excluded.phase,
            scrape_status = 'failed',
            scrape_error = excluded.scrape_error,
            retry_needed = excluded.retry_needed,
            processed_at = CURRENT_TIMESTAMP
    """, (website, normalized, safe_domain(normalized), phase, error, retry_needed))

    conn.commit()


# ============================================================
# VERIFY CACHE
# ============================================================
def get_mv_status(email: str):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT mv_status, mv_result_raw FROM emails WHERE email = ?", (email,))
    return cur.fetchone()


def save_mv_status(email: str, mv_status: str, mv_result_raw: str):
    conn = get_db()
    cur = conn.cursor()

    cur.execute("""
        INSERT INTO emails (email, mv_status, mv_result_raw)
        VALUES (?, ?, ?)
        ON CONFLICT(email) DO UPDATE SET
            mv_status = excluded.mv_status,
            mv_result_raw = excluded.mv_result_raw,
            verified_at = CURRENT_TIMESTAMP
    """, (email, mv_status, mv_result_raw))

    conn.commit()


def get_unique_unverified_emails(limit: int | None = None):
    conn = get_db()
    cur = conn.cursor()

    query = """
        SELECT DISTINCT we.email
        FROM website_emails we
        LEFT JOIN emails e ON e.email = we.email
        WHERE e.email IS NULL
        ORDER BY we.email
    """
    if limit is not None:
        query += f" LIMIT {int(limit)}"

    cur.execute(query)
    return [row["email"] for row in cur.fetchall()]


def verify_with_millionverifier(email: str):
    cached = get_mv_status(email)
    if cached:
        return cached["mv_status"] == "ok", cached["mv_status"]

    try:
        if not MILLIONVERIFIER_API_KEY:
            save_mv_status(email, "skipped_no_api_key", json.dumps({"message": "missing api key"}))
            return False, "skipped_no_api_key"

        url = f"https://api.millionverifier.com/api/v3/?api={MILLIONVERIFIER_API_KEY}&email={quote(email)}&timeout=10"
        response = get_session().get(url, timeout=15)
        data = response.json()

        result = str(data.get("result", "")).lower().strip()
        accepted = (result == "ok") if VERIFY_ONLY_OK else result in {"ok", "catch_all"}
        final_status = "ok" if accepted else (result or "error")

        save_mv_status(email, final_status, json.dumps(data, ensure_ascii=False))

        if SLEEP_BETWEEN_VERIFY_CALLS:
            time.sleep(SLEEP_BETWEEN_VERIFY_CALLS)

        return accepted, final_status

    except Exception as e:
        save_mv_status(email, "error", json.dumps({"error": str(e)}, ensure_ascii=False))
        return False, "error"


def run_verify_phase(limit: int | None = None):
    emails = get_unique_unverified_emails(limit=limit)
    total = len(emails)

    logger.info(f"VERIFY phase start | unique emails to verify: {total}")
    if not emails:
        return

    done = 0
    with ThreadPoolExecutor(max_workers=VERIFIER_MAX_THREADS) as executor:
        future_map = {executor.submit(verify_with_millionverifier, email): email for email in emails}

        for future in as_completed(future_map):
            try:
                future.result()
            except Exception:
                pass

            done += 1
            if done % 1000 == 0:
                logger.info(f"VERIFY progress: {done}/{total}")


# ============================================================
# INSTANTLY
# ============================================================
def get_pending_verified_rows_for_instantly(limit=10000):
    conn = get_db()
    cur = conn.cursor()

    cur.execute("""
        SELECT we.website, we.email, e.mv_status
        FROM website_emails we
        JOIN emails e ON e.email = we.email
        WHERE e.mv_status = 'ok'
          AND (we.instantly_status IS NULL OR we.instantly_status = 'not_sent')
        LIMIT ?
    """, (limit,))

    return cur.fetchall()


def update_instantly_status(website: str, email: str, status: str, message: str = ""):
    conn = get_db()
    cur = conn.cursor()

    cur.execute("""
        UPDATE website_emails
        SET instantly_status = ?, instantly_message = ?, instantly_created_at = CURRENT_TIMESTAMP
        WHERE website = ? AND email = ?
    """, (status, message, website, email))

    conn.commit()


def send_batch_to_instantly(leads_batch: list[dict]) -> dict:
    if not INSTANTLY_API_KEY or not INSTANTLY_CAMPAIGN_ID:
        return {"status_code": 0, "data": {"error": "Missing Instantly credentials"}, "created_emails": set()}

    url = "https://api.instantly.ai/api/v2/leads/add"
    headers = {
        "Authorization": f"Bearer {INSTANTLY_API_KEY}",
        "Content-Type": "application/json"
    }
    payload = {
        "campaign_id": INSTANTLY_CAMPAIGN_ID,
        "skip_if_in_workspace": True,
        "verify_leads_on_import": False,
        "leads": leads_batch,
    }

    try:
        response = get_session().post(url, json=payload, headers=headers, timeout=40)

        try:
            data = response.json()
        except Exception:
            data = {"raw_text": response.text}

        created_emails = set()
        if response.status_code in (200, 201):
            for item in data.get("created_leads", []):
                email = (item.get("email") or "").strip().lower()
                if email:
                    created_emails.add(email)

        return {
            "status_code": response.status_code,
            "data": data,
            "created_emails": created_emails
        }
    except Exception as e:
        return {
            "status_code": 0,
            "data": {"error": str(e)},
            "created_emails": set()
        }


def push_verified_to_instantly(limit: int | None = None):
    rows = get_pending_verified_rows_for_instantly(limit=limit or 10000)
    if not rows:
        logger.info("INSTANTLY phase: no pending verified rows")
        return

    logger.info(f"INSTANTLY phase start | rows: {len(rows)}")

    lead_items = []
    for row in rows:
        website = row["website"]
        email = row["email"]
        domain = safe_domain(website)

        lead_items.append({
            "website": website,
            "email": email,
            "source_domain": domain,
            "custom_variables": {
                "website_source": website,
                "source_domain": domain
            }
        })

    for i in range(0, len(lead_items), INSTANTLY_BATCH_SIZE):
        batch = lead_items[i:i + INSTANTLY_BATCH_SIZE]
        api_batch = [{"email": x["email"], "custom_variables": x["custom_variables"]} for x in batch]

        resp = send_batch_to_instantly(api_batch)
        status_code = resp["status_code"]
        data = resp["data"]
        created = resp["created_emails"]

        if status_code not in (200, 201):
            msg = data.get("message") or data.get("error") or json.dumps(data, ensure_ascii=False)
            for item in batch:
                update_instantly_status(item["website"], item["email"], "failed", msg)

            if SLEEP_BETWEEN_INSTANTLY_BATCHES:
                time.sleep(SLEEP_BETWEEN_INSTANTLY_BATCHES)
            continue

        skipped_count = int(data.get("skipped_count", 0) or 0)
        duplicated_count = int(data.get("duplicated_leads", 0) or 0)

        for item in batch:
            email = item["email"].strip().lower()
            if email in created:
                update_instantly_status(item["website"], email, "added", "created_in_campaign")
            elif skipped_count > 0 or duplicated_count > 0:
                update_instantly_status(item["website"], email, "skipped_existing", "existing_or_skipped")
            else:
                update_instantly_status(item["website"], email, "failed", "batch_success_but_not_in_created")

        if SLEEP_BETWEEN_INSTANTLY_BATCHES:
            time.sleep(SLEEP_BETWEEN_INSTANTLY_BATCHES)


# ============================================================
# SCRAPE PHASE RUNNER
# ============================================================
def run_scrape_phase(phase_name: str):
    if phase_name == "fast":
        worker = scrape_site_fast
        max_threads = FAST_MAX_THREADS
        batch_size = FAST_BATCH_SIZE
    elif phase_name == "retry":
        worker = scrape_site_retry
        max_threads = RETRY_MAX_THREADS
        batch_size = RETRY_BATCH_SIZE
    else:
        raise ValueError("Unsupported phase")

    buffer_sites = []
    total_seen = 0

    for website, normalized in iter_pending_websites_for_phase(phase_name):
        buffer_sites.append((website, normalized))
        total_seen += 1

        if len(buffer_sites) >= batch_size:
            run_scrape_batch(buffer_sites, worker, phase_name, max_threads)
            buffer_sites = []

        if total_seen % CHECKPOINT_EVERY_N_SITES == 0:
            logger.info(f"{phase_name.upper()} checkpoint: processed {total_seen} websites")

    if buffer_sites:
        run_scrape_batch(buffer_sites, worker, phase_name, max_threads)


def run_scrape_batch(batch_sites, worker, phase_name: str, max_threads: int):
    with ThreadPoolExecutor(max_workers=max_threads) as executor:
        future_map = {
            executor.submit(worker, website): (website, normalized)
            for website, normalized in batch_sites
        }

        for future in as_completed(future_map):
            website, normalized = future_map[future]
            try:
                result = future.result()
                upsert_site_result(result, scrape_status="done", scrape_error="")
                logger.info(f"[{phase_name}] {website} | Found: {len(result.get('valid_emails', []))} | Retry: {result.get('retry_needed', 0)}")
            except Exception as e:
                retry_flag = 1 if phase_name == "fast" else 0
                mark_site_failed(website, normalized, phase_name, str(e), retry_needed=retry_flag)
                logger.info(f"[{phase_name}] {website} | Failed: {str(e)}")


# ============================================================
# FINAL EXPORT - ONLY ONE FILE
# ============================================================
def export_output_csv():
    conn = get_db()
    cur = conn.cursor()

    cur.execute("""
        SELECT we.website,
               we.email,
               COALESCE(e.mv_status, '') AS mv_status,
               COALESCE(we.instantly_status, 'not_sent') AS instantly_status,
               COALESCE(we.instantly_message, '') AS instantly_message
        FROM website_emails we
        LEFT JOIN emails e ON e.email = we.email
        ORDER BY we.website, we.email
    """)
    rows = cur.fetchall()

    with open(OUTPUT_FILE, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow([
            "website",
            "email",
            "mv_status",
            "instantly_status",
            "instantly_message",
            "instantly_website_source"
        ])

        current_website = None
        current_count = 0

        for row in rows:
            website = row["website"]

            if website != current_website:
                current_website = website
                current_count = 0

            if current_count >= MAX_VALID_EMAILS_PER_WEBSITE:
                continue

            writer.writerow([
                row["website"],
                row["email"],
                row["mv_status"],
                row["instantly_status"],
                row["instantly_message"],
                row["website"]
            ])
            current_count += 1

    logger.info(f"Only one output file generated: {OUTPUT_FILE}")


# ============================================================
# SUMMARY
# ============================================================
def print_summary():
    conn = get_db()
    cur = conn.cursor()

    cur.execute("SELECT COUNT(*) AS total FROM websites")
    total_sites = int(cur.fetchone()["total"] or 0)

    cur.execute("SELECT COUNT(*) AS total FROM website_emails")
    total_emails = int(cur.fetchone()["total"] or 0)

    cur.execute("SELECT COUNT(*) AS total FROM emails WHERE mv_status = 'ok'")
    verified_ok = int(cur.fetchone()["total"] or 0)

    cur.execute("SELECT COUNT(*) AS total FROM website_emails WHERE instantly_status = 'added'")
    instantly_added = int(cur.fetchone()["total"] or 0)

    logger.info("=" * 80)
    logger.info("PIPELINE SUMMARY")
    logger.info("=" * 80)
    logger.info(f"Websites total: {total_sites}")
    logger.info(f"Emails stored total: {total_emails}")
    logger.info(f"Verified ok total: {verified_ok}")
    logger.info(f"Instantly added total: {instantly_added}")
    logger.info(f"Final file: {OUTPUT_FILE}")
    logger.info("=" * 80)


# ============================================================
# MAIN
# ============================================================
def main():
    init_db()

    logger.info("1M SCALE SCRAPER STARTED")
    logger.info("Step 0: Seeding input")
    seed_websites_from_input()

    logger.info("Step 1: FAST scrape phase")
    run_scrape_phase("fast")

    logger.info("Step 2: RETRY scrape phase")
    run_scrape_phase("retry")

    logger.info("Step 3: VERIFY unique emails")
    run_verify_phase()

    logger.info("Step 4: INSTANTLY push verified emails")
    push_verified_to_instantly()

    logger.info("Step 5: EXPORT only output.csv")
    export_output_csv()

    print_summary()


if __name__ == "__main__":
    main()