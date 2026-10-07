# app_netno.py — AI Netnography Tool
# Spiegel Institut · Community-Analyse aus HTML-Exporten
#
# Pipeline:
#   HTML-Dateien (manuell gesammelt)
#     -> Extraktion (1 Kommentar = 1 Datensatz)   [Preflight, Fail Loud]
#     -> Bereinigung (Dedupe, Quote-Stripping, Sprache)
#     -> Kodierung (induktiv / deduktiv / hybrid, Batch-LLM, ID-basiert)
#     -> Aggregation (N Kommentare / N Autoren / N Threads / N Communities)
#     -> Export (CSV, Excel, HTML-Dashboard, Methodensteckbrief)
#
# Architekturprinzipien (aus dem Transkript-Mapper übernommen):
#   * Fail Loud: kein stiller Fehlschlag, PARSE_ERROR wird zum Datensatz.
#   * Verbatim-Treue: das Modell gibt IDs zurück, das Tool rekonstruiert Zitate.
#   * Prompt-Caching auf SQLite-Ebene, ungültige Antworten werden NICHT gecacht.

import streamlit as st
import streamlit.components.v1 as components
import pandas as pd
import requests
import re
import os
import io
import json
import time
import math
import html as html_module
import hashlib
import sqlite3
import random
import unicodedata
import copy as _copy
import email
import email.policy
import quopri
import base64 as _b64
from datetime import datetime, timezone
from collections import Counter, defaultdict
from typing import List, Dict, Optional, Tuple, Any, Callable
from concurrent.futures import ThreadPoolExecutor, as_completed

# ── Optionale Abhängigkeiten ────────────────────────────────────────────────
try:
    from bs4 import BeautifulSoup, NavigableString, Tag
    HAS_BS4 = True
except ImportError:
    HAS_BS4 = False

try:
    import lxml  # noqa: F401
    BS_PARSER = "lxml"
except ImportError:
    BS_PARSER = "html.parser"

try:
    from charset_normalizer import from_bytes as cn_from_bytes
    HAS_CHARSET = True
except ImportError:
    HAS_CHARSET = False

try:
    import pyodbc
    HAS_PYODBC = True
except Exception:
    HAS_PYODBC = False


# ========================
# Grundkonfiguration
# ========================
APP_NAME                = "AI Netnography Tool"
OUTPUT_LANGUAGE         = "Deutsch"
DEFAULT_DEPLOYMENT_NAME = "gpt-6-luna"
DEFAULT_API_VERSION     = "2025-04-01-preview"   # Azure: reasoning_effort / max_completion_tokens
# GPT-6 ist ein Reasoning-Modell. "none" = kein Reasoning, dann ist temperature
# erlaubt (temperature=0 hält die Kodierung reproduzierbar). Bei low/medium/high/
# xhigh/max wird temperature NICHT gesendet und das Token-Budget aufgestockt.
DEFAULT_REASONING_EFFORT = "none"
REASONING_EFFORTS        = ["none", "low", "medium", "high", "xhigh", "max"]
REASONING_TOKEN_HEADROOM = 8000    # Zusatzbudget für Reasoning-Tokens (zählen in max_completion_tokens)
# Preise in USD pro 1M Tokens (input, output); unbekannte Modelle -> alte Staffel
MODEL_PRICES_USD = {
    "gpt-6-luna":   (0.10, 0.50),
    "gpt-4.1-mini": (0.40, 1.60),
}
USD_TO_EUR               = 0.86    # grobe Umrechnung für die Kostenanzeige

MIN_COMMENT_CHARS       = 15      # kürzere Fragmente = Navigationsreste
MAX_COMMENT_CHARS       = 12000   # längere Blöcke = vermutlich ganze Seite
CODEBOOK_SAMPLE_SIZE    = 90      # Kommentare pro Induktionsrunde
CODEBOOK_ROUNDS         = 3       # Runden für Sättigungsprüfung
ASSIGN_BATCH_SIZE       = 12      # Kommentare pro Kodier-Call
MAX_WORKERS_DEFAULT     = 6
CACHE_DB                = "netno_cache.sqlite"

st.set_page_config(page_title=APP_NAME, layout="wide")


# ========================
# Basis-Hilfsfunktionen
# ========================
def safe_str(x) -> str:
    try:
        if x is None:
            return ""
        if isinstance(x, float) and math.isnan(x):
            return ""
        return str(x).strip()
    except Exception:
        return ""


def norm_ws(t: str) -> str:
    """Whitespace normalisieren, Zero-Width-Zeichen entfernen."""
    t = safe_str(t)
    t = t.replace("\u200b", "").replace("\ufeff", "").replace("\xa0", " ")
    t = unicodedata.normalize("NFKC", t)
    t = re.sub(r"[ \t]+", " ", t)
    t = re.sub(r"\n{3,}", "\n\n", t)
    return t.strip()


def norm_key(t: str) -> str:
    """Aggressive Normalisierung für Dedupe-Vergleiche."""
    t = norm_ws(t).lower()
    t = re.sub(r"[^\w\s]", "", t, flags=re.UNICODE)
    t = re.sub(r"\s+", " ", t)
    return t.strip()


def sha1(s: str) -> str:
    return hashlib.sha1(safe_str(s).encode("utf-8", "replace")).hexdigest()


def safe_sheet_name(name: str) -> str:
    if not name:
        return "Sheet"
    name = re.sub(r"[:\\/?*\[\]]", " ", str(name)).strip()
    name = re.sub(r"\s+", " ", name)
    return (name or "Sheet")[:31]


def unique_sheet_name(name: str, used: set) -> str:
    """Excel erlaubt keine doppelten Sheetnamen — deterministisch entdoppeln."""
    base = safe_sheet_name(name)
    cand = base
    i = 2
    while cand.lower() in used:
        suffix = f"_{i}"
        cand = base[: 31 - len(suffix)] + suffix
        i += 1
    used.add(cand.lower())
    return cand


def find_secret(keys: List[str]):
    for k in keys:
        v = os.getenv(k)
        if v:
            return v
        try:
            if k in st.secrets:
                return st.secrets[k]
        except Exception:
            pass
    return None


def decode_bytes(raw: bytes) -> Tuple[str, str, List[str]]:
    """Bytes -> Text. Gibt (text, encoding, warnungen) zurück. Fail Loud bei Mojibake."""
    warn: List[str] = []
    if raw is None:
        return "", "none", ["Datei leer"]

    # 1) Meta-Charset aus dem HTML-Kopf lesen (überschreibt Heuristik)
    head = raw[:4096].decode("ascii", "ignore").lower()
    m = re.search(r'charset=["\']?([a-z0-9\-_]+)', head)
    meta_enc = m.group(1) if m else None

    candidates = []
    if meta_enc:
        candidates.append(meta_enc)
    if HAS_CHARSET:
        try:
            best = cn_from_bytes(raw).best()
            if best and best.encoding:
                candidates.append(best.encoding)
        except Exception:
            pass
    candidates += ["utf-8", "cp1252", "latin-1"]

    for enc in candidates:
        try:
            txt = raw.decode(enc)
        except Exception:
            continue
        # Mojibake-Score: typische Fehl-Dekodierungen
        bad = len(re.findall(r"Ã[¤¶¼\x84\x96\x9c]|â€|Â\s", txt))
        if bad > max(3, len(txt) / 20000):
            warn.append(f"Mojibake-Verdacht bei Encoding '{enc}' ({bad} Treffer)")
            continue
        return txt, enc, warn

    return raw.decode("utf-8", "replace"), "utf-8/replace", warn + ["Encoding unsicher — Ersatzzeichen eingesetzt"]


# ========================
# MHTML / MHT-Archive
# ========================
# Browser speichern "Webseite, komplett" als MHTML: ein MIME-Multipart-Archiv,
# in dem das HTML quoted-printable oder base64 codiert steckt. Wer diese Datei
# direkt an einen HTML-Parser gibt, bekommt Zeichensalat ("=3D", "=\r\n") und
# damit null Kommentare. Das ist der haeufigste Grund fuer eine leere Extraktion.

def is_mhtml(raw: bytes) -> bool:
    if not raw:
        return False
    head = raw[:4000].lower()
    return (b"mime-version:" in head and b"content-type:" in head
            and (b"multipart/related" in head or b"snapshot-content-location:" in head
                 or b"content-transfer-encoding:" in head))


def unpack_mhtml(raw: bytes) -> Tuple[str, dict, List[str]]:
    """MHTML -> (haupt_html, meta, warnungen).

    Das Archiv enthaelt oft dutzende HTML-Fragmente (Werbe-iframes, Consent-
    Container). Genommen wird die Ressource, deren Content-Location mit der
    Snapshot-Content-Location uebereinstimmt; nur wenn die fehlt, wird nach
    Groesse entschieden.
    """
    warn: List[str] = []
    meta: dict = {}
    try:
        msg = email.message_from_bytes(raw, policy=email.policy.default)
    except Exception as e:
        return "", meta, [f"MHTML nicht lesbar: {e}"]

    loc = safe_str(msg.get("Snapshot-Content-Location"))
    subj = safe_str(msg.get("Subject"))
    if loc:
        meta["url"] = loc
    if subj:
        meta["thread_titel"] = subj[:250]
    dt = safe_str(msg.get("Date"))
    if dt:
        meta["abrufdatum_roh"] = dt

    exact, largest, n_html = None, None, 0
    for part in msg.walk():
        if part.get_content_type() != "text/html":
            continue
        n_html += 1
        try:
            payload = part.get_payload(decode=True) or b""
        except Exception:
            continue
        if not payload:
            continue
        charset = part.get_content_charset() or ""
        for enc in ([charset] if charset else []) + ["utf-8", "cp1252", "latin-1"]:
            try:
                txt = payload.decode(enc)
                break
            except Exception:
                txt = None
        if txt is None:
            txt = payload.decode("utf-8", "replace")
        cl = safe_str(part.get("Content-Location"))
        if loc and cl == loc and exact is None:
            exact = txt
        if largest is None or len(txt) > len(largest):
            largest = txt

    html_text = exact if exact else (largest or "")
    if not html_text:
        return "", meta, warn + ["MHTML enthaelt keinen lesbaren HTML-Teil"]
    if exact is None and n_html > 1:
        warn.append(f"MHTML: Hauptdokument nicht eindeutig ({n_html} HTML-Teile) — "
                    f"groesster Teil verwendet")
    warn.append(f"MHTML entpackt ({n_html} HTML-Teile, {len(html_text)} Zeichen genutzt)")
    return html_text, meta, warn


def unwrap_quoted_printable(text: str) -> str:
    """Notfall fuer MHTML-Dateien, die das email-Modul nicht als Multipart erkennt
    (abgeschnittene Downloads, manuell zusammenkopierte Archive)."""
    if "=3D" not in text and "=\r\n" not in text and "=\n" not in text:
        return text
    try:
        return quopri.decodestring(text.encode("utf-8", "replace")).decode("utf-8", "replace")
    except Exception:
        return text


def load_document(raw: bytes, filename: str = "") -> Tuple[str, dict, str, List[str]]:
    """Einheitlicher Eingang fuer alle Dateiformate.
    Rueckgabe: (html_text, meta, encoding, warnungen)"""
    warn: List[str] = []
    meta: dict = {}
    if not raw:
        return "", meta, "none", ["Datei leer"]

    if is_mhtml(raw) or safe_str(filename).lower().endswith((".mhtml", ".mht", ".eml")):
        html_text, meta, w = unpack_mhtml(raw)
        warn += w
        if html_text:
            return html_text, meta, "mhtml", warn
        warn.append("MHTML-Entpacken fehlgeschlagen — Datei wird als reines HTML gelesen")

    text, enc, w = decode_bytes(raw)
    warn += w
    before = len(text)
    text = unwrap_quoted_printable(text)
    if len(text) != before:
        warn.append("Quoted-Printable-Codierung nachtraeglich aufgeloest")
    return text, meta, enc, warn


# ============================================================
# URL-ABRUF
# ============================================================
# Wichtig zu verstehen, bevor man das benutzt: ein Server-seitiger Abruf holt
# das HTML VOR der JavaScript-Ausfuehrung. Foren, die ihre Beitraege im Browser
# nachladen (Reddit, Facebook, viele React-Foren), liefern dabei eine leere
# Huelle. Der Browser-Speicherweg (MHTML) liefert dagegen das FERTIG gerenderte
# DOM. Der URL-Abruf ist deshalb die bequemere, nicht die bessere Methode —
# das Tool prueft nach jedem Abruf, ob eine Huelle angekommen ist, und sagt es.

FETCH_DIR = "netno_fetched"
FETCH_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/126.0 Safari/537.36")

JS_SHELL_MARKERS = [
    (re.compile(r'id=["\'](root|app|__next|__nuxt)["\']', re.I), "SPA-Container"),
    (re.compile(r"__NEXT_DATA__|window\.__INITIAL_STATE__|ng-app|data-reactroot", re.I),
     "Framework-Bootstrap"),
    (re.compile(r"<noscript>[^<]*(javascript|aktivier|enable)", re.I), "noscript-Hinweis"),
]


def _fetch_path(url: str) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", safe_str(url).lower())
    slug = re.sub(r"^https?-+", "", slug).strip("-")[:70]
    return os.path.join(FETCH_DIR, f"{sha1(url)[:10]}_{slug or 'seite'}.html")


def robots_allows(url: str, ua: str = FETCH_UA) -> Tuple[bool, str]:
    """robots.txt pruefen. Keine Hoeflichkeitsgeste, sondern die Grundlage dafuer,
    den Abruf in der Methodik ueberhaupt vertreten zu koennen."""
    try:
        from urllib.parse import urlparse
        from urllib.robotparser import RobotFileParser
        u = urlparse(url)
        if not u.scheme or not u.netloc:
            return False, "Keine gueltige URL"
        rp = RobotFileParser()
        rp.set_url(f"{u.scheme}://{u.netloc}/robots.txt")
        rp.read()
        ok = rp.can_fetch(ua, url)
        return bool(ok), "" if ok else "robots.txt untersagt den Abruf dieser Seite"
    except Exception as e:
        # Keine robots.txt erreichbar: kein Freibrief, aber auch kein Verbot.
        return True, f"robots.txt nicht pruefbar ({type(e).__name__}) — Abruf auf eigene Verantwortung"


def detect_js_shell(html_text: str, n_comments: int = -1) -> Tuple[bool, List[str]]:
    """Erkennt eine leere Single-Page-App-Huelle."""
    reasons = []
    if not html_text:
        return True, ["Antwort leer"]
    try:
        soup = _soup(html_text)
        for t in soup.find_all(["script", "style", "noscript"]):
            t.decompose()
        text_len = len((soup.body or soup).get_text(" ", strip=True))
    except Exception:
        text_len = len(re.sub(r"<[^>]+>", " ", html_text))
    ratio = text_len / max(1, len(html_text))

    for pat, name in JS_SHELL_MARKERS:
        if pat.search(html_text[:200000]):
            reasons.append(name)
    if text_len < 900:
        reasons.append(f"nur {text_len} Zeichen sichtbarer Text")
    if ratio < 0.012:
        reasons.append(f"Textanteil {ratio:.1%} des Quelltexts")
    if n_comments == 0:
        reasons.append("0 Kommentare extrahiert")

    # Entscheidend ist nicht, ob die Seite ein Framework benutzt, sondern ob
    # Inhalt angekommen ist. Viele Foren rendern serverseitig UND nutzen React;
    # umgekehrt ist eine kurze Seite mit sauber extrahierten Beitraegen in
    # Ordnung. Deshalb schlaegt ein erfolgreicher Extraktionslauf jede Heuristik.
    if n_comments >= 2:
        return False, []
    if n_comments == 1:
        return (text_len < 400), (reasons if text_len < 400 else [])
    if n_comments == 0:
        return True, reasons or ["0 Kommentare trotz Serverantwort"]
    # n_comments unbekannt (-1): nur bei klarer Huelle Alarm schlagen
    has_marker = any(name in reasons for _, name in JS_SHELL_MARKERS)
    is_shell = (text_len < 500) or (ratio < 0.012 and has_marker)
    return is_shell, (reasons if is_shell else [])


def find_pagination_links(html_text: str, page_url: str, max_pages: int = 10) -> List[str]:
    """Folgeseiten eines Threads finden.

    Ohne das holt man Seite 1 von 12 und wertet ein Achtel der Diskussion aus —
    ein Fehler, der im Ergebnis voellig unauffaellig aussieht.
    """
    if max_pages <= 1:
        return []
    try:
        from urllib.parse import urljoin, urlparse, parse_qs
        soup = _soup(html_text)
    except Exception:
        return []

    found: Dict[int, str] = {}

    def page_no(u: str) -> Optional[int]:
        for pat in (r"[?&](?:page|seite|p|start|offset)=(\d+)",
                    r"/(?:page|seite)/(\d+)", r"[-_]p(\d+)\.html?$", r"/(\d+)/?$"):
            m = re.search(pat, u, re.I)
            if m:
                try:
                    return int(m.group(1))
                except Exception:
                    return None
        return None

    base_host = urlparse(page_url).netloc
    # 1) rel=next-Kette und klassische Seitenzahl-Links
    for a in soup.find_all(["a", "link"], href=True):
        href = urljoin(page_url, a["href"].strip())
        if urlparse(href).netloc != base_host:
            continue
        rel = " ".join(a.get("rel") or []).lower()
        txt = norm_ws(a.get_text(" ", strip=True))
        n = page_no(href)
        if rel == "next" and n:
            found[n] = href
        elif n and (txt.isdigit() or rel == "next"):
            # nur Links, die sich vom Ausgangs-URL wirklich nur in der Seitenzahl
            # unterscheiden — sonst landen Nachbarthreads im Korpus
            stem_a = re.sub(r"\d+", "#", href)
            stem_b = re.sub(r"\d+", "#", page_url)
            if stem_a == stem_b or href.split("?")[0] == page_url.split("?")[0]:
                found[n] = href

    cur = page_no(page_url) or 1
    out = [u for n, u in sorted(found.items()) if n > cur and u != page_url]
    return out[:max_pages - 1]


def fetch_url(url: str, use_cache: bool = True, timeout: int = 30,
              respect_robots: bool = True) -> Tuple[bytes, dict, List[str]]:
    """Eine Seite abrufen und lokal ablegen.
    Rueckgabe: (rohbytes, meta, warnungen)"""
    warn: List[str] = []
    meta: dict = {"url": url, "quelle": "abgerufen"}
    os.makedirs(FETCH_DIR, exist_ok=True)
    path = _fetch_path(url)

    if use_cache and os.path.exists(path):
        with open(path, "rb") as f:
            raw = f.read()
        meta["pfad"] = path
        meta["abgerufen_am"] = datetime.fromtimestamp(
            os.path.getmtime(path)).strftime("%Y-%m-%d %H:%M")
        warn.append(f"Aus lokalem Archiv geladen ({meta['abgerufen_am']}) — "
                    f"kein erneuter Serverzugriff")
        return raw, meta, warn

    if respect_robots:
        ok, reason = robots_allows(url)
        if not ok:
            return b"", meta, [f"ABGEBROCHEN: {reason}"]
        if reason:
            warn.append(reason)

    try:
        r = requests.get(url, timeout=timeout, headers={
            "User-Agent": FETCH_UA,
            "Accept": "text/html,application/xhtml+xml",
            "Accept-Language": "de-DE,de;q=0.9,en;q=0.8",
        })
    except requests.exceptions.RequestException as e:
        return b"", meta, [f"Abruf fehlgeschlagen: {e}"]

    if r.status_code != 200:
        return b"", meta, [f"Abruf fehlgeschlagen: HTTP {r.status_code}"
                           + (" — Seite verlangt vermutlich Login oder blockt Bots."
                              if r.status_code in (401, 403, 429) else "")]
    raw = r.content
    meta["abgerufen_am"] = datetime.now().strftime("%Y-%m-%d %H:%M")
    meta["final_url"] = safe_str(r.url)
    if safe_str(r.url) != url:
        warn.append(f"Weiterleitung auf {r.url}")
    with open(path, "wb") as f:
        f.write(raw)
    meta["pfad"] = path
    warn.append(f"{len(raw)/1024:.0f} KB abgerufen und lokal gesichert: {path}")
    return raw, meta, warn


def fetch_thread(url: str, max_pages: int = 5, use_cache: bool = True,
                 delay: float = 1.5, respect_robots: bool = True) -> List[dict]:
    """Thread inklusive Folgeseiten abrufen.
    Rueckgabe: Liste von {name, html, meta, warnungen} — eine Seite je Eintrag."""
    out = []
    raw, meta, warn = fetch_url(url, use_cache, respect_robots=respect_robots)
    if not raw:
        return [{"name": url, "html": "", "meta": meta, "warnungen": warn}]

    html_text, dmeta, enc, w2 = load_document(raw, url)
    meta.update({k: v for k, v in dmeta.items() if v})
    meta["encoding"] = enc
    out.append({"name": url, "html": html_text, "meta": dict(meta), "warnungen": warn + w2})

    if max_pages > 1:
        pages = find_pagination_links(html_text, meta.get("final_url", url), max_pages)
        for p in pages:
            time.sleep(max(0.0, delay))   # nicht hämmern: eine Seite pro Sekunde reicht
            praw, pmeta, pwarn = fetch_url(p, use_cache, respect_robots=respect_robots)
            if not praw:
                out.append({"name": p, "html": "", "meta": pmeta, "warnungen": pwarn})
                continue
            ptxt, pdmeta, penc, pw2 = load_document(praw, p)
            pmeta.update({k: v for k, v in pdmeta.items() if v})
            pmeta["encoding"] = penc
            out.append({"name": p, "html": ptxt, "meta": pmeta, "warnungen": pwarn + pw2})
    return out


def url_to_filename(url: str, page_idx: int = 0) -> str:
    """Sprechender Anzeigename fuer eine abgerufene Seite."""
    try:
        from urllib.parse import urlparse
        u = urlparse(url)
        stem = re.sub(r"[^A-Za-z0-9\-_]+", "_", (u.path or "/").strip("/"))[-60:] or "index"
        name = f"{u.netloc}_{stem}"
    except Exception:
        name = re.sub(r"[^A-Za-z0-9]+", "_", url)[:70]
    return f"{name}{'_s' + str(page_idx + 1) if page_idx else ''}.html"

# ========================
# Sprach-Erkennung (abhängigkeitsfrei)
# ========================
_LANG_STOP = {
    "de": {"und","der","die","das","ich","nicht","mit","ist","auch","aber","habe","für","eine","mir","mich","wir","sehr","schon","noch","weil","wenn"},
    "en": {"the","and","that","have","for","not","with","you","this","but","are","was","just","like","really","would","about","they","from","been"},
    "fr": {"les","des","est","pas","une","que","pour","dans","avec","plus","mais","vous","nous","cette","comme","tout","être","fait"},
    "es": {"que","los","las","con","por","para","una","como","pero","más","este","muy","todo","porque","cuando","también"},
    "it": {"che","non","per","una","con","sono","come","questo","anche","più","molto","perché","quando","tutto"},
    "nl": {"het","een","niet","dat","van","voor","maar","ook","heb","zijn","deze","erg","omdat"},
    "pl": {"nie","jest","się","tak","tego","ale","jak","bardzo","tylko","czy","dla"},
    "pt": {"que","não","uma","para","com","mais","como","mas","muito","porque","quando","também"},
}


def detect_lang_simple(text: str) -> str:
    """Stopwort-basierte Spracherkennung. Bewusst simpel: transparent und offline."""
    toks = re.findall(r"[a-zà-ÿąćęłńóśźż]+", safe_str(text).lower())
    if len(toks) < 4:
        return "?"
    ts = set(toks)
    scores = {lg: len(ts & sw) for lg, sw in _LANG_STOP.items()}
    best = max(scores, key=scores.get)
    if scores[best] < 2:
        return "?"
    # Eindeutigkeit prüfen: knapper Vorsprung = unsicher
    second = sorted(scores.values(), reverse=True)[1] if len(scores) > 1 else 0
    if scores[best] - second < 1:
        return "?"
    return best


# ========================
# Prompt-Cache (SQLite)
# ========================
_cache_lock_created = False


def _cache_conn():
    con = sqlite3.connect(CACHE_DB, timeout=30, check_same_thread=False)
    con.execute("PRAGMA journal_mode=WAL")
    con.execute("""CREATE TABLE IF NOT EXISTS prompt_cache (
        key TEXT PRIMARY KEY,
        response TEXT,
        tokens INTEGER,
        cost REAL,
        finish_reason TEXT,
        created TEXT
    )""")
    return con


def cache_get(key: str):
    try:
        con = _cache_conn()
        row = con.execute(
            "SELECT response, tokens, cost, finish_reason FROM prompt_cache WHERE key=?",
            (key,)).fetchone()
        con.close()
        if row:
            return row[0], int(row[1] or 0), float(row[2] or 0.0), row[3] or "cached"
    except Exception:
        pass
    return None


def cache_put(key: str, response: str, tokens: int, cost: float, finish_reason: str):
    try:
        con = _cache_conn()
        con.execute(
            "INSERT OR REPLACE INTO prompt_cache VALUES (?,?,?,?,?,?)",
            (key, response, int(tokens), float(cost), safe_str(finish_reason),
             datetime.now(timezone.utc).isoformat()))
        con.commit()
        con.close()
    except Exception:
        pass


def cache_clear():
    try:
        con = _cache_conn()
        con.execute("DELETE FROM prompt_cache")
        con.commit()
        con.close()
        return True
    except Exception:
        return False


def cache_stats() -> Tuple[int, float]:
    try:
        con = _cache_conn()
        row = con.execute("SELECT COUNT(*), COALESCE(SUM(cost),0) FROM prompt_cache").fetchone()
        con.close()
        return int(row[0]), float(row[1])
    except Exception:
        return 0, 0.0


# ========================
# LLM-Layer
# ========================
def get_cost_per_token(num_tokens: int) -> float:
    if num_tokens <= 500:
        return 0.000881 / 500
    if num_tokens <= 1000:
        return 0.001242 / 1000
    if num_tokens <= 2000:
        return 0.00196 / 2000
    return 0.00228 / 2000


def model_price(deployment: str) -> Optional[Tuple[float, float]]:
    d = safe_str(deployment).lower()
    for name, price in MODEL_PRICES_USD.items():
        if d.startswith(name):
            return price
    return None


def estimate_cost_eur(deployment: str, prompt_tokens: int, completion_tokens: int) -> float:
    price = model_price(deployment)
    if price is None:
        total = int(prompt_tokens) + int(completion_tokens)
        return float(total) * get_cost_per_token(total)
    return (prompt_tokens * price[0] + completion_tokens * price[1]) / 1_000_000 * USD_TO_EUR


def is_reasoning_model(cfg: dict) -> bool:
    """GPT-5/6 und o-Serie brauchen max_completion_tokens + reasoning_effort.
    Azure-Deployments haben freie Namen -> per OPENAI_REASONING_API=1/0 erzwingbar."""
    forced = safe_str(cfg.get("reasoning_api")).lower()
    if forced in ("1", "true", "yes"):
        return True
    if forced in ("0", "false", "no"):
        return False
    d = safe_str(cfg.get("deployment")).lower()
    return bool(re.match(r"^(gpt-5|gpt-6|o1|o3|o4)", d))


def resolve_llm_cfg() -> dict:
    """Konfiguration EINMAL im Main-Thread auflösen (Worker dürfen nicht auf st.* zugreifen)."""
    return {
        "api_key": find_secret(["OPENAI_API_KEY", "AZURE_OPENAI_KEY", "OPENAI_KEY"]),
        "endpoint": find_secret(["OPENAI_ENDPOINT", "AZURE_OPENAI_ENDPOINT"]),
        "deployment": (find_secret(["AZURE_OPENAI_DEPLOYMENT", "OPENAI_DEPLOYMENT", "DEPLOYMENT_NAME"])
                       or st.session_state.get("OPENAI_DEPLOYMENT") or DEFAULT_DEPLOYMENT_NAME),
        "api_version": (find_secret(["AZURE_OPENAI_API_VERSION", "OPENAI_API_VERSION"])
                        or st.session_state.get("OPENAI_API_VERSION") or DEFAULT_API_VERSION),
        "reasoning_effort": (find_secret(["OPENAI_REASONING_EFFORT", "REASONING_EFFORT"])
                             or st.session_state.get("OPENAI_REASONING_EFFORT")
                             or DEFAULT_REASONING_EFFORT),
        "reasoning_api": find_secret(["OPENAI_REASONING_API"]),
    }


def call_llm(prompt: str, system_prompt: str, max_tokens: int = 1400,
             temperature: float = 0.0, llm_cfg: dict = None,
             max_retries: int = 3) -> Tuple[str, int, float, str]:
    """Gibt (text, tokens, kosten, finish_reason) zurück.
    finish_reason == 'length' bedeutet: Antwort ist ABGESCHNITTEN und darf nicht
    als gültig behandelt werden."""
    cfg = llm_cfg or resolve_llm_cfg()
    api_key = cfg.get("api_key")
    endpoint = cfg.get("endpoint")
    deployment = cfg.get("deployment")
    api_version = cfg.get("api_version")

    if not api_key:
        raise Exception("API-Key fehlt (OPENAI_API_KEY / AZURE_OPENAI_KEY).")

    messages = [
        {"role": "system", "content": safe_str(system_prompt)},
        {"role": "user", "content": safe_str(prompt)},
    ]

    if is_reasoning_model(cfg):
        effort = safe_str(cfg.get("reasoning_effort")) or DEFAULT_REASONING_EFFORT
        payload = {"messages": messages, "reasoning_effort": effort}
        if effort == "none":
            # temperature ist nur ohne Reasoning erlaubt
            payload["temperature"] = temperature
            payload["max_completion_tokens"] = max_tokens
        else:
            # Reasoning-Tokens zählen ins Budget -> ohne Aufschlag droht finish_reason=length
            payload["max_completion_tokens"] = max_tokens + REASONING_TOKEN_HEADROOM
    else:
        payload = {"messages": messages, "temperature": temperature, "max_tokens": max_tokens}

    if endpoint:
        url = (f"{endpoint.rstrip('/')}/openai/deployments/{deployment}"
               f"/chat/completions?api-version={api_version}")
        headers = {"Content-Type": "application/json", "api-key": api_key}
    else:
        url = "https://api.openai.com/v1/chat/completions"
        headers = {"Content-Type": "application/json", "Authorization": f"Bearer {api_key}"}
        payload = {"model": deployment, **payload}

    result, last_err = None, None
    for attempt in range(max_retries + 1):
        try:
            r = requests.post(url, json=payload, headers=headers, timeout=180)
            if r.status_code == 400:
                # Nicht retrybar: Prompt-/Content-Fehler. Sofort laut scheitern.
                raise Exception(f"HTTP 400 (nicht wiederholbar): {r.text[:400]}")
            if r.status_code in (401, 403):
                raise Exception(f"HTTP {r.status_code}: Authentifizierung fehlgeschlagen.")
            if r.status_code == 429 or r.status_code >= 500:
                ra = r.headers.get("Retry-After")
                wait = float(ra) if ra else min(2 ** attempt * 2, 30) + random.uniform(0, 1.5)
                last_err = Exception(f"HTTP {r.status_code}")
                if attempt < max_retries:
                    time.sleep(wait)
                    continue
                r.raise_for_status()
            r.raise_for_status()
            result = r.json()
            break
        except requests.exceptions.RequestException as e:
            last_err = e
            if attempt < max_retries:
                time.sleep(min(2 ** attempt * 2, 30) + random.uniform(0, 1.5))
                continue

    if result is None:
        raise Exception(f"LLM-Request fehlgeschlagen nach {max_retries + 1} Versuchen: {last_err} "
                        f"| Endpoint={endpoint} | Deployment={deployment}")

    output_text, finish_reason = "", "unknown"
    if isinstance(result, dict) and result.get("choices"):
        choice = result["choices"][0]
        finish_reason = safe_str(choice.get("finish_reason")) or "unknown"
        msg = choice.get("message")
        if isinstance(msg, dict):
            output_text = msg.get("content") or ""
        elif "text" in choice:
            output_text = choice.get("text") or ""
        else:
            output_text = json.dumps(choice, ensure_ascii=False)
    else:
        output_text = json.dumps(result, ensure_ascii=False)

    total_tokens, prompt_tokens, completion_tokens = None, None, None
    if isinstance(result, dict) and isinstance(result.get("usage"), dict):
        usage = result["usage"]
        total_tokens = usage.get("total_tokens")
        prompt_tokens = usage.get("prompt_tokens")
        completion_tokens = usage.get("completion_tokens")   # inkl. Reasoning-Tokens
    if total_tokens is None:
        prompt_tokens = len(safe_str(system_prompt).split()) + len(safe_str(prompt).split())
        completion_tokens = len(safe_str(output_text).split())
        total_tokens = prompt_tokens + completion_tokens
    if prompt_tokens is None or completion_tokens is None:
        prompt_tokens, completion_tokens = int(total_tokens), 0

    cost = estimate_cost_eur(deployment, int(prompt_tokens), int(completion_tokens))
    return safe_str(output_text), int(total_tokens), float(cost), finish_reason


def call_llm_cached(prompt: str, system_prompt: str, max_tokens: int = 1400,
                    temperature: float = 0.0, llm_cfg: dict = None,
                    validate: Optional[Callable[[str], bool]] = None,
                    use_cache: bool = True) -> Tuple[str, int, float, str, bool]:
    """Wie call_llm, aber mit SQLite-Cache.
    validate(): darf die Antwort gecacht werden? Abgeschnittene oder unparsbare
    Antworten werden NIE gecacht — sonst friert ein Fehler dauerhaft ein.
    Rückgabe: (text, tokens, cost, finish_reason, was_cached)"""
    cfg = llm_cfg or resolve_llm_cfg()
    key = sha1("|".join([safe_str(cfg.get("deployment")), safe_str(cfg.get("reasoning_effort")),
                         str(temperature), str(max_tokens), system_prompt, prompt]))
    if use_cache:
        hit = cache_get(key)
        if hit:
            return hit[0], 0, 0.0, hit[3], True

    text, tokens, cost, finish = call_llm(prompt, system_prompt, max_tokens,
                                          temperature, cfg)
    ok = (finish != "length")
    if ok and validate is not None:
        try:
            ok = bool(validate(text))
        except Exception:
            ok = False
    if use_cache and ok:
        cache_put(key, text, tokens, cost, finish)
    return text, tokens, cost, finish, False


def strip_json_fences(text: str) -> str:
    t = safe_str(text)
    t = re.sub(r"^```(?:json)?\s*", "", t)
    t = re.sub(r"\s*```$", "", t)
    return t.strip()


def parse_json_loose(text: str):
    """JSON aus einer LLM-Antwort ziehen — robust, aber ohne stilles Raten."""
    t = strip_json_fences(text)
    try:
        return json.loads(t)
    except Exception:
        pass
    # erstes balanciertes Objekt/Array suchen
    for opener, closer in (("[", "]"), ("{", "}")):
        start = t.find(opener)
        if start < 0:
            continue
        depth, in_str, esc = 0, False, False
        for i in range(start, len(t)):
            ch = t[i]
            if in_str:
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
                continue
            if ch == '"':
                in_str = True
            elif ch == opener:
                depth += 1
            elif ch == closer:
                depth -= 1
                if depth == 0:
                    try:
                        return json.loads(t[start:i + 1])
                    except Exception:
                        break
    return None


# ============================================================
# HTML-EXTRAKTION — der kritische Teil der Pipeline
# ============================================================
# Reihenfolge der Strategien (höchste Treue zuerst):
#   1. jsonld     — schema.org DiscussionForumPosting / QAPage / Comment
#   2. microdata  — itemtype=".../Comment" | ".../Answer"
#   3. platform   — bekannte Plattform-Signaturen (Reddit, XenForo, phpBB, ...)
#   4. selector   — manuell gesetzter CSS-Selektor
#   5. repeat     — generische Erkennung wiederholter DOM-Blöcke
# Jede Strategie liefert eine Konfidenz; das Ergebnis wird im Preflight
# ausgewiesen und ist vor der Analyse korrigierbar.

BOILERPLATE_TAGS = ["script", "style", "noscript", "svg", "iframe", "form",
                    "nav", "header", "footer", "aside", "button", "select",
                    "template", "link", "meta"]

QUOTE_SELECTORS = ["blockquote", ".quote", ".bbCodeBlock", ".quoteContainer",
                   ".messageQuote", "[class*='quote']", ".md-spoiler-text"]

AUTHOR_HINTS = re.compile(r"(author|username|user-?name|poster|by-?line|nick|"
                          r"member-?name|profile-?link)", re.I)
DATE_HINTS = re.compile(r"(date|time|posted|created|timestamp|ago)", re.I)

NAV_TEXT_PATTERNS = re.compile(
    r"^(anmelden|login|registrieren|sign in|sign up|cookie|datenschutz|impressum|"
    r"antworten|reply|zitieren|quote|melden|report|teilen|share|mehr anzeigen|"
    r"show more|weiterlesen|read more|\d+\s*(antwort(en)?|repl(y|ies)|kommentare?|"
    r"comments?)|nach oben|zurück|weiter|seite \d+|page \d+)\s*$", re.I)

PLATFORM_SIGNATURES = [
    # (Name, Erkennungsmerkmal im HTML, CSS-Selektor für Kommentare)
    ("Reddit",        r"reddit\.com|shreddit|_1oQyIsiPHYt6nx7VOmd1sz",
     "shreddit-comment, div[data-testid='comment'], div.Comment, div[data-type='comment']"),
    ("XenForo",       r"xenforo|js-post|message-userContent",
     "article.message, div.message, li.message"),
    ("Motor-Talk",    r"motor-talk\.de",
     "section.Post, [itemtype*='Comment'], [itemtype*='DiscussionForumPosting']"),
    ("Motorrad/Auto-Foren (Woltlab)", r"woltlab|wbbCore|messageBody",
     "article.wbbPost, li.wbbPost, div.messageBody"),
    ("phpBB",         r"phpbb3?[\-_/]|class=\"post[\s\"]|id=\"page-body",
     "div.post, div.postbody"),
    ("vBulletin",     r"vbulletin|postcontainer",
     "li.postcontainer, div.postdetails"),
    ("Discourse",     r"discourse|topic-post|cooked",
     "div.topic-post, article[id^='post_']"),
    ("Disqus",        r"disqus",
     "li.post, div.post-content"),
    ("WordPress",     r"wp-content|comment-body|commentlist",
     "li.comment, div.comment-body, article.comment"),
    ("Gutefrage",     r"gutefrage\.net|answer-box",
     "div.answer-box, div[class*='Answer']"),
    ("Chefkoch",      r"chefkoch\.de|forum-post",
     "div.forum-post, li.forum-post"),
    ("Facebook",      r"facebook\.com|x1lliihq",
     "div[role='article']"),
    ("YouTube",       r"youtube\.com|ytd-comment",
     "ytd-comment-thread-renderer, ytd-comment-renderer"),
    ("Stack/Q&A",     r"stackexchange|stackoverflow|question-summary",
     "div.answer, div.question, div.comment"),
    ("Trustpilot",    r"trustpilot",
     "article[data-service-review-card-paper], section.review"),
    ("Amazon Review", r"amazon\.(de|com|co\.uk)|review-text-content",
     "div[data-hook='review'], span[data-hook='review-body']"),
]


def _soup(html_text: str):
    if not HAS_BS4:
        raise RuntimeError("BeautifulSoup4 ist nicht installiert (pip install beautifulsoup4 lxml).")
    return BeautifulSoup(html_text, BS_PARSER)


def _kill_boilerplate(node) -> None:
    for tag in node.find_all(BOILERPLATE_TAGS):
        tag.decompose()


def _block_text(node) -> str:
    """Text eines Knotens mit Zeilenumbrüchen an Block-Grenzen."""
    if node is None:
        return ""
    for br in node.find_all("br"):
        br.replace_with("\n")
    for p in node.find_all(["p", "div", "li"]):
        if p.string:
            p.string.replace_with(p.get_text() + "\n")
    return norm_ws(node.get_text(" ", strip=True))


def _link_density(node) -> float:
    """Anteil verlinkten Textes. Hoch = Navigation, nicht Inhalt."""
    total = len(node.get_text(" ", strip=True)) or 1
    linked = sum(len(a.get_text(" ", strip=True)) for a in node.find_all("a"))
    return linked / total


def _extract_quotes(block) -> Tuple[str, str]:
    """Zitierte Fremdbeiträge aus einem Kommentar herauslösen.
    Ohne diesen Schritt wird zitierter Text mehrfach gezählt und verfälscht jedes N."""
    quoted_parts = []
    for sel in QUOTE_SELECTORS:
        try:
            for q in block.select(sel):
                txt = norm_ws(q.get_text(" ", strip=True))
                if txt:
                    quoted_parts.append(txt)
                q.decompose()
        except Exception:
            continue
    return _block_text(block), " || ".join(quoted_parts)


def _find_author(block) -> str:
    for attr in ("data-author", "data-username", "data-user"):
        v = block.get(attr) if hasattr(block, "get") else None
        if v:
            return norm_ws(v)[:120]
    el = block.find(attrs={"itemprop": "author"})
    if el:
        t = norm_ws(el.get_text(" ", strip=True))
        if t:
            return t[:120]
    for cand in block.find_all(["a", "span", "div", "h3", "h4", "strong"], limit=60):
        cls = " ".join(cand.get("class") or []) + " " + safe_str(cand.get("id"))
        href = safe_str(cand.get("href"))
        if AUTHOR_HINTS.search(cls) or re.search(r"/(user|users|u|member|profile)/", href):
            t = norm_ws(cand.get_text(" ", strip=True))
            if 1 <= len(t) <= 60:
                return t
    return ""


DATE_TEXT_PATTERNS = [
    re.compile(r"\b\d{4}-\d{2}-\d{2}(?:[T ]\d{2}:\d{2})?\b"),
    re.compile(r"\b\d{1,2}[./]\d{1,2}[./]\d{2,4}\b"),
    re.compile(r"\b\d{1,2}\.?\s*(?:Jan|Feb|Mär|Mar|Apr|Mai|May|Jun|Jul|Aug|Sep|Okt|Oct|Nov|Dez|Dec)"
               r"[a-zä]*\.?\s*\d{4}\b", re.I),
    re.compile(r"\b(?:January|February|March|April|May|June|July|August|September|October|"
               r"November|December)\s+\d{1,2},?\s*\d{4}\b", re.I),
    re.compile(r"\bvor\s+\d+\s+(?:Minuten?|Stunden?|Tagen?|Wochen?|Monaten?|Jahren?)\b", re.I),
    re.compile(r"\b\d+\s+(?:minutes?|hours?|days?|weeks?|months?|years?)\s+ago\b", re.I),
]


def _find_date(block) -> str:
    """Datum in vier Stufen, von exakt nach heuristisch.

    Stufe 4 (Textscan) ist noetig, weil viele Foren das Datum in generisch
    benannten Spans ausliefern (Motor-Talk: "Typography-metaSecondary").
    Der Scan ist auf den Blockanfang begrenzt, weil dort der Kopfbereich steht
    und nicht der Fliesstext — sonst wird ein im Beitrag genanntes Datum
    faelschlich zum Postdatum.
    """
    # 1) <time>
    t = block.find("time")
    if t:
        for a in ("datetime", "data-time", "data-timestamp", "title"):
            if t.get(a):
                return norm_ws(t.get(a))[:60]
        txt = norm_ws(t.get_text(" ", strip=True))
        if txt:
            return txt[:60]

    # 2) Microdata / OpenGraph-Meta
    for el in block.select("[itemprop='datePublished'], [itemprop='dateCreated'], "
                           "[itemprop='dateModified'], [property='article:published_time']"):
        v = el.get("content") or el.get("datetime") or el.get_text(" ", strip=True)
        if safe_str(v):
            return norm_ws(v)[:60]

    # 3) Klassen-/ID-Hinweis
    for cand in block.find_all(["span", "div", "a", "p", "li"], limit=80):
        cls = " ".join(cand.get("class") or []) + " " + safe_str(cand.get("id"))
        for attr in ("data-date", "data-time", "title"):
            if DATE_HINTS.search(cls) and cand.get(attr):
                return norm_ws(cand.get(attr))[:60]
        if DATE_HINTS.search(cls):
            txt = norm_ws(cand.get_text(" ", strip=True))
            if 3 <= len(txt) <= 45:
                return txt

    # 4) Textscan im Kopfbereich
    head_txt = norm_ws(block.get_text(" ", strip=True))[:260]
    for pat in DATE_TEXT_PATTERNS:
        m = pat.search(head_txt)
        if m:
            return norm_ws(m.group(0))[:60]
    return ""


def _mk_record(text: str, quoted: str, author: str, date: str, order: int,
               role: str = "beitrag") -> dict:
    return {"text": text, "quoted_text": quoted, "author": author,
            "date_raw": date, "order": order, "role": role}


META_TAG_HINTS = re.compile(
    r"(author|username|user-?name|poster|by-?line|nick|member-?name|profile-?link|"
    r"date|time|posted|created|timestamp|signature|sig-?block|post-?meta|"
    r"message-?attribution|reactions?|vote|score|karma|toolbar|actions?|"
    r"footer|controls|share|report)", re.I)


def _block_to_record(el, order: int) -> Optional[dict]:
    """Ein DOM-Block -> ein Kommentar-Datensatz.

    Arbeitet auf einer KOPIE des Knotens. Das ist entscheidend: die Strategien
    laufen nacheinander auf demselben Soup; wer das Original zerlegt, sabotiert
    die naechste Strategie und damit die Vergleichbarkeit im Preflight.

    Metadaten (Autor, Datum, Signatur, Buttonleisten) werden VOR der
    Textextraktion entfernt, sonst landet "Lisa gestern" im Verbatim.
    """
    author = _find_author(el)
    date = _find_date(el)
    try:
        node = _copy.copy(el)
    except Exception:
        node = el

    # Autor-/Datums-/Meta-Elemente entfernen
    try:
        for t in node.find_all("time"):
            t.decompose()
        for cand in list(node.find_all(["span", "div", "a", "h3", "h4", "h5",
                                        "strong", "small", "em", "ul", "li"])):
            if not getattr(cand, "get", None):
                continue
            marker = " ".join(cand.get("class") or []) + " " + safe_str(cand.get("id"))
            if not marker.strip():
                continue
            if META_TAG_HINTS.search(marker):
                txt = norm_ws(cand.get_text(" ", strip=True))
                # nur kurze Metaschnipsel entfernen, nie den Kommentarkoerper
                if len(txt) <= 80:
                    cand.decompose()
    except Exception:
        pass

    text, quoted = _extract_quotes(node)

    # Sicherheitsnetz: fuehrenden Autornamen/Datum abschneiden, falls er
    # strukturlos im selben Textknoten stand
    if author and text.lower().startswith(author.lower()):
        text = norm_ws(text[len(author):].lstrip(" :\u2013-\u00b7|,"))
    if date and text.lower().startswith(date.lower()):
        text = norm_ws(text[len(date):].lstrip(" :\u2013-\u00b7|,"))

    # Navigationsreste verwerfen
    if NAV_TEXT_PATTERNS.match(text):
        return None
    if not (MIN_COMMENT_CHARS <= len(text) <= MAX_COMMENT_CHARS):
        return None
    return _mk_record(text, quoted, author, date, order)


# ── Strategie 1: JSON-LD ────────────────────────────────────────────────────
def _extract_jsonld(soup) -> Tuple[List[dict], float, List[str]]:
    out, warn = [], []
    blobs = []
    for tag in soup.find_all("script", attrs={"type": re.compile("ld\\+json", re.I)}):
        raw = tag.string or tag.get_text() or ""
        data = parse_json_loose(raw)
        if data is not None:
            blobs.append(data)

    def walk(node):
        if isinstance(node, list):
            for x in node:
                walk(x)
            return
        if not isinstance(node, dict):
            return
        t = node.get("@type") or node.get("type") or ""
        types = t if isinstance(t, list) else [t]
        types = [safe_str(x).lower() for x in types]
        body = node.get("text") or node.get("articleBody") or node.get("reviewBody") or ""
        if any(x in ("comment", "answer", "socialmediaposting", "question",
                     "discussionforumposting", "review", "usercomments") for x in types):
            txt = norm_ws(re.sub(r"<[^>]+>", " ", safe_str(body)))
            if len(txt) >= MIN_COMMENT_CHARS:
                auth = node.get("author")
                if isinstance(auth, dict):
                    auth = auth.get("name", "")
                elif isinstance(auth, list) and auth:
                    auth = auth[0].get("name", "") if isinstance(auth[0], dict) else safe_str(auth[0])
                out.append(_mk_record(txt, "", norm_ws(safe_str(auth))[:120],
                                      safe_str(node.get("dateCreated") or node.get("datePublished")),
                                      len(out)))
        for key in ("comment", "comments", "suggestedAnswer", "acceptedAnswer",
                    "answer", "review", "mainEntity", "itemListElement", "@graph"):
            if key in node:
                walk(node[key])

    for b in blobs:
        walk(b)

    conf = 0.0
    if out:
        conf = 0.95 if len(out) >= 3 else 0.6
        warn.append(f"JSON-LD strukturierte Daten gefunden ({len(out)} Beiträge)")
    return out, conf, warn


# ── Strategie 2: Microdata ──────────────────────────────────────────────────
def _extract_microdata(soup) -> Tuple[List[dict], float, List[str]]:
    blocks = soup.select("[itemtype*='Comment'], [itemtype*='Answer'], "
                         "[itemtype*='Review'], [itemtype*='SocialMediaPosting'], "
                         "[itemtype*='DiscussionForumPosting'], [itemtype*='Question'], "
                         "[itemprop='comment'], [itemprop='suggestedAnswer']")
    out = []
    for b in blocks:
        body = b.find(attrs={"itemprop": re.compile("text|reviewBody|articleBody", re.I)}) or b
        rec = _block_to_record(body, len(out))
        if rec:
            rec["author"] = rec["author"] or _find_author(b)
            rec["date_raw"] = rec["date_raw"] or _find_date(b)
            out.append(rec)
    conf = 0.85 if len(out) >= 3 else (0.5 if out else 0.0)
    return out, conf, ([f"Microdata erkannt ({len(out)} Beiträge)"] if out else [])


# ── Strategie 3: Plattform-Signaturen ───────────────────────────────────────
def _detect_platform(html_text: str) -> Optional[Tuple[str, str]]:
    head = html_text[:200000].lower()
    for name, sig, sel in PLATFORM_SIGNATURES:
        if re.search(sig, head, re.I):
            return name, sel
    return None


def _extract_by_selector(soup, selector: str) -> List[dict]:
    out = []
    try:
        blocks = soup.select(selector)
    except Exception:
        return out
    seen_nodes = []
    for b in blocks:
        # verschachtelte Treffer vermeiden (Kommentar in Kommentar)
        if any(b in parent.descendants for parent in seen_nodes):
            continue
        seen_nodes.append(b)
        rec = _block_to_record(b, len(out))
        if rec:
            out.append(rec)
    return out


# ── Strategie 4: generische Wiederholungs-Erkennung ─────────────────────────
def _signature(el) -> str:
    """Struktur-Signatur eines Elements: Tag + normalisierte Klassen + Tiefe.
    Zahlen und IDs werden entfernt, damit 'post-1' und 'post-2' gleich zählen."""
    cls = el.get("class") or []
    cls = [re.sub(r"\d+", "#", c) for c in cls if len(c) < 40]
    cls = sorted(set(cls))[:4]
    depth = len(list(el.parents))
    return f"{el.name}|{'.'.join(cls)}|{depth}"


def _extract_repeated(soup) -> Tuple[List[dict], float, List[str]]:
    """Findet die Gruppe strukturgleicher Geschwister-Blöcke, die am ehesten
    Kommentare sind. Bewertung nach Anzahl, Textlänge, Linkdichte, Textanteil."""
    body = soup.body or soup
    groups: Dict[str, list] = defaultdict(list)
    for el in body.find_all(["div", "li", "article", "section", "td", "tr"]):
        txt = el.get_text(" ", strip=True)
        if not (MIN_COMMENT_CHARS <= len(txt) <= MAX_COMMENT_CHARS):
            continue
        groups[_signature(el)].append(el)

    total_text = len(body.get_text(" ", strip=True)) or 1
    best, best_score, diag = None, 0.0, []

    for sig, els in groups.items():
        if len(els) < 2:
            continue
        # verschachtelte Elemente derselben Gruppe entfernen
        flat = []
        for e in els:
            if not any((e is not o) and (e in o.descendants) for o in els):
                flat.append(e)
        if len(flat) < 2:
            continue
        lengths = sorted(len(e.get_text(" ", strip=True)) for e in flat)
        median = lengths[len(lengths) // 2]
        share = sum(lengths) / total_text
        ld = sum(_link_density(e) for e in flat) / len(flat)
        var = (max(lengths) / max(1, min(lengths)))

        score = 0.0
        score += min(len(flat), 40) / 40 * 2.0          # viele gleichartige Blöcke
        score += min(median, 600) / 600 * 2.0           # substanzielle Textlänge
        score += min(share, 0.85) * 2.5                 # großer Anteil am Seitentext
        score -= ld * 2.5                               # Linkwüste = Navigation
        score -= 0.4 if var > 60 else 0.0               # extrem heterogen = Container
        if score > best_score:
            best_score, best = score, flat
            diag = [f"Signatur '{sig}': {len(flat)} Blöcke, Median {median} Zeichen, "
                    f"Textanteil {share:.0%}, Linkdichte {ld:.0%}"]

    if not best:
        return [], 0.0, ["Keine wiederholte Blockstruktur gefunden"]

    out = []
    for e in best:
        rec = _block_to_record(e, len(out))
        if rec:
            out.append(rec)

    conf = max(0.0, min(0.75, best_score / 5.0))
    return out, conf, diag


# ── Strategie 5: Notfall — Absätze ──────────────────────────────────────────
def _extract_paragraphs(soup) -> Tuple[List[dict], float, List[str]]:
    out = []
    for p in (soup.body or soup).find_all(["p", "li"]):
        txt = norm_ws(p.get_text(" ", strip=True))
        if MIN_COMMENT_CHARS <= len(txt) <= MAX_COMMENT_CHARS and _link_density(p) < 0.4:
            out.append(_mk_record(txt, "", "", "", len(out)))
    return out, (0.25 if out else 0.0), ["NOTFALL-Modus: Absätze statt Kommentarblöcke. "
                                         "Ergebnis manuell prüfen!"]


def _page_meta(soup, html_text: str) -> dict:
    title = ""
    if soup.title and soup.title.string:
        title = norm_ws(soup.title.string)
    og = soup.find("meta", attrs={"property": "og:title"})
    if og and og.get("content"):
        title = norm_ws(og["content"]) or title
    h1 = soup.find("h1")
    if h1:
        t = norm_ws(h1.get_text(" ", strip=True))
        if 5 <= len(t) <= 250:
            title = t or title
    url = ""
    for sel, attr in (("link[rel='canonical']", "href"),
                      ("meta[property='og:url']", "content")):
        el = soup.select_one(sel)
        if el and el.get(attr):
            url = norm_ws(el[attr])
            break
    if not url:
        m = re.search(r"<!--\s*saved from url=\(\d+\)(.*?)-->", html_text[:5000])
        if m:
            url = norm_ws(m.group(1))
    return {"thread_title": title[:250], "url": url[:500]}


def suggest_selectors(html_text: str, top_n: int = 6) -> List[dict]:
    """Kandidaten-Selektoren fuer den Fall, dass die Automatik danebenliegt.

    Statt die Nutzerin CSS schreiben zu lassen, wird die Seite nach wiederholten
    Blockstrukturen durchsucht und jeder Kandidat mit Trefferzahl und Textprobe
    angeboten. Das ist der generische Ausweg: kein Forum der Welt braucht dann
    noch eine eigene Regel im Code.
    """
    try:
        soup = _soup(html_text)
    except Exception:
        return []
    _kill_boilerplate(soup)
    body = soup.body or soup
    total = len(body.get_text(" ", strip=True)) or 1

    cand: Dict[str, list] = defaultdict(list)
    for el in body.find_all(["div", "li", "article", "section", "td"]):
        txt = el.get_text(" ", strip=True)
        if not (MIN_COMMENT_CHARS <= len(txt) <= MAX_COMMENT_CHARS):
            continue
        classes = [c for c in (el.get("class") or []) if 2 < len(c) < 40]
        keys = []
        if classes:
            # erste Klasse ist bei den meisten Frameworks die Struktur-Klasse
            keys.append(f"{el.name}.{classes[0]}")
            if len(classes) > 1:
                keys.append(f"{el.name}.{classes[0]}.{classes[1]}")
        it = el.get("itemtype")
        if it:
            keys.append(f"[itemtype='{it}']")
        for k in keys:
            cand[k].append(el)

    rows = []
    for sel, els in cand.items():
        flat = [e for e in els
                if not any((e is not o) and (e in o.descendants) for o in els)]
        if len(flat) < 2:
            continue
        lengths = sorted(len(e.get_text(" ", strip=True)) for e in flat)
        median = lengths[len(lengths) // 2]
        share = sum(lengths) / total
        ld = sum(_link_density(e) for e in flat) / len(flat)
        score = (min(len(flat), 40) / 40 * 2.0 + min(median, 600) / 600 * 2.0
                 + min(share, .85) * 2.5 - ld * 2.5)
        sample = norm_ws(flat[0].get_text(" ", strip=True))[:180]
        rows.append({"selektor": sel, "treffer": len(flat), "median_zeichen": median,
                     "textanteil": round(share, 3), "linkdichte": round(ld, 2),
                     "score": round(score, 2), "beispiel": sample})
    rows.sort(key=lambda r: r["score"], reverse=True)
    return rows[:top_n]


def extract_comments(html_text: str, strategy: str = "auto",
                     custom_selector: str = "") -> dict:
    """Zentrale Extraktionsfunktion.
    Rückgabe: dict mit comments, strategy_used, confidence, warnings, meta, platform."""
    result = {"comments": [], "strategy_used": "none", "confidence": 0.0,
              "warnings": [], "thread_title": "", "url": "", "platform": ""}
    if not safe_str(html_text):
        result["warnings"].append("Datei leer oder nicht lesbar")
        return result

    soup = _soup(html_text)
    meta = _page_meta(soup, html_text)
    result.update(meta)

    plat = _detect_platform(html_text)

    _kill_boilerplate(soup)

    attempts: List[Tuple[str, List[dict], float, List[str]]] = []

    def try_strategy(name: str):
        try:
            if name == "jsonld":
                c, conf, w = _extract_jsonld(_soup(html_text))
            elif name == "microdata":
                c, conf, w = _extract_microdata(soup)
            elif name == "platform":
                if not plat:
                    return
                c = _extract_by_selector(soup, plat[1])
                conf = 0.9 if len(c) >= 3 else (0.45 if c else 0.0)
                w = [f"Plattform erkannt: {plat[0]}"] if c else [f"Plattform {plat[0]} erkannt, "
                                                                f"aber Selektor griff nicht"]
            elif name == "selector":
                if not safe_str(custom_selector):
                    return
                c = _extract_by_selector(soup, custom_selector)
                conf = 0.99 if c else 0.0
                w = [f"Manueller Selektor: {custom_selector}"] if c else \
                    [f"Manueller Selektor '{custom_selector}' lieferte 0 Treffer"]
            elif name == "repeat":
                c, conf, w = _extract_repeated(soup)
            elif name == "paragraphs":
                c, conf, w = _extract_paragraphs(soup)
            else:
                return
            attempts.append((name, c, conf, w))
        except Exception as e:
            attempts.append((name, [], 0.0, [f"Strategie '{name}' fehlgeschlagen: {e}"]))

    if strategy != "auto":
        try_strategy(strategy)
        if not attempts or not attempts[0][1]:
            # Fail Loud: die erzwungene Strategie hat versagt, kein stiller Fallback
            w = attempts[0][3] if attempts else []
            result["warnings"] = w + [f"Erzwungene Strategie '{strategy}' lieferte 0 Kommentare. "
                                      f"Kein automatischer Fallback (Modus manuell)."]
            result["strategy_used"] = strategy
            return result
    else:
        for name in ("selector", "jsonld", "microdata", "platform", "repeat", "paragraphs"):
            try_strategy(name)
            if attempts and attempts[-1][2] >= 0.85 and len(attempts[-1][1]) >= 3:
                break  # gute Strategie gefunden, Rest sparen

    if not attempts:
        result["warnings"].append("Keine Extraktionsstrategie anwendbar")
        return result

    name, comments, conf, warns = max(attempts, key=lambda a: (a[2], len(a[1])))
    result["comments"] = comments
    result["strategy_used"] = name
    result["confidence"] = round(float(conf), 2)
    result["warnings"] = list(warns)
    tried = {a[0] for a in attempts}
    if plat:
        # Plattform nur als bestaetigt melden, wenn ihr Selektor auch gegriffen hat.
        result["platform"] = plat[0] if name == "platform" else f"vermutet: {plat[0]}"
        if name != "platform" and "platform" in tried:
            result["warnings"].append(
                f"Plattform-Signatur '{plat[0]}' erkannt, aber deren Selektor lieferte keine "
                f"Treffer — es wurde '{name}' verwendet. HTML-Struktur ggf. veraltet.")

    # Plausibilitätsprüfungen — laut, nicht still
    if not comments:
        result["warnings"].append("0 Kommentare extrahiert — Datei prüfen oder Selektor setzen")
    else:
        lens = [len(c["text"]) for c in comments]
        if len(comments) == 1:
            result["warnings"].append("Nur 1 Block erkannt — evtl. wurde die ganze Seite "
                                      "als ein Kommentar gelesen")
        if max(lens) > 6000:
            result["warnings"].append(f"Längster Block {max(lens)} Zeichen — Verdacht auf "
                                      f"nicht getrennte Kommentare")
        if sum(1 for c in comments if not c["author"]) == len(comments):
            result["warnings"].append("Keine Autoren erkannt — N pro Autor nicht verfügbar")
        if conf < 0.5:
            result["warnings"].append(f"NIEDRIGE KONFIDENZ ({conf:.0%}) — Stichprobe manuell prüfen")

    # alle probierten Strategien dokumentieren (Nachvollziehbarkeit)
    result["attempts"] = [{"strategie": a[0], "treffer": len(a[1]),
                           "konfidenz": round(a[2], 2)} for a in attempts]
    return result


# ============================================================
# KORPUS-AUFBAU & BEREINIGUNG
# ============================================================
CORPUS_COLUMNS = [
    "kommentar_id", "datei", "community", "plattform", "thread_titel", "url",
    "position", "autor", "autor_pseudonym", "datum_roh", "datum", "sprache", "sprache_quelle",
    "zeichen", "woerter", "text", "zitierter_text", "ist_zitatantwort",
    "dupe_status", "dupe_ref", "qualitaet", "ausschlussgrund", "extraktion_strategie",
    "extraktion_konfidenz",
]

# Häufige Wegwerf-Zeilen, die in fast jedem Forum-HTML überleben
JUNK_PATTERNS = [
    re.compile(r"^(zitat|quote|edit|bearbeitet|gesendet von|sent from|"
               r"gefällt mir|like|danke|thanks|thx|\+1|\^this|dito|same)\W*$", re.I),
    re.compile(r"^[\W\d\s]{0,25}$"),
    re.compile(r"(diese website verwendet cookies|akzeptieren sie|"
               r"we use cookies|privacy policy|nutzungsbedingungen)", re.I),
]


def parse_rfc_date(raw: str) -> str:
    """RFC-2822-Datum aus dem MHTML-Kopf (z. B. 'Fri, 28 Aug 2026 14:17:00 +0200')."""
    try:
        from email.utils import parsedate_to_datetime
        return parsedate_to_datetime(safe_str(raw)).strftime("%Y-%m-%d")
    except Exception:
        return ""


def parse_date_loose(raw: str) -> str:
    """Datum best effort in ISO. Gibt '' zurück, wenn unsicher — nie geraten."""
    r = safe_str(raw)
    if not r:
        return ""
    m = re.search(r"(\d{4})-(\d{2})-(\d{2})", r)
    if m:
        return f"{m.group(1)}-{m.group(2)}-{m.group(3)}"
    m = re.search(r"\b(\d{1,2})[./](\d{1,2})[./](\d{2,4})\b", r)
    if m:
        d, mo, y = m.groups()
        y = ("20" + y) if len(y) == 2 else y
        try:
            return datetime(int(y), int(mo), int(d)).strftime("%Y-%m-%d")
        except Exception:
            return ""
    months = {"jan": 1, "feb": 2, "mär": 3, "mar": 3, "apr": 4, "mai": 5, "may": 5,
              "jun": 6, "jul": 7, "aug": 8, "sep": 9, "okt": 10, "oct": 10,
              "nov": 11, "dez": 12, "dec": 12}
    m = re.search(r"\b(\d{1,2})\.?\s*([A-Za-zÄÖÜäöü]{3})\w*\.?\s*(\d{4})", r)
    if m:
        d, mon, y = m.groups()
        mo = months.get(mon[:3].lower())
        if mo:
            try:
                return datetime(int(y), mo, int(d)).strftime("%Y-%m-%d")
            except Exception:
                return ""
    return ""


def pseudonymize(author: str, salt: str) -> str:
    """DSGVO: Nutzernamen sind pseudonyme personenbezogene Daten.
    Für Exporte an Kunden wird ein stabiler, nicht rückrechenbarer Alias erzeugt."""
    a = safe_str(author)
    if not a:
        return ""
    h = hashlib.sha256((salt + "|" + a.lower()).encode("utf-8")).hexdigest()
    return "U" + h[:6].upper()


def is_junk(text: str) -> str:
    """Gibt einen Ausschlussgrund zurück oder ''."""
    t = norm_ws(text)
    if len(t) < MIN_COMMENT_CHARS:
        return "zu_kurz"
    for pat in JUNK_PATTERNS:
        if pat.search(t):
            return "boilerplate"
    words = t.split()
    if len(words) < 4:
        return "zu_wenig_woerter"
    # Reine Linklisten
    if len(re.findall(r"https?://", t)) >= 3 and len(words) < 30:
        return "linkliste"
    # Extreme Wiederholung eines Tokens (Spam)
    if words:
        top = Counter(w.lower() for w in words).most_common(1)[0][1]
        if top / len(words) > 0.5 and len(words) > 8:
            return "spam_wiederholung"
    return ""


def build_corpus(file_results: List[dict], salt: str,
                 exclusion_patterns: List[str] = None,
                 dedupe_scope: str = "global") -> Tuple[pd.DataFrame, dict]:
    """file_results: Liste aus {name, community, extraction:{...}}.
    Erzeugt den flachen Korpus: 1 Zeile = 1 Kommentar."""
    rows = []
    seen: Dict[str, str] = {}
    custom_pats = []
    for p in (exclusion_patterns or []):
        p = safe_str(p)
        if not p:
            continue
        try:
            custom_pats.append(re.compile(p, re.I))
        except re.error:
            custom_pats.append(re.compile(re.escape(p), re.I))

    for fr in file_results:
        ex = fr.get("extraction") or {}
        fname = safe_str(fr.get("name"))
        community = safe_str(fr.get("community")) or "Unbekannt"
        for c in ex.get("comments", []):
            text = norm_ws(c.get("text"))
            grund = is_junk(text)
            if not grund:
                for pat in custom_pats:
                    if pat.search(text):
                        grund = "ausschlussmuster"
                        break

            key = norm_key(text)
            scope_key = key if dedupe_scope == "global" else f"{fname}||{key}"
            dupe_status, dupe_ref = "unikat", ""
            if key and scope_key in seen:
                dupe_status, dupe_ref = "duplikat", seen[scope_key]

            cid = f"K{len(rows) + 1:05d}"
            if key and scope_key not in seen:
                seen[scope_key] = cid

            author = safe_str(c.get("author"))
            rows.append({
                "kommentar_id": cid,
                "datei": fname,
                "community": community,
                "plattform": safe_str(fr.get("plattform") or ex.get("platform")),
                "thread_titel": safe_str(fr.get("thread_titel") or ex.get("thread_title")),
                "url": safe_str(fr.get("url") or ex.get("url")),
                "position": int(c.get("order", 0)) + 1,
                "autor": author,
                "autor_pseudonym": pseudonymize(author, salt),
                "datum_roh": safe_str(c.get("date_raw")),
                "datum": parse_date_loose(c.get("date_raw")),
                "sprache": detect_lang_simple(text),
                "sprache_quelle": "erkannt",
                "zeichen": len(text),
                "woerter": len(text.split()),
                "text": text,
                "zitierter_text": safe_str(c.get("quoted_text")),
                "ist_zitatantwort": bool(safe_str(c.get("quoted_text"))),
                "dupe_status": dupe_status,
                "dupe_ref": dupe_ref,
                "qualitaet": "ok" if not grund and dupe_status == "unikat" else "ausgeschlossen",
                "ausschlussgrund": grund or ("duplikat" if dupe_status == "duplikat" else ""),
                "extraktion_strategie": safe_str(ex.get("strategy_used")),
                "extraktion_konfidenz": float(ex.get("confidence") or 0.0),
            })

    df = pd.DataFrame(rows, columns=CORPUS_COLUMNS) if rows else pd.DataFrame(columns=CORPUS_COLUMNS)

    # Kurze Beitraege ("Danke!", "Siehe oben") sind zu kurz fuer eine Stopwort-Erkennung.
    # Statt sie als unbekannt zu fuehren, erben sie die Mehrheitssprache ihres Threads —
    # transparent gemacht ueber die Spalte 'sprache_quelle'.
    if len(df):
        for fname, g in df.groupby("datei"):
            known = g.loc[g["sprache"] != "?", "sprache"]
            if known.empty:
                continue
            major = known.value_counts().idxmax()
            mask = (df["datei"] == fname) & (df["sprache"] == "?")
            df.loc[mask, "sprache"] = major
            df.loc[mask, "sprache_quelle"] = "geerbt (Thread-Mehrheit)"

    stats = {
        "n_dateien": len(file_results),
        "n_roh": len(df),
        "n_analysierbar": int((df["qualitaet"] == "ok").sum()) if len(df) else 0,
        "n_duplikate": int((df["dupe_status"] == "duplikat").sum()) if len(df) else 0,
        "n_autoren": int(df.loc[df["autor"] != "", "autor"].nunique()) if len(df) else 0,
        "n_communities": int(df["community"].nunique()) if len(df) else 0,
        "sprachen": (df.loc[df["qualitaet"] == "ok", "sprache"].value_counts().to_dict()
                     if len(df) else {}),
    }
    return df, stats


def author_concentration(df: pd.DataFrame) -> dict:
    """Wie stark hängt der Korpus an wenigen Vielschreibern?
    Ohne diese Kennzahl liest sich jedes N wie eine Prävalenz — und ist keine."""
    sub = df[(df["qualitaet"] == "ok") & (df["autor"] != "")]
    if sub.empty:
        return {"verfuegbar": False}
    counts = sub["autor"].value_counts()
    n = int(counts.sum())
    top1 = int(counts.iloc[0])
    top10_share = float(counts.head(max(1, int(len(counts) * 0.1))).sum() / n)
    # Gini als Ungleichverteilungsmaß
    vals = sorted(counts.tolist())
    cum = 0.0
    for i, v in enumerate(vals, 1):
        cum += i * v
    gini = (2 * cum) / (len(vals) * sum(vals)) - (len(vals) + 1) / len(vals) if sum(vals) else 0.0
    return {
        "verfuegbar": True,
        "n_autoren": int(len(counts)),
        "beitraege_pro_autor": round(n / len(counts), 2),
        "top_autor_anteil": round(top1 / n, 3),
        "top10pct_anteil": round(top10_share, 3),
        "gini": round(float(gini), 3),
    }


# ============================================================
# PROMPTS
# ============================================================
SYSTEM_BASE = (
    "Du bist Senior-Analyst für Netnographie in der qualitativen Marktforschung. "
    "Du arbeitest präzise, wertfrei und ausschließlich am vorliegenden Material. "
    f"Alle Ausgaben in {OUTPUT_LANGUAGE}. "
    "Du erfindest niemals Inhalte, die nicht im Text stehen. "
    "Du gibst ausschließlich valides JSON zurück, ohne Markdown-Fences, ohne Vorrede."
)


def build_context_block(studienkontext: str, forschungsfragen: List[str]) -> str:
    parts = []
    if safe_str(studienkontext):
        parts.append(f"STUDIENKONTEXT:\n{safe_str(studienkontext)}")
    fq = [safe_str(f) for f in (forschungsfragen or []) if safe_str(f)]
    if fq:
        parts.append("FORSCHUNGSFRAGEN:\n" + "\n".join(f"- {f}" for f in fq))
    return "\n\n".join(parts)


def build_codebook_prompt(samples: List[Tuple[str, str]], kontext: str,
                          bestehend: List[dict], max_ober: int, max_sub: int) -> str:
    txt = "\n".join(f"[{cid}] {t[:1200]}" for cid, t in samples)
    bestehend_str = ""
    if bestehend:
        bestehend_str = ("\n\nBEREITS VORHANDENES CODEBUCH (nicht duplizieren, nur ERGÄNZEN, "
                         "wenn ein Thema wirklich neu ist):\n"
                         + json.dumps([{"obercode": o["obercode"],
                                        "subcodes": [s["subcode"] for s in o.get("subcodes", [])]}
                                       for o in bestehend], ensure_ascii=False))
    return f"""{kontext}

AUFGABE: Entwickle induktiv ein zweistufiges Themen-Codebuch aus den folgenden
Community-Beiträgen. Arbeite streng datengetrieben — leite die Themen aus dem
Material ab, nicht aus Allgemeinwissen über die Kategorie.

REGELN:
- Maximal {max_ober} Obercodes, je Obercode maximal {max_sub} Subcodes.
- Obercodes sind inhaltliche Themenfelder, KEINE Bewertungen ("Positiv"/"Negativ" verboten).
- Subcodes sind konkret und trennscharf; ein Subcode beschreibt genau EINEN Sachverhalt.
- Keine Catch-all-Codes wie "Sonstiges", "Allgemein", "Verschiedenes".
- Benenne so, wie die Community spricht, aber in sauberem {OUTPUT_LANGUAGE}.
- Für jeden Subcode: eine Definition (1 Satz) und 1–3 Beleg-IDs aus dem Material.
- Belege sind ausschließlich IDs in eckigen Klammern. Zitiere KEINEN Text.
{bestehend_str}

MATERIAL:
{txt}

AUSGABEFORMAT (nur JSON):
{{"codebuch":[{{"obercode":"...","definition":"...","subcodes":[
  {{"subcode":"...","definition":"...","belege":["K00012","K00034"]}}]}}]}}"""


def build_assign_prompt(items: List[Tuple[int, str]], codebuch: List[dict],
                        kontext: str, fragen: List[str], offen: bool) -> str:
    """items = [(1, text), (2, text), ...] mit LOKALEN Ganzzahl-IDs.

    Bewusst keine globalen IDs wie 'K00123' im Prompt: Modelle verschreiben sich
    bei langen alphanumerischen Schluesseln (K00123 -> K123, K0123, "12"), und
    jede verschriebene ID kostet einen kompletten Datensatz. Kleine Ganzzahlen
    pro Batch sind robust; das Ruecklinking macht das Tool.
    """
    cb_lines = []
    for o in codebuch:
        subs = o.get("subcodes", [])
        if subs:
            cb_lines.append(f"\n▸ Thema: {o['obercode']}")
            for sdef in subs:
                cb_lines.append(f"    • Subthema: {sdef['subcode']}")
        else:
            cb_lines.append(f"\n▸ Thema: {o['obercode']}  (keine Subthemen)")
    cb = "\n".join(cb_lines) if cb_lines else "(kein Codebuch — arbeite rein offen)"
    txt = "\n\n".join(f"[{i}] {t[:2500]}" for i, t in items)

    fragen_block = ""
    if fragen:
        fragen_block = ("\nFORSCHUNGSFRAGEN (pruefe je Beitrag, ob er eine davon beantwortet):\n"
                        + "\n".join(f"  F{i+1}: {f}" for i, f in enumerate(fragen)) + "\n")

    offen_block = ""
    if offen:
        offen_block = ('- "neue_themen": Themen, die im Beitrag klar vorkommen, aber im Codebuch '
                       'FEHLEN. Leere Liste, wenn nichts Neues. Sei streng: nur echte Luecken.\n')

    return f"""{kontext}

VERFUEGBARE THEMEN UND SUBTHEMEN:
{cb}
{fragen_block}
AUFGABE: Ordne JEDEM der folgenden nummerierten Beitraege die passenden Subthemen zu.

REGELN:
- Codiere jeden Beitrag einzeln und unabhaengig.
- Verwende Subthemen-Namen EXAKT so, wie sie oben stehen. Erfinde keine neuen.
- Mehrfachzuordnung erlaubt (1-4 Subthemen), wenn der Beitrag mehrere Themen anspricht.
- Ordne nichts zu, was nur implizit ist. Im Zweifel: leere Liste.
- "sentiment": positiv | negativ | ambivalent | neutral (Haltung zum Thema).
- "relevanz": 0 = irrelevant, 1 = am Rande, 2 = klar relevant, 3 = zentral.
- "beantwortet_fragen": Liste wie ["F1"], sonst leere Liste.
- "sprecherrolle": betroffen | interessent | experte | haendler | unklar
{offen_block}- Zitiere KEINEN Text. Gib nur Nummern und Codenamen zurueck.

Gib NUR JSON zurueck, keine Erklaerung, keine Markdown-Fences:
{{"ergebnisse":[{{"id":1,"subcodes":["..."],"sentiment":"negativ","relevanz":2,
"beantwortet_fragen":[],"sprecherrolle":"betroffen","neue_themen":[]}}]}}

WICHTIG: Gib fuer JEDE id genau ein Objekt zurueck — auch wenn nichts passt
(dann mit leerer subcodes-Liste). Erwartet werden {len(items)} Objekte
mit den ids {', '.join(str(i) for i, _ in items)}.

BEITRAEGE:
{txt}"""


def build_summary_prompt(thema: str, definition: str, beitraege: List[Tuple[str, str]],
                         kontext: str, n_kommentare: int, n_autoren: int,
                         n_communities: int) -> str:
    txt = "\n".join(f"[{cid}] {t[:900]}" for cid, t in beitraege)
    return f"""{kontext}

THEMA: {thema}
DEFINITION: {definition}
BASIS: {n_kommentare} Beiträge von {n_autoren} unterschiedlichen Autor:innen aus {n_communities} Community/Communities.

AUFGABE: Erstelle eine analytische Verdichtung zu diesem Thema.

REGELN:
- "summary": 4–7 Sätze. Was wird diskutiert, welche Positionen stehen sich gegenüber,
  welche Begründungen werden genannt? Benenne auch Minderheitspositionen.
- "key_insight": EIN Satz, der den nicht-offensichtlichen Kern trifft. Keine Zusammenfassung
  der Zusammenfassung, sondern die Erkenntnis, die eine Entscheidung beeinflussen würde.
- "spannungsfeld": der zentrale Widerspruch/Trade-off im Thema, in einem Satz. "" wenn keiner.
- "sprache_der_community": 3–8 typische Begriffe/Wendungen, die die Community selbst benutzt.
- "beleg_ids": 3–6 IDs, die die Aussagen tragen. NUR IDs, kein Zitattext.
- Keine Prozentangaben erfinden. Formuliere Häufigkeit qualitativ ("mehrheitlich", "vereinzelt").
- Wenn die Basis unter 5 Beiträgen liegt, beginne "summary" mit "Schmale Basis: ".

BEITRÄGE:
{txt}

AUSGABEFORMAT (nur JSON):
{{"summary":"...","key_insight":"...","spannungsfeld":"...",
"sprache_der_community":["..."],"beleg_ids":["K00012"]}}"""


def build_question_answer_prompt(frage: str, beitraege: List[Tuple[str, str]],
                                 kontext: str) -> str:
    txt = "\n".join(f"[{cid}] {t[:900]}" for cid, t in beitraege)
    return f"""{kontext}

FORSCHUNGSFRAGE: {frage}

AUFGABE: Beantworte diese Frage ausschließlich auf Basis der Beiträge.

REGELN:
- "antwort": 4–8 Sätze, differenziert, mit Gegenpositionen.
- "key_insight": ein Satz.
- "evidenzgrad": "stark" (viele unabhängige Beiträge, konsistent), "mittel", "schwach"
  (wenige Beiträge oder widersprüchlich) — begründe in "evidenz_begruendung".
- "offene_luecken": was die Frage NICHT beantwortet, weil das Material dazu schweigt.
- "beleg_ids": 3–6 IDs.
- Wenn das Material die Frage nicht beantwortet, sage das klar und setze evidenzgrad "schwach".

BEITRÄGE:
{txt}

AUSGABEFORMAT (nur JSON):
{{"antwort":"...","key_insight":"...","evidenzgrad":"mittel",
"evidenz_begruendung":"...","offene_luecken":"...","beleg_ids":["K00012"]}}"""


def build_merge_prompt(codebuch: List[dict], neue: List[str], max_ober: int) -> str:
    return f"""BESTEHENDES CODEBUCH:
{json.dumps([{'obercode': o['obercode'], 'subcodes': [s['subcode'] for s in o.get('subcodes', [])]} for o in codebuch], ensure_ascii=False)}

NEU VORGESCHLAGENE THEMEN (aus der Kodierung, mit Häufigkeit):
{json.dumps(neue, ensure_ascii=False)}

AUFGABE: Entscheide je Vorschlag, ob er (a) eine Dublette eines bestehenden Subcodes ist,
(b) als neuer Subcode unter einen bestehenden Obercode gehört, oder (c) einen neuen
Obercode rechtfertigt. Sei restriktiv: neue Obercodes nur, wenn wirklich ein eigenes
Themenfeld vorliegt. Maximal {max_ober} Obercodes insgesamt.

AUSGABEFORMAT (nur JSON):
{{"entscheidungen":[{{"vorschlag":"...","aktion":"dublette|neuer_subcode|neuer_obercode|verwerfen",
"ziel_obercode":"...","finaler_name":"..."}}]}}"""


# ============================================================
# CODEBUCH-LOGIK
# ============================================================
def normalize_code_name(name: str) -> str:
    n = norm_ws(name)
    n = re.sub(r"^[\-\*\u2022\d\.\)\s]+", "", n)
    n = re.sub(r"\s+", " ", n).strip(" .;:,")
    return n[:80]


def parse_codebook(resp: str) -> List[dict]:
    data = parse_json_loose(resp)
    if not isinstance(data, dict):
        return []
    out = []
    for o in data.get("codebuch", []) or []:
        if not isinstance(o, dict):
            continue
        oc = normalize_code_name(o.get("obercode", ""))
        if not oc or oc.lower() in ("sonstiges", "allgemein", "verschiedenes", "positiv", "negativ"):
            continue
        subs = []
        seen = set()
        for s in o.get("subcodes", []) or []:
            if isinstance(s, str):
                s = {"subcode": s}
            if not isinstance(s, dict):
                continue
            sc = normalize_code_name(s.get("subcode", ""))
            if not sc or sc.lower() in seen:
                continue
            seen.add(sc.lower())
            belege = [safe_str(b) for b in (s.get("belege") or []) if safe_str(b)]
            subs.append({"subcode": sc, "definition": norm_ws(s.get("definition", "")),
                         "belege": belege[:5]})
        if subs:
            out.append({"obercode": oc, "definition": norm_ws(o.get("definition", "")),
                        "subcodes": subs})
    return out


def merge_codebooks(base: List[dict], add: List[dict]) -> Tuple[List[dict], int]:
    """Deterministischer Merge über Namensgleichheit. Gibt (codebuch, n_neue_subcodes)."""
    by_ober = {o["obercode"].lower(): o for o in base}
    result = [dict(o, subcodes=list(o["subcodes"])) for o in base]
    idx = {o["obercode"].lower(): i for i, o in enumerate(result)}
    n_new = 0
    for o in add:
        k = o["obercode"].lower()
        if k not in idx:
            result.append({"obercode": o["obercode"], "definition": o.get("definition", ""),
                           "subcodes": list(o["subcodes"])})
            idx[k] = len(result) - 1
            n_new += len(o["subcodes"])
            continue
        tgt = result[idx[k]]
        have = {s["subcode"].lower() for s in tgt["subcodes"]}
        for s in o["subcodes"]:
            if s["subcode"].lower() not in have:
                tgt["subcodes"].append(s)
                have.add(s["subcode"].lower())
                n_new += 1
    return result, n_new


def flatten_subcodes(codebuch: List[dict]) -> List[str]:
    return [s["subcode"] for o in codebuch for s in o.get("subcodes", [])]


def sub_to_ober(codebuch: List[dict]) -> Dict[str, str]:
    return {s["subcode"].lower(): o["obercode"]
            for o in codebuch for s in o.get("subcodes", [])}


def _norm_code(c: str) -> str:
    """Normalisiert einen Codenamen fuer das Matching.

    Trenn- und Bindezeichen werden zu Leerzeichen: eine Modellantwort
    'Bedienung, insbesondere Lenkrad' matcht damit weiter auf den
    Codebuch-Eintrag 'Bedienung – insbesondere Lenkrad'. Ohne diese
    Normalisierung landet ein sachlich richtiger Code im Halluzinations-Log.
    """
    x = safe_str(c).lower().strip()
    x = re.sub(r"[,;|\-–—/]+", " ", x)
    x = re.sub(r"^[\d\.\)\s•▸\*]+", "", x)
    return re.sub(r"\s+", " ", x).strip()


def build_code_lookup(codes: List[str]) -> Dict[str, str]:
    lut = {}
    for c in codes:
        for key in (c.lower().strip(), norm_key(c), _norm_code(c)):
            lut.setdefault(key, c)
    return lut


def match_code(raw: str, lut: Dict[str, str], allowed: List[str]) -> Optional[str]:
    """Exaktes bzw. normalisiertes Matching. Kein Fuzzy-Raten:
    ein frei erfundener Code darf nicht auf einen echten umgebogen werden.
    Toleriert werden nur Schreibvarianten (Gross/Klein, Trennzeichen,
    Aufzaehlungspraefixe), nicht abweichende Bedeutungen."""
    r = safe_str(raw)
    if not r:
        return None
    if r in allowed:
        return r
    for key in (r.lower().strip(), norm_key(r), _norm_code(r)):
        if key in lut:
            return lut[key]
    return None


# ============================================================
# ANALYSE-ENGINE
# ============================================================
class RunLog:
    """Sammelt Fail-Loud-Ereignisse. Wird als eigenes Excel-Sheet exportiert;
    ein Lauf ohne Blick in dieses Log gilt als nicht geprüft."""

    def __init__(self):
        self.events: List[dict] = []
        self.tokens = 0
        self.cost = 0.0
        self.calls = 0
        self.cache_hits = 0

    def add(self, stufe: str, art: str, detail: str, bezug: str = ""):
        self.events.append({"zeitpunkt": datetime.now().strftime("%H:%M:%S"),
                            "stufe": stufe, "art": art, "bezug": bezug,
                            "detail": safe_str(detail)[:800]})

    def account(self, tokens: int, cost: float, cached: bool):
        self.calls += 1
        if cached:
            self.cache_hits += 1
        self.tokens += int(tokens)
        self.cost += float(cost)

    # Nicht jedes Ereignis ist gleich schwer. Ein verworfener Codename ist Rauschen,
    # ein nicht kodierter Beitrag ist eine Luecke im Ergebnis. Wer beides in einen
    # Zaehler wirft, erzeugt Alarmmuedigkeit — und dann wird auch das Echte ignoriert.
    BLOCKING = ("PARSE_ERROR", "API_ERROR", "TRUNCATED", "ALARM")
    REVIEW = ("HALLUZINATION", "WARNUNG")

    @property
    def n_errors(self) -> int:
        return sum(1 for e in self.events if e["art"] in self.BLOCKING)

    @property
    def n_reviews(self) -> int:
        return sum(1 for e in self.events if e["art"] in self.REVIEW)

    def diagnose(self) -> List[dict]:
        """Uebersetzt Log-Ereignisse in konkrete Handlungsanweisungen."""
        hints = {
            "API_ERROR": ("Die Schnittstelle hat Anfragen abgelehnt.",
                          "Meist Rate-Limit oder Timeout: parallele Threads reduzieren "
                          "(Schritt 4 → Tempo) und Lauf wiederholen. Bereits berechnete "
                          "Prompts kommen aus dem Cache und kosten nichts."),
            "TRUNCATED": ("Antworten wurden vom Modell abgeschnitten.",
                          "Kommentare je LLM-Call verkleinern (Schritt 4 → Tempo, z. B. auf 6). "
                          "Bei Einzelbeitraegen: der Beitrag selbst ist zu lang."),
            "PARSE_ERROR": ("Beitraege ohne gueltige Kodierung.",
                            "Batchgroesse senken und Lauf wiederholen. Bleibt es dabei, "
                            "ist das Codebuch vermutlich zu gross oder zu unscharf — "
                            "Anzahl Subthemen in Schritt 4 reduzieren."),
            "ALARM": ("Der Anteil unkodierter Beitraege ist zu hoch.",
                      "Ergebnis nicht weitergeben, bevor die Ursache geklaert ist."),
            "HALLUZINATION": ("Das Modell hat Codenamen ausserhalb des Codebuchs genannt.",
                              "Wurden verworfen, nicht umgebogen. Bei vielen Treffern: die "
                              "genannten Themen fehlen dem Codebuch — Tab 'Neu entdeckt' pruefen."),
            "WARNUNG": ("Auffaelligkeiten, die eine Sichtpruefung verdienen.",
                        "Stichprobe im Tab 'Themen' gegen die Originalbeitraege lesen."),
        }
        counts = Counter(e["art"] for e in self.events)
        out = []
        for art, n in counts.most_common():
            if art == "INFO":
                continue
            beispiel = next((e["detail"] for e in self.events if e["art"] == art), "")
            was, tun = hints.get(art, ("Unbekanntes Ereignis.", "Log pruefen."))
            out.append({"art": art, "anzahl": n, "schwere":
                        "blockierend" if art in self.BLOCKING else "pruefen",
                        "bedeutung": was, "empfehlung": tun, "beispiel": beispiel[:220]})
        return out

    def to_df(self) -> pd.DataFrame:
        return pd.DataFrame(self.events) if self.events else pd.DataFrame(
            columns=["zeitpunkt", "stufe", "art", "bezug", "detail"])


def stratified_sample(df: pd.DataFrame, n: int, seed: int = 42) -> pd.DataFrame:
    """Proportional über Communities schichten und innerhalb nach Länge streuen —
    sonst dominiert die größte Datei das induktive Codebuch."""
    sub = df[df["qualitaet"] == "ok"]
    if sub.empty:
        return sub
    if len(sub) <= n:
        return sub
    rng = random.Random(seed)
    groups = list(sub.groupby("community", sort=True))
    per = max(1, n // max(1, len(groups)))
    picked = []
    for _, g in groups:
        g = g.sort_values("zeichen", ascending=False)
        # aus kurzen, mittleren und langen Beiträgen gleichermaßen ziehen
        thirds = [g.iloc[: len(g) // 3 or 1], g.iloc[len(g) // 3: 2 * len(g) // 3 or 1],
                  g.iloc[2 * len(g) // 3:]]
        take_each = max(1, per // 3)
        for t in thirds:
            if len(t) == 0:
                continue
            idx = rng.sample(list(t.index), min(take_each, len(t)))
            picked.extend(idx)
    picked = list(dict.fromkeys(picked))[:n]
    if len(picked) < n:
        rest = [i for i in sub.index if i not in set(picked)]
        picked += rng.sample(rest, min(n - len(picked), len(rest)))
    return sub.loc[picked]


def induce_codebook(df: pd.DataFrame, kontext: str, cfg: dict, log: RunLog,
                    rounds: int = CODEBOOK_ROUNDS, sample_size: int = CODEBOOK_SAMPLE_SIZE,
                    max_ober: int = 8, max_sub: int = 6, seed_codebook: List[dict] = None,
                    use_cache: bool = True, progress: Callable = None) -> Tuple[List[dict], List[dict]]:
    """Induktives Codebuch mit Sättigungsprüfung.
    Rückgabe: (codebuch, saettigungs_verlauf)"""
    codebuch = list(seed_codebook or [])
    verlauf = []
    for r in range(rounds):
        smp = stratified_sample(df, sample_size, seed=100 + r * 7)
        if smp.empty:
            break
        samples = [(row["kommentar_id"], row["text"]) for _, row in smp.iterrows()]
        prompt = build_codebook_prompt(samples, kontext, codebuch, max_ober, max_sub)

        def _valid(t):
            return bool(parse_codebook(t))

        try:
            txt, tok, cost, finish, cached = call_llm_cached(
                prompt, SYSTEM_BASE, max_tokens=2600, temperature=0.15,
                llm_cfg=cfg, validate=_valid, use_cache=use_cache)
            log.account(tok, cost, cached)
        except Exception as e:
            log.add("Codebuch", "API_ERROR", str(e), f"Runde {r+1}")
            break

        if finish == "length":
            log.add("Codebuch", "TRUNCATED", "Antwort abgeschnitten — Runde verworfen", f"Runde {r+1}")
            continue

        neu = parse_codebook(txt)
        if not neu:
            log.add("Codebuch", "PARSE_ERROR", f"Unparsbare Antwort: {txt[:250]}", f"Runde {r+1}")
            continue

        codebuch, n_new = merge_codebooks(codebuch, neu)
        total = len(flatten_subcodes(codebuch))
        verlauf.append({"runde": r + 1, "stichprobe": len(samples),
                        "neue_subcodes": n_new, "subcodes_gesamt": total,
                        "zuwachs": round(n_new / total, 3) if total else 0.0})
        if progress:
            progress(r + 1, rounds, f"Runde {r+1}: +{n_new} Subcodes (gesamt {total})")

        if r >= 1 and total and (n_new / total) < 0.05:
            log.add("Codebuch", "INFO", f"Sättigung erreicht nach Runde {r+1} "
                                        f"(Zuwachs {n_new/total:.1%})")
            break

    if verlauf and verlauf[-1]["zuwachs"] >= 0.10:
        log.add("Codebuch", "WARNUNG",
                f"Sättigung NICHT erreicht — letzte Runde brachte noch "
                f"{verlauf[-1]['zuwachs']:.0%} neue Subcodes. Mehr Runden oder mehr Material nötig.",
                "Sättigung")
    return codebuch, verlauf


def _coerce_int_id(v) -> Optional[int]:
    """Modelle liefern ids als 1, "1", "[1]", "Beitrag 1", "id_1". Alle gleich behandeln."""
    if isinstance(v, bool):
        return None
    if isinstance(v, int):
        return v
    m = re.search(r"\d+", safe_str(v))
    return int(m.group(0)) if m else None


def _extract_result_list(data) -> List[dict]:
    """Akzeptiert die ueblichen Wrapper-Varianten statt nur eine zu erlauben."""
    if isinstance(data, list):
        return [x for x in data if isinstance(x, dict)]
    if not isinstance(data, dict):
        return []
    for key in ("ergebnisse", "results", "antworten", "answers", "items", "data"):
        v = data.get(key)
        if isinstance(v, list):
            return [x for x in v if isinstance(x, dict)]
    # Einzelobjekt ohne Wrapper
    if "id" in data or "subcodes" in data:
        return [data]
    return []


def _parse_assign(txt: str, local_ids: List[int], allowed: List[str],
                  lut: Dict[str, str], log: RunLog,
                  bezug: str = "") -> Tuple[Dict[int, dict], int]:
    """Parst eine Batch-Antwort. Rueckgabe: ({lokale_id: eintrag}, n_verworfene_codes).

    Fehlende ids werden hier NICHT mit Platzhaltern aufgefuellt — sie gehen in
    den Reparatur-Pass. Ein stiller Platzhalter waere von einer echten Kodierung
    im Export nicht mehr unterscheidbar.
    """
    data = parse_json_loose(txt)
    raw_items = _extract_result_list(data)
    if not raw_items:
        log.add("Kodierung", "PARSE_ERROR",
                f"Antwort ohne verwertbare Ergebnisliste. Rohantwort: {safe_str(txt)[:300]}",
                bezug)
        return {}, 0

    id_set = set(local_ids)
    out: Dict[int, dict] = {}
    dropped_codes = 0
    unmatched_ids = 0

    def build_entry(item: dict) -> dict:
        codes, dropped = [], []
        for raw in (item.get("subcodes") or item.get("codes") or []):
            if isinstance(raw, dict):
                raw = raw.get("subcode") or raw.get("code") or raw.get("name") or ""
            m = match_code(safe_str(raw), lut, allowed)
            if m:
                if m not in codes:
                    codes.append(m)
            elif safe_str(raw):
                dropped.append(safe_str(raw))
        sent = safe_str(item.get("sentiment")).lower()
        sent = sent if sent in ("positiv", "negativ", "ambivalent", "neutral") else "neutral"
        try:
            rel = int(float(item.get("relevanz", item.get("relevance", 0))))
        except Exception:
            rel = 0
        rolle = safe_str(item.get("sprecherrolle")).lower()
        rolle = rolle if rolle in ("betroffen", "interessent", "experte", "haendler") else "unklar"
        return {"subcodes": codes, "sentiment": sent, "relevanz": max(0, min(3, rel)),
                "beantwortet_fragen": [safe_str(f).upper() for f in
                                       (item.get("beantwortet_fragen") or []) if safe_str(f)],
                "sprecherrolle": rolle,
                "neue_themen": [normalize_code_name(t) for t in
                                (item.get("neue_themen") or []) if safe_str(t)][:4],
                "status": "ok", "_dropped": dropped}

    for item in raw_items:
        lid = _coerce_int_id(item.get("id", item.get("nr", item.get("nummer"))))
        if lid is None or lid not in id_set:
            unmatched_ids += 1
            continue
        e = build_entry(item)
        dropped_codes += len(e.pop("_dropped"))
        out[lid] = e

    # Positionsbasierte Rettung: das Modell hat die richtige ANZAHL Objekte in der
    # richtigen Reihenfolge geliefert, nur die ids verschrieben. Dann ist die
    # Zuordnung ueber die Position eindeutig — aber sie wird protokolliert.
    if not out and len(raw_items) == len(local_ids):
        for pos, item in enumerate(raw_items):
            e = build_entry(item)
            dropped_codes += len(e.pop("_dropped"))
            e["status"] = "ok_positionsmatch"
            out[local_ids[pos]] = e
        log.add("Kodierung", "WARNUNG",
                f"IDs unbrauchbar, aber Anzahl und Reihenfolge stimmen "
                f"({len(raw_items)}) — positionsbasiert zugeordnet.", bezug)
    elif unmatched_ids:
        log.add("Kodierung", "WARNUNG",
                f"{unmatched_ids} Ergebnisobjekt(e) mit unbekannter id verworfen.", bezug)

    if dropped_codes:
        log.add("Kodierung", "HALLUZINATION",
                f"{dropped_codes} Codenamen nicht im Codebuch — verworfen statt umgebogen.",
                bezug)
    return out, dropped_codes


def _empty_record(cid: str, status: str) -> dict:
    return {"kommentar_id": cid, "subcodes": [], "sentiment": "neutral", "relevanz": 0,
            "beantwortet_fragen": [], "sprecherrolle": "unklar", "neue_themen": [],
            "status": status}


def assign_codes(df: pd.DataFrame, codebuch: List[dict], kontext: str, fragen: List[str],
                 cfg: dict, log: RunLog, offen: bool = True,
                 batch_size: int = ASSIGN_BATCH_SIZE, workers: int = MAX_WORKERS_DEFAULT,
                 use_cache: bool = True, repair: bool = True,
                 progress: Callable = None) -> pd.DataFrame:
    """Batch-Kodierung in drei Stufen — dieselbe Mechanik wie im Coding-Tool:

      1. Batch-Pass    : viele Beitraege pro Call (guenstig)
      2. Auto-Split    : abgeschnittene Antworten werden halbiert und wiederholt,
                         statt den ganzen Batch zu verlieren
      3. Reparatur-Pass: was danach fehlt, wird EINZELN nachkodiert

    Erst was auch die Einzelkodierung nicht loest, wird als PARSE_ERROR gefuehrt.
    Vollstaendigkeitsgarantie: jede Eingabe-ID erscheint in der Ausgabe.
    """
    work = df[df["qualitaet"] == "ok"]
    cols = ["kommentar_id", "subcodes", "sentiment", "relevanz", "beantwortet_fragen",
            "sprecherrolle", "neue_themen", "status"]
    if work.empty:
        return pd.DataFrame(columns=cols)

    allowed = flatten_subcodes(codebuch)
    lut = build_code_lookup(allowed)
    texts = dict(zip(work["kommentar_id"], work["text"]))
    all_ids = list(work["kommentar_id"])

    def run_chunk(chunk_ids: List[str], depth: int = 0) -> Dict[str, dict]:
        """Kodiert eine Liste von Kommentar-IDs. Halbiert sich bei Truncation selbst."""
        if not chunk_ids:
            return {}
        items = [(i + 1, texts[cid]) for i, cid in enumerate(chunk_ids)]
        local_ids = [i for i, _ in items]
        bezug = f"{chunk_ids[0]}…{chunk_ids[-1]} ({len(chunk_ids)})"
        prompt = build_assign_prompt(items, codebuch, kontext, fragen, offen)
        # Budget grosszuegig, aber gedeckelt: 200 Token je Beitrag reichen fuer
        # 4 Subcodes + Metafelder; der Deckel verhindert API-Fehler bei Grossbatches.
        max_tok = min(400 + 200 * len(items), 6000)

        def _valid(t):
            d = parse_json_loose(t)
            return len(_extract_result_list(d)) >= max(1, len(local_ids) // 2)

        try:
            txt, tok, cost, finish, cached = call_llm_cached(
                prompt, SYSTEM_BASE, max_tokens=max_tok, temperature=0.0,
                llm_cfg=cfg, validate=_valid, use_cache=use_cache)
            log.account(tok, cost, cached)
        except Exception as e:
            log.add("Kodierung", "API_ERROR", str(e)[:400], bezug)
            return {}

        if finish == "length":
            if len(chunk_ids) > 1 and depth < 3:
                log.add("Kodierung", "INFO",
                        f"Antwort abgeschnitten — Batch wird halbiert ({len(chunk_ids)} → "
                        f"{len(chunk_ids)//2}+{len(chunk_ids)-len(chunk_ids)//2}).", bezug)
                mid = len(chunk_ids) // 2
                res = run_chunk(chunk_ids[:mid], depth + 1)
                res.update(run_chunk(chunk_ids[mid:], depth + 1))
                return res
            log.add("Kodierung", "TRUNCATED",
                    "Antwort abgeschnitten, auch als Einzelcall. Beitrag evtl. zu lang.", bezug)
            return {}

        parsed, _ = _parse_assign(txt, local_ids, allowed, lut, log, bezug)
        return {chunk_ids[lid - 1]: rec for lid, rec in parsed.items()
                if 1 <= lid <= len(chunk_ids)}

    # ── Stufe 1+2: Batches parallel ─────────────────────────────────────────
    batches = [all_ids[i:i + batch_size] for i in range(0, len(all_ids), batch_size)]
    results: Dict[str, dict] = {}
    done = 0
    with ThreadPoolExecutor(max_workers=max(1, workers)) as pool:
        futs = {pool.submit(run_chunk, b): b for b in batches}
        for fut in as_completed(futs):
            try:
                results.update(fut.result())
            except Exception as e:
                log.add("Kodierung", "API_ERROR", f"Batch abgestuerzt: {e}", "")
            done += len(futs[fut])
            if progress:
                progress(done, len(all_ids), f"{done}/{len(all_ids)} Beitraege kodiert")

    # ── Stufe 3: Reparatur-Pass (Einzelkodierung) ───────────────────────────
    missing = [cid for cid in all_ids if cid not in results]
    n_repaired = 0
    if missing and repair:
        log.add("Kodierung", "INFO",
                f"Reparatur-Pass: {len(missing)} Beitraege werden einzeln nachkodiert.",
                "Reparatur")
        if progress:
            progress(len(all_ids), len(all_ids),
                     f"Reparatur-Pass: {len(missing)} Beitraege einzeln …")
        with ThreadPoolExecutor(max_workers=max(1, workers)) as pool:
            futs = {pool.submit(run_chunk, [cid]): cid for cid in missing}
            for fut in as_completed(futs):
                try:
                    got = fut.result()
                except Exception:
                    got = {}
                if got:
                    n_repaired += len(got)
                    results.update(got)
        if n_repaired:
            log.add("Kodierung", "INFO",
                    f"Reparatur-Pass erfolgreich fuer {n_repaired} von {len(missing)} "
                    f"Beitraegen.", "Reparatur")

    # ── Ergebnis zusammenbauen, Fail Loud fuer den Rest ─────────────────────
    rows = []
    for cid in all_ids:
        rec = results.get(cid)
        if rec is None:
            rows.append(_empty_record(cid, "PARSE_ERROR"))
            log.add("Kodierung", "PARSE_ERROR",
                    "Keine gueltige Kodierung — auch Einzelkodierung fehlgeschlagen.", cid)
        else:
            rows.append({"kommentar_id": cid, **{k: rec[k] for k in
                        ("subcodes", "sentiment", "relevanz", "beantwortet_fragen",
                         "sprecherrolle", "neue_themen", "status")}})

    out = pd.DataFrame(rows, columns=cols)
    n_err = int((out["status"] == "PARSE_ERROR").sum())
    n_pos = int((out["status"] == "ok_positionsmatch").sum())
    if n_pos:
        log.add("Kodierung", "WARNUNG",
                f"{n_pos} Beitraege wurden ueber die Position statt ueber die id "
                f"zugeordnet. Stichprobe pruefen.", "Gesamt")
    if n_err:
        quote = n_err / max(1, len(out))
        art = "ALARM" if quote > 0.05 else "WARNUNG"
        log.add("Kodierung", art,
                f"{n_err} von {len(out)} Beitraegen ohne gueltige Kodierung ({quote:.1%}). "
                f"Ergebnis ist unvollstaendig.", "Gesamt")
    return out


# ============================================================
# AGGREGATION
# ============================================================
def explode_codes(corpus: pd.DataFrame, coded: pd.DataFrame,
                  codebuch: List[dict]) -> pd.DataFrame:
    """Long-Format: 1 Zeile = 1 Kommentar × 1 Subcode. Basis für alle Häufigkeiten."""
    s2o = sub_to_ober(codebuch)
    merged = corpus.merge(coded, on="kommentar_id", how="left", suffixes=("", "_c"))
    rows = []
    for r in merged.itertuples(index=False):
        subs = getattr(r, "subcodes", None)
        if not isinstance(subs, list) or not subs:
            continue
        for sc in subs:
            rows.append({
                "kommentar_id": r.kommentar_id, "datei": r.datei, "community": r.community,
                "plattform": r.plattform, "thread_titel": r.thread_titel, "url": r.url,
                "autor": r.autor, "autor_pseudonym": r.autor_pseudonym, "datum": r.datum,
                "sprache": r.sprache, "obercode": s2o.get(sc.lower(), "Unzugeordnet"),
                "subcode": sc, "sentiment": getattr(r, "sentiment", "neutral"),
                "relevanz": getattr(r, "relevanz", 0),
                "sprecherrolle": getattr(r, "sprecherrolle", "unklar"),
                "text": r.text,
            })
    return pd.DataFrame(rows) if rows else pd.DataFrame(columns=[
        "kommentar_id", "datei", "community", "plattform", "thread_titel", "url", "autor",
        "autor_pseudonym", "datum", "sprache", "obercode", "subcode", "sentiment",
        "relevanz", "sprecherrolle", "text"])


def frequency_table(long_df: pd.DataFrame, corpus: pd.DataFrame,
                    level: str = "subcode") -> pd.DataFrame:
    """Häufigkeiten auf drei Basen zugleich: Kommentare, Autoren, Threads.
    Bewusst nebeneinander — eine Zahl allein lädt zur Fehlinterpretation ein."""
    base_n = int((corpus["qualitaet"] == "ok").sum())
    base_autoren = int(corpus.loc[(corpus["qualitaet"] == "ok") & (corpus["autor"] != ""),
                                  "autor"].nunique())
    base_threads = int(corpus.loc[corpus["qualitaet"] == "ok", "datei"].nunique())
    if long_df.empty:
        return pd.DataFrame(columns=["ebene", "obercode", "subcode", "n_kommentare",
                                     "anteil_kommentare", "n_autoren", "anteil_autoren",
                                     "n_threads", "n_communities", "sentiment_pos",
                                     "sentiment_neg", "sentiment_amb", "netto_sentiment"])
    keys = ["obercode"] if level == "obercode" else ["obercode", "subcode"]
    rows = []
    for key, g in long_df.groupby(keys, sort=False):
        key = key if isinstance(key, tuple) else (key,)
        n_k = g["kommentar_id"].nunique()
        n_a = g.loc[g["autor"] != "", "autor"].nunique()
        pos = int((g["sentiment"] == "positiv").sum())
        neg = int((g["sentiment"] == "negativ").sum())
        amb = int((g["sentiment"] == "ambivalent").sum())
        rows.append({
            "ebene": level,
            "obercode": key[0],
            "subcode": key[1] if len(key) > 1 else "",
            "n_kommentare": n_k,
            "anteil_kommentare": round(n_k / base_n, 4) if base_n else 0.0,
            "n_autoren": n_a,
            "anteil_autoren": round(n_a / base_autoren, 4) if base_autoren else 0.0,
            "n_threads": g["datei"].nunique(),
            "n_communities": g["community"].nunique(),
            "sentiment_pos": pos, "sentiment_neg": neg, "sentiment_amb": amb,
            "netto_sentiment": round((pos - neg) / max(1, n_k), 3),
        })
    out = pd.DataFrame(rows).sort_values(["n_kommentare"], ascending=False)
    out.attrs["basis_kommentare"] = base_n
    out.attrs["basis_autoren"] = base_autoren
    out.attrs["basis_threads"] = base_threads
    return out.reset_index(drop=True)


def split_table(long_df: pd.DataFrame, corpus: pd.DataFrame, split_col: str,
                level: str = "subcode") -> pd.DataFrame:
    """Kreuztabelle Thema × Splitvariable, mit Basis-N je Spalte."""
    if long_df.empty or split_col not in long_df.columns:
        return pd.DataFrame()
    ok = corpus[corpus["qualitaet"] == "ok"]
    if split_col in ok.columns:
        # Basis aus dem Gesamtkorpus: auch Kommentare ohne Code zaehlen zur Basis
        bases = ok.groupby(split_col)["kommentar_id"].nunique().to_dict()
    else:
        # Splitvariable entsteht erst bei der Kodierung (z. B. sprecherrolle, obercode).
        # Dann ist die Basis die Zahl der kodierten Kommentare je Auspraegung.
        bases = long_df.groupby(split_col)["kommentar_id"].nunique().to_dict()
    keys = ["obercode"] if level == "obercode" else ["obercode", "subcode"]
    piv = (long_df.groupby(keys + [split_col])["kommentar_id"].nunique()
           .unstack(fill_value=0))
    piv = piv.reset_index()
    # Basiszeile ergänzen — ohne Basis ist jede Spalte unlesbar
    base_row = {k: ("BASIS (n Kommentare)" if i == 0 else "") for i, k in enumerate(keys)}
    for c in piv.columns:
        if c not in keys:
            base_row[c] = int(bases.get(c, 0))
    out = pd.concat([pd.DataFrame([base_row]), piv], ignore_index=True)
    return out


def summarize_themes(long_df: pd.DataFrame, codebuch: List[dict], kontext: str,
                     cfg: dict, log: RunLog, level: str = "obercode",
                     max_quotes: int = 26, min_n: int = 2, workers: int = 4,
                     use_cache: bool = True, progress: Callable = None) -> Dict[str, dict]:
    """Summary + Key Insight je Thema. Belege sind IDs; die Zitattexte werden
    vom Tool aus dem Korpus rekonstruiert — das Modell schreibt sie nie selbst."""
    if long_df.empty:
        return {}
    defs = {}
    for o in codebuch:
        defs[o["obercode"]] = o.get("definition", "")
        for s in o.get("subcodes", []):
            defs[s["subcode"]] = s.get("definition", "")

    groups = [(k, g) for k, g in long_df.groupby(level, sort=False)
              if g["kommentar_id"].nunique() >= min_n]
    out: Dict[str, dict] = {}
    id2text = dict(zip(long_df["kommentar_id"], long_df["text"]))

    def run(item):
        thema, g = item
        uniq = g.drop_duplicates("kommentar_id").sort_values("relevanz", ascending=False)
        beitraege = [(r.kommentar_id, r.text) for r in uniq.head(max_quotes).itertuples(index=False)]
        prompt = build_summary_prompt(
            thema, defs.get(thema, ""), beitraege, kontext,
            uniq["kommentar_id"].nunique(),
            uniq.loc[uniq["autor"] != "", "autor"].nunique(),
            uniq["community"].nunique())

        def _valid(t):
            d = parse_json_loose(t)
            return isinstance(d, dict) and bool(safe_str(d.get("summary")))

        try:
            txt, tok, cost, finish, cached = call_llm_cached(
                prompt, SYSTEM_BASE, max_tokens=1100, temperature=0.2,
                llm_cfg=cfg, validate=_valid, use_cache=use_cache)
        except Exception as e:
            return thema, None, 0, 0.0, False, f"API_ERROR:{e}"
        if finish == "length":
            return thema, None, tok, cost, cached, "TRUNCATED"
        d = parse_json_loose(txt)
        if not isinstance(d, dict):
            return thema, None, tok, cost, cached, f"PARSE_ERROR:{txt[:200]}"
        return thema, d, tok, cost, cached, ""

    done = 0
    with ThreadPoolExecutor(max_workers=max(1, workers)) as pool:
        futs = [pool.submit(run, it) for it in groups]
        for fut in as_completed(futs):
            thema, d, tok, cost, cached, err = fut.result()
            log.account(tok, cost, cached)
            done += 1
            if progress:
                progress(done, len(groups), f"{done}/{len(groups)} Themen verdichtet")
            if err:
                log.add("Summary", err.split(":")[0], err, thema)
                out[thema] = {"summary": "", "key_insight": "", "spannungsfeld": "",
                              "sprache_der_community": [], "belege": [],
                              "status": err.split(":")[0]}
                continue
            belege = []
            for bid in (d.get("beleg_ids") or [])[:8]:
                bid = safe_str(bid)
                if bid in id2text:
                    belege.append({"id": bid, "text": id2text[bid]})
                else:
                    log.add("Summary", "WARNUNG",
                            f"Beleg-ID '{bid}' existiert nicht — Beleg verworfen, "
                            f"Summary bleibt gueltig", thema)
            out[thema] = {
                "summary": norm_ws(d.get("summary", "")),
                "key_insight": norm_ws(d.get("key_insight", "")),
                "spannungsfeld": norm_ws(d.get("spannungsfeld", "")),
                "sprache_der_community": [norm_ws(x) for x in (d.get("sprache_der_community") or [])][:8],
                "belege": belege,
                "status": "ok",
            }
    return out


def answer_questions(long_df: pd.DataFrame, corpus: pd.DataFrame, coded: pd.DataFrame,
                     fragen: List[str], kontext: str, cfg: dict, log: RunLog,
                     max_quotes: int = 30, use_cache: bool = True) -> List[dict]:
    """Beantwortet jede Forschungsfrage aus den Beiträgen, die ihr zugeordnet wurden."""
    if not fragen:
        return []
    out = []
    id2text = dict(zip(corpus["kommentar_id"], corpus["text"]))
    for i, frage in enumerate(fragen):
        tag = f"F{i+1}"
        hits = coded[coded["beantwortet_fragen"].apply(
            lambda x: isinstance(x, list) and tag in x)]["kommentar_id"].tolist()
        if not hits:
            out.append({"frage": frage, "tag": tag, "n": 0, "antwort": "",
                        "key_insight": "", "evidenzgrad": "keine",
                        "evidenz_begruendung": "Kein Beitrag wurde dieser Frage zugeordnet.",
                        "offene_luecken": "Das Material adressiert diese Frage nicht.",
                        "belege": [], "status": "leer"})
            log.add("Fragen", "WARNUNG", f"{tag} ohne zugeordnete Beiträge", frage[:80])
            continue
        beitraege = [(h, id2text.get(h, "")) for h in hits[:max_quotes]]
        prompt = build_question_answer_prompt(frage, beitraege, kontext)

        def _valid(t):
            d = parse_json_loose(t)
            return isinstance(d, dict) and bool(safe_str(d.get("antwort")))

        try:
            txt, tok, cost, finish, cached = call_llm_cached(
                prompt, SYSTEM_BASE, max_tokens=1200, temperature=0.2,
                llm_cfg=cfg, validate=_valid, use_cache=use_cache)
            log.account(tok, cost, cached)
        except Exception as e:
            log.add("Fragen", "API_ERROR", str(e), tag)
            continue
        if finish == "length":
            log.add("Fragen", "TRUNCATED", "Antwort abgeschnitten", tag)
            continue
        d = parse_json_loose(txt) or {}
        belege = [{"id": b, "text": id2text[b]} for b in (d.get("beleg_ids") or [])
                  if safe_str(b) in id2text][:8]
        out.append({
            "frage": frage, "tag": tag, "n": len(hits),
            "antwort": norm_ws(d.get("antwort", "")),
            "key_insight": norm_ws(d.get("key_insight", "")),
            "evidenzgrad": safe_str(d.get("evidenzgrad")) or "unklar",
            "evidenz_begruendung": norm_ws(d.get("evidenz_begruendung", "")),
            "offene_luecken": norm_ws(d.get("offene_luecken", "")),
            "belege": belege, "status": "ok",
        })
    return out


def beschreibe_erhebung(file_results: List[dict]) -> str:
    """Formuliert den Erhebungsweg fuer den Methodensteckbrief aus den Fakten.

    Der Satz darf nicht fest verdrahtet sein: sobald eine Seite automatisch
    abgerufen wurde, stimmt 'manuelle Sammlung' nicht mehr — und genau dieser
    Satz ist es, den ein Kunde oder eine Rechtsabteilung nachliest.
    """
    c = Counter(safe_str(f.get("quelle")) or "manuell" for f in (file_results or []))
    n_manuell = sum(v for k, v in c.items() if not k.startswith("URL"))
    n_abruf = sum(v for k, v in c.items() if k.startswith("URL"))
    teile = []
    if n_manuell:
        teile.append(f"{n_manuell} Seite(n) manuell im Browser geöffnet und als "
                     f"HTML/MHTML gespeichert (gerendertes DOM)")
    if n_abruf:
        teile.append(f"{n_abruf} Seite(n) automatisiert per HTTP-GET abgerufen "
                     f"(robots.txt geprüft, Rohdaten lokal archiviert)")
    if not teile:
        return "Keine Quellen erfasst."
    return ("Öffentlich zugängliche Community-Seiten: " + "; ".join(teile)
            + ". Keine Login-Bereiche, keine automatisierte Massenerhebung.")


def source_register(corpus: pd.DataFrame, file_results: List[dict]) -> pd.DataFrame:
    """Quellenregister — Pflichtbestandteil jeder netnographischen Dokumentation."""
    rows = []
    for fr in file_results:
        ex = fr.get("extraction") or {}
        name = safe_str(fr.get("name"))
        sub = corpus[corpus["datei"] == name]
        ok = sub[sub["qualitaet"] == "ok"]
        dates = [d for d in ok["datum"].tolist() if d]
        rows.append({
            "datei": name,
            "community": safe_str(fr.get("community")),
            "plattform": safe_str(fr.get("plattform") or ex.get("platform")),
            "thread_titel": safe_str(fr.get("thread_titel") or ex.get("thread_title")),
            "url": safe_str(fr.get("url") or ex.get("url")),
            "erhebungsweg": safe_str(fr.get("quelle")) or "manuell",
            "lokales_archiv": safe_str(fr.get("archiv")),
            "abrufdatum": safe_str(fr.get("abrufdatum")),
            "n_extrahiert": len(sub),
            "n_analysiert": len(ok),
            "n_autoren": int(ok.loc[ok["autor"] != "", "autor"].nunique()),
            "zeitraum_von": min(dates) if dates else "",
            "zeitraum_bis": max(dates) if dates else "",
            "sprachen": ", ".join(sorted(set(ok["sprache"].tolist()))),
            "extraktion_strategie": safe_str(ex.get("strategy_used")),
            "extraktion_konfidenz": ex.get("confidence", 0.0),
            "warnungen": " | ".join(ex.get("warnings", []))[:600],
        })
    return pd.DataFrame(rows)


# ============================================================
# EXPORTE
# ============================================================
def corpus_to_csv(df: pd.DataFrame, pseudonym_only: bool = True) -> bytes:
    out = df.copy()
    if pseudonym_only and "autor" in out.columns:
        out = out.drop(columns=["autor"])
    return out.to_csv(index=False, sep=";", encoding="utf-8-sig").encode("utf-8-sig")


def build_methods_sheet(meta: dict, stats: dict, konz: dict, verlauf: List[dict],
                        log: RunLog, codebuch: List[dict]) -> pd.DataFrame:
    rows = [
        ("Projekt", meta.get("projekt", "")),
        ("Analyst:in", meta.get("user", "")),
        ("Datum der Auswertung", datetime.now().strftime("%Y-%m-%d %H:%M")),
        ("Methode", "Netnographie / computergestützte qualitative Inhaltsanalyse"),
        ("Datenerhebung", meta.get("erhebung", "Manuelle Sammlung öffentlich zugänglicher "
                                              "Community-Seiten als HTML.")),
        ("Modell", meta.get("modell", "")),
        ("Analysemodus", meta.get("modus", "")),
        ("Studienkontext", meta.get("kontext", "")[:900]),
        ("Forschungsfragen", " | ".join(meta.get("fragen", []))[:900]),
        ("", ""),
        ("Dateien", stats.get("n_dateien", 0)),
        ("Communities", stats.get("n_communities", 0)),
        ("Extrahierte Beiträge (roh)", stats.get("n_roh", 0)),
        ("Analysierte Beiträge (nach Bereinigung)", stats.get("n_analysierbar", 0)),
        ("Ausgeschlossene Duplikate", stats.get("n_duplikate", 0)),
        ("Unterschiedliche Autor:innen", stats.get("n_autoren", 0)),
        ("Sprachverteilung", json.dumps(stats.get("sprachen", {}), ensure_ascii=False)),
        ("", ""),
        ("Beiträge je Autor:in (Ø)", konz.get("beitraege_pro_autor", "n/v")),
        ("Anteil des aktivsten Autors", konz.get("top_autor_anteil", "n/v")),
        ("Anteil der aktivsten 10 % der Autor:innen", konz.get("top10pct_anteil", "n/v")),
        ("Gini-Koeffizient der Beitragsverteilung", konz.get("gini", "n/v")),
        ("", ""),
        ("Obercodes", len(codebuch)),
        ("Subcodes", len(flatten_subcodes(codebuch))),
        ("Sättigungsrunden", len(verlauf)),
        ("Zuwachs in letzter Runde", f"{verlauf[-1]['zuwachs']:.1%}" if verlauf else "n/v"),
        ("", ""),
        ("LLM-Calls", log.calls),
        ("davon aus Cache", log.cache_hits),
        ("Tokens gesamt", log.tokens),
        ("Kosten (EUR, geschätzt)", round(log.cost, 4)),
        ("Fail-Loud-Ereignisse", len(log.events)),
        ("davon Fehler", log.n_errors),
        ("", ""),
        ("GELTUNGSBEREICH", "Community-Daten sind eine selbstselektierte, nicht "
                            "repräsentative Quelle. Häufigkeiten beschreiben die "
                            "Salienz im Diskurs, NICHT die Prävalenz in der "
                            "Grundgesamtheit. Nennungen dürfen nicht auf Marktanteile "
                            "oder Bevölkerungsanteile hochgerechnet werden."),
        ("DATENSCHUTZ", "Nutzernamen wurden pseudonymisiert (SHA-256 mit Projekt-Salt). "
                        "Verbatims stammen aus öffentlich zugänglichen Beiträgen und "
                        "können bei wörtlicher Wiedergabe re-identifizierbar sein — "
                        "vor Weitergabe an Dritte prüfen."),
        ("VERBATIM-TREUE", "Zitate werden vom Tool aus dem Quelltext rekonstruiert. "
                           "Das Modell gibt ausschließlich IDs zurück und formuliert "
                           "keine Zitate."),
    ]
    return pd.DataFrame(rows, columns=["Feld", "Wert"])


def export_excel(corpus: pd.DataFrame, coded: pd.DataFrame, long_df: pd.DataFrame,
                 freq_ober: pd.DataFrame, freq_sub: pd.DataFrame,
                 splits: Dict[str, pd.DataFrame], summaries_ober: dict,
                 summaries_sub: dict, fragen_out: List[dict], quellen: pd.DataFrame,
                 methods: pd.DataFrame, log: RunLog, codebuch: List[dict],
                 cooc: List[dict] = None, signals: List[dict] = None,
                 idx_matrices: Dict[str, pd.DataFrame] = None) -> bytes:
    buf = io.BytesIO()
    used = set()
    with pd.ExcelWriter(buf, engine="xlsxwriter") as xw:
        methods.to_excel(xw, sheet_name=unique_sheet_name("00_Methodik", used), index=False)
        quellen.to_excel(xw, sheet_name=unique_sheet_name("01_Quellenregister", used), index=False)

        cb_rows = []
        for o in codebuch:
            for s in o.get("subcodes", []):
                cb_rows.append({"obercode": o["obercode"], "ober_definition": o.get("definition", ""),
                                "subcode": s["subcode"], "sub_definition": s.get("definition", ""),
                                "belege": ", ".join(s.get("belege", []))})
        pd.DataFrame(cb_rows).to_excel(
            xw, sheet_name=unique_sheet_name("02_Codebuch", used), index=False)

        freq_ober.to_excel(xw, sheet_name=unique_sheet_name("03_Haeufigkeit_Themen", used), index=False)
        freq_sub.to_excel(xw, sheet_name=unique_sheet_name("04_Haeufigkeit_Subthemen", used), index=False)

        sum_rows = []
        for lvl, d in (("Thema", summaries_ober), ("Subthema", summaries_sub)):
            for k, v in (d or {}).items():
                sum_rows.append({
                    "ebene": lvl, "thema": k, "status": v.get("status", ""),
                    "key_insight": v.get("key_insight", ""), "summary": v.get("summary", ""),
                    "spannungsfeld": v.get("spannungsfeld", ""),
                    "community_sprache": ", ".join(v.get("sprache_der_community", [])),
                    "beleg_ids": ", ".join(b["id"] for b in v.get("belege", [])),
                })
        pd.DataFrame(sum_rows).to_excel(
            xw, sheet_name=unique_sheet_name("05_Summaries", used), index=False)

        if fragen_out:
            pd.DataFrame([{k: (", ".join(b["id"] for b in v) if k == "belege" else v)
                           for k, v in f.items()} for f in fragen_out]).to_excel(
                xw, sheet_name=unique_sheet_name("06_Forschungsfragen", used), index=False)

        if signals:
            pd.DataFrame(signals).to_excel(
                xw, sheet_name=unique_sheet_name("06b_Signale", used), index=False)
        if cooc:
            pd.DataFrame(cooc).to_excel(
                xw, sheet_name=unique_sheet_name("06c_Zusammenhaenge", used), index=False)
        for name, m in (idx_matrices or {}).items():
            if m is not None and not m.empty:
                m.to_excel(xw, sheet_name=unique_sheet_name(f"06d_Index_{name}", used),
                           index=False)
        for name, sdf in (splits or {}).items():
            if sdf is not None and not sdf.empty:
                sdf.to_excel(xw, sheet_name=unique_sheet_name(f"07_Split_{name}", used), index=False)

        exp = corpus.merge(coded, on="kommentar_id", how="left")
        for c in ("subcodes", "beantwortet_fragen", "neue_themen"):
            if c in exp.columns:
                exp[c] = exp[c].apply(lambda v: "; ".join(v) if isinstance(v, list) else "")
        exp.drop(columns=[c for c in ["autor"] if c in exp.columns]).to_excel(
            xw, sheet_name=unique_sheet_name("08_Korpus_kodiert", used), index=False)

        if not long_df.empty:
            long_df.drop(columns=[c for c in ["autor"] if c in long_df.columns]).to_excel(
                xw, sheet_name=unique_sheet_name("09_Belegstellen", used), index=False)

        diag = pd.DataFrame(log.diagnose())
        if not diag.empty:
            diag.to_excel(xw, sheet_name=unique_sheet_name("98_Diagnose", used), index=False)
        log.to_df().to_excel(xw, sheet_name=unique_sheet_name("99_Fail_Loud_Log", used), index=False)

        # Spaltenbreiten
        wb = xw.book
        wrap = wb.add_format({"text_wrap": True, "valign": "top"})
        for ws in xw.sheets.values():
            ws.set_column(0, 0, 26)
            ws.set_column(1, 6, 22)
            ws.set_column(7, 30, 46, wrap)
            ws.freeze_panes(1, 0)
    return buf.getvalue()


# ============================================================
# ERKENNTNIS-COCKPIT
# ============================================================
# Warum das hier existiert: Ein Report, den man liest, wird konsumiert.
# Ein Report, in dem man etwas SUCHT, vergleicht oder vorhersagt, wird verarbeitet.
# Die folgenden Bausteine sind deshalb nicht nur huebschere Tabellen, sondern
# erzwingen kleine Urteilsakte: Groessenvergleich (Landkarte), Abweichung vom
# Durchschnitt (Index-Matrix), Widerspruch zur Erwartung (Signale, Blindmodus).

def compute_cooccurrence(long_df: pd.DataFrame, level: str = "obercode",
                         min_pair: int = 2) -> List[dict]:
    """Welche Themen tauchen im selben Beitrag auf?

    Zwei Masse, weil sie Verschiedenes zeigen:
      jaccard = wie stark ueberlappen die Themen insgesamt
      lift    = wie viel haeufiger als bei Zufall (1.0 = unabhaengig)
    Ein Lift von 2,5 bei kleinem Jaccard ist die interessante Kombination:
    selten, aber wenn, dann fast immer zusammen.
    """
    if long_df.empty or level not in long_df.columns:
        return []
    sets: Dict[str, set] = defaultdict(set)
    for r in long_df.itertuples(index=False):
        sets[getattr(r, level)].add(r.kommentar_id)
    total = long_df["kommentar_id"].nunique() or 1
    names = sorted(sets, key=lambda n: -len(sets[n]))
    out = []
    for i, a in enumerate(names):
        for b in names[i + 1:]:
            inter = sets[a] & sets[b]
            if len(inter) < min_pair:
                continue
            union = len(sets[a] | sets[b]) or 1
            pa, pb = len(sets[a]) / total, len(sets[b]) / total
            lift = (len(inter) / total) / (pa * pb) if pa and pb else 0.0
            out.append({"a": a, "b": b, "n": len(inter),
                        "jaccard": round(len(inter) / union, 3),
                        "lift": round(lift, 2),
                        "anteil_a": round(len(inter) / len(sets[a]), 3),
                        "anteil_b": round(len(inter) / len(sets[b]), 3)})
    return sorted(out, key=lambda e: -e["n"])


def compute_index_matrix(long_df: pd.DataFrame, corpus: pd.DataFrame, split_col: str,
                         level: str = "obercode", min_base: int = 8) -> pd.DataFrame:
    """Index statt Rohzahl: 100 = so haeufig wie im Gesamtkorpus.

    Rohzahlen zwischen unterschiedlich grossen Communities zu vergleichen ist
    der haeufigste Lesefehler in Splittabellen. Der Index normiert das weg.
    Gruppen unter min_base Beitraegen werden ausgelassen — ein Index auf n=3
    schwankt so stark, dass er nur Scheingenauigkeit erzeugt.
    """
    if long_df.empty or split_col not in long_df.columns:
        return pd.DataFrame()
    ok = corpus[corpus["qualitaet"] == "ok"]
    if split_col in ok.columns:
        bases = ok.groupby(split_col)["kommentar_id"].nunique()
    else:
        bases = long_df.groupby(split_col)["kommentar_id"].nunique()
    bases = bases[bases >= min_base]
    if bases.empty:
        return pd.DataFrame()
    total_base = int(ok["kommentar_id"].nunique()) or 1

    rows = []
    for thema, g in long_df.groupby(level, sort=False):
        gesamt_anteil = g["kommentar_id"].nunique() / total_base
        if gesamt_anteil <= 0:
            continue
        row = {"thema": thema, "n_gesamt": g["kommentar_id"].nunique(),
               "anteil_gesamt": round(gesamt_anteil, 4)}
        for grp, base in bases.items():
            n = g[g[split_col] == grp]["kommentar_id"].nunique()
            row[str(grp)] = int(round(100 * (n / base) / gesamt_anteil))
        rows.append(row)
    df = pd.DataFrame(rows).sort_values("n_gesamt", ascending=False)
    df.attrs["basen"] = {str(k): int(v) for k, v in bases.items()}
    return df.reset_index(drop=True)


def compute_signals(freq: pd.DataFrame, long_df: pd.DataFrame, corpus: pd.DataFrame,
                    idx_matrices: Dict[str, pd.DataFrame], cooc: List[dict],
                    max_signals: int = 8) -> List[dict]:
    """Strukturelle Auffaelligkeiten, die man in einer Tabelle uebersieht.

    Jedes Signal beantwortet die Frage, die eine Zahl allein nicht beantwortet:
    'Und warum sollte mich das interessieren?'
    """
    sig = []
    if freq.empty:
        return sig
    base_n = int((corpus["qualitaet"] == "ok").sum()) or 1

    for r in freq.itertuples(index=False):
        n = int(r.n_kommentare)
        if n < 3:
            continue
        pos, neg = int(r.sentiment_pos), int(r.sentiment_neg)
        thema = r.obercode if not getattr(r, "subcode", "") else r.subcode

        # 1) Umstritten: viel Zustimmung UND viel Ablehnung im selben Thema
        pol = min(pos, neg) / n
        if pol >= 0.25 and min(pos, neg) >= 3:
            sig.append({"typ": "Umstritten", "thema": thema, "wert": f"{pol:.0%}",
                        "score": pol * 2.2,
                        "text": f"{pos} zustimmende und {neg} ablehnende Beiträge im selben "
                                f"Thema. Kein Mittelwert bilden — hier stehen sich zwei "
                                f"Lager gegenüber, die getrennt zu verstehen sind."})

        # 2) Echo: viele Beitraege, wenige Koepfe
        if int(r.n_autoren) >= 1:
            ratio = n / int(r.n_autoren)
            if ratio >= 3.0 and n >= 6:
                sig.append({"typ": "Echo", "thema": thema, "wert": f"{ratio:.1f}×",
                            "score": min(ratio / 6, 1.0) * 1.9,
                            "text": f"{n} Beiträge von nur {int(r.n_autoren)} Personen. "
                                    f"Das Thema ist laut, nicht zwingend verbreitet — als "
                                    f"Einzelmeinung behandeln, bis Gegenbelege da sind."})

        # 3) Breit: taucht quer durch die Threads auf
        if int(r.n_threads) >= 3 and n / max(1, int(r.n_threads)) <= 2.5:
            sig.append({"typ": "Breit", "thema": thema, "wert": f"{int(r.n_threads)} Threads",
                        "score": min(int(r.n_threads) / 8, 1.0) * 1.15,
                        "text": f"Kommt in {int(r.n_threads)} unabhängigen Diskussionen vor, "
                                f"jeweils nur vereinzelt. Solche Themen sind belastbarer als "
                                f"gleich grosse aus einem einzigen Thread."})

        # 4) Randnotiz mit Gewicht: klein, aber durchgehend als zentral markiert
        sub = long_df[long_df.get("obercode", pd.Series(dtype=str)) == r.obercode]
        if not sub.empty and n <= max(4, base_n * 0.05):
            mrel = float(sub["relevanz"].mean() or 0)
            if mrel >= 2.4:
                sig.append({"typ": "Unterschätzt", "thema": thema, "wert": f"Ø {mrel:.1f}/3",
                            "score": mrel / 3 * 1.4,
                            "text": f"Nur {n} Beiträge, aber dort jeweils zentral. Kleine "
                                    f"Themen mit hoher Relevanz sind typische Kandidaten für "
                                    f"vertiefende Nachrecherche."})

    # 5) Split-Divergenz
    for name, m in (idx_matrices or {}).items():
        if m is None or m.empty:
            continue
        cols = [c for c in m.columns if c not in ("thema", "n_gesamt", "anteil_gesamt")]
        # bewusst iterrows statt itertuples: itertuples benennt Spalten mit
        # Sonderzeichen um ("Reddit r/BMW" -> "_5") und macht sie unauffindbar.
        for _, r in m.iterrows():
            vals = {c: r[c] for c in cols if isinstance(r[c], (int, float))}
            if len(vals) < 2 or int(r["n_gesamt"]) < 4:
                continue
            hi = max(vals, key=vals.get)
            lo = min(vals, key=vals.get)
            spread = vals[hi] - vals[lo]
            if spread >= 70:
                sig.append({"typ": "Gespalten", "thema": r["thema"],
                            "wert": f"Index {vals[hi]} vs. {vals[lo]}",
                            "score": min(spread / 160, 1.0) * 2.4,
                            "text": f"Nach {name}: in „{hi}“ Index {vals[hi]}, in „{lo}“ nur "
                                    f"{vals[lo]} (100 = Durchschnitt). Das Thema ist kein "
                                    f"Gesamtbefund, sondern gruppenspezifisch."})

    # 6) Starke Kopplung
    for e in (cooc or [])[:20]:
        if e["lift"] >= 1.8 and e["n"] >= 3:
            sig.append({"typ": "Gekoppelt", "thema": f"{e['a']} + {e['b']}",
                        "wert": f"Lift {e['lift']}",
                        "score": min(e["lift"] / 4, 1.0) * 1.6,
                        "text": f"{e['n']} Beiträge nennen beides — {e['lift']}× häufiger als "
                                f"bei Zufall. {e['anteil_a']:.0%} aller Beiträge zu "
                                f"„{e['a']}“ sprechen auch „{e['b']}“ an."})

    # Vielfalt vor Rangfolge: acht Karten desselben Typs sind keine Uebersicht.
    seen, per_typ, out = set(), Counter(), []
    for s in sorted(sig, key=lambda x: -x["score"]):
        key = (s["typ"], s["thema"])
        if key in seen or per_typ[s["typ"]] >= 2:
            continue
        seen.add(key)
        per_typ[s["typ"]] += 1
        out.append(s)
        if len(out) >= max_signals:
            break
    # Falls die Typquote zu wenig Karten laesst, mit den naechstbesten auffuellen
    if len(out) < min(4, len(sig)):
        for s in sorted(sig, key=lambda x: -x["score"]):
            if (s["typ"], s["thema"]) in seen:
                continue
            seen.add((s["typ"], s["thema"]))
            out.append(s)
            if len(out) >= max_signals:
                break
    return out


def force_layout(nodes: List[dict], edges: List[dict], width: int = 940, height: int = 520,
                 iterations: int = 420, seed: int = 7) -> Dict[str, Tuple[float, float]]:
    """Fruchterman-Reingold in reinem Python.

    Absichtlich hier statt in JavaScript: das Layout wird damit deterministisch
    (gleicher Seed = gleiches Bild in Streamlit, im Export und im Ausdruck) und
    das Dashboard bleibt ohne externe Bibliothek offline lauffaehig.
    """
    ids = [n["id"] for n in nodes]
    if not ids:
        return {}
    if len(ids) == 1:
        return {ids[0]: (width / 2, height / 2)}
    rnd = random.Random(seed)
    # Startpositionen auf einem Kreis: reproduzierbar und ohne Ueberlagerung
    pos = {}
    for i, nid in enumerate(ids):
        ang = 2 * math.pi * i / len(ids)
        pos[nid] = [math.cos(ang) * 0.6 + rnd.uniform(-.04, .04),
                    math.sin(ang) * 0.6 + rnd.uniform(-.04, .04)]
    rad = {n["id"]: max(n.get("r", 10), 6) for n in nodes}
    maxr = max(rad.values()) or 1
    k = 1.35 / math.sqrt(len(ids))

    adj = defaultdict(list)
    for e in edges:
        if e["a"] in pos and e["b"] in pos:
            adj[e["a"]].append((e["b"], e.get("w", 1.0)))
            adj[e["b"]].append((e["a"], e.get("w", 1.0)))

    for it in range(iterations):
        temp = 0.16 * (1.0 - it / iterations) + 0.004
        disp = {n: [0.0, 0.0] for n in ids}
        for i, a in enumerate(ids):
            for b in ids[i + 1:]:
                dx, dy = pos[a][0] - pos[b][0], pos[a][1] - pos[b][1]
                d = math.hypot(dx, dy) or 1e-4
                # grosse Knoten stossen staerker ab, damit Labels lesbar bleiben
                mass = (rad[a] + rad[b]) / (2 * maxr)
                f = (k * k / d) * (0.55 + 0.9 * mass)
                ux, uy = dx / d, dy / d
                disp[a][0] += ux * f; disp[a][1] += uy * f
                disp[b][0] -= ux * f; disp[b][1] -= uy * f
        for a, lst in adj.items():
            for b, w in lst:
                dx, dy = pos[a][0] - pos[b][0], pos[a][1] - pos[b][1]
                d = math.hypot(dx, dy) or 1e-4
                f = (d * d / k) * min(1.6, 0.45 + w)
                ux, uy = dx / d, dy / d
                disp[a][0] -= ux * f; disp[a][1] -= uy * f
        for n in ids:
            dx, dy = disp[n]
            d = math.hypot(dx, dy) or 1e-4
            pos[n][0] += dx / d * min(d, temp)
            pos[n][1] += dy / d * min(d, temp)
            # sanft zur Mitte ziehen, damit nichts wegdriftet
            pos[n][0] *= 0.995
            pos[n][1] *= 0.995

    xs = [p[0] for p in pos.values()]; ys = [p[1] for p in pos.values()]
    minx, maxx = min(xs), max(xs); miny, maxy = min(ys), max(ys)
    pad = maxr + 46
    sx = (width - 2 * pad) / ((maxx - minx) or 1)
    sy = (height - 2 * pad) / ((maxy - miny) or 1)
    out = {n: (pad + (pos[n][0] - minx) * sx, pad + (pos[n][1] - miny) * sy) for n in ids}

    # Kollisionsaufloesung: Kreise duerfen sich nicht ueberlappen
    for _ in range(90):
        moved = False
        for i, a in enumerate(ids):
            for b in ids[i + 1:]:
                ax, ay = out[a]; bx, by = out[b]
                dx, dy = ax - bx, ay - by
                d = math.hypot(dx, dy) or 1e-4
                need = rad[a] + rad[b] + 16
                if d < need:
                    sh = (need - d) / 2
                    ux, uy = dx / d, dy / d
                    out[a] = (min(width - pad / 2, max(pad / 2, ax + ux * sh)),
                              min(height - pad / 2, max(pad / 2, ay + uy * sh)))
                    out[b] = (min(width - pad / 2, max(pad / 2, bx - ux * sh)),
                              min(height - pad / 2, max(pad / 2, by - uy * sh)))
                    moved = True
        if not moved:
            break
    return out


# ============================================================
# HTML-DASHBOARD
# ============================================================
DASH_CSS = """
*,*::before,*::after{box-sizing:border-box;margin:0;padding:0}
:root{
  --bg:#F7F8FA;--s1:#FFFFFF;--s2:#F0F2F5;--s3:#E8EBF0;--s4:#DDE1E9;
  --b:rgba(0,0,0,.07);--b2:rgba(0,0,0,.12);--b3:rgba(0,0,0,.18);
  --accent:#E63D50;--accent2:#c0293b;--accent-light:rgba(230,61,80,.08);
  --text:#1A1D23;--t2:#4A5060;--t3:#8892A0;--t4:#B8C0CC;
  --green:#0A9154;--green-bg:rgba(10,145,84,.08);
  --blue:#1A6FBF;--blue-bg:rgba(26,111,191,.08);
  --amber:#B06010;--amber-bg:rgba(176,96,16,.08);
  --r:10px;--rs:6px;--ease:cubic-bezier(.4,0,.2,1);--tr:.16s;
  --shadow-sm:0 1px 3px rgba(0,0,0,.08),0 1px 2px rgba(0,0,0,.05);
  --shadow:0 4px 12px rgba(0,0,0,.08),0 2px 4px rgba(0,0,0,.05);
  --shadow-lg:0 8px 24px rgba(0,0,0,.10),0 4px 8px rgba(0,0,0,.06);
}
html{scroll-behavior:smooth}
body{font-family:'Inter',sans-serif;background:var(--bg);color:var(--text);line-height:1.6;-webkit-font-smoothing:antialiased}
.hdr{position:sticky;top:0;z-index:200;background:rgba(255,255,255,.94);backdrop-filter:blur(16px) saturate(180%);border-bottom:1.5px solid var(--b);padding:0 32px;display:flex;align-items:center;justify-content:space-between;height:56px;gap:18px;box-shadow:var(--shadow-sm)}
.logo{display:flex;align-items:center;gap:11px;flex-shrink:0}
.logo-mark{font-family:'DM Mono',monospace;font-size:13px;font-weight:600;letter-spacing:-.01em}
.logo-mark em{color:var(--accent);font-style:normal}
.logo-sep{width:1px;height:16px;background:var(--b3)}
.logo-badge{font-family:'DM Mono',monospace;font-size:9px;color:var(--accent);letter-spacing:.1em;text-transform:uppercase;border:1px solid rgba(230,61,80,.3);border-radius:3px;padding:2px 7px;background:var(--accent-light)}
.hnav{display:flex;gap:4px}
.hnav a{font-family:'DM Mono',monospace;font-size:10px;text-transform:uppercase;letter-spacing:.08em;color:var(--t3);text-decoration:none;padding:6px 10px;border-radius:var(--rs)}
.hnav a:hover{color:var(--accent);background:var(--accent-light)}
.search-wrap{position:relative;flex-shrink:0}
.search-wrap svg{position:absolute;left:10px;top:50%;transform:translateY(-50%);color:var(--t3);pointer-events:none}
.si{background:#fff;border:1.5px solid var(--b2);border-radius:var(--rs);font-family:'Inter',sans-serif;font-size:13px;padding:7px 14px 7px 32px;width:200px;outline:none;transition:border-color var(--tr),width var(--tr)}
.si:focus{border-color:var(--accent);width:260px;box-shadow:0 0 0 3px rgba(230,61,80,.12)}
.wrap{max-width:1140px;margin:0 auto;padding:36px 32px 100px}
.ptitle h1{font-size:11px;font-weight:600;letter-spacing:.14em;text-transform:uppercase;color:var(--accent);font-family:'DM Mono',monospace;margin-bottom:8px}
.ptitle-project{font-size:28px;font-weight:700;line-height:1.15;letter-spacing:-.02em}
.ptitle p{font-size:12px;color:var(--t3);margin-top:6px;font-family:'DM Mono',monospace}
.pills{display:flex;flex-wrap:wrap;gap:6px;margin-top:14px}
.pill{display:inline-flex;align-items:center;gap:5px;background:#fff;border:1.5px solid var(--b2);border-radius:100px;padding:4px 12px;font-size:11px;color:var(--t2);font-family:'DM Mono',monospace;box-shadow:var(--shadow-sm)}
.dot{width:6px;height:6px;border-radius:50%;flex-shrink:0}
.kpis{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px;margin:26px 0 8px}
.kpi{background:#fff;border:1.5px solid var(--b);border-radius:var(--r);padding:14px 16px;box-shadow:var(--shadow-sm)}
.kpi .v{font-size:24px;font-weight:700;letter-spacing:-.02em}
.kpi .l{font-family:'DM Mono',monospace;font-size:9.5px;text-transform:uppercase;letter-spacing:.09em;color:var(--t3);margin-top:2px}
.kpi .h{font-size:11px;color:var(--t4);margin-top:4px}
.banner{border-left:4px solid var(--amber);background:var(--amber-bg);border-radius:var(--rs);padding:12px 16px;margin:18px 0 6px;font-size:12.5px;color:#7a4409;line-height:1.6}
.banner b{color:#5e340a}
.banner.err{border-left-color:var(--accent);background:rgba(230,61,80,.06);color:#8d1b2a}
.sec{margin-top:40px}
.sec-h{font-family:'DM Mono',monospace;font-size:10px;text-transform:uppercase;letter-spacing:.12em;color:var(--t4);margin-bottom:12px;display:flex;justify-content:space-between;align-items:center}
.tbtn{background:#fff;border:1.5px solid var(--b2);border-radius:var(--rs);color:var(--t2);cursor:pointer;font-family:'Inter',sans-serif;font-size:12px;font-weight:500;padding:5px 14px;transition:all var(--tr);box-shadow:var(--shadow-sm)}
.tbtn:hover{background:var(--accent);border-color:var(--accent);color:#fff}
.qcard{background:var(--s1);border:1.5px solid var(--b);border-radius:var(--r);margin-bottom:10px;overflow:hidden;box-shadow:var(--shadow-sm);transition:border-color var(--tr),box-shadow var(--tr)}
.qcard:hover{border-color:var(--b2);box-shadow:var(--shadow)}
.qcard.open{border-color:rgba(230,61,80,.3);box-shadow:0 4px 20px rgba(230,61,80,.10)}
.qcard-hdr{display:flex;align-items:center;gap:14px;padding:15px 20px;cursor:pointer;user-select:none}
.qcard-hdr:hover{background:var(--s2)}
.qnum{font-family:'DM Mono',monospace;font-size:9px;font-weight:600;color:var(--accent);letter-spacing:.1em;background:var(--accent-light);border:1px solid rgba(230,61,80,.25);border-radius:4px;padding:3px 8px;flex-shrink:0}
.qtitle{flex:1;font-size:14.5px;font-weight:600;line-height:1.35}
.qmeta{display:flex;align-items:center;gap:6px;flex-shrink:0}
.qbadge{font-family:'DM Mono',monospace;font-size:9.5px;color:var(--t3);background:var(--s2);border:1.5px solid var(--b);border-radius:4px;padding:2px 8px;white-space:nowrap}
.qbadge.pos{color:var(--green);background:var(--green-bg);border-color:rgba(10,145,84,.2)}
.qbadge.neg{color:var(--accent);background:var(--accent-light);border-color:rgba(230,61,80,.25)}
.qbadge.warn{color:var(--amber);background:var(--amber-bg);border-color:rgba(176,96,16,.2)}
.chev{width:24px;height:24px;border-radius:50%;border:1.5px solid var(--b2);display:flex;align-items:center;justify-content:center;color:var(--t3);transition:transform var(--tr),background var(--tr),color var(--tr);flex-shrink:0}
.qcard.open .chev{transform:rotate(180deg);background:var(--accent);border-color:var(--accent);color:#fff}
.qcard-body{display:none;border-top:1.5px solid var(--b)}
.qcard.open .qcard-body{display:block;animation:fd .2s var(--ease)}
@keyframes fd{from{opacity:0;transform:translateY(-4px)}to{opacity:1;transform:translateY(0)}}
.itabs{display:flex;border-bottom:1.5px solid var(--b);padding:0 20px;background:var(--s2);overflow-x:auto}
.itab{font-family:'DM Mono',monospace;font-size:9.5px;text-transform:uppercase;letter-spacing:.09em;color:var(--t3);cursor:pointer;padding:11px 15px;border-bottom:2.5px solid transparent;margin-bottom:-1.5px;white-space:nowrap;user-select:none}
.itab:hover{color:var(--t2)}
.itab.active{color:var(--accent);border-bottom-color:var(--accent)}
.ipanel{display:none}.ipanel.active{display:block}
.igrid{display:grid;grid-template-columns:1fr 1fr;gap:16px;padding:20px}
@media(max-width:760px){.igrid{grid-template-columns:1fr}}
.iblock{background:var(--s2);border-radius:var(--r);padding:16px 18px;border:1.5px solid var(--b);position:relative;overflow:hidden}
.iblock::before{content:'';position:absolute;top:0;left:0;right:0;height:2px}
.iblock.ki{border-color:rgba(230,61,80,.2);background:#FFF9FA}
.iblock.ki::before{background:linear-gradient(90deg,var(--accent),transparent)}
.iblock.sm::before{background:linear-gradient(90deg,var(--t4),transparent)}
.iblock.tn{border-color:rgba(26,111,191,.2);background:#F7FBFF}
.iblock.tn::before{background:linear-gradient(90deg,var(--blue),transparent)}
.iblock-lbl{font-family:'DM Mono',monospace;font-size:9px;text-transform:uppercase;letter-spacing:.1em;display:flex;align-items:center;justify-content:space-between;margin-bottom:10px;color:var(--t3)}
.iblock.ki .iblock-lbl{color:var(--accent)}
.iblock.tn .iblock-lbl{color:var(--blue)}
.iblock-txt{font-size:13.5px;line-height:1.7;color:var(--t2)}
.iblock.ki .iblock-txt{font-size:14px;color:var(--text)}
.lex{display:flex;flex-wrap:wrap;gap:5px;margin-top:8px}
.lex span{font-family:'DM Mono',monospace;font-size:10.5px;background:#fff;border:1px solid var(--b2);border-radius:100px;padding:2px 9px;color:var(--t2)}
.cbtn{background:#fff;border:1.5px solid var(--b2);border-radius:var(--rs);color:var(--t3);cursor:pointer;font-family:'Inter',sans-serif;font-size:10.5px;padding:3px 10px;transition:all var(--tr);white-space:nowrap;box-shadow:var(--shadow-sm)}
.cbtn:hover{background:var(--accent-light);border-color:var(--accent);color:var(--accent)}
.cbtn.copied{border-color:var(--green);color:var(--green);background:var(--green-bg)}
.sub-panel{padding:16px 20px 20px}
.oc-block{margin-bottom:8px;border:1.5px solid var(--b);border-radius:var(--rs);overflow:hidden;box-shadow:var(--shadow-sm)}
.oc-hdr{display:flex;align-items:center;gap:12px;padding:10px 14px;cursor:pointer;background:var(--s1);user-select:none}
.oc-hdr:hover{background:var(--s2)}
.oc-name{font-size:13px;font-weight:600;flex:0 0 auto;min-width:150px;max-width:44%}
.oc-bar-w{flex:1;display:flex;align-items:center;gap:10px}
.oc-bar{flex:1;height:4px;background:var(--s3);border-radius:2px;overflow:hidden}
.oc-bar-f{height:100%;background:var(--accent);border-radius:2px}
.oc-n{font-family:'DM Mono',monospace;font-size:11px;color:var(--accent);font-weight:600;flex-shrink:0}
.oc-cv{color:var(--t3);font-size:9px;transition:transform var(--tr);flex-shrink:0}
.oc-block.open .oc-cv{transform:rotate(180deg)}
.quotes-wrap{display:none;background:#fff;border-top:1px solid var(--b);padding:8px 14px}
.oc-block.open .quotes-wrap{display:block;animation:fd .13s ease}
.quote{display:flex;gap:10px;align-items:flex-start;padding:9px 4px;border-bottom:1px solid var(--b)}
.quote:last-child{border-bottom:none}
.quote:hover{background:var(--s2)}
.q-dot{width:4px;height:4px;border-radius:50%;background:var(--accent);flex-shrink:0;margin-top:9px;opacity:.7}
.q-content{flex:1;min-width:0}
.q-text{font-size:13px;line-height:1.65}
.q-src{display:flex;flex-wrap:wrap;gap:4px;margin-top:6px}
.chip{font-family:'DM Mono',monospace;font-size:9.5px;padding:2px 8px;border-radius:100px;border:1px solid var(--b2);background:var(--s2);color:var(--t3)}
.chip.pos{color:var(--green);background:var(--green-bg);border-color:rgba(10,145,84,.2)}
.chip.neg{color:var(--accent);background:var(--accent-light);border-color:rgba(230,61,80,.25)}
.chip.amb{color:var(--amber);background:var(--amber-bg);border-color:rgba(176,96,16,.2)}
table.dt{width:100%;border-collapse:collapse;font-size:12.5px}
table.dt th{background:var(--s3);font-weight:600;padding:8px 10px;text-align:left;border:1px solid var(--b);font-size:11.5px;white-space:nowrap}
table.dt td{padding:6px 10px;border:1px solid var(--b);vertical-align:top}
table.dt tr.basis td{background:var(--s2);font-weight:700;font-family:'DM Mono',monospace;font-size:11.5px}
.tbl-wrap{overflow-x:auto;background:#fff;border:1.5px solid var(--b);border-radius:var(--r);padding:14px;box-shadow:var(--shadow-sm)}
.mini{font-size:11.5px;color:var(--t3);margin-top:8px;font-family:'DM Mono',monospace}
#nores{display:none;text-align:center;padding:50px;color:var(--t3);font-style:italic}
::-webkit-scrollbar{width:6px;height:6px}
::-webkit-scrollbar-thumb{background:var(--b3);border-radius:3px}
@media print{.hdr,.tbtn,.cbtn,.si{display:none!important}.qcard-body{display:block!important}.ipanel{display:block!important}}
"""

DASH_JS = """
function esc(s){return String(s??'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')}
function cp(text,btn){
  navigator.clipboard.writeText(text).then(function(){
    var o=btn.textContent;btn.textContent='Kopiert \\u2713';btn.classList.add('copied');
    setTimeout(function(){btn.textContent=o;btn.classList.remove('copied')},1600);
  });
}
function cpEl(id,btn){var el=document.getElementById(id);if(el)cp(el.innerText,btn);}
function toggleQ(c,ev){if(ev&&ev.target.closest('.cbtn'))return;c.classList.toggle('open')}
function toggleOC(h){h.parentElement.classList.toggle('open')}
function expandAll(){document.querySelectorAll('.qcard').forEach(function(c){c.classList.add('open')})}
function collapseAll(){document.querySelectorAll('.qcard,.oc-block').forEach(function(c){c.classList.remove('open')})}
function switchTab(card,name,ev){
  if(ev)ev.stopPropagation();
  card.querySelectorAll('.itab').forEach(function(t){t.classList.toggle('active',t.dataset.tab===name)});
  card.querySelectorAll('.ipanel').forEach(function(p){p.classList.toggle('active',p.dataset.panel===name)});
}
var si=document.getElementById('searchInput');
if(si){si.addEventListener('input',function(e){
  var q=e.target.value.toLowerCase().trim();var any=false;
  document.querySelectorAll('.qcard').forEach(function(c){
    var hit=!q||c.innerText.toLowerCase().indexOf(q)>-1;
    c.style.display=hit?'':'none';if(hit)any=true;
    if(q&&hit)c.classList.add('open');
  });
  var nr=document.getElementById('nores');if(nr)nr.style.display=any?'none':'block';
});}
"""


def _h(s) -> str:
    return html_module.escape("" if s is None else str(s))


def _js(s) -> str:
    s = "" if s is None else str(s)
    s = s.replace("\\", "\\\\").replace("'", "\\'")
    s = s.replace("\n", "\\n").replace("\r", "\\r").replace("</", "<\\/")
    return f"'{s}'"


COCKPIT_CSS = """
.ck{--ck-bg:#0A0D14;--ck-bg2:#111725;--ck-line:rgba(120,160,220,.13);
 --ck-txt:#E8EDF7;--ck-dim:#7E8DA8;--ck-dim2:#56637C;
 --ck-red:#FF4D63;--ck-cyan:#28E1E8;--ck-amber:#FFB547;--ck-vio:#8B7CFF;
 background:radial-gradient(1200px 600px at 15% -10%,#16203a 0%,#0A0D14 60%);
 border:1px solid var(--ck-line);border-radius:16px;padding:0;margin:26px 0 8px;
 color:var(--ck-txt);overflow:hidden;position:relative;
 box-shadow:0 20px 60px rgba(10,13,20,.28),inset 0 1px 0 rgba(255,255,255,.05)}
.ck::before{content:'';position:absolute;inset:0;pointer-events:none;
 background-image:linear-gradient(var(--ck-line) 1px,transparent 1px),
 linear-gradient(90deg,var(--ck-line) 1px,transparent 1px);
 background-size:44px 44px;opacity:.5;
 mask-image:radial-gradient(700px 420px at 30% 0%,#000 0%,transparent 78%);
 -webkit-mask-image:radial-gradient(700px 420px at 30% 0%,#000 0%,transparent 78%)}
.ck-top{display:flex;align-items:center;justify-content:space-between;gap:16px;
 padding:18px 24px 12px;border-bottom:1px solid var(--ck-line);position:relative;z-index:2}
.ck-ttl{font-family:'DM Mono',monospace;font-size:10px;letter-spacing:.24em;
 text-transform:uppercase;color:var(--ck-cyan)}
.ck-ttl b{display:block;font-family:'Inter',sans-serif;font-size:20px;font-weight:600;
 letter-spacing:-.02em;color:var(--ck-txt);margin-top:5px;text-transform:none}
.ck-tools{display:flex;gap:7px;align-items:center;flex-wrap:wrap}
.ck-btn{background:rgba(255,255,255,.05);border:1px solid var(--ck-line);color:var(--ck-dim);
 border-radius:7px;font-family:'DM Mono',monospace;font-size:10px;letter-spacing:.09em;
 text-transform:uppercase;padding:6px 12px;cursor:pointer;transition:.16s}
.ck-btn:hover{color:var(--ck-cyan);border-color:rgba(40,225,232,.45);
 background:rgba(40,225,232,.08);box-shadow:0 0 18px rgba(40,225,232,.14)}
.ck-btn.on{color:#08131a;background:var(--ck-cyan);border-color:var(--ck-cyan);font-weight:500}
.ck-grid{display:grid;grid-template-columns:1fr 340px;gap:0;position:relative;z-index:2}
@media(max-width:900px){.ck-grid{grid-template-columns:1fr}}
.ck-map{padding:6px 10px 14px;min-width:0}
.ck-map svg{width:100%;height:auto;display:block}
.ck-side{border-left:1px solid var(--ck-line);padding:16px 20px 20px;min-width:0}
.ck-lbl{font-family:'DM Mono',monospace;font-size:9px;letter-spacing:.18em;text-transform:uppercase;
 color:var(--ck-dim2);margin:0 0 10px;display:flex;justify-content:space-between;align-items:center}
.ck-sig{border-left:2px solid var(--ck-vio);background:linear-gradient(90deg,rgba(139,124,255,.09),transparent 70%);
 border-radius:0 8px 8px 0;padding:9px 12px;margin-bottom:8px;cursor:default;transition:.16s}
.ck-sig:hover{background:linear-gradient(90deg,rgba(139,124,255,.16),transparent 70%)}
.ck-sig.t-Umstritten{border-left-color:var(--ck-red)}
.ck-sig.t-Echo{border-left-color:var(--ck-amber)}
.ck-sig.t-Breit,.ck-sig.t-Gekoppelt{border-left-color:var(--ck-cyan)}
.ck-sig-h{display:flex;justify-content:space-between;gap:8px;align-items:baseline}
.ck-sig-t{font-family:'DM Mono',monospace;font-size:9px;letter-spacing:.14em;text-transform:uppercase;color:var(--ck-dim)}
.ck-sig-v{font-family:'DM Mono',monospace;font-size:10px;color:var(--ck-cyan)}
.ck-sig-n{font-size:13px;font-weight:600;margin:3px 0 4px;line-height:1.3}
.ck-sig-x{font-size:12px;line-height:1.55;color:var(--ck-dim)}
.ck-detail{border-top:1px solid var(--ck-line);padding:16px 24px 20px;position:relative;z-index:2;min-height:96px}
.ck-d-name{font-size:17px;font-weight:600;letter-spacing:-.01em}
.ck-d-meta{display:flex;gap:6px;flex-wrap:wrap;margin:8px 0 10px}
.ck-chip{font-family:'DM Mono',monospace;font-size:9.5px;padding:3px 9px;border-radius:99px;
 border:1px solid var(--ck-line);background:rgba(255,255,255,.04);color:var(--ck-dim)}
.ck-chip.pos{color:var(--ck-cyan);border-color:rgba(40,225,232,.35)}
.ck-chip.neg{color:var(--ck-red);border-color:rgba(255,77,99,.35)}
.ck-d-txt{font-size:13.5px;line-height:1.65;color:#C3CDE0;max-width:80ch}
.ck-d-ki{font-size:14px;line-height:1.6;color:var(--ck-txt);border-left:2px solid var(--ck-red);
 padding-left:12px;margin-bottom:10px}
.ck-hint{font-family:'DM Mono',monospace;font-size:10.5px;color:var(--ck-dim2);letter-spacing:.04em}
.ck-rows{padding:4px 24px 22px;position:relative;z-index:2}
.ck-row{display:flex;align-items:center;gap:12px;padding:7px 0;border-bottom:1px solid rgba(120,160,220,.07)}
.ck-row:last-child{border-bottom:none}
.ck-row-n{font-family:'DM Mono',monospace;font-size:10px;color:var(--ck-dim2);width:24px;flex:0 0 auto}
.ck-row-t{font-size:13px;flex:0 0 auto;width:190px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.ck-bar{flex:1;height:7px;border-radius:4px;background:rgba(255,255,255,.06);overflow:hidden;min-width:60px}
.ck-bar-f{display:block;height:100%;border-radius:4px;transition:width .5s cubic-bezier(.4,0,.2,1)}
.ck-row-v{font-family:'DM Mono',monospace;font-size:11px;color:var(--ck-txt);width:104px;
 text-align:right;flex:0 0 auto}
/* Blindmodus: es reicht nicht, die Balken auszublenden. Solange die Reihenfolge,
   die Kreisgroessen und die Heatmap sichtbar sind, steht die Antwort weiter da. */
.ck.blind .ck-bar-f{width:0!important}
.ck.blind .ck-row-v i{display:none}
.ck.blind .ck-row-v::after{content:'?';font-style:normal;letter-spacing:.16em;color:var(--ck-dim2)}
.ck:not(.blind) .ck-row-v::after{content:''}
.ck.blind .ck-row-n{color:var(--ck-cyan)}
.ck.blind .ck-nlabel{visibility:hidden}
.ck.blind .ck-d-meta{display:none}
.ck.blind .ck-hm td[style]{background:rgba(255,255,255,.05)!important;color:transparent!important}
.ck.blind .ck-hm td.name{color:var(--ck-txt)!important;background:rgba(255,255,255,.04)!important}
.ck.blind .ck-hm td i{visibility:hidden}
.ck-cover{display:none;border:1px dashed rgba(120,160,220,.28);border-radius:10px;
 padding:20px;text-align:center;color:var(--ck-dim);font-size:12.5px;line-height:1.6}
.ck.blind .ck-cover{display:block}
.ck.blind #ckSignals{display:none}
.ck-grip{width:16px;flex:0 0 auto;color:var(--ck-dim2);font-size:13px;line-height:1;
 cursor:grab;visibility:hidden;user-select:none;text-align:center}
.ck.blind .ck-grip{visibility:visible}
.ck.blind .ck-row{cursor:grab;background:rgba(255,255,255,.02);border-radius:6px;
 margin-bottom:3px;padding:9px 8px;border-bottom:1px solid transparent;
 transition:background .14s,transform .14s}
.ck.blind .ck-row:hover{background:rgba(40,225,232,.09)}
.ck-row.dragging{opacity:.45;cursor:grabbing;background:rgba(40,225,232,.16)!important}
.ck-move{display:none;gap:2px;flex:0 0 auto}
.ck.blind .ck-move{display:flex}
.ck-move button{background:rgba(255,255,255,.05);border:1px solid var(--ck-line);
 color:var(--ck-dim);border-radius:4px;width:20px;height:18px;font-size:9px;line-height:1;
 cursor:pointer;padding:0}
.ck-move button:hover{color:var(--ck-cyan);border-color:rgba(40,225,232,.45)}
.ck-delta{font-family:'DM Mono',monospace;font-size:10px;padding:2px 7px;border-radius:99px;
 flex:0 0 auto;width:52px;text-align:center;display:none}
.ck.scored .ck-delta{display:inline-block}
.ck-delta.hit{background:rgba(40,225,232,.16);color:var(--ck-cyan);border:1px solid rgba(40,225,232,.35)}
.ck-delta.near{background:rgba(255,181,71,.14);color:var(--ck-amber);border:1px solid rgba(255,181,71,.3)}
.ck-delta.miss{background:rgba(255,77,99,.14);color:var(--ck-red);border:1px solid rgba(255,77,99,.32)}
.ck-score{display:none;margin:10px 0 4px;padding:12px 14px;border-radius:10px;
 background:linear-gradient(90deg,rgba(40,225,232,.10),transparent 70%);
 border:1px solid rgba(40,225,232,.22);font-size:13px;line-height:1.6}
.ck.scored .ck-score{display:block}
.ck-score b{color:var(--ck-cyan)}
.ck-hm{width:100%;border-collapse:separate;border-spacing:2px;font-family:'DM Mono',monospace;font-size:10.5px}
.ck-hm th{color:var(--ck-dim2);font-weight:400;text-align:left;padding:4px 6px;letter-spacing:.08em;
 text-transform:uppercase;font-size:9px}
.ck-hm td{padding:6px 8px;border-radius:5px;text-align:center;color:#0A0D14;font-weight:600}
.ck-hm td.name{text-align:left;background:rgba(255,255,255,.04);color:var(--ck-txt);
 font-family:'Inter',sans-serif;font-size:12px;font-weight:500;max-width:210px;overflow:hidden;
 text-overflow:ellipsis;white-space:nowrap}
.ck-node{cursor:pointer}
.ck-node circle.hit{fill:transparent}
.ck-node text{pointer-events:none}
.ck.sel .ck-node:not(.on){opacity:.2}
.ck.sel .ck-edge:not(.on){opacity:.05}
.ck-legend{display:flex;gap:14px;flex-wrap:wrap;padding:0 24px 16px;position:relative;z-index:2}
.ck-legend span{font-family:'DM Mono',monospace;font-size:9.5px;color:var(--ck-dim2);
 display:flex;align-items:center;gap:6px;letter-spacing:.06em}
.ck-legend i{width:9px;height:9px;border-radius:50%;display:inline-block}
@media print{.ck{background:#0A0D14!important;-webkit-print-color-adjust:exact;print-color-adjust:exact}}
"""

COCKPIT_JS = """
(function(){
 var root=document.querySelector('.ck'); if(!root) return;
 var DATA=window.__CK_DATA__||{nodes:[],edges:[]};
 var byId={}; DATA.nodes.forEach(function(n){byId[n.id]=n});
 var det=document.getElementById('ckDetail');
 var sel=null;
 function show(id){
   var n=byId[id]; if(!n) return;
   sel=id; root.classList.add('sel');
   var nb={}; DATA.edges.forEach(function(e){ if(e.a===id)nb[e.b]=e; if(e.b===id)nb[e.a]=e; });
   root.querySelectorAll('.ck-node').forEach(function(g){
     g.classList.toggle('on', g.dataset.id===id || nb[g.dataset.id]!==undefined); });
   root.querySelectorAll('.ck-edge').forEach(function(p){
     p.classList.toggle('on', p.dataset.a===id||p.dataset.b===id); });
   var links=Object.keys(nb).sort(function(a,b){return nb[b].lift-nb[a].lift}).slice(0,4)
     .map(function(k){return '<span class="ck-chip">'+esc(k)+' · Lift '+nb[k].lift+' · n='+nb[k].n+'</span>'}).join('');
   det.innerHTML='<div class="ck-d-name">'+esc(n.label)+'</div>'
     +'<div class="ck-d-meta"><span class="ck-chip">n='+n.n+' Beiträge</span>'
     +'<span class="ck-chip">'+n.autoren+' Autor:innen</span>'
     +'<span class="ck-chip">'+n.threads+' Threads</span>'
     +'<span class="ck-chip '+(n.netto>0.15?'pos':(n.netto<-0.15?'neg':''))+'">Netto '
     +(n.netto>0?'+':'')+n.netto.toFixed(2)+'</span>'+links+'</div>'
     +(n.ki?'<div class="ck-d-ki">'+esc(n.ki)+'</div>':'')
     +'<div class="ck-d-txt">'+esc(n.sum||'Keine Verdichtung vorhanden.')+'</div>';
 }
 function clear(){ sel=null; root.classList.remove('sel');
   root.querySelectorAll('.on').forEach(function(e){e.classList.remove('on')});
   det.innerHTML='<div class="ck-hint">Knoten anklicken — Größe = Zahl der Beiträge, '
     +'Verbindung = gemeinsame Nennung im selben Beitrag, Farbe = Netto-Stimmung.</div>'; }
 function esc(s){return String(s==null?'':s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')}
 root.querySelectorAll('.ck-node').forEach(function(g){
   g.addEventListener('click',function(ev){ ev.stopPropagation();
     if(sel===g.dataset.id){clear()}else{show(g.dataset.id)} }); });
 var svg=root.querySelector('.ck-map svg'); if(svg) svg.addEventListener('click',clear);
 /* ---- Blindmodus: schaetzen, dann aufloesen ------------------------------
    Nur Balken auszublenden reicht nicht. Solange die Zeilen nach Groesse
    sortiert sind, ist die Reihenfolge selbst die Antwort. Deshalb werden im
    Blindmodus die Zeilen gemischt, die Kreise auf Einheitsgroesse gesetzt,
    Heatmap und Befunde verdeckt — und der Nutzer sortiert selbst. */
 var rowsBox=document.getElementById('ckRows'), bb=document.getElementById('ckBlind'),
     scoreBox=document.getElementById('ckScore'), hint=document.getElementById('ckRowHint');
 function rows(){ return Array.prototype.slice.call(rowsBox.querySelectorAll('.ck-row')); }

 function setNodeSizes(uniform){
   root.querySelectorAll('.ck-node').forEach(function(g){
     var cs=g.querySelectorAll('circle');
     cs.forEach(function(c){
       if(!c.dataset.r0) c.dataset.r0=c.getAttribute('r');
       c.setAttribute('r', uniform ? (parseFloat(c.dataset.r0)>=30?'34':
         (parseFloat(c.dataset.r0)<8?c.dataset.r0:'26')) : c.dataset.r0);
     });
   });
 }
 function shuffle(a){ // deterministisch: gleiche Reihenfolge in App, Export und Ausdruck
   var seed=97; function rnd(){ seed=(seed*1103515245+12345)%2147483648; return seed/2147483648; }
   for(var i=a.length-1;i>0;i--){ var j=Math.floor(rnd()*(i+1)); var t=a[i];a[i]=a[j];a[j]=t; }
   return a;
 }
 function renumber(){ rows().forEach(function(r,i){
     r.querySelector('.ck-row-n').textContent=('0'+(i+1)).slice(-2); }); }

 function enterBlind(){
   root.classList.add('blind'); root.classList.remove('scored');
   scoreBox.innerHTML=''; clear(); setNodeSizes(true);
   shuffle(rows()).forEach(function(r){ rowsBox.appendChild(r); });
   renumber();
   hint.textContent='Reihenfolge festlegen — ziehen oder ▲▼ — dann auflösen';
   bb.textContent='Auflösen';
 }
 function reveal(){
   var rs=rows();
   var guess={}; rs.forEach(function(r,i){ guess[r.dataset.theme]=i+1; });
   rs.sort(function(a,b){ return (+a.dataset.rank)-(+b.dataset.rank); })
     .forEach(function(r){ rowsBox.appendChild(r); });
   root.classList.remove('blind'); root.classList.add('scored');
   setNodeSizes(false); renumber();
   var n=rs.length, exact=0, near=0, sumAbs=0, sumD2=0;
   rs.forEach(function(r){
     var truth=+r.dataset.rank, g=guess[r.dataset.theme], d=g-truth;
     sumAbs+=Math.abs(d); sumD2+=d*d;
     var el=r.querySelector('.ck-delta');
     if(d===0){ exact++; el.className='ck-delta hit'; el.textContent='genau'; }
     else { if(Math.abs(d)===1) near++;
       el.className='ck-delta '+(Math.abs(d)===1?'near':'miss');
       el.textContent=(d>0?'▲ ':'▼ ')+Math.abs(d); }
   });
   // Spearman ueber Rangdifferenzen
   var rho = n>1 ? 1-(6*sumD2)/(n*(n*n-1)) : 1;
   var worst=rs.slice().sort(function(a,b){
     return Math.abs(guess[b.dataset.theme]-b.dataset.rank)
          - Math.abs(guess[a.dataset.theme]-a.dataset.rank); })[0];
   var wd=Math.abs(guess[worst.dataset.theme]-worst.dataset.rank);
   scoreBox.innerHTML='<b>'+exact+' von '+n+'</b> exakt, <b>'+(exact+near)+'</b> auf ±1 genau · '
     +'Rangkorrelation <b>'+rho.toFixed(2)+'</b> · mittlere Abweichung <b>'
     +(sumAbs/n).toFixed(1)+'</b> Plätze'
     +(wd>=2?'<br><span style="color:#7E8DA8">Grösste Fehleinschätzung: „'
       +esc(worst.dataset.theme)+'“ — '+wd+' Plätze daneben. Genau dieses Thema lohnt '
       +'einen Blick in die Originalbeiträge.</span>':'');
   hint.textContent='Aufgelöst — Blindmodus erneut starten für die nächste Schätzung';
   bb.textContent='Blindmodus';
 }
 if(bb) bb.addEventListener('click',function(){
   bb.classList.toggle('on');
   if(root.classList.contains('blind')) reveal(); else enterBlind(); });

 // Pfeiltasten
 rowsBox.addEventListener('click',function(ev){
   var b=ev.target.closest('.ck-move button'); if(!b||!root.classList.contains('blind')) return;
   var row=b.closest('.ck-row'), dir=+b.dataset.dir;
   var sib=dir<0?row.previousElementSibling:row.nextElementSibling;
   if(!sib) return;
   if(dir<0) rowsBox.insertBefore(row,sib); else rowsBox.insertBefore(sib,row);
   renumber();
 });

 // Ziehen (Pointer Events: funktioniert mit Maus, Trackpad und Touch)
 var drag=null;
 rowsBox.addEventListener('pointerdown',function(ev){
   if(!root.classList.contains('blind')) return;
   if(ev.target.closest('.ck-move')) return;
   var row=ev.target.closest('.ck-row'); if(!row) return;
   drag=row; row.classList.add('dragging');
   rowsBox.setPointerCapture(ev.pointerId); ev.preventDefault();
 });
 rowsBox.addEventListener('pointermove',function(ev){
   if(!drag) return;
   var others=rows().filter(function(r){return r!==drag});
   for(var i=0;i<others.length;i++){
     var b=others[i].getBoundingClientRect();
     if(ev.clientY>b.top && ev.clientY<b.bottom){
       var before = ev.clientY < b.top+b.height/2;
       rowsBox.insertBefore(drag, before?others[i]:others[i].nextSibling);
       renumber(); break;
     }
   }
 });
 function endDrag(ev){ if(!drag) return; drag.classList.remove('dragging'); drag=null;
   try{rowsBox.releasePointerCapture(ev.pointerId)}catch(e){} }
 rowsBox.addEventListener('pointerup',endDrag);
 rowsBox.addEventListener('pointercancel',endDrag);
 var eb=document.getElementById('ckEdges');
 if(eb) eb.addEventListener('click',function(){
   var g=root.querySelector('#ckEdgeLayer'); if(!g) return;
   var off=g.style.display==='none'; g.style.display=off?'':'none'; eb.classList.toggle('on',!off); });
 clear();
})();
"""


def _sent_rgb(netto: float) -> Tuple[int, int, int]:
    """Rot (ablehnend) über Bernstein (gemischt) nach Cyan (zustimmend)."""
    t = max(-1.0, min(1.0, float(netto or 0.0)))
    if t < 0:
        f = t + 1
        return (255, int(77 + (181 - 77) * f), int(99 + (71 - 99) * f))
    return (int(255 + (40 - 255) * t), int(181 + (225 - 181) * t), int(71 + (232 - 71) * t))


def _sent_color(netto: float, alpha: float = None) -> str:
    r, g, b = _sent_rgb(netto)
    if alpha is None:
        return f"rgb({r},{g},{b})"
    return f"rgba({r},{g},{b},{alpha:.2f})"


def render_topic_map(freq: pd.DataFrame, cooc: List[dict], summaries: dict,
                     width: int = 940, height: int = 520) -> Tuple[str, str]:
    """Themen-Landkarte als SVG. Rückgabe: (svg_html, node_json)."""
    if freq.empty:
        return '<div class="ck-hint" style="padding:40px 24px">Keine Themen für die ' \
               'Landkarte.</div>', "{}"
    rows = list(freq.itertuples(index=False))
    nmax = max(int(r.n_kommentare) for r in rows) or 1
    nodes = []
    for r in rows:
        n = int(r.n_kommentare)
        # Radius über Wurzel: Fläche proportional zur Menge, nicht der Durchmesser —
        # sonst überschätzt das Auge große Themen systematisch.
        rad = 16 + 40 * math.sqrt(n / nmax)
        s = summaries.get(r.obercode, {})
        nodes.append({"id": r.obercode, "label": r.obercode, "n": n, "r": round(rad, 1),
                      "autoren": int(r.n_autoren), "threads": int(r.n_threads),
                      "netto": float(r.netto_sentiment),
                      "ki": safe_str(s.get("key_insight")), "sum": safe_str(s.get("summary"))})
    ids = {n["id"] for n in nodes}
    edges = [{"a": e["a"], "b": e["b"], "n": e["n"], "lift": e["lift"],
              "w": min(1.5, e["jaccard"] * 3.2)}
             for e in cooc if e["a"] in ids and e["b"] in ids]

    pos = force_layout(nodes, edges, width=width, height=height)

    epaths = []
    lmax = max([e["lift"] for e in edges], default=1.0) or 1.0
    for e in edges:
        (x1, y1), (x2, y2) = pos[e["a"]], pos[e["b"]]
        mx, my = (x1 + x2) / 2, (y1 + y2) / 2
        # leichte Krümmung, damit parallele Kanten unterscheidbar bleiben
        cx, cy = mx + (y2 - y1) * 0.09, my - (x2 - x1) * 0.09
        op = 0.16 + 0.55 * min(1.0, e["lift"] / lmax)
        sw = 0.8 + 3.2 * min(1.0, e["w"] / 1.5)
        epaths.append(
            f'<path class="ck-edge" data-a="{_h(e["a"])}" data-b="{_h(e["b"])}" '
            f'd="M{x1:.1f},{y1:.1f} Q{cx:.1f},{cy:.1f} {x2:.1f},{y2:.1f}" fill="none" '
            f'stroke="url(#ckEdge)" stroke-width="{sw:.2f}" stroke-opacity="{op:.2f}" '
            f'stroke-linecap="round"/>')

    gnodes = []
    for nd in nodes:
        x, y = pos[nd["id"]]
        col = _sent_color(nd["netto"])
        label = nd["label"] if len(nd["label"]) <= 26 else nd["label"][:25] + "…"
        gnodes.append(f'''<g class="ck-node" data-id="{_h(nd['id'])}">
  <circle cx="{x:.1f}" cy="{y:.1f}" r="{nd['r']+12:.1f}" fill="{col}" opacity=".10"/>
  <circle cx="{x:.1f}" cy="{y:.1f}" r="{nd['r']:.1f}" fill="{col}" fill-opacity=".17"
          stroke="{col}" stroke-width="1.6" filter="url(#ckGlow)"/>
  <circle cx="{x:.1f}" cy="{y:.1f}" r="{max(2.6, nd['r']*0.13):.1f}" fill="{col}"/>
  <text x="{x:.1f}" y="{y + nd['r'] + 17:.1f}" text-anchor="middle" fill="#E8EDF7"
        font-family="Inter,sans-serif" font-size="12.5" font-weight="500">{_h(label)}</text>
  <text class="ck-nlabel" x="{x:.1f}" y="{y + nd['r'] + 31:.1f}" text-anchor="middle"
        fill="#7E8DA8" font-family="DM Mono,monospace" font-size="10">n={nd['n']} · {nd['autoren']} Aut.</text>
  <circle class="hit" cx="{x:.1f}" cy="{y:.1f}" r="{nd['r']+14:.1f}"/>
</g>''')

    svg = f'''<svg viewBox="0 0 {width} {height}" role="img"
  aria-label="Themen-Landkarte: Kreisgröße zeigt die Zahl der Beiträge, Linien zeigen
  gemeinsame Nennungen im selben Beitrag.">
<defs>
  <linearGradient id="ckEdge" x1="0" y1="0" x2="1" y2="1">
    <stop offset="0%" stop-color="#28E1E8"/><stop offset="100%" stop-color="#8B7CFF"/>
  </linearGradient>
  <filter id="ckGlow" x="-60%" y="-60%" width="220%" height="220%">
    <feGaussianBlur stdDeviation="5" result="b"/>
    <feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge>
  </filter>
</defs>
<g id="ckEdgeLayer">{"".join(epaths)}</g>
{"".join(gnodes)}
</svg>'''
    return svg, json.dumps({"nodes": nodes, "edges": edges}, ensure_ascii=False)


def render_cockpit(freq: pd.DataFrame, cooc: List[dict], signals: List[dict],
                   summaries: dict, idx_matrices: Dict[str, pd.DataFrame],
                   stats: dict) -> str:
    """Das komplette Cockpit als eigenständiger HTML-Block."""
    svg, njson = render_topic_map(freq, cooc, summaries)

    sig_html = "".join(
        f'<div class="ck-sig t-{_h(s["typ"])}"><div class="ck-sig-h">'
        f'<span class="ck-sig-t">{_h(s["typ"])}</span>'
        f'<span class="ck-sig-v">{_h(s["wert"])}</span></div>'
        f'<div class="ck-sig-n">{_h(s["thema"])}</div>'
        f'<div class="ck-sig-x">{_h(s["text"])}</div></div>' for s in (signals or [])) \
        or '<div class="ck-hint">Keine strukturellen Auffälligkeiten oberhalb der Schwellen. ' \
           'Bei kleinem Korpus normal.</div>'

    # Größen-Ranking mit Blindmodus
    base_n = int(stats.get("n_analysierbar", 0)) or 1
    rows = []
    if not freq.empty:
        nmax = max(int(r.n_kommentare) for r in freq.itertuples(index=False)) or 1
        for i, r in enumerate(freq.itertuples(index=False), 1):
            n = int(r.n_kommentare)
            col = _sent_color(float(r.netto_sentiment))
            col2 = _sent_color(float(r.netto_sentiment), 0.33)
            rows.append(
                f'<div class="ck-row" data-rank="{i}" data-theme="{_h(r.obercode)}">'
                f'<span class="ck-grip">⠿</span>'
                f'<span class="ck-row-n">{i:02d}</span>'
                f'<span class="ck-row-t" title="{_h(r.obercode)}">{_h(r.obercode)}</span>'
                f'<span class="ck-move"><button type="button" data-dir="-1" '
                f'aria-label="nach oben">▲</button><button type="button" data-dir="1" '
                f'aria-label="nach unten">▼</button></span>'
                f'<span class="ck-delta"></span>'
                f'<span class="ck-bar"><span class="ck-bar-f" style="width:{100*n/nmax:.0f}%;'
                f'background:linear-gradient(90deg,{col},{col2})"></span></span>'
                f'<span class="ck-row-v"><i>{n} · {100*n/base_n:.0f}%</i></span></div>')

    # Index-Heatmap
    hm = ""
    for name, m in (idx_matrices or {}).items():
        if m is None or m.empty:
            continue
        cols = [c for c in m.columns if c not in ("thema", "n_gesamt", "anteil_gesamt")]
        if not cols:
            continue
        basen = m.attrs.get("basen", {})
        head = "".join(f'<th>{_h(c)}<br><span style="opacity:.6">n={basen.get(c,"?")}</span></th>'
                       for c in cols)
        body = []
        for _, r in m.head(12).iterrows():
            tds = []
            for c in cols:
                v = r[c]
                v = int(v) if isinstance(v, (int, float)) else 0
                # 100 = Durchschnitt. Farbe nur bei relevanter Abweichung.
                # Breites neutrales Band mit Absicht: Indexwerte schwanken bei
                # Gruppengroessen unter ~50 stark. Wer 92 und 108 einfaerbt,
                # laesst Rauschen wie Befund aussehen.
                if v >= 150:
                    bg, fg = "#28E1E8", "#06181c"
                elif v >= 125:
                    bg, fg = "rgba(40,225,232,.38)", "#DFF7F9"
                elif v <= 55:
                    bg, fg = "#FF4D63", "#2a0509"
                elif v <= 80:
                    bg, fg = "rgba(255,77,99,.32)", "#FFE2E6"
                else:
                    bg, fg = "rgba(255,255,255,.055)", "#8E9BB4"
                tds.append(f'<td style="background:{bg};color:{fg}"><i>{v}</i></td>')
            body.append(f'<tr><td class="name" title="{_h(r["thema"])}">{_h(r["thema"])}</td>'
                        f'<td style="background:rgba(255,255,255,.03);color:#7E8DA8">'
                        f'<i>{int(r["n_gesamt"])}</i></td>{"".join(tds)}</tr>')
        hm += (f'<div class="ck-lbl" style="margin-top:16px">Index nach {_h(name)} '
               f'<span>100 = Durchschnitt des Gesamtkorpus</span></div>'
               f'<div style="overflow-x:auto"><table class="ck-hm"><tr><th>Thema</th>'
               f'<th>n</th>{head}</tr>{"".join(body)}</table></div>')

    return f'''<div class="ck" id="cockpit">
  <div class="ck-top">
    <div class="ck-ttl">Erkenntnis-Cockpit
      <b>Themen-Landkarte</b></div>
    <div class="ck-tools">
      <button class="ck-btn on" id="ckEdges">Verbindungen</button>
      <button class="ck-btn" id="ckBlind">Blindmodus</button>
    </div>
  </div>
  <div class="ck-grid">
    <div class="ck-map">{svg}</div>
    <div class="ck-side">
      <div class="ck-lbl">Was auffällt <span>{len(signals or [])}</span></div>
      <div class="ck-cover">Im Blindmodus verdeckt.<br><br>
        Die Befunde nennen konkrete Zahlen — wer sie jetzt liest, hat nichts mehr
        zu schätzen. Erst die Reihenfolge links festlegen, dann auflösen.</div>
      <div id="ckSignals">{sig_html}</div>
    </div>
  </div>
  <div class="ck-legend">
    <span><i style="background:#FF4D63"></i>überwiegend ablehnend</span>
    <span><i style="background:#FFB547"></i>gemischt</span>
    <span><i style="background:#28E1E8"></i>überwiegend zustimmend</span>
    <span><i style="background:linear-gradient(90deg,#28E1E8,#8B7CFF)"></i>Linie = gemeinsame Nennung</span>
    <span>Fläche ∝ Zahl der Beiträge</span>
  </div>
  <div class="ck-detail" id="ckDetail"></div>
  <div class="ck-rows">
    <div class="ck-lbl">Größenordnung
      <span id="ckRowHint">Blindmodus: erst schätzen, dann auflösen</span></div>
    <div class="ck-score" id="ckScore"></div>
    <div id="ckRows">{"".join(rows)}</div>
    {hm}
  </div>
</div>
<script>window.__CK_DATA__ = {njson};</script>
<script>{COCKPIT_JS}</script>'''


def _sent_class(row) -> str:
    p, n = int(row.get("sentiment_pos", 0)), int(row.get("sentiment_neg", 0))
    if n > p * 1.5 and n >= 2:
        return "neg"
    if p > n * 1.5 and p >= 2:
        return "pos"
    return ""


def generate_dashboard(meta: dict, stats: dict, konz: dict, codebuch: List[dict],
                       freq_ober: pd.DataFrame, freq_sub: pd.DataFrame,
                       summaries_ober: dict, summaries_sub: dict,
                       long_df: pd.DataFrame, fragen_out: List[dict],
                       quellen: pd.DataFrame, splits: Dict[str, pd.DataFrame],
                       log: RunLog, cooc: List[dict] = None, signals: List[dict] = None,
                       idx_matrices: Dict[str, pd.DataFrame] = None,
                       max_quotes_per_sub: int = 8) -> bytes:
    base_n = int(stats.get("n_analysierbar", 0)) or 1

    # ── KPI-Zeile ───────────────────────────────────────────────────────────
    kpis = [
        (f"{stats.get('n_analysierbar', 0):,}".replace(",", "."), "Beiträge analysiert",
         f"von {stats.get('n_roh', 0)} extrahiert"),
        (f"{stats.get('n_autoren', 0):,}".replace(",", "."), "Autor:innen",
         f"Ø {konz.get('beitraege_pro_autor', 'n/v')} Beiträge"),
        (str(stats.get("n_communities", 0)), "Communities", f"{stats.get('n_dateien', 0)} Dateien"),
        (str(len(codebuch)), "Themen", f"{len(flatten_subcodes(codebuch))} Subthemen"),
        (f"{stats.get('n_duplikate', 0)}", "Duplikate entfernt", "nicht mitgezählt"),
    ]
    kpi_html = "".join(
        f'<div class="kpi"><div class="v">{_h(v)}</div><div class="l">{_h(l)}</div>'
        f'<div class="h">{_h(h)}</div></div>' for v, l, h in kpis)

    # ── Warnbanner ──────────────────────────────────────────────────────────
    banners = ['<div class="banner"><b>Lesehinweis:</b> Community-Daten sind selbstselektiert. '
               'Die N-Werte beschreiben die <b>Salienz im Diskurs</b>, nicht die Verbreitung in '
               'der Zielgruppe. Nicht auf Marktanteile hochrechnen.</div>']
    if konz.get("verfuegbar") and konz.get("top10pct_anteil", 0) > 0.5:
        banners.append(f'<div class="banner"><b>Konzentration:</b> Die aktivsten 10 % der '
                       f'Autor:innen stellen {konz["top10pct_anteil"]:.0%} aller Beiträge '
                       f'(Gini {konz.get("gini")}). Themen können das Interesse weniger '
                       f'Vielschreiber:innen abbilden.</div>')
    n_unkod = int(meta.get("n_unkodiert", 0) or 0)
    if n_unkod:
        banners.append(f'<div class="banner err"><b>{n_unkod} Beiträge ohne Kodierung.</b> '
                       f'Sie zählen in keiner Häufigkeit mit; die N-Werte unten beziehen sich '
                       f'auf den kodierten Teil des Korpus. Details im Excel-Sheet '
                       f'"99_Fail_Loud_Log".</div>')
    elif log.n_errors:
        banners.append(f'<div class="banner"><b>{log.n_errors} technische Ereignisse</b> im Lauf, '
                       f'durch Auto-Split bzw. Reparatur-Pass aufgefangen. Alle Beiträge sind '
                       f'kodiert. Details im Excel-Sheet "99_Fail_Loud_Log".</div>')
    low_conf = quellen[quellen["extraktion_konfidenz"] < 0.5] if not quellen.empty else pd.DataFrame()
    if not low_conf.empty:
        banners.append(f'<div class="banner"><b>{len(low_conf)} Datei(en)</b> mit niedriger '
                       f'Extraktionskonfidenz — Kommentartrennung dort manuell prüfen: '
                       f'{_h(", ".join(low_conf["datei"].head(6).tolist()))}</div>')

    # ── Forschungsfragen ────────────────────────────────────────────────────
    fragen_html = ""
    if fragen_out:
        cards = []
        for i, f in enumerate(fragen_out):
            ev = safe_str(f.get("evidenzgrad"))
            evc = {"stark": "pos", "mittel": "", "schwach": "warn"}.get(ev, "warn")
            belege = "".join(
                f'<div class="quote"><div class="q-dot"></div><div class="q-content">'
                f'<div class="q-text">{_h(b["text"][:600])}</div>'
                f'<div class="q-src"><span class="chip">{_h(b["id"])}</span></div></div>'
                f'<button class="cbtn" onclick="cp({_js(b["text"])},this)">Copy</button></div>'
                for b in f.get("belege", []))
            report = (f"{f['frage']}\n\nKEY INSIGHT: {f.get('key_insight','')}\n\n"
                      f"ANTWORT: {f.get('antwort','')}\n\nEVIDENZ: {ev} — "
                      f"{f.get('evidenz_begruendung','')}\n\nLÜCKEN: {f.get('offene_luecken','')}\n\n"
                      f"Basis: {f.get('n',0)} Beiträge")
            cards.append(f"""
<div class="qcard" onclick="toggleQ(this,event)">
  <div class="qcard-hdr">
    <div class="qnum">{_h(f.get('tag',''))}</div>
    <div class="qtitle">{_h(f['frage'])}</div>
    <div class="qmeta">
      <span class="qbadge">n={f.get('n',0)}</span>
      <span class="qbadge {evc}">Evidenz {_h(ev)}</span>
      <button class="cbtn" onclick="cp({_js(report)},this)">Copy</button>
    </div>
    <div class="chev">&#9662;</div>
  </div>
  <div class="qcard-body" onclick="event.stopPropagation()">
    <div class="igrid">
      <div class="iblock ki"><div class="iblock-lbl">Key Insight
        <button class="cbtn" onclick="cp({_js(f.get('key_insight',''))},this)">Copy</button></div>
        <div class="iblock-txt">{_h(f.get('key_insight',''))}</div></div>
      <div class="iblock sm"><div class="iblock-lbl">Antwort
        <button class="cbtn" onclick="cp({_js(f.get('antwort',''))},this)">Copy</button></div>
        <div class="iblock-txt">{_h(f.get('antwort',''))}</div></div>
      <div class="iblock tn"><div class="iblock-lbl">Evidenzbewertung</div>
        <div class="iblock-txt">{_h(f.get('evidenz_begruendung',''))}</div></div>
      <div class="iblock sm"><div class="iblock-lbl">Offene Lücken</div>
        <div class="iblock-txt">{_h(f.get('offene_luecken',''))}</div></div>
    </div>
    <div class="sub-panel"><div class="iblock-lbl">Belege</div>{belege}</div>
  </div>
</div>""")
        fragen_html = (f'<div class="sec" id="fragen"><div class="sec-h"><span>Forschungsfragen</span>'
                       f'<span>{len(fragen_out)}</span></div>{"".join(cards)}</div>')

    # ── Themenkarten ────────────────────────────────────────────────────────
    quotes_by_sub: Dict[str, List[dict]] = defaultdict(list)
    if not long_df.empty:
        for r in long_df.sort_values("relevanz", ascending=False).itertuples(index=False):
            if len(quotes_by_sub[r.subcode]) < max_quotes_per_sub:
                quotes_by_sub[r.subcode].append({
                    "id": r.kommentar_id, "text": r.text, "sent": r.sentiment,
                    "community": r.community, "autor": r.autor_pseudonym,
                    "datum": r.datum, "url": r.url})

    sub_by_ober: Dict[str, list] = defaultdict(list)
    if not freq_sub.empty:
        for r in freq_sub.itertuples(index=False):
            sub_by_ober[r.obercode].append(r)

    theme_cards = []
    ober_rows = list(freq_ober.itertuples(index=False)) if not freq_ober.empty else []
    max_n = max([int(r.n_kommentare) for r in ober_rows], default=1)

    for i, r in enumerate(ober_rows, 1):
        ober = r.obercode
        s = summaries_ober.get(ober, {})
        sc = _sent_class({"sentiment_pos": r.sentiment_pos, "sentiment_neg": r.sentiment_neg})

        sub_html = []
        for sr in sub_by_ober.get(ober, []):
            qs = quotes_by_sub.get(sr.subcode, [])
            ssum = summaries_sub.get(sr.subcode, {})
            pct = int(100 * int(sr.n_kommentare) / max(1, max_n))
            qhtml = "".join(
                f'<div class="quote"><div class="q-dot"></div><div class="q-content">'
                f'<div class="q-text">{_h(q["text"][:900])}</div><div class="q-src">'
                f'<span class="chip">{_h(q["id"])}</span>'
                f'<span class="chip">{_h(q["community"])}</span>'
                + (f'<span class="chip">{_h(q["autor"])}</span>' if q["autor"] else "")
                + (f'<span class="chip">{_h(q["datum"])}</span>' if q["datum"] else "")
                + f'<span class="chip {("pos" if q["sent"]=="positiv" else "neg" if q["sent"]=="negativ" else "amb" if q["sent"]=="ambivalent" else "")}">{_h(q["sent"])}</span>'
                + '</div></div>'
                f'<button class="cbtn" onclick="cp({_js(q["text"])},this)">Copy</button></div>'
                for q in qs)
            ki_line = (f'<div class="mini">Key Insight: {_h(ssum.get("key_insight",""))}</div>'
                       if ssum.get("key_insight") else "")
            sub_html.append(f"""
<div class="oc-block">
  <div class="oc-hdr" onclick="toggleOC(this)">
    <div class="oc-name">{_h(sr.subcode)}</div>
    <div class="oc-bar-w"><div class="oc-bar"><div class="oc-bar-f" style="width:{pct}%"></div></div>
      <div class="oc-n">{int(sr.n_kommentare)}</div></div>
    <span class="chip">{int(sr.n_autoren)} Autor:innen</span>
    <span class="chip">{int(sr.n_communities)} Comm.</span>
    <div class="oc-cv">&#9662;</div>
  </div>
  <div class="quotes-wrap">{ki_line}{qhtml or '<div class="mini">Keine Belege verfügbar.</div>'}</div>
</div>""")

        lex = "".join(f"<span>{_h(x)}</span>" for x in s.get("sprache_der_community", []))
        report = (f"THEMA: {ober}\n\nKEY INSIGHT: {s.get('key_insight','')}\n\n"
                  f"SUMMARY: {s.get('summary','')}\n\nSPANNUNGSFELD: {s.get('spannungsfeld','')}\n\n"
                  f"BASIS: {int(r.n_kommentare)} Beiträge ({int(r.anteil_kommentare*100)}% des Korpus), "
                  f"{int(r.n_autoren)} Autor:innen, {int(r.n_threads)} Threads, "
                  f"{int(r.n_communities)} Communities\n"
                  f"SENTIMENT: +{int(r.sentiment_pos)} / -{int(r.sentiment_neg)} / "
                  f"~{int(r.sentiment_amb)}")

        theme_cards.append(f"""
<div class="qcard" onclick="toggleQ(this,event)">
  <div class="qcard-hdr">
    <div class="qnum">T{i:02d}</div>
    <div class="qtitle">{_h(ober)}</div>
    <div class="qmeta">
      <span class="qbadge">n={int(r.n_kommentare)} &#183; {int(r.anteil_kommentare*100)}%</span>
      <span class="qbadge">{int(r.n_autoren)} Autor:innen</span>
      <span class="qbadge {sc}">Netto {r.netto_sentiment:+.2f}</span>
      <button class="cbtn" onclick="cp({_js(report)},this)">Copy</button>
    </div>
    <div class="chev">&#9662;</div>
  </div>
  <div class="qcard-body" onclick="event.stopPropagation()">
    <div class="itabs">
      <div class="itab active" data-tab="ins{i}" onclick="switchTab(this.closest('.qcard'),'ins{i}',event)">Insight</div>
      <div class="itab" data-tab="sub{i}" onclick="switchTab(this.closest('.qcard'),'sub{i}',event)">Subthemen &amp; Belege</div>
      <div class="itab" data-tab="bas{i}" onclick="switchTab(this.closest('.qcard'),'bas{i}',event)">Basis</div>
    </div>
    <div class="ipanel active" data-panel="ins{i}">
      <div class="igrid">
        <div class="iblock ki"><div class="iblock-lbl">Key Insight
          <button class="cbtn" onclick="cp({_js(s.get('key_insight',''))},this)">Copy</button></div>
          <div class="iblock-txt">{_h(s.get('key_insight','') or '—')}</div></div>
        <div class="iblock sm"><div class="iblock-lbl">Summary
          <button class="cbtn" onclick="cp({_js(s.get('summary',''))},this)">Copy</button></div>
          <div class="iblock-txt">{_h(s.get('summary','') or '—')}</div></div>
        <div class="iblock tn"><div class="iblock-lbl">Spannungsfeld</div>
          <div class="iblock-txt">{_h(s.get('spannungsfeld','') or '—')}</div></div>
        <div class="iblock sm"><div class="iblock-lbl">Sprache der Community</div>
          <div class="lex">{lex or '<span>—</span>'}</div></div>
      </div>
    </div>
    <div class="ipanel" data-panel="sub{i}"><div class="sub-panel">{"".join(sub_html) or '<div class="mini">Keine Subthemen.</div>'}</div></div>
    <div class="ipanel" data-panel="bas{i}"><div class="sub-panel">
      <table class="dt"><tr><th>Kennzahl</th><th>Wert</th><th>Bezug</th></tr>
      <tr><td>Beiträge</td><td>{int(r.n_kommentare)}</td><td>{int(r.anteil_kommentare*100)}% von {base_n}</td></tr>
      <tr><td>Autor:innen</td><td>{int(r.n_autoren)}</td><td>{int(r.anteil_autoren*100)}% aller Autor:innen</td></tr>
      <tr><td>Threads</td><td>{int(r.n_threads)}</td><td>Streuung über Diskussionen</td></tr>
      <tr><td>Communities</td><td>{int(r.n_communities)}</td><td>Streuung über Quellen</td></tr>
      <tr><td>Sentiment</td><td>+{int(r.sentiment_pos)} / -{int(r.sentiment_neg)} / ~{int(r.sentiment_amb)}</td><td>Netto {r.netto_sentiment:+.2f}</td></tr>
      </table>
      <div class="mini">Ein Thema, das in vielen Threads und bei vielen Autor:innen auftaucht,
      ist belastbarer als eines mit hohem N aus einem einzigen Thread.</div>
    </div></div>
  </div>
</div>""")

    themen_html = (f'<div class="sec" id="themen"><div class="sec-h"><span>Themen</span>'
                   f'<span><button class="tbtn" onclick="expandAll()">Alle öffnen</button> '
                   f'<button class="tbtn" onclick="collapseAll()">Alle schließen</button></span></div>'
                   f'{"".join(theme_cards)}<div id="nores">Kein Treffer.</div></div>')

    # ── Splits ──────────────────────────────────────────────────────────────
    split_html = ""
    for name, sdf in (splits or {}).items():
        if sdf is None or sdf.empty:
            continue
        head = "".join(f"<th>{_h(c)}</th>" for c in sdf.columns)
        body = []
        for _, row in sdf.iterrows():
            cls = ' class="basis"' if str(row.iloc[0]).startswith("BASIS") else ""
            body.append(f"<tr{cls}>" + "".join(f"<td>{_h(v)}</td>" for v in row.tolist()) + "</tr>")
        split_html += (f'<div class="sec-h" style="margin-top:18px"><span>Split nach {_h(name)}</span>'
                       f'<button class="cbtn" onclick="cpEl(\'split_{_h(name)}\',this)">Tabelle kopieren</button></div>'
                       f'<div class="tbl-wrap"><table class="dt" id="split_{_h(name)}">'
                       f'<tr>{head}</tr>{"".join(body)}</table></div>')
    if split_html:
        split_html = f'<div class="sec" id="splits"><div class="sec-h"><span>Splits</span></div>{split_html}</div>'

    # ── Quellenregister ─────────────────────────────────────────────────────
    qcols = ["datei", "community", "plattform", "thread_titel", "url", "erhebungsweg",
             "abrufdatum", "n_analysiert", "n_autoren", "zeitraum_von", "zeitraum_bis",
             "sprachen", "extraktion_strategie", "extraktion_konfidenz"]
    qcols = [c for c in qcols if c in quellen.columns]
    qhead = "".join(f"<th>{_h(c)}</th>" for c in qcols)
    qbody = []
    for _, row in quellen.iterrows():
        cells = []
        for c in qcols:
            v = row[c]
            if c == "url" and safe_str(v):
                cells.append(f'<td><a href="{_h(v)}" target="_blank" rel="noopener">Link</a></td>')
            elif c == "extraktion_konfidenz":
                col = "var(--green)" if float(v or 0) >= 0.7 else (
                    "var(--amber)" if float(v or 0) >= 0.5 else "var(--accent)")
                cells.append(f'<td style="color:{col};font-weight:600">{float(v or 0):.0%}</td>')
            else:
                cells.append(f"<td>{_h(v)}</td>")
        qbody.append("<tr>" + "".join(cells) + "</tr>")
    quellen_html = (f'<div class="sec" id="quellen"><div class="sec-h"><span>Quellenregister</span>'
                    f'<button class="cbtn" onclick="cpEl(\'srctbl\',this)">Tabelle kopieren</button></div>'
                    f'<div class="tbl-wrap"><table class="dt" id="srctbl"><tr>{qhead}</tr>'
                    f'{"".join(qbody)}</table>'
                    f'<div class="mini">Konfidenz = Sicherheit der automatischen Kommentartrennung. '
                    f'Unter 50 % bitte stichprobenartig gegen die Originalseite prüfen.</div></div></div>')

    cockpit_html = render_cockpit(freq_ober, cooc or [], signals or [], summaries_ober,
                                  idx_matrices or {}, stats)

    pills = (f'<span class="pill"><span class="dot" style="background:var(--accent)"></span>'
             f'{_h(meta.get("modus",""))}</span>'
             f'<span class="pill"><span class="dot" style="background:var(--blue)"></span>'
             f'{_h(meta.get("modell",""))}</span>'
             f'<span class="pill"><span class="dot" style="background:var(--green)"></span>'
             f'{stats.get("n_analysierbar",0)} Beiträge</span>'
             f'<span class="pill"><span class="dot" style="background:var(--t4)"></span>'
             f'{datetime.now().strftime("%d.%m.%Y")}</span>')

    html_out = f"""<!DOCTYPE html>
<html lang="de"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Netno·View — {_h(meta.get('projekt',''))}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&family=DM+Mono:wght@400;500&display=swap">
<style>{DASH_CSS}{COCKPIT_CSS}</style></head><body>
<header class="hdr">
  <div class="logo"><div class="logo-mark">spiegel<em>|</em>institut</div>
  <div class="logo-sep"></div><div class="logo-badge">Netno&#183;View</div></div>
  <div class="hnav">
    {'<a href="#fragen">Fragen</a>' if fragen_out else ''}
    <a href="#cockpit">Cockpit</a>
    <a href="#themen">Themen</a>
    {'<a href="#splits">Splits</a>' if split_html else ''}
    <a href="#quellen">Quellen</a>
  </div>
  <div class="search-wrap">
    <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
      <circle cx="11" cy="11" r="8"/><path d="m21 21-4.35-4.35"/></svg>
    <input class="si" id="searchInput" type="text" placeholder="Themen, Codes, Zitate&#8230;">
  </div>
</header>
<div class="wrap">
  <div class="ptitle"><h1>Netnographie</h1>
    <div class="ptitle-project">{_h(meta.get('projekt','') or 'Community-Analyse')}</div>
    <p>Spiegel Institut Mannheim &#183; {_h(meta.get('user',''))}</p>
    <div class="pills">{pills}</div></div>
  <div class="kpis">{kpi_html}</div>
  {''.join(banners)}
  {cockpit_html}
  {fragen_html}
  {themen_html}
  {split_html}
  {quellen_html}
</div>
<script>{DASH_JS}</script>
</body></html>"""
    return html_out.encode("utf-8")


# ============================================================
# STREAMLIT-UI
# ============================================================
def add_header():
    st.markdown("""
    <style>
      .nhdr{display:flex;justify-content:space-between;align-items:center;
            background:#E63D50;padding:12px 16px;border-radius:8px;}
      .nhdr h1{color:#fff;margin:0;font-size:20px;font-weight:700;}
      .nhdr span{color:rgba(255,255,255,.85);font-size:12px;}
    </style>
    <div class="nhdr"><h1>AI Netnography Tool</h1>
    <span>HTML&nbsp;&rarr;&nbsp;Korpus&nbsp;&rarr;&nbsp;Themen&nbsp;&rarr;&nbsp;Dashboard</span></div>
    """, unsafe_allow_html=True)


add_header()

st.markdown("""
<style>
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&display=swap');
section.main, section.main *, section[data-testid="stMain"], section[data-testid="stMain"] *,
header[data-testid="stHeader"], header[data-testid="stHeader"] * { font-family: 'Inter', sans-serif !important; }
/* Icon-Fonts von der Inter-Regel ausnehmen: Streamlit rendert Icons als Ligaturen.
   Diese Regel MUSS nach der Inter-Regel stehen, sonst erscheint der Ligaturname als Text. */
[data-testid="stIconMaterial"], [data-testid="stIconMaterial"] *,
.material-icons, .material-icons-outlined, .material-icons-round,
[class*="material-symbols"], [class*="material-icons"], span[translate="no"] {
  font-family: 'Material Symbols Rounded', 'Material Symbols Outlined', 'Material Icons' !important;
  font-feature-settings: 'liga' !important;
}
.main .block-container { background:#F7F8FA; padding-top:1.5rem; }
div.stButton > button[kind="primary"], div.stDownloadButton > button[kind="primary"] {
  background:#E63D50 !important; border:none !important; color:#fff !important;
  border-radius:8px !important; font-weight:600 !important; font-size:13.5px !important;
  box-shadow:0 2px 8px rgba(230,61,80,.22) !important; }
div.stButton > button[kind="primary"]:hover { background:#c0293b !important; }
div.stButton > button:not([kind="primary"]) {
  background:#fff !important; border:1.5px solid #D0D5DD !important; color:#344054 !important;
  border-radius:8px !important; font-weight:500 !important; font-size:13px !important; }
div.stButton > button:not([kind="primary"]):hover { border-color:#E63D50 !important; color:#E63D50 !important; }
div.stDownloadButton > button { background:#fff !important; border:1.5px solid #D0D5DD !important;
  color:#344054 !important; border-radius:8px !important; }
details[data-testid="stExpander"] { background:#fff !important; border:1.5px solid #E4E7ED !important;
  border-radius:10px !important; margin-bottom:10px !important; }
details[data-testid="stExpander"] summary { font-weight:600 !important; font-size:13.5px !important; }
div[data-testid="stMetric"] { background:#fff !important; border:1.5px solid #E4E7ED !important;
  border-radius:10px !important; padding:1rem !important; }
div[data-testid="stDataFrame"] { border-radius:10px !important; border:1.5px solid #E4E7ED !important; }
div[data-baseweb="tab-list"] { background:#F0F2F5 !important; border-radius:8px !important; padding:3px !important; }
button[data-baseweb="tab"][aria-selected="true"] { background:#fff !important; color:#E63D50 !important; }
</style>
""", unsafe_allow_html=True)


def step_header(number, title: str, subtitle: str = "", done: bool = False) -> None:
    bg = "#28a745" if done else "#E63D50"
    sub = (f"<div style='font-size:13px;color:#667085;margin-top:2px;'>{subtitle}</div>"
           if subtitle else "")
    st.markdown(f"""
    <div style="display:flex;align-items:flex-start;gap:12px;margin:26px 0 10px 0;">
      <div style="flex:0 0 auto;width:30px;height:30px;border-radius:50%;background:{bg};
                  color:#fff;display:flex;align-items:center;justify-content:center;
                  font-weight:700;font-size:15px;box-shadow:0 2px 6px rgba(0,0,0,.15);">{number}</div>
      <div style="flex:1 1 auto;">
        <div style="font-size:19px;font-weight:700;color:#1A1D23;line-height:30px;">{title}</div>
        {sub}
      </div>
    </div>""", unsafe_allow_html=True)


def sub_step(title: str, subtitle: str = "") -> None:
    sub = (f"<span style='font-weight:400;color:#667085;font-size:13px;'> — {subtitle}</span>"
           if subtitle else "")
    st.markdown(f"<div style='margin:18px 0 4px 0;padding-left:10px;border-left:3px solid #E63D50;"
                f"font-size:14.5px;font-weight:600;color:#1A1D23;'>{title}{sub}</div>",
                unsafe_allow_html=True)


def export_card(icon: str, title: str, desc: str, primary: bool = False,
                ready: bool = None) -> None:
    accent = "#E63D50" if primary else "#98A2B3"
    badge = ""
    if ready is True:
        badge = ("<span style='background:#E7F6EC;color:#177245;font-size:10.5px;font-weight:700;"
                 "padding:2px 7px;border-radius:99px;margin-left:8px;'>BEREIT</span>")
    elif ready is False:
        badge = ("<span style='background:#F0F2F5;color:#98A2B3;font-size:10.5px;font-weight:700;"
                 "padding:2px 7px;border-radius:99px;margin-left:8px;'>OFFEN</span>")
    st.markdown(f"""
    <div style="border-left:4px solid {accent};padding:2px 0 2px 12px;margin-bottom:8px;">
      <div style="font-size:{'16px' if primary else '14px'};font-weight:700;color:#1A1D23;">
        {icon} {title}{badge}</div>
      <div style="font-size:12.5px;color:#667085;margin-top:3px;line-height:1.45;">{desc}</div>
    </div>""", unsafe_allow_html=True)


def dot(filled: bool) -> str:
    return "🟢" if filled else "🔴"


# ── Session-State ───────────────────────────────────────────────────────────
SS = st.session_state
SS.setdefault("files", {})          # name -> {"raw":bytes,"html":str,"encoding":str}
SS.setdefault("file_meta", {})      # name -> dict
SS.setdefault("extractions", {})    # name -> extraction dict
SS.setdefault("corpus", None)
SS.setdefault("stats", {})
SS.setdefault("results", None)
SS.setdefault("salt", hashlib.sha256(str(time.time()).encode()).hexdigest()[:16])

if not HAS_BS4:
    st.error("**BeautifulSoup4 fehlt.** Ohne HTML-Parser läuft nichts: "
             "`pip install beautifulsoup4 lxml`")
    st.stop()


# ── Sidebar ─────────────────────────────────────────────────────────────────
st.sidebar.markdown("### Projekt-Informationen")
p_id = st.sidebar.text_input("Projekt-ID", key="p_id")
p_name = st.sidebar.text_input("Projektname", key="p_name")
p_user = st.sidebar.text_input("Analyst:in", key="p_user")
st.sidebar.markdown(
    f"{dot(bool(p_id))} Projekt-ID &nbsp; {dot(bool(p_name))} Projektname &nbsp; "
    f"{dot(bool(p_user))} Analyst:in", unsafe_allow_html=True)

st.sidebar.markdown("---")
st.sidebar.markdown("### Modell")
_cfg_preview = resolve_llm_cfg()
st.sidebar.caption(f"Deployment: `{_cfg_preview.get('deployment')}`")
if is_reasoning_model(_cfg_preview):
    st.sidebar.selectbox(
        "Reasoning-Effort", REASONING_EFFORTS,
        index=REASONING_EFFORTS.index(_cfg_preview.get("reasoning_effort"))
        if _cfg_preview.get("reasoning_effort") in REASONING_EFFORTS else 0,
        key="OPENAI_REASONING_EFFORT",
        help="'none' = schnell, günstig, temperature=0 (reproduzierbar). "
             "Höhere Stufen denken mehr nach, kosten mehr Output-Tokens und "
             "ignorieren temperature.")
    _cfg_preview = resolve_llm_cfg()
st.sidebar.caption("Endpoint: " + ("gesetzt ✅" if _cfg_preview.get("endpoint") else "OpenAI-Default"))
st.sidebar.caption("API-Key: " + ("gesetzt ✅" if _cfg_preview.get("api_key") else "FEHLT ❌"))

use_cache = st.sidebar.checkbox("Prompt-Cache nutzen", value=True,
                                help="Identische Prompts werden nicht erneut bezahlt. "
                                     "Abgeschnittene oder unparsbare Antworten landen nie im Cache.")
_n_cache, _c_cache = cache_stats()
st.sidebar.caption(f"Cache: {_n_cache} Einträge · {_c_cache:.2f} € bereits bezahlt")
if st.sidebar.button("Cache leeren"):
    st.sidebar.success("Cache geleert." if cache_clear() else "Fehlgeschlagen.")

st.sidebar.markdown("---")
st.sidebar.markdown("### Datenschutz")
st.sidebar.caption("Nutzernamen werden pseudonymisiert. Der Projekt-Salt wechselt pro Session, "
                   "d. h. Pseudonyme sind zwischen Projekten nicht verknüpfbar.")
fixed_salt = st.sidebar.text_input("Fester Salt (optional, für reproduzierbare Pseudonyme)",
                                   value="", type="password")
if fixed_salt:
    SS["salt"] = fixed_salt


# ============================================================
# SCHRITT 1 — Dateien
# ============================================================
step_header(1, "Communities hochladen", "Ein HTML-Export je Diskussion. Drag & Drop.",
            done=bool(SS["files"]))

uploads = st.file_uploader("HTML-/MHTML-Dateien", type=["html", "htm", "mhtml", "mht", "txt"],
                           accept_multiple_files=True, label_visibility="collapsed")

with st.expander("🔗 Stattdessen (oder zusätzlich) URLs abrufen"):
    st.markdown(
        "<div style='background:#FFF7E6;border-left:4px solid #B06010;border-radius:6px;"
        "padding:10px 13px;font-size:13px;line-height:1.55;margin-bottom:10px;'>"
        "<b>Der URL-Abruf ist der bequemere Weg, nicht der bessere.</b> Er holt das HTML "
        "<i>vor</i> der JavaScript-Ausführung. Foren, die ihre Beiträge im Browser nachladen "
        "(Reddit, Facebook, viele moderne Foren), liefern dabei eine leere Hülle. Das im "
        "Browser gespeicherte MHTML enthält dagegen das fertig gerenderte DOM — inklusive "
        "nachgeladener Kommentare. Für belastbare Studien bleibt MHTML die erste Wahl; das "
        "Tool warnt, wenn beim Abruf eine Hülle ankommt.</div>", unsafe_allow_html=True)
    url_raw = st.text_area("URLs (eine pro Zeile)", height=110,
                           placeholder="https://www.motor-talk.de/forum/…-t8197382.html")
    fc1, fc2, fc3 = st.columns(3)
    max_pages = fc1.number_input("Folgeseiten je Thread", 1, 25, 5,
                                 help="Ein Thread mit 12 Seiten liefert bei 1 nur ein "
                                      "Zwölftel der Diskussion — unauffällig im Ergebnis.")
    fetch_delay = fc2.slider("Pause zwischen Seiten (s)", 0.0, 5.0, 1.5, 0.5)
    reuse = fc3.checkbox("Lokales Archiv nutzen", value=True,
                         help=f"Bereits geladene Seiten aus ./{FETCH_DIR} verwenden, "
                              f"statt den Server erneut zu belasten.")
    respect_robots = st.checkbox("robots.txt beachten", value=True)
    consent = st.checkbox("Ich habe geprüft, dass der Abruf dieser Seiten zulässig ist "
                          "(Nutzungsbedingungen, keine Login-Bereiche, keine "
                          "personenbezogenen Sonderkategorien).")
    if not respect_robots:
        st.warning("Ohne robots.txt-Prüfung lässt sich der Abruf in der Methodik nicht "
                   "mehr als regelkonform ausweisen.")

    if st.button("URLs abrufen", type="primary",
                 disabled=not (safe_str(url_raw) and consent)):
        urls = [u.strip() for u in url_raw.splitlines() if u.strip().startswith("http")]
        prog, note = st.progress(0.0), st.empty()
        for ui, u in enumerate(urls, 1):
            note.info(f"Lade {u} …")
            try:
                pages = fetch_thread(u, int(max_pages), reuse, float(fetch_delay),
                                     respect_robots)
            except Exception as e:
                st.error(f"{u}: {e}")
                prog.progress(ui / len(urls))
                continue
            for pi, pg in enumerate(pages):
                if not pg["html"]:
                    st.error(f"{pg['name']}: " + " | ".join(pg["warnungen"]))
                    continue
                fname = url_to_filename(pg["name"], pi)
                m = pg["meta"]
                SS["files"][fname] = {"html": pg["html"],
                                      "encoding": safe_str(m.get("encoding")),
                                      "warn": pg["warnungen"]}
                SS["file_meta"][fname] = {
                    "community": safe_str(m.get("thread_titel"))[:60]
                                 or re.sub(r"^www\.", "", fname.split("_")[0]),
                    "plattform": "", "thread_titel": safe_str(m.get("thread_titel")),
                    "url": safe_str(m.get("final_url") or m.get("url") or pg["name"]),
                    "abrufdatum": safe_str(m.get("abgerufen_am"))[:10]
                                  or datetime.now().strftime("%Y-%m-%d"),
                    "quelle": "URL abgerufen", "archiv": safe_str(m.get("pfad")),
                    "strategie": "auto", "selector": "",
                }
            prog.progress(ui / len(urls))
        prog.empty(); note.empty()
        SS["extractions"], SS["corpus"], SS["results"] = {}, None, None
        st.rerun()

col_a, col_b = st.columns([3, 1])
with col_b:
    if st.button("Dateien zurücksetzen"):
        SS["files"], SS["file_meta"], SS["extractions"] = {}, {}, {}
        SS["corpus"], SS["results"] = None, None
        st.rerun()

if uploads:
    new = 0
    for up in uploads:
        if up.name in SS["files"]:
            continue
        raw = up.read()
        text, dmeta, enc, warn = load_document(raw, up.name)
        SS["files"][up.name] = {"html": text, "encoding": enc, "warn": warn}
        # MHTML liefert Quell-URL, Seitentitel und Abrufdatum frei Haus —
        # genau die Felder, die das Quellenregister sonst per Hand braucht.
        abruf = parse_rfc_date(dmeta.get("abrufdatum_roh", "")) or \
            datetime.now().strftime("%Y-%m-%d")
        SS["file_meta"].setdefault(up.name, {
            "community": re.sub(r"\.(html?|mhtml|mht|txt)$", "", up.name, flags=re.I)[:60],
            "plattform": "", "thread_titel": safe_str(dmeta.get("thread_titel")),
            "url": safe_str(dmeta.get("url")),
            "abrufdatum": abruf,
            "quelle": "MHTML/HTML manuell" if enc == "mhtml" else "HTML manuell",
            "archiv": "",
            "strategie": "auto", "selector": "",
        })
        new += 1
    if new:
        st.success(f"{new} Datei(en) eingelesen.")

if not SS["files"]:
    st.info("Noch keine Dateien. Tipp: Seite im Browser vollständig ausklappen "
            "(„Weitere Kommentare laden“) und dann als **Webseite, komplett** speichern — "
            "sonst fehlt genau der Teil der Diskussion, der interessant ist.")
    st.stop()


# ============================================================
# SCHRITT 2 — Extraktion & Preflight
# ============================================================
step_header(2, "Datei-Check", "Wurde jede Diskussion korrekt in einzelne Kommentare zerlegt?",
            done=bool(SS["extractions"]))

c1, c2, c3 = st.columns([1.4, 1.4, 1])
with c1:
    if st.button("Extraktion starten / wiederholen", type="primary"):
        prog = st.progress(0.0)
        for i, (name, f) in enumerate(SS["files"].items(), 1):
            meta = SS["file_meta"][name]
            SS["extractions"][name] = extract_comments(
                f["html"], strategy=meta.get("strategie", "auto"),
                custom_selector=meta.get("selector", ""))
            prog.progress(i / len(SS["files"]))
        prog.empty()
        SS["corpus"] = None
        st.rerun()
with c2:
    dedupe_scope = st.selectbox("Duplikat-Prüfung", ["global", "pro Datei"], index=0,
                                help="Global: identischer Text zählt über alle Communities "
                                     "hinweg nur einmal (Cross-Posting). Pro Datei: Duplikate "
                                     "nur innerhalb eines Threads entfernen.")
with c3:
    st.caption(f"BS4-Parser: `{BS_PARSER}`")

if not SS["extractions"]:
    st.warning("Extraktion noch nicht gelaufen.")
    st.stop()

# Preflight-Tabelle
pf_rows = []
for name, f in SS["files"].items():
    ex = SS["extractions"].get(name, {})
    m = SS["file_meta"][name]
    n = len(ex.get("comments", []))
    lens = [len(c["text"]) for c in ex.get("comments", [])]
    status = "ok"
    if n == 0:
        status = "LEER"
    elif ex.get("confidence", 0) < 0.5:
        status = "PRUEFEN"
    elif n < 3:
        status = "sehr wenig"
    shell, shell_reasons = detect_js_shell(f["html"], n)
    if shell and safe_str(m.get("quelle")).startswith("URL"):
        status = "JS-HUELLE"
    pf_rows.append({
        "Datei": name, "Status": status, "Kommentare": n,
        "Herkunft": safe_str(m.get("quelle")) or "manuell",
        "Konfidenz": round(float(ex.get("confidence", 0)), 2),
        "Strategie": ex.get("strategy_used", ""),
        "Plattform": ex.get("platform", ""),
        "Ø Zeichen": int(sum(lens) / len(lens)) if lens else 0,
        "Max Zeichen": max(lens) if lens else 0,
        "Community": m["community"],
        "Thread-Titel": m["thread_titel"] or ex.get("thread_title", ""),
        "URL": m["url"] or ex.get("url", ""),
        "Abrufdatum": m["abrufdatum"],
        "Warnungen": (("JS-Hülle: " + ", ".join(shell_reasons) + " | ") if shell else "")
                     + " | ".join(ex.get("warnings", []))[:200],
    })
pf_df = pd.DataFrame(pf_rows)

n_shell = int((pf_df["Status"] == "JS-HUELLE").sum())
if n_shell:
    st.error(f"**{n_shell} abgerufene Seite(n) sind leere JavaScript-Hüllen.** Der Server hat "
             f"nur das Gerüst geliefert, die Beiträge werden erst im Browser nachgeladen. "
             f"Diese Seiten im Browser öffnen, vollständig ausklappen und als "
             f"**Webseite, komplett (*.mhtml)** speichern — dann hier hochladen.")

n_bad = int((pf_df["Status"] != "ok").sum())
if n_bad:
    st.warning(f"**{n_bad} von {len(pf_df)} Dateien brauchen einen Blick.** "
               f"Nicht überspringen: Wenn die Kommentartrennung hier falsch ist, "
               f"stimmt später jede einzelne Zahl nicht — und sieht trotzdem plausibel aus.")
else:
    st.success(f"Alle {len(pf_df)} Dateien sauber extrahiert.")

edited = st.data_editor(
    pf_df, use_container_width=True, hide_index=True, key="pf_editor",
    disabled=["Datei", "Status", "Kommentare", "Herkunft", "Konfidenz", "Strategie",
              "Plattform", "Ø Zeichen", "Max Zeichen", "Warnungen"],
    column_config={
        "Community": st.column_config.TextColumn(help="Gruppierungsebene für 'N pro Community'"),
        "URL": st.column_config.TextColumn(width="medium"),
    })
for _, r in edited.iterrows():
    m = SS["file_meta"].get(r["Datei"])
    if m:
        m["community"] = safe_str(r["Community"]) or "Unbekannt"
        m["thread_titel"] = safe_str(r["Thread-Titel"])
        m["url"] = safe_str(r["URL"])
        m["abrufdatum"] = safe_str(r["Abrufdatum"])

with st.expander("🔧 Einzelne Datei nachbessern (Strategie / CSS-Selektor / Vorschau)"):
    pick = st.selectbox("Datei", list(SS["files"].keys()))
    ex = SS["extractions"].get(pick, {})
    a, b = st.columns([1, 2])
    with a:
        strat = st.selectbox("Strategie", ["auto", "jsonld", "microdata", "platform",
                                           "selector", "repeat", "paragraphs"],
                             index=["auto", "jsonld", "microdata", "platform", "selector",
                                    "repeat", "paragraphs"].index(
                                 SS["file_meta"][pick].get("strategie", "auto")))
    with b:
        sel = st.text_input("CSS-Selektor (bei Strategie 'selector')",
                            value=SS["file_meta"][pick].get("selector", ""),
                            placeholder="z. B. div.comment-body, article.post")
    if st.button("Diese Datei neu extrahieren"):
        SS["file_meta"][pick]["strategie"] = strat
        SS["file_meta"][pick]["selector"] = sel
        SS["extractions"][pick] = extract_comments(SS["files"][pick]["html"],
                                                   strategy=strat, custom_selector=sel)
        SS["corpus"] = None
        st.rerun()

    if ex.get("attempts"):
        st.caption("Versuchte Strategien: " + ", ".join(
            f"{a['strategie']}={a['treffer']} ({a['konfidenz']:.0%})" for a in ex["attempts"]))

    if len(ex.get("comments", [])) < 3 or ex.get("confidence", 0) < 0.5:
        st.markdown("**Rettungsanker — Kandidaten aus der Seitenstruktur**")
        st.caption("Wenn die Automatik danebenliegt: hier stehen die wiederkehrenden "
                   "Blöcke der Seite. Den passenden auswählen, statt CSS zu schreiben.")
        cands = suggest_selectors(SS["files"][pick]["html"])
        if not cands:
            st.warning("Keine wiederkehrende Blockstruktur gefunden. Wahrscheinlich wurde die "
                       "Seite gespeichert, bevor die Kommentare nachgeladen waren — "
                       "Seite komplett ausklappen und erneut speichern.")
        for i, c in enumerate(cands):
            cc1, cc2 = st.columns([5, 1])
            cc1.markdown(
                f"<div style='background:#fff;border:1.5px solid #E4E7ED;border-radius:8px;"
                f"padding:8px 10px;margin-bottom:4px;font-size:12.5px;'>"
                f"<code>{html_module.escape(c['selektor'])}</code> — "
                f"<b>{c['treffer']} Blöcke</b>, Ø {c['median_zeichen']} Zeichen, "
                f"{c['textanteil']:.0%} des Seitentexts<br>"
                f"<span style='color:#667085;'>{html_module.escape(c['beispiel'])}</span></div>",
                unsafe_allow_html=True)
            if cc2.button("Nehmen", key=f"cand_{pick}_{i}"):
                SS["file_meta"][pick]["strategie"] = "selector"
                SS["file_meta"][pick]["selector"] = c["selektor"]
                SS["extractions"][pick] = extract_comments(
                    SS["files"][pick]["html"], strategy="selector",
                    custom_selector=c["selektor"])
                SS["corpus"] = None
                st.rerun()
    for w in ex.get("warnings", []):
        st.caption(f"⚠️ {w}")
    st.markdown("**Vorschau der ersten Kommentare** — hier entscheidet sich die Datenqualität:")
    for c in ex.get("comments", [])[:6]:
        st.markdown(
            f"<div style='background:#fff;border:1.5px solid #E4E7ED;border-radius:8px;"
            f"padding:10px 12px;margin-bottom:6px;font-size:13px;'>"
            f"<span style='font-family:monospace;font-size:10.5px;color:#8892A0;'>"
            f"#{c['order']+1} · {html_module.escape(c['author'] or 'kein Autor')} · "
            f"{html_module.escape(c['date_raw'] or 'kein Datum')} · {len(c['text'])} Z.</span><br>"
            f"{html_module.escape(c['text'][:420])}</div>", unsafe_allow_html=True)


# ============================================================
# SCHRITT 3 — Korpus
# ============================================================
step_header(3, "Korpus aufbauen", "1 Kommentar = 1 Zeile. Duplikate, Müll und Zitate raus.",
            done=SS["corpus"] is not None)

with st.expander("🚫 Ausschluss-Muster (optional)"):
    excl_raw = st.text_area(
        "Ein Muster pro Zeile (Text oder Regex). Treffer werden nicht analysiert.",
        placeholder="Gesendet von meinem iPhone\n^Danke!?$\nwerbung|affiliate", height=90)
excl = [l for l in (excl_raw or "").splitlines() if l.strip()]

if st.button("Korpus erzeugen", type="primary"):
    file_results = []
    for name in SS["files"]:
        m = SS["file_meta"][name]
        ex = SS["extractions"].get(name, {})
        file_results.append({"name": name, "community": m["community"],
                             "plattform": m["plattform"] or ex.get("platform", ""),
                             "thread_titel": m["thread_titel"] or ex.get("thread_title", ""),
                             "url": m["url"] or ex.get("url", ""),
                             "abrufdatum": m["abrufdatum"],
                             "quelle": m.get("quelle", "manuell"),
                             "archiv": m.get("archiv", ""), "extraction": ex})
    corpus, stats = build_corpus(file_results, SS["salt"], excl,
                                 "global" if dedupe_scope == "global" else "file")
    SS["corpus"], SS["stats"] = corpus, stats
    SS["file_results"] = file_results
    SS["results"] = None
    st.rerun()

if SS["corpus"] is None:
    st.stop()

corpus, stats = SS["corpus"], SS["stats"]
konz = author_concentration(corpus)

k1, k2, k3, k4, k5 = st.columns(5)
k1.metric("Beiträge analysierbar", f"{stats['n_analysierbar']:,}".replace(",", "."))
k2.metric("Autor:innen", stats["n_autoren"])
k3.metric("Communities", stats["n_communities"])
k4.metric("Duplikate raus", stats["n_duplikate"])
k5.metric("Ø Wörter", int(corpus.loc[corpus["qualitaet"] == "ok", "woerter"].mean() or 0))

if konz.get("verfuegbar") and konz["top10pct_anteil"] > 0.5:
    st.warning(f"**Konzentrationswarnung:** Die aktivsten 10 % der Autor:innen stellen "
               f"{konz['top10pct_anteil']:.0%} aller Beiträge (Gini {konz['gini']}). "
               f"Häufigkeiten bilden dann eher die Lautstärke Einzelner ab als die Breite "
               f"des Diskurses. Zusätzlich N-pro-Autor:in betrachten.")
if stats["n_autoren"] == 0:
    st.warning("Keine Autoren erkannt — 'N pro Autor:in' ist nicht verfügbar. "
               "Alle Häufigkeiten beruhen ausschließlich auf Kommentaranzahl.")

langs = stats.get("sprachen", {})
if len([l for l in langs if l != "?"]) > 1:
    st.info("Mehrsprachiges Material: " + ", ".join(f"{k}={v}" for k, v in langs.items())
            + ". Die Analyse läuft sprachübergreifend; Verbatims bleiben im Original.")

with st.expander("📋 Korpus ansehen / Ausschlüsse prüfen"):
    tab_ok, tab_ex = st.tabs([f"Analysierbar ({stats['n_analysierbar']})",
                              f"Ausgeschlossen ({stats['n_roh'] - stats['n_analysierbar']})"])
    with tab_ok:
        st.dataframe(corpus[corpus["qualitaet"] == "ok"][
            ["kommentar_id", "community", "autor_pseudonym", "datum", "sprache",
             "woerter", "text"]].head(300), use_container_width=True, hide_index=True)
    with tab_ex:
        st.dataframe(corpus[corpus["qualitaet"] != "ok"][
            ["kommentar_id", "community", "ausschlussgrund", "woerter", "text"]].head(300),
            use_container_width=True, hide_index=True)


# ============================================================
# SCHRITT 4 — Analyse konfigurieren
# ============================================================
step_header(4, "Analyse konfigurieren", "Offen entdecken, gezielt suchen — oder beides.",
            done=SS["results"] is not None)

modus = st.radio(
    "Analysemodus", ["Hybrid (empfohlen)", "Offen (rein induktiv)", "Gerichtet (nur meine Themen)"],
    horizontal=True, index=0,
    help="Hybrid: das Tool entdeckt Themen selbst UND prüft deine Themen/Fragen. "
         "Gerichtet allein ist blind für alles, was du nicht vorher wusstest — "
         "und das ist bei Netnographie meistens der eigentliche Ertrag.")

kontext_txt = st.text_area(
    "Studienkontext", height=90,
    placeholder="Kategorie, Marke, Zielgruppe, Anlass der Studie. Je konkreter, desto "
                "trennschärfer die Codes.")

col_f, col_t = st.columns(2)
with col_f:
    fragen_raw = st.text_area("Forschungsfragen (eine pro Zeile)", height=120,
                              placeholder="Welche Barrieren nennen Nutzer:innen beim Umstieg?\n"
                                          "Wie wird der Preis bewertet?")
with col_t:
    themen_raw = st.text_area("Vorgegebene Themen (eine pro Zeile, optional)", height=120,
                              placeholder="Preis-Leistung\nBedienbarkeit\nService")
fragen = [l.strip() for l in (fragen_raw or "").splitlines() if l.strip()]
vorgabe_themen = [l.strip() for l in (themen_raw or "").splitlines() if l.strip()]

if modus.startswith("Gerichtet") and not (fragen or vorgabe_themen):
    st.error("Gerichteter Modus ohne Themen oder Fragen ist leer. Bitte oben etwas eintragen "
             "oder auf Hybrid wechseln.")

with st.expander("⚙️ Codebuch & Sättigung"):
    c1, c2, c3, c4 = st.columns(4)
    max_ober = c1.number_input("Max. Themen", 3, 20, 8)
    max_sub = c2.number_input("Max. Subthemen je Thema", 2, 12, 6)
    rounds = c3.number_input("Sättigungsrunden", 1, 6, 3,
                             help="Mehrere Runden auf verschiedenen Stichproben. Wenn die letzte "
                                  "Runde kaum noch neue Themen bringt, ist die Sättigung erreicht.")
    sample_size = c4.number_input("Stichprobe je Runde", 20, 250, CODEBOOK_SAMPLE_SIZE, step=10)

with st.expander("⚡ Tempo, Kosten & Robustheit"):
    c1, c2, c3 = st.columns(3)
    batch_size = c1.slider("Kommentare je LLM-Call", 4, 25, ASSIGN_BATCH_SIZE,
                           help="Größere Batches sind billiger, riskieren aber abgeschnittene "
                                "Antworten. Bei TRUNCATED-Meldungen: verkleinern.")
    workers = c2.slider("Parallele Threads", 1, 12, MAX_WORKERS_DEFAULT)
    min_n_summary = c3.slider("Mindest-N für Summary", 1, 15, 3,
                              help="Themen unter dieser Schwelle bekommen keine Verdichtung — "
                                   "eine Zusammenfassung von zwei Beiträgen ist keine Erkenntnis.")
    sub_summaries = st.checkbox("Auch Subthemen verdichten (mehr Calls, mehr Kosten)", value=False)

split_options = ["community", "plattform", "datei", "sprache", "sprecherrolle", "obercode"]
splits_selected = st.multiselect(
    "Auswertung splitten nach", split_options, default=["community"],
    help="Erzeugt Kreuztabellen inkl. Basis-N je Spalte.")

# Kostenschätzung vor dem Lauf — keine Überraschungen
n_work = stats["n_analysierbar"]
est_calls = math.ceil(n_work / max(1, batch_size)) + int(rounds) + max_ober + len(fragen)
_est_in = 2500 + 250 * max(1, batch_size)   # grob: System-Prompt + Kommentare je Call
_est_out = 1500 + (REASONING_TOKEN_HEADROOM // 2
                   if is_reasoning_model(_cfg_preview)
                   and _cfg_preview.get("reasoning_effort") != "none" else 0)
est_cost = est_calls * estimate_cost_eur(_cfg_preview.get("deployment"), _est_in, _est_out)
st.caption(f"Grobschätzung: ~{est_calls} LLM-Calls, ~{est_cost:.2f} € "
           f"(ohne Cache-Treffer; die tatsächlichen Kosten stehen nach dem Lauf im Log).")


# ============================================================
# SCHRITT 5 — Lauf
# ============================================================
step_header(5, "Analyse starten", f"{n_work} Beiträge werden kodiert und verdichtet.")

if st.button("🚀 Analyse starten", type="primary", disabled=(n_work == 0)):
    cfg = resolve_llm_cfg()
    if not cfg.get("api_key"):
        st.error("Kein API-Key gefunden. Analyse abgebrochen.")
        st.stop()

    log = RunLog()
    t0 = time.time()
    kontext = build_context_block(kontext_txt, fragen)
    bar = st.progress(0.0)
    status = st.empty()

    # 5a) Codebuch
    seed_cb = []
    if vorgabe_themen:
        seed_cb = [{"obercode": t, "definition": "Vom Team vorgegebenes Thema.",
                    "subcodes": [{"subcode": t, "definition": "Vorgegebenes Thema (Oberebene).",
                                  "belege": []}]} for t in vorgabe_themen]

    if modus.startswith("Gerichtet"):
        codebuch, verlauf = seed_cb, []
        status.info("Gerichteter Modus: es wird ausschließlich gegen die Vorgaben kodiert.")
    else:
        status.info("Schritt 1/3 — Themen induktiv entwickeln …")
        codebuch, verlauf = induce_codebook(
            corpus, kontext, cfg, log, rounds=int(rounds), sample_size=int(sample_size),
            max_ober=int(max_ober), max_sub=int(max_sub), seed_codebook=seed_cb,
            use_cache=use_cache,
            progress=lambda a, b, m: (bar.progress(0.15 * a / max(1, b)), status.info(m)))

    if not codebuch:
        st.error("Kein Codebuch entstanden. Details im Fail-Loud-Log unten.")
        st.dataframe(log.to_df(), use_container_width=True)
        st.stop()

    # 5b) Kodierung
    status.info(f"Schritt 2/3 — {n_work} Beiträge kodieren …")
    coded = assign_codes(
        corpus, codebuch, kontext, fragen, cfg, log,
        offen=not modus.startswith("Gerichtet"), batch_size=int(batch_size),
        workers=int(workers), use_cache=use_cache,
        progress=lambda a, b, m: (bar.progress(0.15 + 0.55 * a / max(1, b)), status.info(m)))

    # 5c) neu entdeckte Themen einsammeln (nur zur Transparenz, nicht automatisch übernommen)
    neue_counter = Counter()
    for lst in coded.get("neue_themen", pd.Series(dtype=object)).dropna():
        for t in (lst or []):
            neue_counter[t] += 1
    neue_top = [{"thema": t, "n": n} for t, n in neue_counter.most_common(20) if n >= 2]

    long_df = explode_codes(corpus, coded, codebuch)
    freq_ober = frequency_table(long_df, corpus, "obercode")
    freq_sub = frequency_table(long_df, corpus, "subcode")

    # 5d) Verdichtung
    status.info("Schritt 3/3 — Themen verdichten …")
    summaries_ober = summarize_themes(
        long_df, codebuch, kontext, cfg, log, level="obercode", min_n=int(min_n_summary),
        workers=int(workers), use_cache=use_cache,
        progress=lambda a, b, m: (bar.progress(0.70 + 0.2 * a / max(1, b)), status.info(m)))
    summaries_sub = {}
    if sub_summaries:
        summaries_sub = summarize_themes(
            long_df, codebuch, kontext, cfg, log, level="subcode", min_n=int(min_n_summary),
            workers=int(workers), use_cache=use_cache)

    fragen_out = answer_questions(long_df, corpus, coded, fragen, kontext, cfg, log,
                                  use_cache=use_cache)

    splits, idx_matrices = {}, {}
    for s in splits_selected:
        col = s if s in long_df.columns else None
        if col:
            splits[s] = split_table(long_df, corpus, col, "subcode")
            m = compute_index_matrix(long_df, corpus, col, "obercode")
            if not m.empty and len([c for c in m.columns
                                    if c not in ("thema", "n_gesamt", "anteil_gesamt")]) >= 2:
                idx_matrices[s] = m

    cooc = compute_cooccurrence(long_df, "obercode")
    signals = compute_signals(freq_ober, long_df, corpus, idx_matrices, cooc)

    bar.progress(1.0)
    status.success(f"Fertig in {int(time.time()-t0)} s · {log.calls} Calls "
                   f"({log.cache_hits} aus Cache) · {log.tokens:,} Tokens · {log.cost:.3f} €"
                   .replace(",", "."))

    SS["results"] = {
        "codebuch": codebuch, "verlauf": verlauf, "coded": coded, "long": long_df,
        "freq_ober": freq_ober, "freq_sub": freq_sub, "summaries_ober": summaries_ober,
        "summaries_sub": summaries_sub, "fragen_out": fragen_out, "splits": splits,
        "log": log, "neue_themen": neue_top, "konz": konz,
        "cooc": cooc, "signals": signals, "idx": idx_matrices,
        "meta": {"projekt": p_name or p_id, "user": p_user, "modus": modus,
                 "erhebung": beschreibe_erhebung(SS.get("file_results", [])),
                 "n_unkodiert": int((coded["status"] == "PARSE_ERROR").sum()) if len(coded) else 0,
                 "modell": (f'{cfg.get("deployment")} (reasoning_effort={cfg.get("reasoning_effort")})'
                            if is_reasoning_model(cfg) else cfg.get("deployment")), "kontext": kontext_txt, "fragen": fragen},
    }
    st.rerun()


# ============================================================
# SCHRITT 6 — Ergebnisse & Export
# ============================================================
if SS["results"] is None:
    st.stop()

R = SS["results"]
log: RunLog = R["log"]
step_header(6, "Ergebnisse", "Prüfen, dann exportieren.", done=True)

n_unkodiert = int((R["coded"]["status"] == "PARSE_ERROR").sum()) if len(R["coded"]) else 0
n_ok = int((R["coded"]["status"].astype(str).str.startswith("ok")).sum()) if len(R["coded"]) else 0
if n_unkodiert:
    st.error(f"**{n_unkodiert} von {len(R['coded'])} Beiträgen ohne Kodierung** "
             f"({n_unkodiert/max(1,len(R['coded'])):.0%}). Sie stehen im Export als "
             f"PARSE_ERROR und zählen in keiner Häufigkeit mit.")
elif log.n_errors:
    st.warning(f"{log.n_errors} technische Ereignisse im Lauf — alle Beiträge wurden "
               f"trotzdem kodiert (Auto-Split bzw. Reparatur-Pass haben gegriffen).")
else:
    st.success(f"Alle {n_ok} Beiträge sauber kodiert.")

_diag = log.diagnose()
if _diag:
    with st.expander(f"🩺 Diagnose — was ist passiert und was hilft ({len(_diag)} Befunde)",
                     expanded=bool(n_unkodiert)):
        for d in _diag:
            farbe = "#E63D50" if d["schwere"] == "blockierend" else "#B06010"
            st.markdown(
                f"<div style='border-left:4px solid {farbe};padding:6px 0 6px 12px;"
                f"margin-bottom:10px;'>"
                f"<b>{d['art']} · {d['anzahl']}×</b><br>"
                f"<span style='font-size:13px;'>{d['bedeutung']}</span><br>"
                f"<span style='font-size:13px;color:#0A9154;'><b>Was hilft:</b> "
                f"{d['empfehlung']}</span><br>"
                f"<span style='font-size:11.5px;color:#8892A0;font-family:monospace;'>"
                f"{html_module.escape(d['beispiel'])}</span></div>", unsafe_allow_html=True)
if R["verlauf"] and R["verlauf"][-1]["zuwachs"] >= 0.10:
    st.warning(f"**Sättigung nicht erreicht:** die letzte Induktionsrunde brachte noch "
               f"{R['verlauf'][-1]['zuwachs']:.0%} neue Subthemen. Mehr Material oder mehr "
               f"Runden — sonst fehlen dem Codebuch systematisch Themen.")

sub_step("Erkenntnis-Cockpit", "Größe, Zusammenhang, Auffälligkeit — vor den Tabellen")
st.caption("Erst hinschauen, dann lesen. Der Blindmodus blendet die Zahlen aus: eigene "
           "Erwartung bilden, dann auflösen. Was Sie falsch schätzen, bleibt hängen — "
           "was Sie nur lesen, meistens nicht.")
_ck_html = f'''<!DOCTYPE html><html><head><meta charset="utf-8">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&family=DM+Mono:wght@400;500&display=swap">
<style>body{{margin:0;background:#F7F8FA;font-family:Inter,sans-serif}}{DASH_CSS}{COCKPIT_CSS}</style>
</head><body>{render_cockpit(R["freq_ober"], R.get("cooc", []), R.get("signals", []),
                             R["summaries_ober"], R.get("idx", {}), stats)}</body></html>'''
components.html(_ck_html, height=1180, scrolling=True)

tabs = st.tabs(["Themen", "Zusammenhänge", "Forschungsfragen", "Neu entdeckt", "Splits",
                "Codebuch", "Quellen", "Lauf-Log", "Export"])

with tabs[0]:
    st.dataframe(R["freq_ober"], use_container_width=True, hide_index=True)
    for r in R["freq_ober"].itertuples(index=False):
        s = R["summaries_ober"].get(r.obercode, {})
        with st.expander(f"**{r.obercode}** — n={int(r.n_kommentare)} "
                         f"({int(r.n_autoren)} Autor:innen, {int(r.n_threads)} Threads)"):
            if s.get("key_insight"):
                st.markdown(f"**Key Insight:** {s['key_insight']}")
            if s.get("summary"):
                st.markdown(s["summary"])
            if s.get("spannungsfeld"):
                st.caption(f"Spannungsfeld: {s['spannungsfeld']}")
            if s.get("sprache_der_community"):
                st.caption("Community-Sprache: " + ", ".join(s["sprache_der_community"]))
            sub = R["freq_sub"][R["freq_sub"]["obercode"] == r.obercode]
            st.dataframe(sub[["subcode", "n_kommentare", "n_autoren", "n_threads",
                              "n_communities", "netto_sentiment"]],
                         use_container_width=True, hide_index=True)

with tabs[1]:
    st.caption("Welche Themen tauchen im selben Beitrag auf? **Lift** = wie viel häufiger "
               "als bei Zufall (1,0 = unabhängig). Ein hoher Lift bei kleinem n ist die "
               "interessante Kombination: selten, aber dann fast immer gemeinsam.")
    if R.get("cooc"):
        cdf = pd.DataFrame(R["cooc"]).rename(columns={
            "a": "Thema A", "b": "Thema B", "n": "gemeinsame Beiträge",
            "jaccard": "Jaccard", "lift": "Lift",
            "anteil_a": "Anteil an A", "anteil_b": "Anteil an B"})
        st.dataframe(cdf, use_container_width=True, hide_index=True)
    else:
        st.info("Keine Themenpaare mit mindestens 2 gemeinsamen Beiträgen. "
                "Bei kleinem Korpus normal.")
    for name, m in (R.get("idx") or {}).items():
        st.markdown(f"**Index nach {name}** — 100 = Durchschnitt des Gesamtkorpus")
        st.dataframe(m, use_container_width=True, hide_index=True)

with tabs[2]:
    if not R["fragen_out"]:
        st.info("Keine Forschungsfragen definiert.")
    for f in R["fragen_out"]:
        with st.expander(f"**{f['tag']}** {f['frage']} — n={f['n']}, Evidenz: {f['evidenzgrad']}"):
            st.markdown(f"**Key Insight:** {f.get('key_insight','')}")
            st.markdown(f.get("antwort", ""))
            st.caption(f"Evidenz: {f.get('evidenz_begruendung','')}")
            st.caption(f"Offene Lücken: {f.get('offene_luecken','')}")
            for b in f.get("belege", []):
                st.markdown(f"> [{b['id']}] {b['text'][:400]}")

with tabs[3]:
    st.caption("Themen, die das Modell im Material gesehen hat, die aber nicht im Codebuch "
               "stehen. Sie werden NICHT automatisch übernommen — nimm sie in die "
               "Themenvorgabe auf und lass den Lauf erneut durchlaufen, wenn sie relevant sind.")
    if R["neue_themen"]:
        st.dataframe(pd.DataFrame(R["neue_themen"]), use_container_width=True, hide_index=True)
    else:
        st.success("Keine relevanten Lücken gemeldet — ein Indiz für ein vollständiges Codebuch.")
    if R["verlauf"]:
        st.markdown("**Sättigungsverlauf**")
        st.dataframe(pd.DataFrame(R["verlauf"]), use_container_width=True, hide_index=True)

with tabs[4]:
    if not R["splits"]:
        st.info("Keine Splits gewählt.")
    for name, sdf in R["splits"].items():
        st.markdown(f"**Split nach {name}**")
        st.dataframe(sdf, use_container_width=True, hide_index=True)

with tabs[5]:
    cb_rows = [{"obercode": o["obercode"], "subcode": s["subcode"],
                "definition": s.get("definition", ""), "belege": ", ".join(s.get("belege", []))}
               for o in R["codebuch"] for s in o.get("subcodes", [])]
    st.dataframe(pd.DataFrame(cb_rows), use_container_width=True, hide_index=True)
    st.download_button("Codebuch als JSON",
                       json.dumps(R["codebuch"], ensure_ascii=False, indent=2).encode("utf-8"),
                       "codebuch.json", "application/json")
    up_cb = st.file_uploader("Codebuch aus früherer Welle laden (JSON)", type=["json"],
                             key="cb_up")
    if up_cb is not None:
        try:
            loaded = json.loads(up_cb.read().decode("utf-8"))
            st.success(f"{len(loaded)} Themen geladen. Als Themenvorgabe in Schritt 4 einfügen, "
                       f"um Wellen vergleichbar zu halten.")
            st.code("\n".join(o["obercode"] for o in loaded))
        except Exception as e:
            st.error(f"Konnte JSON nicht lesen: {e}")

quellen = source_register(corpus, SS.get("file_results", []))
with tabs[6]:
    st.dataframe(quellen, use_container_width=True, hide_index=True)

with tabs[7]:
    c1, c2, c3, c4 = st.columns(4)
    c1.metric("LLM-Calls", log.calls)
    c2.metric("Cache-Treffer", log.cache_hits)
    c3.metric("Tokens", f"{log.tokens:,}".replace(",", "."))
    c4.metric("Kosten", f"{log.cost:.3f} €")
    st.dataframe(log.to_df(), use_container_width=True, hide_index=True)

with tabs[8]:
    methods = build_methods_sheet(R["meta"], stats, R["konz"], R["verlauf"], log, R["codebuch"])

    e1, e2 = st.columns(2)
    with e1:
        export_card("📊", "HTML-Dashboard", "Interaktiv, offline lauffähig, überall Copy-Buttons. "
                                            "Das Deliverable für Kolleg:innen und Kunden.",
                    primary=True, ready=True)
        dash = generate_dashboard(R["meta"], stats, R["konz"], R["codebuch"], R["freq_ober"],
                                  R["freq_sub"], R["summaries_ober"], R["summaries_sub"],
                                  R["long"], R["fragen_out"], quellen, R["splits"], log,
                                  cooc=R.get("cooc"), signals=R.get("signals"),
                                  idx_matrices=R.get("idx"))
        st.download_button("Dashboard herunterladen", dash,
                           f"netnographie_{re.sub(r'[^A-Za-z0-9]+','_',p_name or 'projekt')}.html",
                           "text/html", type="primary")

        export_card("📗", "Excel-Arbeitsmappe",
                    "Methodik, Quellenregister, Codebuch, Häufigkeiten, Splits, "
                    "kodierter Korpus, Belegstellen, Fail-Loud-Log.", ready=True)
        xls = export_excel(corpus, R["coded"], R["long"], R["freq_ober"], R["freq_sub"],
                           R["splits"], R["summaries_ober"], R["summaries_sub"],
                           R["fragen_out"], quellen, methods, log, R["codebuch"],
                           cooc=R.get("cooc"), signals=R.get("signals"),
                           idx_matrices=R.get("idx"))
        st.download_button("Excel herunterladen", xls,
                           f"netnographie_{re.sub(r'[^A-Za-z0-9]+','_',p_name or 'projekt')}.xlsx",
                           "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    with e2:
        export_card("📄", "Korpus als CSV", "1 Kommentar = 1 Zeile, pseudonymisiert. "
                                            "Für eigene Weiterverarbeitung.", ready=True)
        st.download_button("CSV herunterladen", corpus_to_csv(corpus),
                           "korpus.csv", "text/csv")

        export_card("🔍", "Klartext-Korpus (mit Klarnamen)",
                    "Enthält Original-Nutzernamen. Nur intern verwenden, nicht an Kunden "
                    "weitergeben.", ready=True)
        st.download_button("Klartext-CSV herunterladen",
                           corpus_to_csv(corpus, pseudonym_only=False),
                           "korpus_klartext.csv", "text/csv")

    st.markdown("---")
    st.caption("**Vor der Weitergabe prüfen:** (1) Fail-Loud-Log ohne offene Fehler, "
               "(2) Extraktionskonfidenz aller Quellen ≥ 50 %, (3) Sättigung erreicht, "
               "(4) Verbatims stichprobenartig gegen die Originalseite gegengelesen, "
               "(5) Keine Aussage im Bericht, die N als Prävalenz interpretiert.")
