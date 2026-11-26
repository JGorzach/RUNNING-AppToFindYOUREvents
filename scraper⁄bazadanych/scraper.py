import asyncio
import base64
import hashlib
import json
import os
import random
import re
import socket
import sqlite3
from datetime import date, datetime, timedelta
from typing import Literal, Optional
from urllib.parse import urljoin, urlparse

import httpx
import litellm
from bs4 import BeautifulSoup
from crawl4ai import (
    AsyncWebCrawler,
    BrowserConfig,
    CacheMode,
    CrawlerRunConfig,
    LLMConfig,
    LLMExtractionStrategy,
)
from litellm import acompletion
from pydantic import BaseModel, Field, ValidationError, field_validator

# Wycisza banery "LiteLLM.Info: If you need to debug..." przy chwilowych błędach 429/503
litellm.suppress_debug_info = True

# Opcjonalne wczytywanie GEMINI_API_KEY z pliku .env (jeśli zainstalowano python-dotenv)
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

# --- ŚCIEŻKI I KONFIGURACJA ---
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "wydarzenia.db")
OUTPUT_JSON = os.path.join(BASE_DIR, "wydarzenia_sportowe.json")

# Modele LLM:
# - tekst: szybki i pojemny flash-lite
# - plakaty: najpierw 3.8-flash (lepszy OCR), przy 503/429/404 automatyczny fallback na 3.5-flash-lite
MODEL_PROVIDER = "gemini/gemini-3.5-flash-lite"
POSTER_MODELS = [
    "gemini/gemini-3.5-flash-lite",
    "gemini/gemini-3.8-flash",
]

# Limity pod darmowy plan API (RPM / RPD)
BATCH_LIMIT = 15                  # Ile źródeł z tabeli 'sources' sprawdzić w jednym uruchomieniu
DELAY_AFTER_LLM_CALL = (6.0, 8.5) # Pauza w sekundach po faktycznym zapytaniu do API
MAX_RETRIES = 3                   # Próby dla ekstrakcji tekstu (429 / 503)
POSTER_RETRIES_PER_MODEL = 2      # Próby na jeden model plakatu zanim przełączy na zapasowy
BASE_BACKOFF_SECONDS = 15.0
MAX_DETAIL_PAGES_PER_SITE = 10
MAX_POSTERS_PER_EVENT = 3
SPA_JS_DELAY_SECONDS = 2.0        # Czas na wyrenderowanie stron SPA / JS (np. orzysz.pl)

# Lista awaryjna — używana wyłącznie wtedy, gdy tabela 'sources' w bazie jest pusta
FALLBACK_URLS = [
    "https://gminadywity.pl/aktualnosci",
    "https://osir.olsztyn.pl/aktualnosci",
]

# Limity i filtry obrazków plakatów
MIN_POSTER_BYTES = 15_000      # 15 KB
MAX_POSTER_BYTES = 8_000_000   # 8 MB
ALLOWED_IMAGE_MIMES = {"image/jpeg", "image/jpg", "image/png", "image/webp"}

IGNORED_IMAGE_KEYWORDS = (
    "logo", "herb", "godlo", "bip", "icon", "ikona", "favicon", "avatar",
    "facebook", "instagram", "youtube", "twitter", "tiktok", "linkedin",
    "cookie", "rodo", "wcag", "flag", "flaga", "ue-", "unijne", "fundusze",
    "dotacj", "mapa-strony", "spinner", "loader", "placeholder", "baner-glowny",
)
BOOST_IMAGE_KEYWORDS = (
    "plakat", "afisz", "zaproszen", "bieg", "turniej", "mecz", "rajd",
    "zawod", "sport", "wydarzen", "uploads", "wp-content", "galeria",
)


class DailyQuotaExhaustedError(Exception):
    """Wyjątek rzucany po wyczerpaniu dziennego limitu zapytań (RPD)."""


# --- MODELE DANYCH (PYDANTIC + FILTR TYPU ARTYKUŁU) ---
class SportEvent(BaseModel):
    title: str = Field(..., description="Nazwa wydarzenia sportowego")
    article_type: Literal[
        "zapowiedz_wydarzenia",
        "relacja_wyniki",
        "inwestycja_remont",
        "komunikat_inne",
    ] = Field(
        "zapowiedz_wydarzenia",
        description=(
            "zapowiedz_wydarzenia = nadchodzący bieg, turniej, mecz, rajd, zajęcia otwarte; "
            "relacja_wyniki = opis przeszłego wydarzenia, sukcesy, medale, fotorelacja; "
            "inwestycja_remont = modernizacja, budowa, dotacja, przetarg, otwarcie obiektu; "
            "komunikat_inne = awarie, godziny otwarcia, nabory do pracy, sesje rady."
        ),
    )
    event_date: Optional[str] = Field(
        None, description="Data wydarzenia w formacie YYYY-MM-DD (lub null, jeśli brak)"
    )
    time: Optional[str] = Field(
        None, description="Godzina rozpoczęcia, np. 10:00 (lub null)"
    )
    location: Optional[str] = Field(
        None, description="Miejsce lub miejscowość, np. Orlik w Dywitach"
    )
    discipline: Optional[str] = Field(
        "inne", description="Dyscyplina sportu, np. bieganie, piłka nożna, siatkówka, rower"
    )
    url: Optional[str] = Field(
        None, description="Czysty link (URL) do podstrony artykułu bez formatowania Markdown"
    )
    summary: Optional[str] = Field(
        "", description="Krótkie, jednozdaniowe podsumowanie"
    )

    @field_validator("article_type", mode="before")
    @classmethod
    def _normalize_article_type(cls, value):
        if not isinstance(value, str):
            return "zapowiedz_wydarzenia"
        trans = str.maketrans("ąćęłńóśźż ", "acelnoszz_")
        norm = value.strip().lower().translate(trans)
        if "zapowiedz" in norm or "wydarzen" in norm:
            return "zapowiedz_wydarzenia"
        if "relacj" in norm or "wynik" in norm:
            return "relacja_wyniki"
        if "inwestycj" in norm or "remont" in norm or "modernizacj" in norm:
            return "inwestycja_remont"
        return "komunikat_inne"


class EventDetails(BaseModel):
    is_upcoming_sport_event: bool = Field(
        True,
        description=(
            "False, jeśli artykuł to relacja z przeszłego wydarzenia, gratulacje/sukces zespołu, "
            "remont/modernizacja obiektu, przetarg lub ogólny komunikat."
        ),
    )
    rejection_reason: Optional[str] = Field(
        None, description="Krótki powód odrzucenia, jeśli is_upcoming_sport_event=False"
    )
    poster_raw_text: Optional[str] = Field(
        None, description="Dosłowny przepis napisów z plakatu (data, godzina, miejsce)"
    )
    event_date: Optional[str] = Field(
        None, description="Dokładna data wydarzenia YYYY-MM-DD (nie data publikacji artykułu!)"
    )
    time: Optional[str] = Field(
        None, description="Godzina rozpoczęcia wydarzenia w formacie HH:MM, np. 10:00"
    )
    location: Optional[str] = Field(
        None, description="Dokładne miejsce, obiekt sportowy, adres lub miejscowość"
    )
    summary: Optional[str] = Field(
        None, description="Krótkie podsumowanie z uwzględnieniem zapisów lub dystansu"
    )


# --- SANITYZACJA URL, DNS I FILTRY DAT ---
def sanitize_url(raw_url: Optional[str], base_url: Optional[str] = None) -> Optional[str]:
    """Wyciąga czysty adres HTTP/HTTPS (obsługuje format Markdown [tekst](url) i linki względne)."""
    if not raw_url or not isinstance(raw_url, str):
        return None

    text = raw_url.strip()
    if not text or text.startswith("#"):
        return None

    md_match = re.search(r"\[[^\]]*\]\(([^)]+)\)", text)
    if md_match:
        text = md_match.group(1).strip()

    text = text.strip("<>\"'()[] ")
    if not text or text.startswith(("#", "javascript:", "mailto:", "tel:")):
        return None

    if base_url:
        text = urljoin(base_url, text)

    parsed = urlparse(text)
    if parsed.scheme not in ("http", "https") or not parsed.netloc:
        return None

    return text


def is_domain_resolvable(url: str) -> bool:
    host = urlparse(url).hostname
    if not host:
        return False
    try:
        socket.getaddrinfo(host, None)
        return True
    except socket.gaierror:
        return False


def is_past_event(event_date: Optional[str]) -> bool:
    """Zwraca True, jeśli data wydarzenia jest starsza niż wczoraj."""
    if not event_date or not isinstance(event_date, str):
        return False
    match = re.search(r"\d{4}-\d{2}-\d{2}", event_date)
    if not match:
        return False
    try:
        parsed = date.fromisoformat(match.group(0))
        return parsed < (date.today() - timedelta(days=1))
    except ValueError:
        return False


def has_past_year_in_url(url: Optional[str]) -> bool:
    """Wykrywa archiwalne wpisy po roku w ścieżce URL (np. /2024/06/...), oszczędzając API."""
    if not url:
        return False
    path = urlparse(url).path
    years = [int(y) for y in re.findall(r"/(20\d{2})/", path)]
    return bool(years) and max(years) < date.today().year


# --- BAZA DANYCH (SQLite) ---
def init_db(db_path: str = DB_PATH) -> sqlite3.Connection:
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS pages (
            url TEXT PRIMARY KEY,
            content_hash TEXT NOT NULL,
            last_checked TEXT NOT NULL,
            last_changed TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS events (
            event_key TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            event_date TEXT,
            time TEXT,
            location TEXT,
            discipline TEXT NOT NULL,
            url TEXT,
            summary TEXT NOT NULL,
            source_page TEXT NOT NULL,
            first_seen TEXT NOT NULL,
            last_seen TEXT NOT NULL
        );
        """
    )
    conn.commit()
    return conn


def load_urls_from_db(db_path: str = DB_PATH, batch_limit: int = BATCH_LIMIT) -> list[str]:
    """
    Pobiera aktywne źródła z tabeli 'sources':
    1) najpierw niesprawdzone jeszcze strony z priorytetem OSiR -> obiekt_sportowy -> GOK -> gmina,
    2) gdy wszystkie były już raz sprawdzone, rotuje sprawiedliwie od najdawniej sprawdzanych.
    """
    conn = init_db(db_path)
    try:
        has_sources = conn.execute(
            "SELECT 1 FROM sqlite_master WHERE type='table' AND name='sources'"
        ).fetchone()
        if not has_sources:
            return []

        rows = conn.execute(
            """
            SELECT s.url
            FROM sources s
            LEFT JOIN pages p ON p.url = s.url
            WHERE s.status = 'active'
            ORDER BY
                p.last_checked IS NOT NULL,
                CASE
                    WHEN p.last_checked IS NULL THEN
                        CASE s.source_type
                            WHEN 'osir' THEN 0
                            WHEN 'obiekt_sportowy' THEN 1
                            WHEN 'gok' THEN 2
                            ELSE 3
                        END
                    ELSE 0
                END,
                p.last_checked ASC,
                CASE s.source_type
                    WHEN 'osir' THEN 0
                    WHEN 'obiekt_sportowy' THEN 1
                    WHEN 'gok' THEN 2
                    ELSE 3
                END
            LIMIT ?
            """,
            (batch_limit,),
        ).fetchall()
        return [row["url"] for row in rows]
    except sqlite3.Error as exc:
        print(f"[BŁĄD SQLite] Nie udało się wczytać źródeł: {exc}")
        return []
    finally:
        conn.close()


def record_source_failure(conn: sqlite3.Connection, url: str) -> None:
    """Zlicza błędy pobierania strony; po 2 błędach wyłącza martwe źródło z kolejki."""
    try:
        conn.execute(
            """
            UPDATE sources
            SET fail_count = fail_count + 1,
                status = CASE WHEN fail_count + 1 >= 2 THEN 'disabled' ELSE status END
            WHERE url = ?
            """,
            (url,),
        )
        conn.commit()
    except sqlite3.OperationalError:
        pass


def reset_source_failures(conn: sqlite3.Connection, url: str) -> None:
    try:
        conn.execute("UPDATE sources SET fail_count = 0 WHERE url = ? AND fail_count > 0", (url,))
        conn.commit()
    except sqlite3.OperationalError:
        pass


def compute_content_hash(markdown_text: str) -> str:
    normalized = re.sub(r"\s+", " ", markdown_text).strip()
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def make_event_key(event: SportEvent, source_page: str) -> str:
    """Buduje klucz deduplikacji bez nadpisywania różnych wydarzeń pod tym samym linkiem."""
    clean_url = (event.url or "").split("#")[0].strip().rstrip("/").lower()
    clean_source = source_page.split("#")[0].strip().rstrip("/").lower()
    norm_title = re.sub(r"\s+", " ", event.title).strip().lower()

    if clean_url and clean_url != clean_source:
        raw_key = f"url:{clean_url}|{norm_title}"
    else:
        raw_key = f"meta:{clean_source}|{norm_title}|{event.event_date or ''}"

    return hashlib.sha256(raw_key.encode("utf-8")).hexdigest()


def get_saved_hash(conn: sqlite3.Connection, url: str) -> Optional[str]:
    row = conn.execute("SELECT content_hash FROM pages WHERE url = ?", (url,)).fetchone()
    return row["content_hash"] if row else None


def mark_page_checked(conn: sqlite3.Connection, url: str) -> None:
    now = datetime.now().isoformat(timespec="seconds")
    conn.execute("UPDATE pages SET last_checked = ? WHERE url = ?", (now, url))
    conn.commit()


def save_page_hash(conn: sqlite3.Connection, url: str, content_hash: str) -> None:
    now = datetime.now().isoformat(timespec="seconds")
    conn.execute(
        """
        INSERT INTO pages (url, content_hash, last_checked, last_changed)
        VALUES (?, ?, ?, ?)
        ON CONFLICT(url) DO UPDATE SET
            content_hash = excluded.content_hash,
            last_checked = excluded.last_checked,
            last_changed = excluded.last_changed
        """,
        (url, content_hash, now, now),
    )
    conn.commit()


def upsert_event(conn: sqlite3.Connection, event: SportEvent, source_page: str) -> bool:
    now = datetime.now().isoformat(timespec="seconds")
    event_key = make_event_key(event, source_page)
    exists = conn.execute("SELECT 1 FROM events WHERE event_key = ?", (event_key,)).fetchone()

    discipline = (event.discipline or "inne").strip() or "inne"
    summary = (event.summary or "").strip()

    conn.execute(
        """
        INSERT INTO events (
            event_key, title, event_date, time, location, discipline,
            url, summary, source_page, first_seen, last_seen
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(event_key) DO UPDATE SET
            title = excluded.title,
            event_date = COALESCE(excluded.event_date, events.event_date),
            time = COALESCE(excluded.time, events.time),
            location = COALESCE(excluded.location, events.location),
            discipline = CASE
                WHEN excluded.discipline != 'inne' THEN excluded.discipline
                ELSE events.discipline
            END,
            url = COALESCE(excluded.url, events.url),
            summary = CASE
                WHEN length(excluded.summary) > length(events.summary) THEN excluded.summary
                ELSE events.summary
            END,
            last_seen = excluded.last_seen
        """,
        (
            event_key,
            event.title.strip(),
            event.event_date,
            event.time,
            event.location,
            discipline,
            event.url,
            summary,
            source_page,
            now,
            now,
        ),
    )
    conn.commit()
    return exists is None


def delete_event(conn: sqlite3.Connection, event: SportEvent, source_page: str) -> None:
    event_key = make_event_key(event, source_page)
    conn.execute("DELETE FROM events WHERE event_key = ?", (event_key,))
    conn.commit()


def export_db_to_json(conn: sqlite3.Connection, output_file: str = OUTPUT_JSON) -> int:
    rows = conn.execute(
        """
        SELECT title, event_date, time, location, discipline, url, summary, source_page, first_seen
        FROM events
        ORDER BY event_date IS NULL, event_date ASC, title ASC
        """
    ).fetchall()
    data = [dict(row) for row in rows]
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    return len(data)


# --- STRATEGIE LLM (TEKST, CHUNKING WYŁĄCZONY) ---
def _get_api_key() -> str:
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key:
        raise RuntimeError("Brak zmiennej środowiskowej GEMINI_API_KEY.")
    return api_key


def _get_llm_config() -> LLMConfig:
    return LLMConfig(provider=MODEL_PROVIDER, api_token=_get_api_key())


def build_list_strategy() -> LLMExtractionStrategy:
    today = date.today().isoformat()
    instruction = f"""
    Dzisiejsza data to {today}.
    Przeanalizuj listę wpisów na stronie urzędu gminy / OSiR i wyciągnij WYŁĄCZNIE zapowiedzi
    nadchodzących wydarzeń sportowych i rekreacyjnych, w których mieszkańcy mogą wziąć udział
    lub kibicować (biegi, turnieje, mecze, rajdy rowerowe, zawody, zajęcia sportowe).

    BEZWZGLĘDNIE POMIJAJ (lub oznacz innym article_type niż "zapowiedz_wydarzenia"):
    - inwestycje, remonty, przetargi, konkursy ofert, dotacje (np. "modernizacja ośrodka sportowego", "budowa orlika"),
    - relacje, wyniki, gratulacje i podsumowania z przeszłości (np. "sukces naszego zespołu", "medale zawodników", "za nami turniej", "fotorelacja"),
    - komunikaty organizacyjne i urzędowe (np. "basen nieczynny", "sesja rady", "odbiór odpadów", "koncert").

    Zasady:
    1. Dla każdego wpisu podaj dokładny czysty link URL (bez formatowania Markdown) oraz poprawne pole article_type.
    2. Jeśli na liście widać datę, godzinę lub miejsce samego wydarzenia, wpisz je (nie myl daty publikacji wpisu z datą wydarzenia).
    3. Jeśli na stronie nie ma żadnych zapowiedzi wydarzeń sportowych, zwróć pustą listę [].
    """
    return LLMExtractionStrategy(
        llm_config=_get_llm_config(),
        schema=SportEvent.model_json_schema(),
        extraction_type="schema",
        instruction=instruction,
        input_format="markdown",
        apply_chunking=False,  # Cała strona idzie w 1 zapytaniu — nie podwaja zużycia RPM
        extra_args={"temperature": 0.0},
    )


def build_detail_strategy() -> LLMExtractionStrategy:
    today = date.today().isoformat()
    instruction = f"""
    Dzisiejsza data to {today}.
    To jest pełna treść artykułu ze strony gminy / OSiR.

    KROK 1 — WERYFIKACJA:
    Ustaw "is_upcoming_sport_event": false (i wpisz krótki powód w "rejection_reason"), jeśli artykuł to:
    - relacja/podsumowanie/wyniki/fotorelacja z wydarzenia, które już się odbyło,
    - gratulacje lub informacja o sukcesie sportowca/zespołu,
    - modernizacja, remont, budowa obiektu, dotacja, konkurs ofert lub przetarg,
    - komunikat techniczny (awaria, przerwa techniczna, cennik) lub oferta czysto kulturalna.
    WAŻNE: Jeśli artykuł jest bardzo krótki i odsyła do plakatu/grafiki (brak daty w samym tekście),
    ZOSTAW "is_upcoming_sport_event": true — datę sprawdzi osobny krok analizy plakatu.

    KROK 2 — SZCZEGÓŁY (jeśli to zapowiedź nadchodzącego wydarzenia):
    - event_date: dokładna data odbycia się wydarzenia w formacie YYYY-MM-DD (przelicz daty względne względem {today}; NIE podawaj daty publikacji artykułu),
    - time: godzina startu / zbiórki (np. 10:00),
    - location: dokładne miejsce, hala, boisko, ulica lub miejscowość,
    - summary: krótkie podsumowanie (1 zdanie: dystans, zapisy, kategoria).
    Zwróć dokładnie jeden obiekt w liście.
    """
    return LLMExtractionStrategy(
        llm_config=_get_llm_config(),
        schema=EventDetails.model_json_schema(),
        extraction_type="schema",
        instruction=instruction,
        input_format="markdown",
        apply_chunking=False,
        extra_args={"temperature": 0.0},
    )


def _is_retryable_api_error(text: str) -> bool:
    """Wykrywa limity RPM (429) oraz chwilowe przeciążenia serwerów Gemini (500/502/503/504)."""
    lower = text.lower()
    return any(
        t in lower
        for t in (
            "429", "rate_limit", "ratelimit", "resource_exhausted", "too many requests",
            "503", "502", "504", "serviceunavailable", "high demand", "overloaded", "unavailable",
        )
    )


def _is_daily_quota(text: str) -> bool:
    lower = text.lower()
    return any(t in lower for t in ("perday", "per_day", "daily", "requestsperday"))


def _is_model_not_found(text: str) -> bool:
    lower = text.lower()
    return "404" in lower or "notfounderror" in lower or "no longer available" in lower


# --- WIELOOBRAZKOWY ODCZYT PLAKATÓW (BEAUTIFULSOUP + FALLBACK MODELI) ---
def _is_candidate_image_url(url: str, alt: str = "") -> bool:
    parsed = urlparse(url)
    if parsed.scheme not in ("http", "https"):
        return False

    path_lower = parsed.path.lower()
    if path_lower.endswith((".svg", ".ico", ".gif")):
        return False

    haystack = f"{url} {alt}".lower()
    if any(bad in haystack for bad in IGNORED_IMAGE_KEYWORDS):
        return False

    return True


def _pick_largest_from_srcset(srcset: str) -> Optional[str]:
    best_url, best_width = None, -1
    for part in srcset.split(","):
        tokens = part.strip().split()
        if not tokens:
            continue
        url = tokens[0]
        width = 0
        if len(tokens) > 1 and tokens[1].endswith("w"):
            try:
                width = int(tokens[1][:-1])
            except ValueError:
                width = 0
        if width >= best_width:
            best_width = width
            best_url = url
    return best_url


def select_poster_candidates_from_html(
    html_content: str,
    base_url: str,
    max_candidates: int = MAX_POSTERS_PER_EVENT,
) -> list[str]:
    """Szuka pełnych plakatów wyłącznie w głównej treści artykułu (bez nagłówka i paska bocznego)."""
    soup = BeautifulSoup(html_content, "html.parser")

    for tag in soup.select("header, footer, nav, aside, .sidebar, .menu, .cookie, #cookie"):
        tag.decompose()

    container = (
        soup.select_one(
            "article, main, .entry-content, .post-content, .article-content, "
            ".news-content, .tresc, #content"
        )
        or soup
    )

    scored: dict[str, float] = {}

    for idx, img in enumerate(container.find_all("img")):
        candidate_urls: list[tuple[str, float]] = []

        parent_a = img.find_parent("a", href=True)
        if parent_a:
            href_url = sanitize_url(parent_a["href"], base_url=base_url)
            if href_url and urlparse(href_url).path.lower().endswith(
                (".jpg", ".jpeg", ".png", ".webp")
            ):
                candidate_urls.append((href_url, 10.0))

        for attr in ("data-large-file", "data-orig-file", "data-src", "data-lazy-src", "data-original"):
            val = img.get(attr)
            if val and not str(val).startswith("data:"):
                u = sanitize_url(str(val), base_url=base_url)
                if u:
                    candidate_urls.append((u, 5.0))

        for srcset_attr in ("data-srcset", "srcset"):
            if img.get(srcset_attr):
                largest = _pick_largest_from_srcset(str(img[srcset_attr]))
                u = sanitize_url(largest, base_url=base_url)
                if u:
                    candidate_urls.append((u, 4.0))

        src = img.get("src")
        if src and not str(src).startswith("data:"):
            u = sanitize_url(str(src), base_url=base_url)
            if u:
                candidate_urls.append((u, 2.0))

        if not candidate_urls:
            continue

        best_url, base_score = max(candidate_urls, key=lambda x: x[1])
        alt = str(img.get("alt") or "")
        if not _is_candidate_image_url(best_url, alt):
            continue

        haystack = f"{best_url} {alt}".lower()
        keyword_bonus = sum(2.5 for kw in BOOST_IMAGE_KEYWORDS if kw in haystack)
        thumb_penalty = -4.0 if re.search(r"-\d{2,3}x\d{2,3}\.", best_url) else 0.0
        position_bonus = max(0.0, 2.0 - idx * 0.3)

        total_score = base_score + keyword_bonus + thumb_penalty + position_bonus
        scored[best_url] = max(scored.get(best_url, -999.0), total_score)

    for a in container.find_all("a", href=True):
        href_url = sanitize_url(a["href"], base_url=base_url)
        if not href_url:
            continue
        if not urlparse(href_url).path.lower().endswith((".jpg", ".jpeg", ".png", ".webp")):
            continue
        link_text = a.get_text(" ", strip=True)
        if not _is_candidate_image_url(href_url, link_text):
            continue
        bonus = 8.0 + sum(2.5 for kw in BOOST_IMAGE_KEYWORDS if kw in f"{href_url} {link_text}".lower())
        scored[href_url] = max(scored.get(href_url, -999.0), bonus)

    ranked = sorted(scored.items(), key=lambda kv: kv[1], reverse=True)
    return [url for url, _ in ranked[:max_candidates]]


async def download_posters_as_data_urls(
    candidates: list[str],
    referer: str,
    max_images: int = MAX_POSTERS_PER_EVENT,
) -> list[tuple[str, str]]:
    """Pobiera do max_images poprawnych plakatów (verify=False obsługuje niepełne SSL gmin)."""
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
        "Referer": referer,
    }
    downloaded: list[tuple[str, str]] = []

    async with httpx.AsyncClient(
        follow_redirects=True, timeout=15.0, headers=headers, verify=False
    ) as client:
        for img_url in candidates:
            if len(downloaded) >= max_images:
                break
            try:
                resp = await client.get(img_url)
                if resp.status_code != 200:
                    print(f"    [PLAKAT POMINIĘTY] HTTP {resp.status_code}: {img_url}")
                    continue

                ctype = resp.headers.get("content-type", "").split(";")[0].strip().lower()
                if ctype not in ALLOWED_IMAGE_MIMES:
                    continue

                size = len(resp.content)
                if size < MIN_POSTER_BYTES or size > MAX_POSTER_BYTES:
                    print(f"    [PLAKAT POMINIĘTY] Zły rozmiar ({size // 1024} KB): {img_url}")
                    continue

                mime = "image/jpeg" if ctype == "image/jpg" else ctype
                b64 = base64.b64encode(resp.content).decode("ascii")
                downloaded.append((img_url, f"data:{mime};base64,{b64}"))
            except httpx.HTTPError as exc:
                print(f"    [PLAKAT BŁĄD POBIERANIA] {type(exc).__name__}: {img_url}")

    return downloaded


def _parse_json_response(raw_text: str) -> Optional[dict]:
    cleaned = raw_text.strip()
    if cleaned.startswith("```"):
        cleaned = re.sub(r"^```(?:json)?\s*|\s*```$", "", cleaned, flags=re.IGNORECASE).strip()
    try:
        data = json.loads(cleaned)
    except json.JSONDecodeError:
        return None
    if isinstance(data, list) and data and isinstance(data[0], dict):
        return data[0]
    return data if isinstance(data, dict) else None


async def extract_details_from_posters_with_retry(
    posters: list[tuple[str, str]],
    event_title: str,
) -> tuple[Optional[EventDetails], bool]:
    """
    Wysyła do 3 grafik w 1 zapytaniu multimodalnym z automatycznym fallbackiem modeli
    (3.8-flash -> 3.5-flash-lite).
    Zwraca: (EventDetails lub None, czy_wystąpił_błąd_przejściowy_API).
    """
    today = date.today().isoformat()
    prompt = f"""
    Dzisiejsza data to {today}.
    Przesyłam grafiki z artykułu o wydarzeniu: "{event_title}".
    Jedna z nich to prawdopodobnie plakat wydarzenia (pozostałe mogą być zdjęciami ozdobnymi — zignoruj je).

    ZADANIE (wykonaj po kolei):
    1. Odszukaj na plakacie wszystkie napisy określające: dzień/miesiąc/rok, godzinę startu/zbiórki oraz dokładne miejsce/obiekt/miejscowość.
    2. Przepisz te napisy dosłownie do pola "poster_raw_text".
    3. Na podstawie przepisanych napisów wypełnij obiekt JSON:
       - "is_upcoming_sport_event": false jeśli grafika dotyczy przeszłej relacji/wyników lub remontu/inwestycji, w przeciwnym razie true,
       - "rejection_reason": powód odrzucenia (lub null),
       - "poster_raw_text": dosłownie przepisany tekst z datą, godziną i miejscem z plakatu (lub null),
       - "event_date": data w formacie "YYYY-MM-DD" (jeśli brak roku na plakacie, dobierz najbliższą datę względem {today}; jeśli brak -> null),
       - "time": godzina w formacie "HH:MM" (np. "10:00", jeśli jest kilka godzin podaj pierwszą / start; jeśli brak -> null),
       - "location": pełna nazwa miejsca / obiektu / ulicy / miejscowości (lub null),
       - "summary": krótkie zdanie o wydarzeniu (dystans, zapisy, opłata) lub null.

    Zwróć WYŁĄCZNIE poprawny obiekt JSON. Nie zgaduj danych, których nie ma na obrazku.
    """

    content_blocks: list[dict] = [{"type": "text", "text": prompt}]
    for _, data_url in posters:
        content_blocks.append({"type": "image_url", "image_url": {"url": data_url}})

    api_key = _get_api_key()
    transient_error = False

    for model_idx, model_name in enumerate(POSTER_MODELS):
        has_fallback = model_idx < len(POSTER_MODELS) - 1

        for attempt in range(POSTER_RETRIES_PER_MODEL):
            try:
                response = await acompletion(
                    model=model_name,
                    api_key=api_key,
                    temperature=0.0,
                    response_format={"type": "json_object"},
                    messages=[{"role": "user", "content": content_blocks}],
                )
                content = response.choices[0].message.content or ""
                parsed = _parse_json_response(content)
                if not parsed:
                    print(f"    [BŁĄD PLAKATU ({model_name})] Niepoprawny JSON: {content[:120]}")
                    return None, False

                details = EventDetails.model_validate(parsed)
                if details.poster_raw_text:
                    print(f"    [PLAKAT OCR ({model_name})] Odczytano: {details.poster_raw_text}")
                return details, False

            except ValidationError as exc:
                loc = exc.errors()[0].get("loc") if exc.errors() else "?"
                print(f"    [BŁĄD PLAKATU ({model_name})] Niezgodny schemat (pole {loc}).")
                return None, False
            except Exception as exc:
                error_text = str(exc)

                if _is_model_not_found(error_text):
                    print(f"    [PLAKAT] Model {model_name} niedostępny (404) — przełączam na zapasowy...")
                    break

                if _is_daily_quota(error_text):
                    if has_fallback:
                        print(f"    [PLAKAT] Limit dzienny na {model_name} — przełączam na zapasowy...")
                        break
                    transient_error = True
                    print(f"    [PLAKAT] Limit dzienny wyczerpany dla wszystkich modeli plakatowych.")
                    return None, True

                if _is_retryable_api_error(error_text):
                    transient_error = True
                    if attempt < POSTER_RETRIES_PER_MODEL - 1:
                        wait_time = BASE_BACKOFF_SECONDS * (2**attempt) + random.uniform(1.0, 4.0)
                        print(
                            f"    [429/503 PLAKAT {model_name}] Czekam {wait_time:.1f} s "
                            f"(próba {attempt + 1}/{POSTER_RETRIES_PER_MODEL})..."
                        )
                        await asyncio.sleep(wait_time)
                        continue
                    if has_fallback:
                        print(f"    [PLAKAT] {model_name} przeciążony — przełączam na {POSTER_MODELS[model_idx + 1]}...")
                        await asyncio.sleep(2.0)
                        break

                print(f"    [BŁĄD PLAKATU ({model_name})] {error_text[:180]}")
                if has_fallback:
                    break
                return None, transient_error

    return None, transient_error


# --- EKSTRAKCJA Z TEKSTU I WZBOGACANIE WYDARZEŃ ---
async def extract_from_html_with_retry(
    crawler: AsyncWebCrawler,
    cleaned_html: str,
    llm_cfg: CrawlerRunConfig,
) -> Optional[list[dict]]:
    raw_url = f"raw:{cleaned_html}"

    for attempt in range(MAX_RETRIES + 1):
        error_text = ""
        try:
            result = await crawler.arun(url=raw_url, config=llm_cfg)
            if not result.success:
                error_text = result.error_message or "Nieznany błąd ekstrakcji"
            elif not result.extracted_content:
                return []
            else:
                raw_items = json.loads(result.extracted_content)
                if not isinstance(raw_items, list):
                    return []

                llm_errors = [
                    str(item.get("content", item))
                    for item in raw_items
                    if isinstance(item, dict) and item.get("error")
                ]
                if not llm_errors:
                    return raw_items
                error_text = " | ".join(llm_errors)

        except json.JSONDecodeError:
            print("  [BŁĄD] Model nie zwrócił poprawnego JSON-a.")
            return None
        except Exception as exc:
            error_text = str(exc)

        if _is_daily_quota(error_text):
            raise DailyQuotaExhaustedError(error_text)

        if _is_retryable_api_error(error_text) and attempt < MAX_RETRIES:
            wait_time = BASE_BACKOFF_SECONDS * (2**attempt) + random.uniform(1.0, 4.0)
            print(f"  [429/503] Limit lub przeciążenie — czekam {wait_time:.1f} s (próba {attempt + 1}/{MAX_RETRIES})...")
            await asyncio.sleep(wait_time)
            continue

        print(f"  [BŁĄD LLM] {error_text[:200]}")
        return None

    return None


def _merge_details(event: SportEvent, details: EventDetails) -> None:
    if not event.event_date and details.event_date:
        event.event_date = details.event_date
    if not event.time and details.time:
        event.time = details.time
    if not event.location and details.location:
        event.location = details.location
    if details.summary and len(details.summary.strip()) > len((event.summary or "").strip()):
        event.summary = details.summary.strip()


async def enrich_event_from_detail_page(
    crawler: AsyncWebCrawler,
    event: SportEvent,
    detail_fetch_cfg: CrawlerRunConfig,
    detail_llm_cfg: CrawlerRunConfig,
) -> tuple[int, bool, bool, bool]:
    """
    Wchodzi w podstronę wydarzenia, weryfikuje czy to nadchodzące wydarzenie sportowe,
    uzupełnia dane z tekstu, a przy brakach analizuje do 3 plakatów z fallbackiem modeli.
    Zwraca: (liczba_zapytań_LLM, czy_użyto_plakatu, czy_zachować_wydarzenie, czy_błąd_przejściowy).
    """
    if not event.url:
        return 0, False, True, False

    if not await asyncio.to_thread(is_domain_resolvable, event.url):
        print(f"    [BŁĄD DNS] Nieosiągalna podstrona: {event.url}")
        return 0, False, True, False

    print(f"    -> Sprawdzam podstronę: {event.url}")
    page_res = await crawler.arun(url=event.url, config=detail_fetch_cfg)
    if not page_res.success or not page_res.cleaned_html:
        print("    [BŁĄD] Nie udało się pobrać podstrony.")
        return 0, False, True, False

    llm_calls = 0
    poster_used = False
    had_transient_error = False

    # KROK 2A: Weryfikacja i ekstrakcja z tekstu podstrony
    raw_details = await extract_from_html_with_retry(crawler, page_res.cleaned_html, detail_llm_cfg)
    llm_calls += 1

    if raw_details is None:
        had_transient_error = True
    else:
        for item in raw_details:
            if not isinstance(item, dict) or item.get("error"):
                continue
            try:
                details = EventDetails.model_validate(item)
                if not details.is_upcoming_sport_event:
                    print(f"    [ODFILTROWANO] {details.rejection_reason or 'to nie zapowiedź wydarzenia'}")
                    return llm_calls, False, False, False
                _merge_details(event, details)
                break
            except ValidationError:
                continue

    if is_past_event(event.event_date):
        print(f"    [ODFILTROWANO] Wydarzenie już się odbyło ({event.event_date}).")
        return llm_calls, False, False, False

    # KROK 2B: Wieloobrazkowy fallback na plakaty (gdy w tekście nadal brakuje daty/godziny/miejsca)
    still_missing = not (event.event_date and event.time and event.location)
    if still_missing:
        source_html = page_res.html or page_res.cleaned_html
        candidates = select_poster_candidates_from_html(source_html, event.url)
        if candidates:
            posters = await download_posters_as_data_urls(candidates, referer=event.url)
            if posters:
                poster_names = ", ".join(os.path.basename(urlparse(u).path) or u for u, _ in posters)
                print(f"    -> Analizuję plakaty ({len(posters)}): {poster_names}")
                await asyncio.sleep(random.uniform(*DELAY_AFTER_LLM_CALL))

                poster_details, poster_err = await extract_details_from_posters_with_retry(
                    posters, event.title
                )
                llm_calls += 1
                poster_used = True
                if poster_err:
                    had_transient_error = True

                if poster_details:
                    if not poster_details.is_upcoming_sport_event:
                        print(
                            f"    [ODFILTROWANO PO PLAKACIE] "
                            f"{poster_details.rejection_reason or 'to nie zapowiedź wydarzenia'}"
                        )
                        return llm_calls, True, False, False

                    _merge_details(event, poster_details)
                    print(
                        f"    [PLAKAT OK] data={event.event_date}, "
                        f"godz={event.time}, miejsce={event.location}"
                    )

                    if is_past_event(event.event_date):
                        print(f"    [ODFILTROWANO PO PLAKACIE] Data z przeszłości ({event.event_date}).")
                        return llm_calls, True, False, False

    return llm_calls, poster_used, True, had_transient_error

MAX_LLM_HTML_CHARS = 45_000

def trim_html_for_llm(cleaned_html: str, max_chars: int = MAX_LLM_HTML_CHARS) -> str:
    """Usuwa ciężkie SVG/base64 i przycina zbyt długie strony archiwalne."""
    no_svg = re.sub(r"<svg\b[^>]*>.*?</svg>", "", cleaned_html, flags=re.IGNORECASE | re.DOTALL)
    no_b64 = re.sub(r"data:image/[^\"'\s)]+", "", no_svg, flags=re.IGNORECASE)
    if len(no_b64) <= max_chars:
        return no_b64
    return no_b64[:max_chars]
async def scrape_municipalities(urls: list[str]):
    conn = init_db(DB_PATH)
    browser_cfg = BrowserConfig(
        headless=True,
        verbose=False,
        extra_args=["--ignore-certificate-errors"],
    )
    list_strategy = build_list_strategy()
    detail_strategy = build_detail_strategy()

    # Opóźnienie JS (delay_before_return_html) pozwala wyrenderować strony SPA (np. orzysz.pl)
    list_fetch_cfg = CrawlerRunConfig(
        cache_mode=CacheMode.BYPASS,
        excluded_tags=["nav", "footer", "header", "aside"],
        word_count_threshold=10,
        delay_before_return_html=SPA_JS_DELAY_SECONDS,
        verbose=False,
    )
    detail_fetch_cfg = CrawlerRunConfig(
        cache_mode=CacheMode.BYPASS,
        excluded_tags=["nav", "footer"],
        word_count_threshold=5,
        delay_before_return_html=1.0,
        verbose=False,
    )
    list_llm_cfg = CrawlerRunConfig(
        cache_mode=CacheMode.BYPASS, extraction_strategy=list_strategy, verbose=False
    )
    detail_llm_cfg = CrawlerRunConfig(
        cache_mode=CacheMode.BYPASS, extraction_strategy=detail_strategy, verbose=False
    )

    stats = {
        "skipped": 0,
        "llm_calls": 0,
        "poster_reads": 0,
        "new_events": 0,
        "updated_events": 0,
        "rejected_events": 0,
    }

    try:
        async with AsyncWebCrawler(config=browser_cfg) as crawler:
            for idx, raw_url in enumerate(urls, start=1):
                url = sanitize_url(raw_url)
                if not url:
                    print(f"[{idx}/{len(urls)}] [POMINIĘTO] Niepoprawny adres URL: {raw_url!r}")
                    continue

                if not await asyncio.to_thread(is_domain_resolvable, url):
                    print(f"[{idx}/{len(urls)}] [BŁĄD DNS] Domena nie istnieje lub brak sieci: {url}")
                    record_source_failure(conn, url)
                    continue

                print(f"[{idx}/{len(urls)}] Sprawdzam: {url}")

                page_res = await crawler.arun(url=url, config=list_fetch_cfg)
                if not page_res.success or not page_res.cleaned_html:
                    err_text = page_res.error_message or "nieznany błąd"
                    goto_line = next(
                        (
                            line.strip()
                            for line in err_text.splitlines()
                            if "Page.goto:" in line or "Blocked" in line
                        ),
                        err_text.splitlines()[0],
                    )
                    print(f"  [BŁĄD POBIERANIA] {goto_line[:180]}")
                    record_source_failure(conn, url)
                    continue

                reset_source_failures(conn, url)

                current_hash = compute_content_hash(str(page_res.markdown or ""))
                if get_saved_hash(conn, url) == current_hash:
                    mark_page_checked(conn, url)
                    stats["skipped"] += 1
                    print("  [POMINIĘTO] Brak zmian na stronie (0 zapytań do LLM).")
                    continue

                print("  [ZMIANA] Wykryto nową treść — analizuję listę wydarzeń...")
                raw_items = await extract_from_html_with_retry(
                    crawler, trim_html_for_llm(page_res.cleaned_html), list_llm_cfg
                )
                stats["llm_calls"] += 1

                if raw_items is None:
                    # Błąd LLM (np. 503): nie zapisujemy hasha ani nie dezaktywujemy źródła
                    continue

                new_on_page = 0
                updated_on_page = 0
                rejected_on_page = 0
                details_fetched = 0
                page_had_transient_error = False
                base_clean = url.split("#")[0].rstrip("/")

                # PRZEBIEG 1: Filtr z listy + natychmiastowy zapis do SQLite
                parsed_events: list[SportEvent] = []
                for item in raw_items:
                    if not isinstance(item, dict) or item.get("error"):
                        continue
                    try:
                        event = SportEvent.model_validate(item)
                    except ValidationError as exc:
                        field_loc = exc.errors()[0].get("loc") if exc.errors() else "?"
                        print(f"  [ODRZUCONO WALIDACJA] {item.get('title')!r}: błąd pola {field_loc}")
                        continue

                    if event.article_type != "zapowiedz_wydarzenia":
                        rejected_on_page += 1
                        print(f"  [POMINIĘTO TYP={event.article_type}] {event.title}")
                        continue

                    event.url = sanitize_url(event.url, base_url=url)

                    # Odrzuca archiwalne wpisy po roku w URL (np. /2024/06/...) bez wywoływania API
                    if has_past_year_in_url(event.url):
                        rejected_on_page += 1
                        print(f"  [POMINIĘTO ARCHIWUM URL] {event.title} ({event.url})")
                        continue

                    event_clean = (event.url or "").split("#")[0].rstrip("/")
                    has_distinct_url = bool(event_clean) and event_clean != base_clean

                    # Jeśli na liście pojawiła się data z przeszłości (często data publikacji):
                    # - przy braku podstrony odrzucamy od razu,
                    # - przy dostępnej podstronie zerujemy datę i pozwalamy podstronie/plakatowi ją zweryfikować.
                    if is_past_event(event.event_date):
                        if not has_distinct_url:
                            rejected_on_page += 1
                            print(f"  [POMINIĘTO PRZESZŁE={event.event_date}] {event.title}")
                            continue
                        event.event_date = None

                    if upsert_event(conn, event, url):
                        new_on_page += 1
                    else:
                        updated_on_page += 1
                    parsed_events.append(event)

                # PRZEBIEG 2: Weryfikacja podstron + wieloobrazkowy odczyt plakatów z fallbackiem
                for event in parsed_events:
                    needs_details = not (event.event_date and event.time and event.location)
                    event_clean = (event.url or "").split("#")[0].rstrip("/")
                    has_distinct_url = bool(event_clean) and event_clean != base_clean

                    if needs_details and has_distinct_url and details_fetched < MAX_DETAIL_PAGES_PER_SITE:
                        await asyncio.sleep(random.uniform(*DELAY_AFTER_LLM_CALL))
                        calls_made, used_poster, keep_event, transient_err = (
                            await enrich_event_from_detail_page(
                                crawler, event, detail_fetch_cfg, detail_llm_cfg
                            )
                        )
                        stats["llm_calls"] += calls_made
                        if used_poster:
                            stats["poster_reads"] += 1
                        if calls_made > 0:
                            details_fetched += 1
                        if transient_err:
                            page_had_transient_error = True

                        if not keep_event:
                            delete_event(conn, event, url)
                            rejected_on_page += 1
                            if new_on_page > 0:
                                new_on_page -= 1
                        elif calls_made > 0:
                            upsert_event(conn, event, url)

                if page_had_transient_error:
                    print("  [INFO] Nie zapisano hasha strony (chwilowy błąd API) — ponowię przy kolejnym cyklu.")
                else:
                    save_page_hash(conn, url, current_hash)

                stats["new_events"] += new_on_page
                stats["updated_events"] += updated_on_page
                stats["rejected_events"] += rejected_on_page
                print(
                    f"  [OK] Nowe: {new_on_page}, zaktualizowane: {updated_on_page}, "
                    f"odfiltrowane: {rejected_on_page} (podstron: {details_fetched})"
                )

                if idx < len(urls):
                    await asyncio.sleep(random.uniform(*DELAY_AFTER_LLM_CALL))

    except DailyQuotaExhaustedError:
        print("\n[STOP] Wyczerpano dzienny limit (RPD) API. Zapisano wszystkie zebrane dotąd wydarzenia.")
    except KeyboardInterrupt:
        print("\n[STOP] Przerwano ręcznie.")
    finally:
        total_exported = export_db_to_json(conn, OUTPUT_JSON)
        conn.close()
        print(
            f"\nPodsumowanie: pominięte={stats['skipped']}, "
            f"zapytania LLM={stats['llm_calls']} (w tym plakaty={stats['poster_reads']}), "
            f"nowe={stats['new_events']}, zaktualizowane={stats['updated_events']}, "
            f"odfiltrowane={stats['rejected_events']}."
        )
        print(f"Zapisano łącznie {total_exported} wydarzeń do: {OUTPUT_JSON}")


if __name__ == "__main__":
    MUNICIPAL_URLS = load_urls_from_db(DB_PATH, batch_limit=BATCH_LIMIT)

    if MUNICIPAL_URLS:
        print(f"Załadowano {len(MUNICIPAL_URLS)} stron z bazy SQLite.")
    else:
        print("Tabela 'sources' jest pusta — uruchamiam scraper na liście FALLBACK_URLS.")
        MUNICIPAL_URLS = FALLBACK_URLS

    asyncio.run(scrape_municipalities(MUNICIPAL_URLS))