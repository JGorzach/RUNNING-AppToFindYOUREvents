import asyncio
import os
import re
import socket
import sqlite3
from datetime import datetime
from typing import Optional
from urllib.parse import urljoin, urlparse

import httpx
from bs4 import BeautifulSoup
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass
# --- ŚCIEŻKI I KONFIGURACJA ---
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "wydarzenia.db")
PREVIEW_TXT = os.path.join(BASE_DIR, "zrodla_podglad.txt")
MANUAL_SEEDS_TXT = os.path.join(BASE_DIR, "moje_zrodla.txt")  # Opcjonalny plik z własnymi domenami

# Region: woj. warmińsko-mazurskie (Q54184 / PL-28).
# Ustaw None w obu polach, aby przeszukać całą Polskę.
VOIVODESHIP_QID = "Q54184"
VOIVODESHIP_ISO = "PL-28"

# Dozwolone końcówki domen (odcina przejęte domeny spamowe typu .cheap, .com, .xyz)
ALLOWED_TLDS = (".pl", ".eu")

# Osobne User-Agent: opisowy z kontaktem dla Wikidanych/Overpass oraz przeglądarkowy dla stron gmin
API_USER_AGENT = "GminySportEventsFinder/1.2 (mailto:{CONTACT_EMAIL})"
BROWSER_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)

OVERPASS_ENDPOINTS = [
    "https://overpass-api.de/api/interpreter",
    "https://lz4.overpass-api.de/api/interpreter",
    "https://z.overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://overpass.private.coffee/api/interpreter",
]

MAX_CONCURRENCY = 10
REQUEST_TIMEOUT = 12.0

IGNORED_DOMAINS = (
    "facebook.com", "fb.com", "instagram.com", "youtube.com", "youtu.be",
    "tiktok.com", "twitter.com", "x.com", "wikipedia.org", "booking.com",
    "google.com", "goo.gl", "bip.", "gov.pl", "zdrofit.pl", "cityfit.pl",
    "aftermarket.pl", "premium.pl", "sedo.com", "nazwa.pl", "home.pl",
)
IGNORED_EXTENSIONS = (
    ".pdf", ".jpg", ".jpeg", ".png", ".webp", ".gif", ".svg",
    ".doc", ".docx", ".xls", ".xlsx", ".zip", ".rar", ".mp4",
)
PARKED_PAGE_MARKERS = (
    "domena na sprzedaż", "domain for sale", "buy this domain",
    "domena została zarejestrowana", "strona w budowie", "under construction",
    "aftermarket.pl", "sedoparking", "casino", "gambling",
)
LINKED_UNIT_KEYWORDS = ("osir", "mosir", "csir", "gosir", "gok", "mgok", "mok", "ckis", "gokis")


# --- BAZA DANYCH (SQLite) ---
def init_sources_table(db_path: str = DB_PATH) -> sqlite3.Connection:
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS sources (
            url TEXT PRIMARY KEY,
            homepage_url TEXT NOT NULL,
            name TEXT,
            source_type TEXT NOT NULL,
            origin TEXT NOT NULL,
            status TEXT NOT NULL DEFAULT 'active',
            fail_count INTEGER NOT NULL DEFAULT 0,
            last_verified TEXT NOT NULL
        );
        """
    )
    conn.commit()
    return conn


def save_source(
    conn: sqlite3.Connection,
    url: str,
    homepage_url: str,
    name: str,
    source_type: str,
    origin: str,
) -> None:
    now = datetime.now().isoformat(timespec="seconds")
    conn.execute(
        """
        INSERT INTO sources (url, homepage_url, name, source_type, origin, status, fail_count, last_verified)
        VALUES (?, ?, ?, ?, ?, 'active', 0, ?)
        ON CONFLICT(url) DO UPDATE SET
            homepage_url = excluded.homepage_url,
            name = COALESCE(NULLIF(excluded.name, ''), sources.name),
            status = 'active',
            fail_count = 0,
            last_verified = excluded.last_verified
        """,
        (url, homepage_url, name, source_type, origin, now),
    )
    conn.commit()


def export_sources_preview(conn: sqlite3.Connection, path: str = PREVIEW_TXT) -> int:
    rows = conn.execute(
        "SELECT url, source_type, name FROM sources WHERE status = 'active' ORDER BY source_type, name"
    ).fetchall()
    with open(path, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(f"{r['url']}  # [{r['source_type']}] {r['name']}\n")
    return len(rows)


# --- SANITYZACJA I WALIDACJA DOMEN ---
def sanitize_seed_url(raw: Optional[str]) -> Optional[str]:
    """Czyści URL, usuwa linki spoza .pl/.eu oraz ignorowane serwisy (BIP, social media)."""
    if not raw or not isinstance(raw, str):
        return None

    text = raw.strip()
    if not text or text.startswith("#"):
        return None

    md_match = re.search(r"\[[^\]]*\]\(([^)]+)\)", text)
    if md_match:
        text = md_match.group(1).strip()

    text = text.split()[0].strip("<>\"'(),;[] ")
    if not text:
        return None
    if not text.startswith(("http://", "https://")):
        text = "https://" + text

    parsed = urlparse(text)
    if parsed.scheme not in ("http", "https") or not parsed.netloc or "." not in parsed.netloc:
        return None

    host = (parsed.hostname or "").lower()
    if not host.endswith(ALLOWED_TLDS):
        return None
    if any(bad in host for bad in IGNORED_DOMAINS):
        return None

    clean_path = parsed.path.rstrip("/")
    return f"{parsed.scheme}://{parsed.netloc}"


def _base_domain(url: str) -> str:
    host = (urlparse(url).hostname or "").lower()
    return host[4:] if host.startswith("www.") else host


def is_dns_resolvable(url: str) -> bool:
    host = urlparse(url).hostname
    if not host:
        return False
    try:
        socket.getaddrinfo(host, None)
        return True
    except socket.gaierror:
        return False


def is_parked_or_spam_page(soup: BeautifulSoup, html_text: str) -> bool:
    """Wykrywa puste strony, parkingi domen i przejęte serwisy spamowe."""
    if len(html_text.strip()) < 400:
        return True
    title_text = (soup.title.string or "").lower() if soup.title and soup.title.string else ""
    sample = f"{title_text} {soup.get_text(' ', strip=True)[:1500].lower()}"
    return any(marker in sample for marker in PARKED_PAGE_MARKERS)


# --- ŹRÓDŁO 1: WIKIDATA (SZYBKIE ZAPYTANIE BEZ REKURENCJI) ---
async def fetch_gminy_from_wikidata(client: httpx.AsyncClient) -> list[dict]:
    if VOIVODESHIP_QID:
        region_block = f"""
        {{
          ?item wdt:P131 wd:{VOIVODESHIP_QID} .
        }} UNION {{
          ?item wdt:P131 ?powiat .
          ?powiat wdt:P131 wd:{VOIVODESHIP_QID} .
        }}
        """
    else:
        region_block = "?item wdt:P17 wd:Q36 ."

    sparql = f"""
    SELECT DISTINCT ?itemLabel ?website WHERE {{
      VALUES ?type {{ wd:Q2616791 wd:Q3491915 wd:Q3504085 wd:Q925381 wd:Q15334 }}
      ?item wdt:P31 ?type .
      {region_block}
      ?item wdt:P856 ?website .
      SERVICE wikibase:label {{ bd:serviceParam wikibase:language "pl". }}
    }}
    """

    print("[1/3] Pobieram strony gmin z Wikidanych (SPARQL)...")
    bindings = []

    for attempt in range(1, 4):
        try:
            resp = await client.post(
                "https://query.wikidata.org/sparql",
                data={"query": sparql},
                headers={
                    "Accept": "application/sparql-results+json",
                    "User-Agent": API_USER_AGENT,
                },
                timeout=35.0,
            )
            if resp.status_code in (429, 500, 502, 503, 504) and attempt < 3:
                print(f"  [WIKIDATA] Status {resp.status_code} — ponawiam próbę ({attempt}/3)...")
                await asyncio.sleep(4 * attempt)
                continue

            resp.raise_for_status()
            bindings = resp.json().get("results", {}).get("bindings", [])
            break
        except httpx.HTTPStatusError as exc:
            body = exc.response.text[:160].replace("\n", " ")
            print(f"  [BŁĄD WIKIDATA] HTTP {exc.response.status_code}: {body}")
            return []
        except Exception as exc:
            print(f"  [BŁĄD WIKIDATA] {type(exc).__name__}: {exc}")
            if attempt < 3:
                await asyncio.sleep(3 * attempt)
            else:
                return []

    seeds = []
    for row in bindings:
        url = sanitize_seed_url(row.get("website", {}).get("value"))
        name = row.get("itemLabel", {}).get("value", "").strip()
        if url:
            seeds.append({"url": url, "name": name, "source_type": "gmina", "origin": "wikidata"})

    print(f"  -> Znaleziono kandydatów (gminy): {len(seeds)}")
    return seeds


# --- ŹRÓDŁO 2: OPENSTREETMAP OVERPASS (INDEKSOWANE + MIRRORY) ---
async def fetch_units_from_osm(client: httpx.AsyncClient) -> list[dict]:
    area_selector = (
        f'area["ISO3166-2"="{VOIVODESHIP_ISO}"]->.a;'
        if VOIVODESHIP_ISO
        else 'area["ISO3166-1"="PL"]->.a;'
    )
    query = f"""
    [out:json][timeout:25];
    {area_selector}
    (
      nwr["leisure"="sports_centre"]["website"](area.a);
      nwr["leisure"="sports_centre"]["contact:website"](area.a);
      nwr["leisure"="stadium"]["website"](area.a);
      nwr["leisure"="stadium"]["contact:website"](area.a);
      nwr["amenity"="community_centre"]["website"](area.a);
      nwr["amenity"="community_centre"]["contact:website"](area.a);
    );
    out tags;
    """

    print("[2/3] Pobieram strony OSiR / stadionów / GOK z OpenStreetMap...")
    elements = []

    for endpoint in OVERPASS_ENDPOINTS:
        try:
            resp = await client.post(
                endpoint,
                data={"data": query},
                headers={"User-Agent": API_USER_AGENT},
                timeout=35.0,
            )
            if resp.status_code == 200:
                elements = resp.json().get("elements", [])
                print(f"  -> Odpowiedział serwer: {endpoint}")
                break
            print(f"  [OVERPASS] {endpoint} zwrócił HTTP {resp.status_code} — próbuję kolejny serwer...")
        except Exception as exc:
            print(f"  [OVERPASS] {endpoint} nieosiągalny ({type(exc).__name__}) — próbuję kolejny serwer...")
        await asyncio.sleep(1.5)

    if not elements:
        print("  [BŁĄD OVERPASS] Wszystkie publiczne serwery Overpass są chwilowo przeciążone.")
        return []

    seeds = []
    for el in elements:
        tags = el.get("tags", {})
        raw_url = tags.get("website") or tags.get("contact:website")
        url = sanitize_seed_url(raw_url)
        if not url:
            continue

        name = tags.get("name", "").strip()
        combined = f"{name} {url}".lower()
        if any(k in combined for k in ("osir", "mosir", "csir", "gosir", "sport", "stadion", "basen", "hala")):
            stype = "osir"
        elif any(k in combined for k in ("gok", "mok", "kultur", "dom kultury", "ckis")):
            stype = "gok"
        else:
            stype = "obiekt_sportowy"

        seeds.append({"url": url, "name": name or _base_domain(url), "source_type": stype, "origin": "osm"})

    print(f"  -> Znaleziono kandydatów (OSiR/GOK/obiekty): {len(seeds)}")
    return seeds


# --- ŹRÓDŁO 3 (OPCJONALNE): LOKALNY PLIK moje_zrodla.txt ---
def load_manual_seeds(path: str = MANUAL_SEEDS_TXT) -> list[dict]:
    if not os.path.exists(path):
        return []
    seeds = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            url = sanitize_seed_url(line)
            if url:
                seeds.append({
                    "url": url,
                    "name": _base_domain(url),
                    "source_type": "gmina",
                    "origin": "manual",
                })
    if seeds:
        print(f"[INFO] Wczytano {len(seeds)} własnych adresów z pliku '{os.path.basename(path)}'.")
    return seeds


# --- ETAP 3: ŁOWCA ZAKŁADEK AKTUALNOŚCI / KALENDARZY (BEZ POJEDYNCZYCH ARTYKUŁÓW) ---
def find_best_events_subpage(soup: BeautifulSoup, homepage_url: str) -> str:
    """Wybiera najlepszą podstronę z listą aktualności lub kalendarzem, odrzucając pojedyncze wpisy."""
    home_domain = _base_domain(homepage_url)
    best_url = homepage_url
    best_score = 0

    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if not href or href.startswith(("#", "mailto:", "tel:", "javascript:")):
            continue

        full_url = urljoin(homepage_url, href).split("#")[0].rstrip("/")
        parsed = urlparse(full_url)
        if parsed.scheme not in ("http", "https") or _base_domain(full_url) != home_domain:
            continue

        path_lower = parsed.path.lower()
        # Odrzucamy załączniki oraz pojedyncze strony artykułów kończące się na .html/.htm
        if path_lower.endswith(IGNORED_EXTENSIONS) or path_lower.endswith((".html", ".htm")):
            continue

        # Odrzucamy pojedyncze pliki .php (np. polozenie.php), chyba że to lista (index.php / aktualnosci.php)
        if path_lower.endswith(".php") and not any(
            k in path_lower for k in ("index.php", "aktualn", "wydarz", "kalendarz", "news")
        ):
            continue

        # Odrzucamy linki z długim ID artykułu (np. /6385-puchar-..., /artykuly/465/...)
        if re.search(r"(/|-)\d{3,}", path_lower):
            continue

        # Pomijamy techniczny prefiks 'index.php' przy liczeniu głębokości ścieżki
        raw_segments = [seg for seg in parsed.path.split("/") if seg]
        segments = [seg for seg in raw_segments if seg.lower() != "index.php"]
        if not segments or len(segments) > 2:
            continue
        # Jeśli 1. segment to nazwa działu, a 2. ma myślnik (np. /news/kajakiem-przez-mazury), to pojedynczy wpis
        if len(segments) == 2 and segments[0].lower() in ("news", "aktualnosci", "wydarzenia", "artykuly") and "-" in \
                segments[1]:
            continue

        # Długi slug z 3+ myślnikami (np. /800-lecie-lubawy-kalendarz-imprez) to prawie zawsze pojedynczy wpis
        if any(seg.count("-") >= 3 for seg in segments):
            continue

        text = a.get_text(" ", strip=True).lower()
        combined = f"{path_lower} {text}"

        score = 0
        if any(k in combined for k in ("kalendarz", "wydarzeni", "zapowiedzi", "imprez")):
            score += 14
        if any(k in combined for k in ("aktualnosci", "aktualności", "wiadomosci", "wiadomości", "news")):
            score += 10
        # Bonus za "sport" wyłącznie w połączeniu z aktualnościami/wydarzeniami (nie dla statycznego wykazu obiektów)
        if any(k in combined for k in ("sport", "rekreacj")) and any(
            k in combined for k in ("aktualn", "wydarz", "kalendarz", "news", "imprez")
        ):
            score += 6

        if any(
            k in combined
            for k in (
                "bip", "przetarg", "rodo", "kontakt", "polityk", "archiwum",
                "sesj", "uchwal", "galeria", "obiekty", "polozenie", "położenie",
                "dla-mediow", "dla mediów", "statut", "rada", "solectw", "sołectw",
                "cennik", "regulamin", "dokumenty", "oferty", "praca","osp", "straz", "straż", "edukacj", "szkol", "szkoł",
"filmy", "o-nas", "dla-turysty", "turyst", "biznes",
            )
        ):
            score -= 25

        if len(segments) == 1:
            score += 3
        if parsed.query:
            score -= 3

        if score > best_score:
            best_score = score
            best_url = full_url

    return best_url


def discover_linked_units(soup: BeautifulSoup, homepage_url: str) -> list[dict]:
    """Wyciąga ze strony gminy linki wychodzące do stron podległego OSiR-u lub GOK-u."""
    home_domain = _base_domain(homepage_url)
    found = []

    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if not href.startswith(("http://", "https://")):
            continue
        clean = sanitize_seed_url(href)
        if not clean or _base_domain(clean) == home_domain:
            continue

        text = a.get_text(" ", strip=True)
        combined = f"{clean} {text}".lower()
        if any(kw in combined for kw in LINKED_UNIT_KEYWORDS):
            stype = "osir" if any(k in combined for k in ("osir", "mosir", "csir", "gosir")) else "gok"
            found.append({
                "url": clean,
                "name": text[:80] or _base_domain(clean),
                "source_type": stype,
                "origin": "gmina_link",
            })
    return found


async def inspect_seed(
    client: httpx.AsyncClient,
    sem: asyncio.Semaphore,
    seed: dict,
) -> tuple[Optional[dict], list[dict]]:
    """Sprawdza DNS, przekierowania (blokuje ucieczkę poza .pl/.eu), spam i wyszukuje zakładkę listy."""
    url = seed["url"]
    async with sem:
        if not await asyncio.to_thread(is_dns_resolvable, url):
            return None, []

        try:
            resp = await client.get(url, follow_redirects=True, timeout=REQUEST_TIMEOUT)
            if resp.status_code >= 400:
                return None, []
            ctype = resp.headers.get("content-type", "").lower()
            if "text/html" not in ctype:
                return None, []
        except httpx.HTTPError:
            return None, []

        # Ponowna sanityzacja po przekierowaniach — odcina wygasłe domeny przekierowujące na spam (np. .cheap)
        final_home = sanitize_seed_url(str(resp.url))
        if not final_home:
            return None, []

        final_host = (urlparse(final_home).hostname or "").lower()
        if not final_host.endswith(ALLOWED_TLDS):
            return None, []

        soup = BeautifulSoup(resp.text, "html.parser")
        if is_parked_or_spam_page(soup, resp.text):
            return None, []

        target_url = find_best_events_subpage(soup, final_home)

        extra_units = (
            discover_linked_units(soup, final_home)
            if seed["source_type"] == "gmina"
            else []
        )

        verified = {
            "url": target_url,
            "homepage_url": final_home,
            "name": seed["name"],
            "source_type": seed["source_type"],
            "origin": seed["origin"],
        }
        return verified, extra_units


async def run_discovery():
    conn = init_sources_table(DB_PATH)
    sem = asyncio.Semaphore(MAX_CONCURRENCY)

    async with httpx.AsyncClient(headers={"User-Agent": API_USER_AGENT}) as api_client:
        wikidata_seeds = await fetch_gminy_from_wikidata(api_client)
        osm_seeds = await fetch_units_from_osm(api_client)

    manual_seeds = load_manual_seeds(MANUAL_SEEDS_TXT)

    unique_by_domain: dict[str, dict] = {}
    for seed in wikidata_seeds + osm_seeds + manual_seeds:
        dom = _base_domain(seed["url"])
        if dom not in unique_by_domain:
            unique_by_domain[dom] = seed

    if not unique_by_domain:
        print("\n[UWAGA] Nie zebrano żadnych kandydatów do sprawdzenia.")
        conn.close()
        return

    print(f"[3/3] Weryfikuję {len(unique_by_domain)} unikalnych domen (.pl/.eu) i szukam zakładek wydarzeń...")
    saved_count = 0
    extra_candidates: dict[str, dict] = {}

    # Osobny klient do stron gminnych: przeglądarkowy User-Agent + verify=False na niepełne certyfikaty SSL
    async with httpx.AsyncClient(
        headers={"User-Agent": BROWSER_USER_AGENT},
        verify=False,
    ) as site_client:
        results = await asyncio.gather(
            *[inspect_seed(site_client, sem, seed) for seed in unique_by_domain.values()]
        )

        for verified, linked_units in results:
            if verified:
                save_source(conn, **verified)
                saved_count += 1
            for unit in linked_units:
                dom = _base_domain(unit["url"])
                if dom not in unique_by_domain and dom not in extra_candidates:
                    extra_candidates[dom] = unit

        if extra_candidates:
            print(f"  -> Sprawdzam {len(extra_candidates)} dodatkowych stron OSiR/GOK znalezionych na stronach gmin...")
            extra_results = await asyncio.gather(
                *[inspect_seed(site_client, sem, seed) for seed in extra_candidates.values()]
            )
            for verified, _ in extra_results:
                if verified:
                    save_source(conn, **verified)
                    saved_count += 1

    total_active = export_sources_preview(conn, PREVIEW_TXT)
    conn.close()
    print(f"\nGotowe! Zweryfikowano i zapisano: {saved_count} źródeł.")
    print(f"Łącznie aktywnych źródeł w bazie '{DB_PATH}': {total_active} (podgląd w '{PREVIEW_TXT}').")


if __name__ == "__main__":
    asyncio.run(run_discovery())