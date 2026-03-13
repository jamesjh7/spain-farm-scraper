"""
Spain Rural Property Scraper
Collects farmhouse/finca/cortijo listings suitable for farming, Airbnb, and event venues.
"""

import asyncio
import json
import csv
import re
import time
import random
import logging
import hashlib
from datetime import datetime
from pathlib import Path
from typing import Optional
from urllib.parse import urljoin, urlparse, quote_plus

import requests
from bs4 import BeautifulSoup
import pandas as pd
from playwright.async_api import async_playwright, Page, Browser

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

OUTPUT_DIR = Path(".")
LOG_FILE = OUTPUT_DIR / "scrape_log.txt"
JSON_FILE = OUTPUT_DIR / "spain_properties.json"
CSV_FILE = OUTPUT_DIR / "spain_properties.csv"
SUMMARY_FILE = OUTPUT_DIR / "spain_properties_summary.md"

PRICE_MIN = 50_000
PRICE_MAX = 2_000_000
MIN_PLOT_M2 = 10_000  # 1 hectare

USER_AGENTS = [
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.2 Safari/605.1.15",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:121.0) Gecko/20100101 Firefox/121.0",
]

# Spanish → English translation map
ES_TRANSLATIONS = {
    "dormitorios": "bedrooms",
    "habitaciones": "bedrooms",
    "baños": "bathrooms",
    "aseos": "bathrooms",
    "hectáreas": "hectares",
    "hectarea": "hectares",
    "parcela": "plot",
    "superficie": "area",
    "construida": "built",
    "terreno": "land",
    "piscina": "pool",
    "garage": "garage",
    "garaje": "garage",
    "bodega": "wine cellar",
    "cortijo": "cortijo",
    "finca": "finca",
    "masía": "masia",
    "hacienda": "hacienda",
    "olivos": "olive trees",
    "viñedo": "vineyard",
    "naranjos": "orange trees",
    "almendros": "almond trees",
    "agua": "water",
    "pozo": "well",
    "riego": "irrigation",
    "establos": "stables",
    "cochera": "garage/barn",
    "reformado": "renovated",
    "reformar": "needs renovation",
    "ruina": "ruins",
    "estado": "condition",
}

AIRPORTS = {
    "Andalusia": [
        ("Málaga", "AGP"),
        ("Sevilla", "SVQ"),
        ("Granada", "GRX"),
        ("Almería", "LEI"),
    ],
    "Valencia": [("Valencia", "VLC"), ("Alicante", "ALC")],
    "Murcia": [("Alicante", "ALC"), ("Murcia", "MJV")],
    "Catalonia": [("Barcelona", "BCN")],
    "Castilla-La Mancha": [("Madrid", "MAD")],
    "Extremadura": [("Badajoz", "BJZ"), ("Sevilla", "SVQ")],
}

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler(LOG_FILE, encoding="utf-8"),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def rand_delay(min_s=2.0, max_s=4.5):
    time.sleep(random.uniform(min_s, max_s))

def random_ua() -> str:
    return random.choice(USER_AGENTS)

def make_id(url: str) -> str:
    return hashlib.md5(url.encode()).hexdigest()[:12]

def safe_int(val) -> Optional[int]:
    try:
        return int(re.sub(r"[^\d]", "", str(val)))
    except Exception:
        return None

def safe_float(val) -> Optional[float]:
    try:
        cleaned = re.sub(r"[^\d.,]", "", str(val)).replace(",", ".")
        return float(cleaned)
    except Exception:
        return None

def extract_number(text: str) -> Optional[float]:
    m = re.search(r"[\d.,]+", str(text).replace(".", "").replace(",", "."))
    if m:
        try:
            return float(m.group())
        except Exception:
            return None
    return None

def score_property(prop: dict) -> int:
    score = 0

    # Farmland quality (0-3)
    land_ha = prop.get("land_area_hectares") or 0
    if land_ha >= 10:
        score += 3
    elif land_ha >= 3:
        score += 2
    elif land_ha >= 1:
        score += 1

    has_water = prop.get("water_source", "unknown") not in ("unknown", None)
    ag = prop.get("agricultural_features") or []
    if has_water and ag:
        score += 1
    if len(ag) >= 2:
        score += 1

    # Event/wedding venue (0-3) — heuristic from description
    desc = (prop.get("description_raw") or "").lower()
    venue_keywords = ["view", "vista", "mountain", "montaña", "event", "wedding", "boda",
                      "barn", "cortijo", "hacienda", "chapel", "capilla", "pool", "piscina",
                      "terrace", "terraza"]
    venue_hits = sum(1 for kw in venue_keywords if kw in desc)
    venue_score = min(3, venue_hits // 2)
    score += venue_score

    # Airbnb potential (0-2)
    beds = prop.get("bedrooms") or 0
    has_pool = prop.get("pool") or False
    condition = (prop.get("condition") or "").lower()
    if beds >= 4 and has_pool:
        score += 2
    elif beds >= 3 or has_pool:
        score += 1
    if condition in ("good", "excellent"):
        score += 1

    # Airport proximity (0-2)
    airport_str = prop.get("nearest_airport") or ""
    km_match = re.search(r"(\d+)\s*km", airport_str)
    if km_match:
        km = int(km_match.group(1))
        if km <= 80:
            score += 2
        elif km <= 130:
            score += 1

    return min(10, score)

# ---------------------------------------------------------------------------
# Base session for static sites
# ---------------------------------------------------------------------------

class StaticSession:
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "en-GB,en;q=0.9,es;q=0.8",
            "Accept-Encoding": "gzip, deflate, br",
            "Connection": "keep-alive",
        })

    def get(self, url: str, **kwargs) -> Optional[BeautifulSoup]:
        self.session.headers["User-Agent"] = random_ua()
        try:
            r = self.session.get(url, timeout=20, **kwargs)
            if r.status_code == 200:
                return BeautifulSoup(r.text, "html.parser")
            elif r.status_code == 403:
                log.warning(f"403 Forbidden: {url}")
            elif r.status_code == 429:
                log.warning(f"429 Rate limited: {url} — backing off 30s")
                time.sleep(30)
            else:
                log.warning(f"HTTP {r.status_code}: {url}")
        except Exception as e:
            log.error(f"Request failed {url}: {e}")
        return None

# ---------------------------------------------------------------------------
# Kyero scraper (static HTML)
# ---------------------------------------------------------------------------

class KyeroScraper:
    BASE = "https://www.kyero.com"
    SEARCH_URLS = [
        "/en/rural-farmhouse-spain-p1",
        "/en/rural-country-house-spain-p1",
        "/en/finca-spain-p1",
    ]

    def __init__(self, session: StaticSession):
        self.sess = session
        self.source = "kyero.com"

    def scrape(self, max_pages=8) -> list[dict]:
        results = []
        for path in self.SEARCH_URLS:
            url = self.BASE + path
            page_num = 1
            while page_num <= max_pages:
                log.info(f"[Kyero] page {page_num}: {url}")
                soup = self.sess.get(url)
                if not soup:
                    break
                listings = self._parse_list(soup)
                if not listings:
                    log.info("[Kyero] No listings found on page — stopping.")
                    break
                for listing_url in listings:
                    rand_delay()
                    detail = self._parse_detail(listing_url)
                    if detail:
                        results.append(detail)
                # Next page
                next_link = soup.select_one("a[rel='next'], .pagination__next a, a.next")
                if next_link and next_link.get("href"):
                    href = next_link["href"]
                    url = href if href.startswith("http") else self.BASE + href
                    page_num += 1
                    rand_delay()
                else:
                    break
        log.info(f"[Kyero] Total collected: {len(results)}")
        return results

    def _parse_list(self, soup: BeautifulSoup) -> list[str]:
        urls = []
        for a in soup.select("article.property a[href*='/en/property/'], a.property-card__link"):
            href = a.get("href", "")
            if href:
                full = href if href.startswith("http") else self.BASE + href
                if full not in urls:
                    urls.append(full)
        # fallback
        if not urls:
            for a in soup.select("a[href*='/property/']"):
                href = a.get("href", "")
                if href and "kyero" not in href.split("/property/")[0].replace("https://www.kyero.com", ""):
                    full = href if href.startswith("http") else self.BASE + href
                    if full not in urls:
                        urls.append(full)
        return urls

    def _parse_detail(self, url: str) -> Optional[dict]:
        soup = self.sess.get(url)
        if not soup:
            return None
        try:
            title = (soup.select_one("h1") or soup.select_one(".property-title")).get_text(strip=True)
        except Exception:
            title = ""

        price_eur = None
        price_el = soup.select_one("[class*='price']")
        if price_el:
            price_eur = safe_int(price_el.get_text())

        # Extract specs
        bedrooms = bathrooms = None
        land_m2 = build_m2 = None
        for el in soup.select("[class*='spec'], [class*='feature'], li, .detail"):
            txt = el.get_text(" ", strip=True).lower()
            if "bed" in txt or "dormitor" in txt or "habitaci" in txt:
                bedrooms = safe_int(txt)
            elif "bath" in txt or "baño" in txt:
                bathrooms = safe_int(txt)
            elif "m²" in txt or "m2" in txt:
                num = extract_number(txt)
                if num:
                    if "plot" in txt or "land" in txt or "parcela" in txt or "terreno" in txt:
                        land_m2 = int(num)
                    elif "build" in txt or "construida" in txt:
                        build_m2 = int(num)

        desc_el = soup.select_one(".description, [class*='description'], [itemprop='description']")
        description = desc_el.get_text("\n", strip=True) if desc_el else ""

        # Location
        region = province = municipality = ""
        loc_el = soup.select_one("[class*='location'], address, [itemprop='addressRegion']")
        if loc_el:
            loc_text = loc_el.get_text(", ", strip=True)
            parts = [p.strip() for p in loc_text.split(",")]
            if len(parts) >= 1:
                municipality = parts[0]
            if len(parts) >= 2:
                province = parts[1]
            region = self._guess_region(province or municipality)

        images = [img["src"] for img in soup.select("img[src*='kyero']") if img.get("src")][:10]

        land_ha = round(land_m2 / 10000, 2) if land_m2 else None

        prop = {
            "listing_id": make_id(url),
            "title": title,
            "url": url,
            "source_site": self.source,
            "region": region,
            "province": province,
            "municipality": municipality,
            "price_eur": price_eur,
            "price_per_sqm_eur": round(price_eur / build_m2) if price_eur and build_m2 else None,
            "land_area_hectares": land_ha,
            "land_area_m2": land_m2,
            "build_area_m2": build_m2,
            "bedrooms": bedrooms,
            "bathrooms": bathrooms,
            "year_built": None,
            "property_type": self._guess_type(title + " " + description),
            "nearest_airport": self._guess_airport(region, province),
            "nearest_city": None,
            "water_source": self._guess_water(description),
            "pool": "pool" in description.lower() or "piscina" in description.lower(),
            "outbuildings": self._guess_outbuildings(description),
            "agricultural_features": self._guess_ag_features(description),
            "event_venue_potential": self._venue_notes(description),
            "airbnb_potential": self._airbnb_notes(description),
            "condition": self._guess_condition(description),
            "energy_rating": self._guess_energy(soup),
            "listing_date": datetime.now().strftime("%Y-%m-%d"),
            "description_raw": description[:3000],
            "notes": "",
            "images": images,
            "login_required": False,
        }
        prop["total_score"] = score_property(prop)
        return prop

    def _guess_region(self, text: str) -> str:
        text = text.lower()
        mapping = {
            "Andalusia": ["andaluc", "málaga", "malaga", "sevilla", "granada", "almería", "almeria",
                          "córdoba", "cordoba", "jaén", "jaen", "huelva", "cádiz", "cadiz"],
            "Valencia": ["valenci", "castellón", "castellon", "alicante"],
            "Murcia": ["murcia"],
            "Catalonia": ["cataluny", "cataluña", "barcelona", "girona", "lleida", "tarragona"],
            "Castilla-La Mancha": ["castilla-la mancha", "toledo", "cuenca", "albacete", "ciudad real", "guadalajara"],
            "Extremadura": ["extremadura", "cáceres", "caceres", "badajoz", "mérida", "merida"],
        }
        for region, keywords in mapping.items():
            if any(kw in text for kw in keywords):
                return region
        return "Unknown"

    def _guess_type(self, text: str) -> str:
        text = text.lower()
        for t in ["cortijo", "finca", "masía", "masia", "hacienda", "casa rural", "villa", "granja", "rancho"]:
            if t in text:
                return t
        return "rural property"

    def _guess_airport(self, region: str, province: str) -> str:
        airports = AIRPORTS.get(region, [])
        if airports:
            name, code = airports[0]
            return f"{name} ({code}) — est. distance varies"
        return "unknown"

    def _guess_water(self, text: str) -> str:
        text = text.lower()
        if "pozo" in text and ("mains" in text or "red" in text or "agua corriente" in text):
            return "both"
        if "pozo" in text or "well" in text:
            return "well"
        if "mains" in text or "red" in text or "municipal" in text:
            return "mains"
        return "unknown"

    def _guess_outbuildings(self, text: str) -> str:
        text = text.lower()
        found = []
        for kw, label in [("barn", "barn"), ("stable", "stables"), ("establos", "stables"),
                           ("bodega", "wine cellar"), ("garage", "garage"), ("warehouse", "warehouse"),
                           ("cochera", "garage"), ("nave", "warehouse"), ("almacén", "storage")]:
            if kw in text:
                found.append(label)
        return ", ".join(set(found)) if found else ""

    def _guess_ag_features(self, text: str) -> list:
        text = text.lower()
        features = []
        checks = [
            ("oliv", "olive grove"), ("viñ", "vineyard"), ("vino", "vineyard"),
            ("naranj", "citrus"), ("limón", "citrus"), ("riego", "irrigated land"),
            ("regad", "irrigated land"), ("almend", "almond grove"),
            ("cerezo", "cherry orchard"), ("huerta", "vegetable garden"),
            ("huertas", "vegetable garden"), ("ganad", "livestock"),
            ("oveja", "sheep"), ("cabra", "goat"), ("vaca", "cattle"),
            ("cereal", "cereal crops"), ("secano", "dryland farming"),
            ("pasto", "pasture"), ("dehesa", "dehesa/cork oak"),
        ]
        for kw, label in checks:
            if kw in text and label not in features:
                features.append(label)
        return features

    def _venue_notes(self, text: str) -> str:
        keywords = ["view", "vista", "panoram", "mountain", "event", "wedding", "boda",
                    "chapel", "pool", "piscina", "terrace", "barn", "cortijo"]
        hits = [kw for kw in keywords if kw in text.lower()]
        if hits:
            return f"Potential venue features: {', '.join(hits[:5])}"
        return "No obvious venue indicators found"

    def _airbnb_notes(self, text: str) -> str:
        keywords = ["tourist license", "licencia turística", "rental", "alquiler",
                    "holiday", "vacacion", "booking", "airbnb"]
        hits = [kw for kw in keywords if kw in text.lower()]
        if hits:
            return f"Rental indicators: {', '.join(hits[:5])}"
        return "No explicit rental history mentioned"

    def _guess_condition(self, text: str) -> str:
        text = text.lower()
        if "ruina" in text or "ruins" in text:
            return "ruins"
        if "renovar" in text or "reformar" in text or "needs renovation" in text or "to renovate" in text:
            return "needs renovation"
        if "reformado" in text or "renovated" in text or "reformed" in text:
            return "good"
        if "excellent" in text or "excelente" in text or "perfect" in text:
            return "excellent"
        if "habitable" in text:
            return "habitable"
        return "unknown"

    def _guess_energy(self, soup: BeautifulSoup) -> str:
        for el in soup.select("[class*='energy'], [class*='cert']"):
            txt = el.get_text(strip=True).upper()
            m = re.search(r"\b([A-G])\b", txt)
            if m:
                return m.group(1)
        return "unknown"


# ---------------------------------------------------------------------------
# Green Acres scraper (static HTML)
# ---------------------------------------------------------------------------

class GreenAcresScraper(KyeroScraper):
    BASE = "https://www.green-acres.es"
    SEARCH_URLS = [
        "/en/properties/spain/farmhouse/?price_min=50000&price_max=2000000",
        "/en/properties/spain/finca/?price_min=50000&price_max=2000000",
        "/en/properties/spain/country-house/?price_min=50000&price_max=2000000",
    ]

    def __init__(self, session: StaticSession):
        self.sess = session
        self.source = "green-acres.es"

    def _parse_list(self, soup: BeautifulSoup) -> list[str]:
        urls = []
        for a in soup.select("a[href*='/en/property/'], a[href*='/immobilier/']"):
            href = a.get("href", "")
            if href:
                full = href if href.startswith("http") else self.BASE + href
                if full not in urls:
                    urls.append(full)
        return urls


# ---------------------------------------------------------------------------
# Rurales.com scraper
# ---------------------------------------------------------------------------

class RuralesScraper(KyeroScraper):
    BASE = "https://www.rurales.com"
    SEARCH_URLS = [
        "/en/properties/?type=farm&country=spain&min_price=50000&max_price=2000000",
        "/propiedades/?tipo=finca&pais=espana",
    ]

    def __init__(self, session: StaticSession):
        self.sess = session
        self.source = "rurales.com"

    def _parse_list(self, soup: BeautifulSoup) -> list[str]:
        urls = []
        for a in soup.select("a[href*='/propiedad/'], a[href*='/property/'], .listing-title a"):
            href = a.get("href", "")
            if href:
                full = href if href.startswith("http") else self.BASE + href
                if full not in urls:
                    urls.append(full)
        return urls


# ---------------------------------------------------------------------------
# Rightmove Overseas scraper
# ---------------------------------------------------------------------------

class RightmoveScraper(KyeroScraper):
    BASE = "https://www.rightmove.co.uk"
    SEARCH_URLS = [
        "/overseas-property/in-Spain/farmhouse.html",
        "/overseas-property/in-Spain/finca.html",
        "/overseas-property/in-Spain/country-house.html",
    ]

    def __init__(self, session: StaticSession):
        self.sess = session
        self.source = "rightmove.co.uk"

    def _parse_list(self, soup: BeautifulSoup) -> list[str]:
        urls = []
        for a in soup.select("a[href*='/overseas-property/property-']"):
            href = a.get("href", "")
            if href:
                full = href if href.startswith("http") else self.BASE + href
                if full not in urls:
                    urls.append(full)
        return urls


# ---------------------------------------------------------------------------
# Playwright-based scraper base for JS-heavy sites
# ---------------------------------------------------------------------------

class PlaywrightScraper:
    """Base class for JS-rendered sites."""

    def __init__(self, source: str):
        self.source = source

    async def _get_page_html(self, page: Page, url: str, wait: str = "networkidle") -> Optional[BeautifulSoup]:
        try:
            await page.goto(url, wait_until=wait, timeout=45000)
            await page.wait_for_timeout(random.randint(2500, 5000))
            # Try to dismiss cookie banners
            for sel in ["#acceptAllButton", "#onetrust-accept-btn-handler",
                        "button[id*='accept']", "button:has-text('Accept all')",
                        "button:has-text('Aceptar')", "button:has-text('Accept')"]:
                try:
                    btn = page.locator(sel).first
                    if await btn.is_visible(timeout=800):
                        await btn.click()
                        await page.wait_for_timeout(1000)
                        break
                except Exception:
                    pass
            html = await page.content()
            return BeautifulSoup(html, "html.parser")
        except Exception as e:
            log.error(f"[{self.source}] Playwright error loading {url}: {e}")
            return None

    # Re-use helpers from KyeroScraper
    _guess_region = KyeroScraper._guess_region
    _guess_type = KyeroScraper._guess_type
    _guess_airport = KyeroScraper._guess_airport
    _guess_water = KyeroScraper._guess_water
    _guess_outbuildings = KyeroScraper._guess_outbuildings
    _guess_ag_features = KyeroScraper._guess_ag_features
    _venue_notes = KyeroScraper._venue_notes
    _airbnb_notes = KyeroScraper._airbnb_notes
    _guess_condition = KyeroScraper._guess_condition
    _guess_energy = KyeroScraper._guess_energy


# ---------------------------------------------------------------------------
# Kyero Playwright scraper
# Confirmed: listing links are /en/property/XXXXXXX-slug on /en/spain page
# ---------------------------------------------------------------------------

class KyeroPlaywrightScraper(PlaywrightScraper):
    BASE = "https://www.kyero.com"
    SEARCH_URLS = [
        "/en/spain?type%5B%5D=country-house&type%5B%5D=farmhouse&location=andalucia&min_price=50000&max_price=2000000",
        "/en/spain?type%5B%5D=country-house&type%5B%5D=farmhouse&location=valenciana&min_price=50000&max_price=2000000",
        "/en/spain?type%5B%5D=country-house&type%5B%5D=farmhouse&location=murcia&min_price=50000&max_price=2000000",
        "/en/spain?type%5B%5D=country-house&type%5B%5D=farmhouse&location=cataluna&min_price=50000&max_price=2000000",
        "/en/spain?type%5B%5D=country-house&type%5B%5D=farmhouse&location=castilla&min_price=50000&max_price=2000000",
        "/en/spain?type%5B%5D=country-house&type%5B%5D=farmhouse&location=extremadura&min_price=50000&max_price=2000000",
    ]

    def __init__(self):
        super().__init__("kyero.com")

    async def scrape(self, browser: Browser, max_pages=6) -> list[dict]:
        results = []
        seen_urls: set[str] = set()
        context = await browser.new_context(user_agent=random_ua(), locale="en-GB", viewport={"width": 1280, "height": 900})
        page = await context.new_page()

        for path in self.SEARCH_URLS:
            url = self.BASE + path
            for pg in range(1, max_pages + 1):
                paged_url = url if pg == 1 else url + f"&page={pg}"
                log.info(f"[Kyero] page {pg}: {paged_url}")
                soup = await self._get_page_html(page, paged_url)
                if not soup:
                    break
                if "captcha" in (soup.get_text() or "").lower():
                    log.warning(f"[Kyero] CAPTCHA — skipping")
                    break
                listing_urls = [u for u in self._parse_list(soup) if u not in seen_urls]
                if not listing_urls:
                    log.info("[Kyero] No new listings found — stopping.")
                    break
                seen_urls.update(listing_urls)
                log.info(f"[Kyero] Found {len(listing_urls)} listings on page {pg}")
                for lurl in listing_urls:
                    await page.wait_for_timeout(random.randint(2500, 5000))
                    detail = await self._parse_detail(page, lurl)
                    if detail:
                        results.append(detail)
                await page.wait_for_timeout(random.randint(3000, 6000))

        await context.close()
        log.info(f"[Kyero] Total collected: {len(results)}")
        return results

    def _parse_list(self, soup: BeautifulSoup) -> list[str]:
        urls = []
        for a in soup.find_all("a", href=True):
            href = a["href"]
            if "/en/property/" in href or "/property/" in href:
                full = href if href.startswith("http") else self.BASE + href
                if full not in urls:
                    urls.append(full)
        return urls

    async def _parse_detail(self, page: Page, url: str) -> Optional[dict]:
        soup = await self._get_page_html(page, url)
        if not soup:
            return None

        title_el = soup.select_one("h1")
        title = title_el.get_text(strip=True) if title_el else ""

        # Use full page text for robust regex-based extraction (Kyero uses Tailwind, no semantic class names)
        full_text = soup.get_text(" ", strip=True)

        # Price: first "€ 795,000" style match
        price_eur = None
        pm = re.search(r'€\s*([\d][0-9,\.]*)', full_text)
        if pm:
            n = safe_int(pm.group(1))
            if n and n > 10000:
                price_eur = n

        # Specs appear as "5Bedrooms", "466m²Build size", "5747m²Plot size"
        bedrooms = bathrooms = land_m2 = build_m2 = None
        bm = re.search(r'(\d+)\s*Bedrooms', full_text)
        if bm:
            bedrooms = int(bm.group(1))
        batm = re.search(r'(\d+)\s*Bathrooms', full_text)
        if batm:
            bathrooms = int(batm.group(1))
        plotm = re.search(r'([\d,]+)\s*m[²2]\s*Plot\s*size', full_text)
        if plotm:
            land_m2 = safe_int(plotm.group(1))
        buildm = re.search(r'([\d,]+)\s*m[²2]\s*Build\s*size', full_text)
        if buildm:
            build_m2 = safe_int(buildm.group(1))

        # Description: use full page text for feature detection (pool, water, outbuildings etc.)
        description = full_text

        # Location: look for "Town, Area, Province, Region, Spain" pattern in a <p> tag
        municipality = province = ""
        for p_el in soup.find_all("p"):
            loc = p_el.get_text(strip=True)
            if ", Spain" in loc and len(loc) < 200:
                parts = [x.strip() for x in loc.replace(", Spain", "").split(",")]
                if len(parts) >= 2:
                    municipality = parts[0]
                    province = parts[-1]
                    break
        # Fallback to breadcrumb-style links
        if not municipality:
            for sel in [".breadcrumbs a", "nav[aria-label*='read'] a", "address"]:
                parts = [el.get_text(strip=True) for el in soup.select(sel)]
                parts = [p for p in parts if p and p not in ("Home", "Spain", "Properties")]
                if len(parts) >= 2:
                    municipality, province = parts[0], parts[-2]
                    break
                elif len(parts) == 1:
                    municipality = parts[0]
                    break

        region = self._guess_region(province + " " + municipality)
        images = []
        for img in soup.select("img[src], img[data-src]"):
            src = img.get("src") or img.get("data-src") or ""
            if src and src not in images and not src.endswith(".svg"):
                images.append(src)
        images = images[:10]
        land_ha = round(land_m2 / 10000, 2) if land_m2 else None

        prop = {
            "listing_id": make_id(url),
            "title": title,
            "url": url,
            "source_site": self.source,
            "region": region,
            "province": province,
            "municipality": municipality,
            "price_eur": price_eur,
            "price_per_sqm_eur": round(price_eur / build_m2) if price_eur and build_m2 else None,
            "land_area_hectares": land_ha,
            "land_area_m2": land_m2,
            "build_area_m2": build_m2,
            "bedrooms": bedrooms,
            "bathrooms": bathrooms,
            "year_built": None,
            "property_type": self._guess_type(title + " " + description),
            "nearest_airport": self._guess_airport(region, province),
            "nearest_city": None,
            "water_source": self._guess_water(description),
            "pool": "pool" in description.lower() or "piscina" in description.lower(),
            "outbuildings": self._guess_outbuildings(description),
            "agricultural_features": self._guess_ag_features(description),
            "event_venue_potential": self._venue_notes(description),
            "airbnb_potential": self._airbnb_notes(description),
            "condition": self._guess_condition(description),
            "energy_rating": self._guess_energy(soup),
            "listing_date": datetime.now().strftime("%Y-%m-%d"),
            "description_raw": description[:3000],
            "notes": "",
            "images": images,
            "login_required": False,
        }
        prop["total_score"] = score_property(prop)
        return prop


# ---------------------------------------------------------------------------
# Green Acres Playwright scraper
# URLs are base64-encoded in data-o attr of .announce-card; extract card data
# directly without visiting individual listing pages.
# ---------------------------------------------------------------------------

class GreenAcresPlaywrightScraper(PlaywrightScraper):
    BASE = "https://www.green-acres.es"
    SEARCH_URLS = [
        "/country-house/andalusia",
        "/country-house/valencia",
        "/country-house/murcia",
        "/country-house/catalonia",
        "/country-house/castile-la-mancha",
        "/country-house/extremadura",
    ]

    def __init__(self):
        super().__init__("green-acres.es")

    async def scrape(self, browser: Browser, max_pages=5) -> list[dict]:
        results = []
        context = await browser.new_context(user_agent=random_ua(), locale="en-GB", viewport={"width": 1366, "height": 900})
        page = await context.new_page()

        for path in self.SEARCH_URLS:
            url = self.BASE + path
            for pg in range(1, max_pages + 1):
                paged_url = url if pg == 1 else url + f"?page={pg}"
                log.info(f"[GreenAcres] {path} / page {pg}")

                try:
                    await page.goto(paged_url, wait_until="domcontentloaded", timeout=45000)
                    await page.wait_for_timeout(2000)

                    # Accept cookie consent (tarteaucitron)
                    for sel in ["#tarteaucitronAllAllowed",
                                "button:has-text('OK, accept everything')",
                                "button:has-text('Accept all')",
                                "button:has-text('OK')"]:
                        try:
                            btn = page.locator(sel).first
                            if await btn.is_visible(timeout=1500):
                                await btn.click()
                                await page.wait_for_timeout(1500)
                                break
                        except Exception:
                            pass

                    # Scroll to trigger AJAX listing load
                    for y in [800, 1600, 2400, 3200]:
                        await page.evaluate(f"window.scrollTo(0, {y})")
                        await page.wait_for_timeout(1000)
                    await page.wait_for_timeout(3000)

                    html = await page.content()
                    soup = BeautifulSoup(html, "html.parser")

                except Exception as e:
                    log.error(f"[GreenAcres] Error loading {paged_url}: {e}")
                    break

                cards = self._parse_cards(soup)
                if not cards:
                    log.info(f"[GreenAcres] No cards on page {pg} — stopping.")
                    break
                log.info(f"[GreenAcres] Found {len(cards)} cards on page {pg}")
                results.extend(cards)
                await page.wait_for_timeout(random.randint(3000, 6000))

        await context.close()
        log.info(f"[GreenAcres] Total collected: {len(results)}")
        return results

    def _parse_cards(self, soup: BeautifulSoup) -> list[dict]:
        """Extract listing data directly from announce-card elements."""
        import base64
        results = []

        for card in soup.select(".announce-card"):
            try:
                data_o = card.get("data-o", "")
                if not data_o:
                    continue
                # Pad base64 and decode URL
                padded = data_o + "=" * (4 - len(data_o) % 4)
                url = base64.b64decode(padded).decode("utf-8", errors="replace")
                if not url.startswith("http"):
                    url = self.BASE + url

                title = card.get("title", "")
                price_eur = None
                price_el = card.select_one(".info-price-container")
                if price_el:
                    price_eur = safe_int(price_el.get_text())

                loc_el = card.select_one(".announce-localisation")
                loc_text = loc_el.get_text(strip=True) if loc_el else ""
                municipality = loc_text.split("(")[0].strip()
                prov_m = re.search(r'\(([^)]+)\)', loc_text)
                province = prov_m.group(1) if prov_m else ""
                region = self._guess_region(province + " " + municipality)

                bedrooms = build_m2 = land_m2 = None
                for tag in card.select(".info-tag"):
                    txt = tag.get_text(strip=True).lower()
                    if "bedroom" in txt or "room" in txt:
                        m = re.search(r"(\d+)", txt)
                        if m and bedrooms is None:
                            bedrooms = int(m.group(1))
                    elif "m²" in txt or "m2" in txt:
                        num = extract_number(txt)
                        if num:
                            if "land" in txt or "plot" in txt or "terrain" in txt:
                                land_m2 = int(num)
                            elif build_m2 is None:
                                build_m2 = int(num)

                land_ha = round(land_m2 / 10000, 2) if land_m2 else None
                description = card.get_text(" ", strip=True)

                prop = {
                    "listing_id": make_id(url),
                    "title": title,
                    "url": url,
                    "source_site": self.source,
                    "region": region,
                    "province": province,
                    "municipality": municipality,
                    "price_eur": price_eur,
                    "price_per_sqm_eur": round(price_eur / build_m2) if price_eur and build_m2 else None,
                    "land_area_hectares": land_ha,
                    "land_area_m2": land_m2,
                    "build_area_m2": build_m2,
                    "bedrooms": bedrooms,
                    "bathrooms": None,
                    "year_built": None,
                    "property_type": self._guess_type(title),
                    "nearest_airport": self._guess_airport(region, province),
                    "nearest_city": None,
                    "water_source": self._guess_water(description),
                    "pool": False,
                    "outbuildings": "",
                    "agricultural_features": self._guess_ag_features(description),
                    "event_venue_potential": self._venue_notes(description),
                    "airbnb_potential": self._airbnb_notes(description),
                    "condition": self._guess_condition(description),
                    "energy_rating": "unknown",
                    "listing_date": datetime.now().strftime("%Y-%m-%d"),
                    "description_raw": description[:1000],
                    "notes": "Card-level data; visit URL for full details",
                    "images": [],
                    "login_required": False,
                }
                prop["total_score"] = score_property(prop)
                results.append(prop)
            except Exception as e:
                log.warning(f"[GreenAcres] Error parsing card: {e}")

        return results


# ---------------------------------------------------------------------------
# Idealista scraper (Playwright)
# ---------------------------------------------------------------------------

class IdealistaScraper(PlaywrightScraper):
    BASE = "https://www.idealista.com"

    SEARCH_CONFIGS = [
        # (region_slug, region_label)
        ("andalucia", "Andalusia"),
        ("comunitat-valenciana", "Valencia"),
        ("region-de-murcia", "Murcia"),
        ("cataluna", "Catalonia"),
        ("castilla-la-mancha", "Castilla-La Mancha"),
        ("extremadura", "Extremadura"),
    ]

    def __init__(self):
        super().__init__("idealista.com")

    async def scrape(self, browser: Browser, max_pages=5) -> list[dict]:
        results = []
        context = await browser.new_context(
            user_agent=random_ua(),
            locale="en-GB",
            viewport={"width": 1280, "height": 900},
        )
        page = await context.new_page()

        search_terms = ["finca", "cortijo", "casa-rural"]

        for region_slug, region_label in self.SEARCH_CONFIGS:
            for term in search_terms:
                for pg in range(1, max_pages + 1):
                    url = f"{self.BASE}/en/sale-homes/{region_slug}/{term}/with-more-500m-built-sqm/"
                    if pg > 1:
                        url = f"{self.BASE}/en/sale-homes/{region_slug}/{term}/with-more-500m-built-sqm/pagina-{pg}.htm"

                    log.info(f"[Idealista] {region_label} / {term} / page {pg}")
                    soup = await self._get_page_html(page, url)
                    if not soup:
                        break

                    # Check for CAPTCHA
                    if "captcha" in soup.get_text().lower() or "robot" in soup.get_text().lower():
                        log.warning(f"[Idealista] CAPTCHA detected on {url} — skipping")
                        break

                    listing_urls = self._parse_list(soup)
                    if not listing_urls:
                        log.info(f"[Idealista] No listings on page {pg} — stopping.")
                        break

                    for lurl in listing_urls:
                        await page.wait_for_timeout(random.randint(2500, 5000))
                        detail = await self._parse_detail(page, lurl, region_label)
                        if detail:
                            results.append(detail)

                    await page.wait_for_timeout(random.randint(3000, 6000))

        await context.close()
        log.info(f"[Idealista] Total collected: {len(results)}")
        return results

    def _parse_list(self, soup: BeautifulSoup) -> list[str]:
        urls = []
        for a in soup.select("a.item-link, a[href*='/inmueble/']"):
            href = a.get("href", "")
            if href:
                full = href if href.startswith("http") else self.BASE + href
                if full not in urls:
                    urls.append(full)
        return urls

    async def _parse_detail(self, page: Page, url: str, region: str) -> Optional[dict]:
        soup = await self._get_page_html(page, url)
        if not soup:
            return None

        if "captcha" in (soup.get_text() or "").lower():
            log.warning(f"[Idealista] CAPTCHA on detail page {url}")
            return None

        title = ""
        h1 = soup.select_one("h1")
        if h1:
            title = h1.get_text(strip=True)

        price_eur = None
        price_el = soup.select_one(".info-data-price, [class*='price']")
        if price_el:
            price_eur = safe_int(price_el.get_text())

        # Extract detail table
        bedrooms = bathrooms = land_m2 = build_m2 = None
        for li in soup.select(".details-property_features li, .feature-list li, li"):
            txt = li.get_text(" ", strip=True).lower()
            if re.search(r"\d+\s*(bed|dormitor|habitaci)", txt):
                bedrooms = safe_int(re.search(r"\d+", txt).group())
            elif re.search(r"\d+\s*(bath|baño|aseo)", txt):
                bathrooms = safe_int(re.search(r"\d+", txt).group())
            elif re.search(r"\d[\d,\.]*\s*m[²2]", txt):
                num = extract_number(txt)
                if num:
                    if any(k in txt for k in ["plot", "land", "parcela", "terreno", "suelo"]):
                        land_m2 = int(num)
                    elif any(k in txt for k in ["built", "construid", "construida"]):
                        build_m2 = int(num)

        desc_el = soup.select_one("#adv-description, .comment .advert-description, [class*='description']")
        description = desc_el.get_text("\n", strip=True) if desc_el else ""

        # Location breadcrumb
        province = municipality = ""
        breadcrumb = soup.select(".breadcrumb a, nav[aria-label='Breadcrumb'] a")
        if breadcrumb:
            texts = [a.get_text(strip=True) for a in breadcrumb]
            if len(texts) >= 3:
                province = texts[-2]
                municipality = texts[-1]
            elif len(texts) >= 2:
                municipality = texts[-1]

        region_guess = self._guess_region(province + " " + municipality + " " + region)
        if region_guess == "Unknown":
            region_guess = region

        images = []
        for img in soup.select("img[src*='idealista'], .main-image img, .gallery img"):
            src = img.get("src") or img.get("data-src")
            if src and src not in images:
                images.append(src)
        images = images[:10]

        land_ha = round(land_m2 / 10000, 2) if land_m2 else None

        prop = {
            "listing_id": make_id(url),
            "title": title,
            "url": url,
            "source_site": self.source,
            "region": region_guess,
            "province": province,
            "municipality": municipality,
            "price_eur": price_eur,
            "price_per_sqm_eur": round(price_eur / build_m2) if price_eur and build_m2 else None,
            "land_area_hectares": land_ha,
            "land_area_m2": land_m2,
            "build_area_m2": build_m2,
            "bedrooms": bedrooms,
            "bathrooms": bathrooms,
            "year_built": None,
            "property_type": self._guess_type(title + " " + description),
            "nearest_airport": self._guess_airport(region_guess, province),
            "nearest_city": None,
            "water_source": self._guess_water(description),
            "pool": "pool" in description.lower() or "piscina" in description.lower(),
            "outbuildings": self._guess_outbuildings(description),
            "agricultural_features": self._guess_ag_features(description),
            "event_venue_potential": self._venue_notes(description),
            "airbnb_potential": self._airbnb_notes(description),
            "condition": self._guess_condition(description),
            "energy_rating": self._guess_energy(soup),
            "listing_date": datetime.now().strftime("%Y-%m-%d"),
            "description_raw": description[:3000],
            "notes": "",
            "images": images,
            "login_required": False,
        }
        prop["total_score"] = score_property(prop)
        return prop


# ---------------------------------------------------------------------------
# Fotocasa scraper — direct API (no Playwright needed)
# Uses the public search API to get rural properties (propertySubtypeIds=9).
# Location IDs discovered from: web.gw.fotocasa.es/v2/propertysearch/urllocationsegments
# ---------------------------------------------------------------------------

class FotocasaScraper(PlaywrightScraper):
    """Fotocasa rural-property scraper using their public JSON API."""
    BASE = "https://www.fotocasa.es"
    API_URL = "https://web.gw.fotocasa.es/v2/propertysearch/search"

    # (url_slug, region_label, combinedLocationIds)
    REGIONS = [
        ("andalucia",            "Andalusia",          "724,1,0,0,0,0,0,0,0"),
        ("comunitat-valenciana", "Valencia",           "724,19,0,0,0,0,0,0,0"),
        ("region-de-murcia",     "Murcia",             "724,16,0,0,0,0,0,0,0"),
        ("cataluna",             "Catalonia",          "724,9,0,0,0,0,0,0,0"),
        ("castilla-la-mancha",   "Castilla-La Mancha", "724,8,0,0,0,0,0,0,0"),
        ("extremadura",          "Extremadura",        "724,11,0,0,0,0,0,0,0"),
    ]

    def __init__(self):
        super().__init__("fotocasa.es")
        self._session = requests.Session()
        self._session.headers.update({
            "User-Agent": random_ua(),
            "Accept": "application/json",
            "Accept-Language": "en-GB,en;q=0.9",
            "Referer": "https://www.fotocasa.es/en/buy/rural-properties/andalucia/all-zones/l",
            "Origin": "https://www.fotocasa.es",
        })

    async def scrape(self, browser: Browser, max_pages: int = 5) -> list[dict]:
        """Scrape using API (browser is not used)."""
        results = []
        seen_ids: set = set()

        for slug, region_label, loc_ids in self.REGIONS:
            for pg in range(1, max_pages + 1):
                log.info(f"[Fotocasa] {region_label} / page {pg}")
                try:
                    r = self._session.get(self.API_URL, params={
                        "combinedLocationIds": loc_ids,
                        "propertyTypeId":    "2",   # residential/casa
                        "propertySubtypeIds": "9",  # rural property subtype
                        "transactionTypeId": "1",   # buy
                        "culture":     "en-GB",
                        "pageNumber":  str(pg),
                        "maxItems":    "30",
                        "siteId":      "1",
                        "sortType":    "scoring",
                    }, timeout=20)
                except Exception as e:
                    log.error(f"[Fotocasa] Request error {region_label} page {pg}: {e}")
                    break

                if r.status_code != 200:
                    log.warning(f"[Fotocasa] HTTP {r.status_code} — {region_label} page {pg}")
                    break

                try:
                    data = r.json()
                except Exception:
                    log.error(f"[Fotocasa] Bad JSON — {region_label} page {pg}")
                    break

                estates = data.get("realEstates", [])
                if not estates:
                    log.info(f"[Fotocasa] No results on page {pg} — stopping")
                    break

                for e in estates:
                    prop_id = e.get("id")
                    if prop_id in seen_ids:
                        continue
                    seen_ids.add(prop_id)
                    prop = self._parse_estate(e, region_label)
                    if prop:
                        results.append(prop)

                rand_delay(1.0, 2.5)

        log.info(f"[Fotocasa] Total collected: {len(results)}")
        return results

    def _parse_estate(self, e: dict, region_label: str) -> Optional[dict]:
        prop_id = e.get("id", 0)
        detail_path = (e.get("detail") or {}).get("en", "")
        url = self.BASE + detail_path if detail_path else ""

        # Price
        price_eur = None
        txns = e.get("transactions") or []
        if txns and txns[0].get("value"):
            v = txns[0]["value"][0]
            if isinstance(v, (int, float)) and 10000 < v < 50_000_000:
                price_eur = int(v)

        # Location
        addr   = e.get("address") or {}
        loc    = addr.get("location") or {}
        municipality = (addr.get("ubication") or "").strip().lstrip()
        province     = (loc.get("level2") or "").strip()
        region = self._guess_region(province + " " + municipality + " " + region_label)
        if region == "Unknown":
            region = region_label

        # Features dict
        feats = {}
        for f in (e.get("features") or []):
            v = f.get("value")
            feats[f["key"]] = v[0] if v else None
        bedrooms  = feats.get("rooms")
        bathrooms = feats.get("bathrooms")
        raw_surface = feats.get("surface")
        has_pool  = bool(feats.get("swimming_pool"))
        cond_code = feats.get("conservationState")
        condition = {1: "new", 2: "excellent", 3: "good", 4: "needs renovation", 5: "ruins"}.get(cond_code, "unknown")

        # Description (Spanish — used for agricultural feature detection)
        description = e.get("description") or ""
        if isinstance(description, dict):
            description = description.get("es") or description.get("en") or ""

        # Extract land area from description text.
        # Fotocasa's 'surface' API field is build area for normal homes, but for some
        # rural listings it returns total area. We trust description-extracted land area
        # over the API surface field (which we cap at 5000 m² for build area).
        land_m2 = None

        # Hectares: "5 ha", "5ha", "5 hectáreas", "5 hectares"
        hm = re.search(r'([\d][0-9,.]*)\s*h(?:a\b|ect[aá]re?as?)', description, re.IGNORECASE)
        if hm:
            try:
                land_m2 = int(float(hm.group(1).replace(".", "").replace(",", ".")) * 10000)
            except Exception:
                pass

        if not land_m2:
            # "10.000 m² de finca/parcela/terreno/tierra"
            pm = re.search(
                r'([\d][0-9.]*)\s*m[²2]\s*(?:de\s*)?(finca|parcela|terreno|tierra)',
                description, re.IGNORECASE)
            if pm:
                land_m2 = safe_int(pm.group(1))

        if not land_m2:
            # Large standalone m² values (≥5000 m² = 0.5 ha) in rural context
            pm2 = re.search(r'(\d[\d.]*[05]\d{3})\s*m[²2]', description)
            if pm2:
                n = safe_int(pm2.group(1))
                if n and n >= 5000:
                    land_m2 = n

        land_ha = round(land_m2 / 10000, 2) if land_m2 else None

        # build_m2: use API surface only if plausible (≤5000 m²); otherwise null
        build_m2 = raw_surface if (raw_surface and raw_surface <= 5000) else None

        images = [m["url"] for m in (e.get("multimedias") or []) if m.get("url")][:10]

        prop = {
            "listing_id":          str(prop_id),
            "title":               municipality or "Rural property",
            "url":                 url,
            "source_site":         self.source,
            "region":              region,
            "province":            province,
            "municipality":        municipality,
            "price_eur":           price_eur,
            "price_per_sqm_eur":   round(price_eur / build_m2) if price_eur and build_m2 else None,
            "land_area_hectares":  land_ha,
            "land_area_m2":        land_m2,
            "build_area_m2":       build_m2,
            "bedrooms":            bedrooms,
            "bathrooms":           bathrooms,
            "year_built":          None,
            "property_type":       "Rural Property",
            "nearest_airport":     self._guess_airport(region, province),
            "nearest_city":        None,
            "water_source":        self._guess_water(description),
            "pool":                has_pool,
            "outbuildings":        self._guess_outbuildings(description),
            "agricultural_features": self._guess_ag_features(description),
            "event_venue_potential": self._venue_notes(description),
            "airbnb_potential":    self._airbnb_notes(description),
            "condition":           condition,
            "energy_rating":       "unknown",
            "listing_date":        datetime.now().strftime("%Y-%m-%d"),
            "description_raw":     description[:3000],
            "notes":               "API search data; rural property subtype",
            "images":              images,
            "login_required":      False,
        }
        prop["total_score"] = score_property(prop)
        return prop


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------

def save_json(properties: list[dict], path: Path):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(properties, f, ensure_ascii=False, indent=2)
    log.info(f"Saved {len(properties)} records to {path}")

def save_csv(properties: list[dict], path: Path):
    if not properties:
        return
    rows = []
    for p in properties:
        price = p.get("price_eur")
        land_ha = p.get("land_area_hectares")
        land_m2 = p.get("land_area_m2")
        build_m2 = p.get("build_area_m2")
        price_per_ha = round(price / land_ha) if price and land_ha else None
        price_per_m2_land = round(price / land_m2) if price and land_m2 else None
        price_per_m2_build = round(price / build_m2) if price and build_m2 else None
        rows.append({
            "score":               p.get("total_score", ""),
            "title":               p.get("title", ""),
            "url":                 p.get("url", ""),
            "source":              p.get("source_site", ""),
            "region":              p.get("region", ""),
            "province":            p.get("province", ""),
            "municipality":        p.get("municipality", ""),
            "price_eur":           price or "",
            "bedrooms":            p.get("bedrooms", ""),
            "bathrooms":           p.get("bathrooms", ""),
            "land_ha":             land_ha or "",
            "land_m2":             land_m2 or "",
            "build_m2":            build_m2 or "",
            "price_per_ha":        price_per_ha or "",
            "price_per_m2_land":   price_per_m2_land or "",
            "price_per_m2_build":  price_per_m2_build or "",
            "property_type":       p.get("property_type", ""),
            "pool":                "yes" if p.get("pool") else "no",
            "water_source":        p.get("water_source", ""),
            "condition":           p.get("condition", ""),
            "outbuildings":        p.get("outbuildings", ""),
            "agricultural_features": ", ".join(p.get("agricultural_features") or []),
            "nearest_airport":     p.get("nearest_airport", ""),
            "listing_date":        p.get("listing_date", ""),
        })
    df = pd.DataFrame(rows)
    df.to_csv(path, index=False, encoding="utf-8-sig")
    log.info(f"Saved CSV ({len(rows)} rows) to {path}")


def _region_stats(properties: list[dict]) -> list[dict]:
    """Compute per-region averages for the summary."""
    from collections import defaultdict
    buckets: dict[str, list] = defaultdict(list)
    for p in properties:
        buckets[p.get("region") or "Unknown"].append(p)

    stats = []
    for region, props in sorted(buckets.items()):
        prices   = [p["price_eur"] for p in props if p.get("price_eur")]
        lands_ha = [p["land_area_hectares"] for p in props if p.get("land_area_hectares")]
        builds   = [p["build_area_m2"] for p in props if p.get("build_area_m2")]
        beds_all = [p["bedrooms"] for p in props if p.get("bedrooms")]
        # Only include €/ha for genuine farm-sized plots (≥1 ha = 10,000 m²)
        pph_list = [p["price_eur"] / p["land_area_hectares"]
                    for p in props
                    if p.get("price_eur") and p.get("land_area_hectares")
                    and p["land_area_hectares"] >= 1.0]
        def avg(lst): return round(sum(lst) / len(lst)) if lst else None
        stats.append({
            "region":       region,
            "count":        len(props),
            "avg_price":    avg(prices),
            "min_price":    min(prices) if prices else None,
            "max_price":    max(prices) if prices else None,
            "avg_land_ha":  round(sum(lands_ha)/len(lands_ha), 1) if lands_ha else None,
            "avg_build_m2": avg(builds),
            "avg_beds":     round(sum(beds_all)/len(beds_all), 1) if beds_all else None,
            "avg_price_per_ha": avg(pph_list),
            "priced_count": len(prices),
            "with_land_count": len(lands_ha),
        })
    return stats


def save_summary(properties: list[dict], path: Path, top_n=20):
    sorted_props = sorted(properties, key=lambda x: x.get("total_score", 0), reverse=True)
    top = sorted_props[:top_n]
    now = datetime.now().strftime("%Y-%m-%d %H:%M")

    priced    = [p for p in properties if p.get("price_eur")]
    landed    = [p for p in properties if p.get("land_area_hectares")]
    # Farm-sized: ≥1 ha — exclude tiny garden plots from €/ha stats
    farm_sized = [p for p in properties if (p.get("land_area_hectares") or 0) >= 1.0]
    pph_list  = [p["price_eur"] / p["land_area_hectares"]
                 for p in farm_sized if p.get("price_eur")]

    def avg(lst): return round(sum(lst) / len(lst)) if lst else None
    def fmt_eur(n): return f"€{n:,}" if n else "—"
    def fmt_ha(n):  return f"{n} ha" if n else "—"

    # ── TLDR block ──────────────────────────────────────────────────────────
    lines = [
        "# Spain Rural Properties — TLDR Summary",
        f"\n_Generated: {now}_\n",
        "## At a Glance",
        f"- **{len(properties)}** total listings scraped across "
        f"{len(set(p.get('source_site','') for p in properties))} sites",
        f"- **{len(priced)}** have a listed price, "
        f"**{len(landed)}** have land area data",
        f"- Overall avg price: **{fmt_eur(avg([p['price_eur'] for p in priced]))}**",
        f"- Overall avg land (all with data): **{fmt_ha(round(sum(p['land_area_hectares'] for p in landed)/len(landed),1) if landed else None)}**",
        f"- Avg price/hectare (plots ≥1 ha only, n={len(pph_list)}): **{fmt_eur(avg(pph_list))}**",
        "",
    ]

    # ── Region breakdown table ────────────────────────────────────────────
    lines.append("## By Region\n")
    lines.append("| Region | Listings | Avg Price | Price Range | Avg Land | Avg €/ha | Avg Beds |")
    lines.append("|--------|----------|-----------|-------------|----------|----------|----------|")
    for s in _region_stats(properties):
        price_range = (f"{fmt_eur(s['min_price'])}–{fmt_eur(s['max_price'])}"
                       if s["min_price"] else "—")
        lines.append(
            f"| {s['region']} | {s['count']} ({s['priced_count']} priced) "
            f"| {fmt_eur(s['avg_price'])} | {price_range} "
            f"| {fmt_ha(s['avg_land_ha'])} | {fmt_eur(s['avg_price_per_ha'])} "
            f"| {s['avg_beds'] or '—'} |"
        )

    # ── Price per hectare distribution ────────────────────────────────────
    if pph_list:
        pph_sorted = sorted(pph_list)
        n = len(pph_sorted)
        lines += [
            "",
            "## Price per Hectare Distribution",
            f"- Cheapest: **{fmt_eur(round(pph_sorted[0]))}**/ha",
            f"- Median:   **{fmt_eur(round(pph_sorted[n//2]))}**/ha",
            f"- Top 25%:  **{fmt_eur(round(pph_sorted[int(n*0.75)]))}**/ha",
            f"- Most expensive: **{fmt_eur(round(pph_sorted[-1]))}**/ha",
        ]

    # ── Source breakdown ──────────────────────────────────────────────────
    from collections import Counter
    sources = Counter(p.get("source_site","?") for p in properties)
    lines += ["", "## By Source"]
    for src, cnt in sources.most_common():
        lines.append(f"- **{src}**: {cnt} listings")

    # ── Top listings ──────────────────────────────────────────────────────
    lines += ["", "---", "", f"## Top {len(top)} Properties by Score", ""]

    for i, p in enumerate(top, 1):
        price_str = fmt_eur(p.get("price_eur"))
        land_ha   = p.get("land_area_hectares")
        land_str  = f"{land_ha} ha" if land_ha else "land unknown"
        build_str = f"{p['build_area_m2']} m²" if p.get("build_area_m2") else ""
        pph       = round(p["price_eur"] / land_ha) if p.get("price_eur") and land_ha else None
        pph_str   = f" · {fmt_eur(pph)}/ha" if pph else ""
        beds_str  = str(p["bedrooms"]) if p.get("bedrooms") else "?"
        region    = p.get("region", "Unknown")
        score     = p.get("total_score", 0)
        ag        = ", ".join(p.get("agricultural_features") or []) or "none noted"
        # Only show €/ha for plots ≥1 ha
        pph_str   = f" · {fmt_eur(pph)}/ha" if pph and land_ha and land_ha >= 1.0 else ""
        loc_parts = [x for x in [p.get("municipality"), p.get("province"), region] if x and x != "Unknown"]
        loc_str   = ", ".join(loc_parts) if loc_parts else region

        lines.append(f"### {i}. {p.get('title', 'Untitled')} — Score: {score}/10")
        lines.append(f"**{price_str}** · {land_str}{pph_str} · {build_str} · {beds_str} beds")
        lines.append(loc_str)
        lines.append(f"[{p.get('source_site','')}]({p.get('url','')})")
        lines.append(f"Type: {p.get('property_type','?').title()} · "
                     f"Pool: {'yes' if p.get('pool') else 'no'} · "
                     f"Water: {p.get('water_source') or '?'} · "
                     f"Airport: {p.get('nearest_airport') or '?'}")
        lines.append(f"Ag features: {ag}")
        lines.append("")

    path.write_text("\n".join(lines), encoding="utf-8")
    log.info(f"Summary saved to {path}")

# ---------------------------------------------------------------------------
# Main orchestrator
# ---------------------------------------------------------------------------

async def main():
    log.info("=" * 60)
    log.info("Spain Rural Property Scraper — starting")
    log.info("=" * 60)

    all_properties: list[dict] = []
    seen_ids: set[str] = set()

    def add_results(new_props: list[dict]):
        for p in new_props:
            pid = p.get("listing_id")
            if pid and pid not in seen_ids:
                seen_ids.add(pid)
                all_properties.append(p)
            elif not pid:
                all_properties.append(p)

    # --- All scrapers now use Playwright (static sites block direct requests) ---
    log.info("\n>>> Starting Playwright browser...")
    async with async_playwright() as pw:
        browser = await pw.chromium.launch(
            headless=True,
            args=["--no-sandbox", "--disable-blink-features=AutomationControlled"],
        )

        log.info("\n>>> Scraping Kyero...")
        kyero = KyeroPlaywrightScraper()
        add_results(await kyero.scrape(browser, max_pages=6))
        save_json(all_properties, JSON_FILE)

        log.info("\n>>> Scraping Green Acres...")
        green = GreenAcresPlaywrightScraper()
        add_results(await green.scrape(browser, max_pages=5))
        save_json(all_properties, JSON_FILE)

        log.info("\n>>> Skipping Idealista (anti-bot protection blocks headless browsers)")

        log.info("\n>>> Scraping Fotocasa...")
        fotocasa = FotocasaScraper()
        add_results(await fotocasa.scrape(browser, max_pages=4))
        save_json(all_properties, JSON_FILE)

        await browser.close()

    # --- Final scoring & output ---
    log.info(f"\nTotal unique properties collected: {len(all_properties)}")

    # Re-score everything in place
    for p in all_properties:
        p["total_score"] = score_property(p)

    all_properties.sort(key=lambda x: x.get("total_score", 0), reverse=True)

    save_json(all_properties, JSON_FILE)
    save_csv(all_properties, CSV_FILE)
    save_summary(all_properties, SUMMARY_FILE, top_n=20)

    log.info("\n" + "=" * 60)
    log.info("Scraping complete.")
    log.info(f"  JSON:    {JSON_FILE}")
    log.info(f"  CSV:     {CSV_FILE}")
    log.info(f"  Summary: {SUMMARY_FILE}")
    log.info(f"  Log:     {LOG_FILE}")
    log.info("=" * 60)


if __name__ == "__main__":
    asyncio.run(main())
