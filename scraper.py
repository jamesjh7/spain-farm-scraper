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
                return BeautifulSoup(r.text, "lxml")
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

    async def _get_page_html(self, page: Page, url: str) -> Optional[BeautifulSoup]:
        try:
            await page.goto(url, wait_until="domcontentloaded", timeout=30000)
            await page.wait_for_timeout(random.randint(2000, 4000))
            html = await page.content()
            return BeautifulSoup(html, "lxml")
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

        region_guess = self._guess_region(self, province + " " + municipality + " " + region)
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
            "property_type": self._guess_type(self, title + " " + description),
            "nearest_airport": self._guess_airport(self, region_guess, province),
            "nearest_city": None,
            "water_source": self._guess_water(self, description),
            "pool": "pool" in description.lower() or "piscina" in description.lower(),
            "outbuildings": self._guess_outbuildings(self, description),
            "agricultural_features": self._guess_ag_features(self, description),
            "event_venue_potential": self._venue_notes(self, description),
            "airbnb_potential": self._airbnb_notes(self, description),
            "condition": self._guess_condition(self, description),
            "energy_rating": self._guess_energy(self, soup),
            "listing_date": datetime.now().strftime("%Y-%m-%d"),
            "description_raw": description[:3000],
            "notes": "",
            "images": images,
            "login_required": False,
        }
        prop["total_score"] = score_property(prop)
        return prop


# ---------------------------------------------------------------------------
# Fotocasa scraper (Playwright)
# ---------------------------------------------------------------------------

class FotocasaScraper(PlaywrightScraper):
    BASE = "https://www.fotocasa.es"

    REGIONS = [
        ("andalucia", "Andalusia"),
        ("comunitat-valenciana", "Valencia"),
        ("region-de-murcia", "Murcia"),
        ("cataluna", "Catalonia"),
        ("castilla-la-mancha", "Castilla-La Mancha"),
        ("extremadura", "Extremadura"),
    ]

    def __init__(self):
        super().__init__("fotocasa.es")

    async def scrape(self, browser: Browser, max_pages=5) -> list[dict]:
        results = []
        context = await browser.new_context(
            user_agent=random_ua(),
            locale="en-GB",
            viewport={"width": 1366, "height": 768},
        )
        page = await context.new_page()

        for region_slug, region_label in self.REGIONS:
            for pg in range(1, max_pages + 1):
                url = f"{self.BASE}/en/homes-for-sale/{region_slug}/all-zones/all-municipalities/all-counties/l"
                if pg > 1:
                    url += f"?page={pg}"

                log.info(f"[Fotocasa] {region_label} / page {pg}")
                soup = await self._get_page_html(page, url)
                if not soup:
                    break

                if "captcha" in (soup.get_text() or "").lower():
                    log.warning(f"[Fotocasa] CAPTCHA on {url}")
                    break

                listing_urls = self._parse_list(soup)
                if not listing_urls:
                    break

                for lurl in listing_urls:
                    await page.wait_for_timeout(random.randint(2000, 4500))
                    detail = await self._parse_detail(page, lurl, region_label)
                    if detail:
                        results.append(detail)

                await page.wait_for_timeout(random.randint(3000, 6000))

        await context.close()
        log.info(f"[Fotocasa] Total collected: {len(results)}")
        return results

    def _parse_list(self, soup: BeautifulSoup) -> list[str]:
        urls = []
        for a in soup.select("a[href*='/en/homes-for-sale/'], a[href*='/inmueble/']"):
            href = a.get("href", "")
            if href and "/homes-for-sale/" in href:
                full = href if href.startswith("http") else self.BASE + href
                if full not in urls and full != f"{self.BASE}/en/homes-for-sale/":
                    urls.append(full)
        return urls

    async def _parse_detail(self, page: Page, url: str, region: str) -> Optional[dict]:
        soup = await self._get_page_html(page, url)
        if not soup:
            return None

        title = ""
        h1 = soup.select_one("h1")
        if h1:
            title = h1.get_text(strip=True)

        price_eur = None
        for sel in ["[class*='price'] span", ".re-DetailHeader-price", "[data-testid='detail-price']"]:
            el = soup.select_one(sel)
            if el:
                price_eur = safe_int(el.get_text())
                break

        bedrooms = bathrooms = land_m2 = build_m2 = None
        for el in soup.select("[class*='feature'], [class*='detail'], li"):
            txt = el.get_text(" ", strip=True).lower()
            if re.search(r"\d+.*(bed|dormitor|habitaci)", txt):
                m = re.search(r"(\d+)", txt)
                if m:
                    bedrooms = int(m.group(1))
            elif re.search(r"\d+.*(bath|baño)", txt):
                m = re.search(r"(\d+)", txt)
                if m:
                    bathrooms = int(m.group(1))

        desc_el = soup.select_one("[class*='description'], [class*='Description']")
        description = desc_el.get_text("\n", strip=True) if desc_el else ""

        region_guess = self._guess_region(self, region)
        images = [img.get("src") or img.get("data-src") for img in soup.select("img") if img.get("src") or img.get("data-src")]
        images = [i for i in images if i and ("fotocasa" in i or "photo" in i)][:10]

        prop = {
            "listing_id": make_id(url),
            "title": title,
            "url": url,
            "source_site": self.source,
            "region": region_guess,
            "province": "",
            "municipality": "",
            "price_eur": price_eur,
            "price_per_sqm_eur": None,
            "land_area_hectares": None,
            "land_area_m2": land_m2,
            "build_area_m2": build_m2,
            "bedrooms": bedrooms,
            "bathrooms": bathrooms,
            "year_built": None,
            "property_type": self._guess_type(self, title + " " + description),
            "nearest_airport": self._guess_airport(self, region_guess, ""),
            "nearest_city": None,
            "water_source": self._guess_water(self, description),
            "pool": "pool" in description.lower() or "piscina" in description.lower(),
            "outbuildings": self._guess_outbuildings(self, description),
            "agricultural_features": self._guess_ag_features(self, description),
            "event_venue_potential": self._venue_notes(self, description),
            "airbnb_potential": self._airbnb_notes(self, description),
            "condition": self._guess_condition(self, description),
            "energy_rating": self._guess_energy(self, soup),
            "listing_date": datetime.now().strftime("%Y-%m-%d"),
            "description_raw": description[:3000],
            "notes": "",
            "images": images,
            "login_required": False,
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
    flat = []
    for p in properties:
        row = dict(p)
        row["agricultural_features"] = ", ".join(row.get("agricultural_features") or [])
        row["images"] = " | ".join(row.get("images") or [])
        flat.append(row)
    df = pd.DataFrame(flat)
    df.to_csv(path, index=False, encoding="utf-8-sig")
    log.info(f"Saved CSV to {path}")

def save_summary(properties: list[dict], path: Path, top_n=20):
    sorted_props = sorted(properties, key=lambda x: x.get("total_score", 0), reverse=True)
    top = sorted_props[:top_n]

    lines = [
        "# Spain Rural Properties — Top Candidates",
        f"\n_Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}_",
        f"\nTotal listings collected: **{len(properties)}**\n",
        "---\n",
    ]

    for i, p in enumerate(top, 1):
        price_str = f"€{p['price_eur']:,}" if p.get("price_eur") else "Price unknown"
        land_str = f"{p['land_area_hectares']} ha" if p.get("land_area_hectares") else "Land area unknown"
        beds_str = f"{p['bedrooms']} bed" if p.get("bedrooms") else "?"
        region = p.get("region", "Unknown")
        score = p.get("total_score", 0)
        ag = ", ".join(p.get("agricultural_features") or []) or "None noted"

        lines.append(f"## {i}. {p.get('title', 'Untitled')} — Score: {score}/10")
        lines.append(f"\n**Source:** [{p.get('source_site')}]({p.get('url')})")
        lines.append(f"**Location:** {p.get('municipality', '')}, {p.get('province', '')}, {region}")
        lines.append(f"**Price:** {price_str} | **Land:** {land_str} | **Beds:** {beds_str}")
        lines.append(f"**Type:** {p.get('property_type', 'unknown').title()}")
        lines.append(f"**Airport:** {p.get('nearest_airport', 'unknown')}")
        lines.append(f"**Agricultural features:** {ag}")
        lines.append(f"**Pool:** {'Yes' if p.get('pool') else 'No'} | **Condition:** {p.get('condition', 'unknown')}")
        lines.append(f"\n**Why it fits:**")
        lines.append(f"- Farming: {p.get('event_venue_potential', 'N/A')}")
        lines.append(f"- Airbnb: {p.get('airbnb_potential', 'N/A')}")
        lines.append(f"\n---\n")

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

    # --- Static scrapers ---
    session = StaticSession()

    log.info("\n>>> Scraping Kyero...")
    kyero = KyeroScraper(session)
    add_results(kyero.scrape(max_pages=8))
    save_json(all_properties, JSON_FILE)

    log.info("\n>>> Scraping Green Acres...")
    green = GreenAcresScraper(session)
    add_results(green.scrape(max_pages=6))
    save_json(all_properties, JSON_FILE)

    log.info("\n>>> Scraping Rurales.com...")
    rurales = RuralesScraper(session)
    add_results(rurales.scrape(max_pages=5))
    save_json(all_properties, JSON_FILE)

    log.info("\n>>> Scraping Rightmove Overseas...")
    rightmove = RightmoveScraper(session)
    add_results(rightmove.scrape(max_pages=5))
    save_json(all_properties, JSON_FILE)

    # --- Playwright scrapers ---
    log.info("\n>>> Starting Playwright for JS-rendered sites...")
    async with async_playwright() as pw:
        browser = await pw.chromium.launch(
            headless=True,
            args=["--no-sandbox", "--disable-blink-features=AutomationControlled"],
        )

        log.info("\n>>> Scraping Idealista...")
        idealista = IdealistaScraper()
        add_results(await idealista.scrape(browser, max_pages=4))
        save_json(all_properties, JSON_FILE)

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
