"""
Test individual scrapers quickly and optionally save output files.

Usage:
    python test_site.py --site kyero
    python test_site.py --site all --save          # saves JSON/CSV/summary
    python test_site.py --site greenacres --max-pages 2 --max-listings 5
    python test_site.py --site fotocasa --headless false
"""

import asyncio
import argparse
import hashlib
from pathlib import Path
from playwright.async_api import async_playwright

from scraper import (
    KyeroPlaywrightScraper,
    GreenAcresPlaywrightScraper,
    FotocasaScraper,
    score_property,
    save_json,
    save_csv,
    save_summary,
)


def _limit_scrape(cls, max_listings):
    """Cap listings visited per search URL for fast iteration."""
    if max_listings <= 0:
        return
    if hasattr(cls, '_parse_list'):
        orig = cls._parse_list
        def limited(self, soup):
            return orig(self, soup)[:max_listings]
        cls._parse_list = limited
    elif hasattr(cls, '_parse_cards'):
        orig = cls._parse_cards
        def limited(self, soup):
            return orig(self, soup)[:max_listings]
        cls._parse_cards = limited
    elif hasattr(cls, 'API_URL'):
        # API-based scraper: limit via maxItems in the API call
        orig_scrape = cls.scrape
        async def limited_scrape(self, browser, max_pages=1):
            orig_get = self._session.get
            def limited_get(url, **kwargs):
                p = kwargs.get("params", {})
                p["maxItems"] = str(max_listings)
                kwargs["params"] = p
                return orig_get(url, **kwargs)
            self._session.get = limited_get
            return await orig_scrape(self, browser, max_pages=1)
        cls.scrape = limited_scrape


SITES = {
    "kyero":       KyeroPlaywrightScraper,
    "greenacres":  GreenAcresPlaywrightScraper,
    "fotocasa":    FotocasaScraper,
}


def print_results(site: str, results: list[dict]):
    print(f"\n{'='*60}")
    print(f"{site.upper()} — {len(results)} properties found")
    print("=" * 60)
    if not results:
        print("  (none)")
        return
    for i, p in enumerate(results, 1):
        price    = f"€{p['price_eur']:,}" if p.get("price_eur") else "€?"
        beds     = p.get("bedrooms", "?")
        land_ha  = p.get("land_area_hectares")
        land_str = f"{land_ha} ha" if land_ha else "? ha"
        region   = p.get("region") or p.get("municipality") or "?"
        score    = p.get("total_score", score_property(p))
        title    = (p.get("title") or "No title")[:60]
        url      = p.get("url", "")
        print(f"\n  [{i}] {title}")
        print(f"       {price}  |  {beds} beds  |  {land_str}  |  {region}  |  score={score:.1f}")
        print(f"       {url}")


all_collected: list[dict] = []
seen_ids: set[str] = set()


async def run(site_name: str, max_pages: int, headless: bool, max_listings: int):
    cls = SITES[site_name]
    _limit_scrape(cls, max_listings)
    label = f"max_listings={max_listings}/url" if max_listings > 0 else "unlimited"
    print(f"\nTesting {site_name} (max_pages={max_pages}, {label}, headless={headless})...")

    async with async_playwright() as pw:
        browser = await pw.chromium.launch(
            headless=headless,
            args=["--no-sandbox", "--disable-blink-features=AutomationControlled"],
        )
        try:
            scraper = cls()
            results = await scraper.scrape(browser, max_pages=max_pages)
            # Accumulate deduplicated results
            for p in results:
                pid = p.get("listing_id") or hashlib.md5(p.get("url","").encode()).hexdigest()
                if pid not in seen_ids:
                    seen_ids.add(pid)
                    all_collected.append(p)
            print_results(site_name, results)
        except Exception as e:
            print(f"\nERROR running {site_name}: {e}")
            import traceback; traceback.print_exc()
        finally:
            await browser.close()


def main():
    parser = argparse.ArgumentParser(description="Test individual scrapers")
    parser.add_argument("--site", choices=["kyero", "greenacres", "fotocasa", "all"],
                        default="kyero", help="Which scraper to test")
    parser.add_argument("--max-pages", type=int, default=1,
                        help="Pages per search URL (default: 1)")
    parser.add_argument("--headless", type=lambda x: x.lower() != "false",
                        default=True, metavar="true/false",
                        help="Run browser headless (default: true)")
    parser.add_argument("--max-listings", type=int, default=2,
                        help="Max listings per search URL (default: 2, 0=unlimited)")
    parser.add_argument("--save", action="store_true",
                        help="Save JSON, CSV and summary markdown after scraping")
    parser.add_argument("--out", default=".",
                        help="Output directory for saved files (default: current dir)")
    args = parser.parse_args()

    sites = list(SITES.keys()) if args.site == "all" else [args.site]

    async def run_all():
        for site in sites:
            await run(site, args.max_pages, args.headless, args.max_listings)

    asyncio.run(run_all())

    if args.save and all_collected:
        out = Path(args.out)
        # Re-score everything
        for p in all_collected:
            p["total_score"] = score_property(p)
        all_collected.sort(key=lambda x: x.get("total_score", 0), reverse=True)

        json_path    = out / "spain_properties.json"
        csv_path     = out / "spain_properties.csv"
        summary_path = out / "spain_properties_summary.md"

        save_json(all_collected, json_path)
        save_csv(all_collected, csv_path)
        save_summary(all_collected, summary_path, top_n=min(20, len(all_collected)))

        print(f"\n{'='*60}")
        print(f"Saved {len(all_collected)} properties:")
        print(f"  {json_path}")
        print(f"  {csv_path}")
        print(f"  {summary_path}")


if __name__ == "__main__":
    main()
