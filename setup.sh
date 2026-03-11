#!/bin/bash
# Setup script for Spain Farm Property Scraper

echo "Creating virtual environment..."
python3 -m venv venv
source venv/bin/activate

echo "Installing Python dependencies..."
pip install -r requirements.txt

echo "Installing Playwright Chromium browser..."
playwright install chromium

echo ""
echo "Setup complete. Run the scraper with:"
echo "  source venv/bin/activate"
echo "  python scraper.py"
