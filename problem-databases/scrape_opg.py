#!/usr/bin/env python3
"""
Scrape Open Problem Garden for open mathematical problems.

Categories available:
- Graph Theory (228)
- Combinatorics
- Number Theory
- Algebra
- Analysis
- Geometry
- Topology
- Logic
"""

import sqlite3
import json
import re
import time
from pathlib import Path
from urllib.request import urlopen, Request
from urllib.error import URLError
from html.parser import HTMLParser

BASE_DIR = Path(__file__).parent
DB_PATH = BASE_DIR / "problems.db"

class OPGParser(HTMLParser):
    """Parse Open Problem Garden HTML."""

    def __init__(self):
        super().__init__()
        self.problems = []
        self.current_problem = None
        self.in_problem_title = False
        self.in_problem_link = False
        self.current_href = None

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)

        # Look for problem links
        if tag == 'a' and 'href' in attrs:
            href = attrs['href']
            if '/op/' in href or '/node/' in href:
                self.in_problem_link = True
                self.current_href = href

    def handle_endtag(self, tag):
        if tag == 'a':
            self.in_problem_link = False

    def handle_data(self, data):
        if self.in_problem_link and self.current_href:
            data = data.strip()
            if data and len(data) > 3:
                self.problems.append({
                    'name': data,
                    'url': self.current_href
                })
            self.current_href = None

def fetch_url(url, timeout=30):
    """Fetch URL with user agent."""
    headers = {
        'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36'
    }
    req = Request(url, headers=headers)
    try:
        with urlopen(req, timeout=timeout) as response:
            return response.read().decode('utf-8', errors='ignore')
    except URLError as e:
        print(f"  Error fetching {url}: {e}")
        return None

def scrape_category(category_url, category_name):
    """Scrape a category from OPG."""
    print(f"  Scraping: {category_name}...")

    html = fetch_url(category_url)
    if not html:
        return []

    parser = OPGParser()
    parser.feed(html)

    # Deduplicate and clean
    seen = set()
    problems = []
    for p in parser.problems:
        name = p['name']
        if name not in seen and len(name) > 5:
            seen.add(name)
            problems.append({
                'name': name,
                'url': f"http://www.openproblemgarden.org{p['url']}" if p['url'].startswith('/') else p['url'],
                'category': category_name
            })

    return problems

def scrape_all_categories():
    """Scrape all OPG categories."""
    categories = [
        ('http://www.openproblemgarden.org/category/graph_theory', 'graph theory'),
        ('http://www.openproblemgarden.org/category/combinatorics', 'combinatorics'),
        ('http://www.openproblemgarden.org/category/number_theory', 'number theory'),
        ('http://www.openproblemgarden.org/category/algebra', 'algebra'),
        ('http://www.openproblemgarden.org/category/analysis', 'analysis'),
        ('http://www.openproblemgarden.org/category/geometry', 'geometry'),
        ('http://www.openproblemgarden.org/category/topology', 'topology'),
        ('http://www.openproblemgarden.org/category/logic', 'logic'),
    ]

    all_problems = []

    for url, name in categories:
        problems = scrape_category(url, name)
        all_problems.extend(problems)
        print(f"    Found {len(problems)} problems")
        time.sleep(1)  # Be nice to the server

    return all_problems

def update_database(problems):
    """Update SQLite database with OPG problems."""
    conn = sqlite3.connect(DB_PATH)

    # Clear old OPG entries (except placeholders)
    conn.execute("DELETE FROM problems WHERE source = 'opg' AND source_id NOT LIKE 'category-%'")

    count = 0
    for p in problems:
        # Generate source_id from URL
        source_id = re.sub(r'[^a-z0-9]+', '-', p['url'].lower())[-50:]

        # Estimate tractability based on category
        tractability_map = {
            'graph theory': 75,
            'combinatorics': 70,
            'number theory': 60,
            'algebra': 65,
            'geometry': 65,
            'analysis': 55,
            'topology': 50,
            'logic': 60,
        }
        tractability = tractability_map.get(p['category'], 60)

        conn.execute("""
            INSERT OR REPLACE INTO problems
            (source, source_id, name, status, domain, tractability_score, urls)
            VALUES (?, ?, ?, 'open', ?, ?, ?)
        """, (
            'opg',
            source_id,
            p['name'],
            p['category'],
            tractability,
            json.dumps([p['url']])
        ))
        count += 1

    # Update source metadata
    conn.execute("""
        UPDATE sources SET last_scraped = datetime('now'), problem_count = ?
        WHERE name = 'opg'
    """, (count,))

    conn.commit()
    conn.close()

    return count

def main():
    print("="*60)
    print("SCRAPING OPEN PROBLEM GARDEN")
    print("="*60)

    problems = scrape_all_categories()

    print(f"\nTotal unique problems found: {len(problems)}")

    if problems:
        count = update_database(problems)
        print(f"✓ Updated database with {count} OPG problems")
    else:
        print("⚠ No problems scraped - site may be down or blocking")

if __name__ == "__main__":
    main()
