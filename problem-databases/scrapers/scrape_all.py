#!/usr/bin/env python3
"""
Master scraper for all open problem sources.

Sources:
1. Open Problem Garden - 710+ problems
2. Wikipedia - List of unsolved problems
3. OEIS - Integer sequence conjectures
4. Polymath - Collaborative targets
5. Mathoverflow - Open problems tag
6. Green's Open Problems - Combinatorics/Number Theory
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from pathlib import Path
import sqlite3
import json
import time
import re
from urllib.request import urlopen, Request
from urllib.error import URLError, HTTPError
from html.parser import HTMLParser
from concurrent.futures import ThreadPoolExecutor, as_completed

BASE_DIR = Path(__file__).parent.parent
DB_PATH = BASE_DIR / "problems.db"

# Common utilities
def fetch_url(url, timeout=30):
    """Fetch URL with proper headers."""
    headers = {
        'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
    }
    req = Request(url, headers=headers)
    try:
        with urlopen(req, timeout=timeout) as response:
            return response.read().decode('utf-8', errors='ignore')
    except (URLError, HTTPError) as e:
        print(f"  Error fetching {url}: {e}")
        return None

def get_db():
    """Get database connection."""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn

def add_problems(source_name, problems):
    """Add problems to database."""
    if not problems:
        return 0

    conn = get_db()

    count = 0
    source_url = ''
    source_desc = ''

    for p in problems:
        # Capture source metadata from first problem
        if not source_url:
            source_url = p.get('source_url', '')
            source_desc = p.get('source_desc', '')

        slug = f"{source_name}-{p.get('source_id', p['name'][:30])}".lower()
        slug = re.sub(r'[^a-z0-9]+', '-', slug)[:100]

        try:
            conn.execute("""
                INSERT OR REPLACE INTO problems
                (source, source_id, name, slug, status, statement, domain,
                 tractability_score, urls, has_lean4)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                source_name,
                p.get('source_id', ''),
                p['name'],
                slug,
                p.get('status', 'open'),
                p.get('statement', ''),
                p.get('domain', ''),
                p.get('tractability', 50),
                json.dumps(p.get('urls', [])),
                False
            ))
            count += 1
        except Exception as e:
            print(f"  Error adding {p['name']}: {e}")

    # Update source metadata
    conn.execute("""
        INSERT OR REPLACE INTO sources (name, url, description, last_scraped, problem_count)
        VALUES (?, ?, ?, datetime('now'), ?)
    """, (source_name, source_url, source_desc, count))

    conn.commit()
    conn.close()
    return count

# ============================================================
# SCRAPER: Open Problem Garden
# ============================================================
def scrape_opg():
    """Scrape Open Problem Garden."""
    print("\n" + "="*60)
    print("SCRAPING: Open Problem Garden")
    print("="*60)

    categories = [
        ('graph_theory', 'graph theory'),
        ('combinatorics', 'combinatorics'),
        ('number_theory_0', 'number theory'),
        ('algebra', 'algebra'),
        ('analysis', 'analysis'),
        ('geometry', 'geometry'),
        ('topology', 'topology'),
        ('logic', 'logic'),
    ]

    all_problems = []

    for cat_slug, cat_name in categories:
        url = f"http://www.openproblemgarden.org/category/{cat_slug}"
        print(f"  Fetching {cat_name}...")

        html = fetch_url(url)
        if not html:
            continue

        # Extract problem links and titles
        # Pattern: <a href="/op/...">Problem Title</a>
        pattern = r'<a[^>]*href="(/op/[^"]+)"[^>]*>([^<]+)</a>'
        matches = re.findall(pattern, html, re.IGNORECASE)

        for href, title in matches:
            title = title.strip()
            if len(title) > 5 and title not in ['Open Problem Garden', 'Home']:
                all_problems.append({
                    'name': title,
                    'source_id': href.split('/')[-1],
                    'domain': cat_name,
                    'status': 'open',
                    'urls': [f"http://www.openproblemgarden.org{href}"],
                    'tractability': estimate_tractability_opg(title, cat_name),
                    'source_url': 'http://www.openproblemgarden.org/',
                    'source_desc': 'Open Problem Garden - curated open problems'
                })

        print(f"    Found {len(matches)} problems")
        time.sleep(0.5)

    # Deduplicate
    seen = set()
    unique = []
    for p in all_problems:
        if p['name'] not in seen:
            seen.add(p['name'])
            unique.append(p)

    count = add_problems('opg', unique)
    print(f"✓ Added {count} Open Problem Garden problems")
    return count

def estimate_tractability_opg(title, domain):
    """Estimate tractability from OPG problem."""
    score = 50
    title_lower = title.lower()

    # Positive indicators
    if any(x in title_lower for x in ['conjecture', 'bound', 'existence']):
        score += 10
    if any(x in title_lower for x in ['graph', 'coloring', 'chromatic']):
        score += 10
    if domain in ['graph theory', 'combinatorics']:
        score += 10

    # Negative indicators
    if any(x in title_lower for x in ['infinite', 'continuous', 'analytic']):
        score -= 15
    if domain in ['analysis', 'topology']:
        score -= 10

    return max(0, min(100, score))

# ============================================================
# SCRAPER: Wikipedia Unsolved Problems
# ============================================================
def scrape_wikipedia():
    """Scrape Wikipedia's list of unsolved problems."""
    print("\n" + "="*60)
    print("SCRAPING: Wikipedia Unsolved Problems")
    print("="*60)

    pages = [
        ('https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics', 'mathematics'),
        ('https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_computer_science', 'computer science'),
    ]

    all_problems = []

    for url, category in pages:
        print(f"  Fetching {category}...")
        html = fetch_url(url)
        if not html:
            continue

        # Extract problem names from list items with links
        # Wikipedia format: <li>...<a href="/wiki/...">Problem Name</a>...</li>
        pattern = r'<li[^>]*>([^<]*<a[^>]*href="/wiki/([^"]+)"[^>]*>([^<]+)</a>[^<]*)</li>'
        matches = re.findall(pattern, html, re.IGNORECASE)

        for full_text, href, title in matches:
            title = title.strip()
            # Filter out navigation and non-problem links
            if (len(title) > 5 and
                'conjecture' in title.lower() or
                'problem' in title.lower() or
                'hypothesis' in title.lower() or
                'theorem' in title.lower()):

                all_problems.append({
                    'name': title,
                    'source_id': href,
                    'domain': category,
                    'status': 'open',
                    'urls': [f"https://en.wikipedia.org/wiki/{href}"],
                    'tractability': estimate_tractability_wiki(title),
                    'source_url': url,
                    'source_desc': 'Wikipedia list of unsolved problems'
                })

        print(f"    Found {len(matches)} potential problems")
        time.sleep(1)

    # Deduplicate
    seen = set()
    unique = []
    for p in all_problems:
        if p['name'] not in seen:
            seen.add(p['name'])
            unique.append(p)

    count = add_problems('wikipedia', unique)
    print(f"✓ Added {count} Wikipedia problems")
    return count

def estimate_tractability_wiki(title):
    """Estimate tractability from Wikipedia problem."""
    score = 50
    title_lower = title.lower()

    # Famous hard problems
    hard = ['riemann', 'goldbach', 'twin prime', 'collatz', 'p versus np',
            'hodge', 'navier-stokes', 'yang-mills', 'birch']
    if any(x in title_lower for x in hard):
        score -= 30

    # Potentially tractable
    tractable = ['graph', 'combinat', 'ramsey', 'coloring', 'latin', 'sidon']
    if any(x in title_lower for x in tractable):
        score += 15

    return max(0, min(100, score))

# ============================================================
# SCRAPER: OEIS Conjectures
# ============================================================
def scrape_oeis():
    """Fetch OEIS sequences with conjectures."""
    print("\n" + "="*60)
    print("SCRAPING: OEIS Conjectures")
    print("="*60)

    # Search for sequences with "conjecture" in comments
    # OEIS has a search API
    search_terms = ['conjecture', 'open+problem', 'unsolved', 'unproven', 'unknown']

    all_problems = []

    for term in search_terms:
        url = f"https://oeis.org/search?q={term}&fmt=json&start=0&count=100"
        print(f"  Searching for '{term}'...")

        html = fetch_url(url)
        if not html:
            continue

        try:
            # OEIS returns JSON - handle different response formats
            data = json.loads(html)
            # OEIS may return results directly or in a 'results' key
            if isinstance(data, list):
                results = data
            elif isinstance(data, dict):
                results = data.get('results', [])
            else:
                results = []

            for seq in results:
                seq_id = seq.get('number', 0)
                name = seq.get('name', '')

                # Check if it has an actual conjecture
                comments = ' '.join(seq.get('comment', []))
                if 'conjecture' in comments.lower() or 'open' in comments.lower():
                    all_problems.append({
                        'name': f"A{seq_id:06d}: {name[:100]}",
                        'source_id': f"A{seq_id:06d}",
                        'domain': 'sequences',
                        'status': 'open',
                        'statement': comments[:500],
                        'urls': [f"https://oeis.org/A{seq_id:06d}"],
                        'tractability': 70,  # OEIS problems are often bounded
                        'source_url': 'https://oeis.org/',
                        'source_desc': 'Online Encyclopedia of Integer Sequences'
                    })

            print(f"    Found {len(results)} sequences")
        except json.JSONDecodeError:
            print(f"    Failed to parse JSON")

        time.sleep(1)

    # Deduplicate
    seen = set()
    unique = []
    for p in all_problems:
        if p['source_id'] not in seen:
            seen.add(p['source_id'])
            unique.append(p)

    count = add_problems('oeis', unique)
    print(f"✓ Added {count} OEIS conjectures")
    return count

# ============================================================
# SCRAPER: Polymath Wiki
# ============================================================
def scrape_polymath():
    """Scrape Polymath wiki for collaborative problem targets."""
    print("\n" + "="*60)
    print("SCRAPING: Polymath Wiki")
    print("="*60)

    url = "https://asone.ai/polymath/index.php?title=Main_Page"
    print(f"  Fetching main page...")

    html = fetch_url(url)
    if not html:
        print("  Could not fetch Polymath wiki")
        return 0

    problems = []

    # Look for project links
    pattern = r'<a[^>]*href="([^"]*Polymath[^"]*)"[^>]*>([^<]+)</a>'
    matches = re.findall(pattern, html, re.IGNORECASE)

    for href, title in matches:
        if 'project' in href.lower() or 'problem' in href.lower():
            problems.append({
                'name': title.strip(),
                'source_id': href.split('=')[-1] if '=' in href else href,
                'domain': 'various',
                'status': 'open',
                'urls': [f"https://asone.ai/polymath/{href}" if not href.startswith('http') else href],
                'tractability': 60,
                'source_url': url,
                'source_desc': 'Polymath - collaborative mathematics projects'
            })

    # Deduplicate
    seen = set()
    unique = []
    for p in problems:
        if p['name'] not in seen and len(p['name']) > 3:
            seen.add(p['name'])
            unique.append(p)

    count = add_problems('polymath', unique)
    print(f"✓ Added {count} Polymath problems")
    return count

# ============================================================
# SCRAPER: MathOverflow Open Problems
# ============================================================
def scrape_mathoverflow():
    """Scrape MathOverflow open-problem tagged questions."""
    print("\n" + "="*60)
    print("SCRAPING: MathOverflow Open Problems")
    print("="*60)

    # Use Stack Exchange API - note: tag is "open-problems" (plural)
    url = "https://api.stackexchange.com/2.3/questions?order=desc&sort=votes&tagged=open-problems&site=mathoverflow&pagesize=100"

    print(f"  Fetching via API...")

    html = fetch_url(url)
    if not html:
        print("  Could not fetch MathOverflow")
        return 0

    problems = []

    try:
        data = json.loads(html)
        items = data.get('items', [])

        for q in items:
            title = q.get('title', '')
            qid = q.get('question_id', 0)
            tags = q.get('tags', [])
            score = q.get('score', 0)

            # Higher voted questions are more significant
            tractability = 50 + min(score, 30)  # Cap bonus at 30

            # Adjust by tags
            if any(t in tags for t in ['graph-theory', 'combinatorics', 'ramsey-theory']):
                tractability += 10
            if any(t in tags for t in ['analytic-number-theory', 'riemann-hypothesis']):
                tractability -= 20

            problems.append({
                'name': title,
                'source_id': str(qid),
                'domain': tags[0] if tags else 'various',
                'status': 'open',
                'urls': [q.get('link', f"https://mathoverflow.net/q/{qid}")],
                'tractability': max(0, min(100, tractability)),
                'source_url': 'https://mathoverflow.net/',
                'source_desc': 'MathOverflow - research-level math Q&A'
            })

        print(f"    Found {len(items)} questions")

    except json.JSONDecodeError:
        print(f"    Failed to parse API response")

    count = add_problems('mathoverflow', problems)
    print(f"✓ Added {count} MathOverflow problems")
    return count

# ============================================================
# MAIN
# ============================================================
def main():
    print("="*60)
    print("COMPREHENSIVE PROBLEM DATABASE SCRAPER")
    print("="*60)

    total = 0

    # Run all scrapers
    scrapers = [
        ('Open Problem Garden', scrape_opg),
        ('Wikipedia', scrape_wikipedia),
        ('OEIS', scrape_oeis),
        ('Polymath', scrape_polymath),
        ('MathOverflow', scrape_mathoverflow),
    ]

    for name, scraper in scrapers:
        try:
            count = scraper()
            total += count
        except Exception as e:
            print(f"  ERROR in {name}: {e}")

    print("\n" + "="*60)
    print(f"SCRAPING COMPLETE: Added {total} new problems")
    print("="*60)

    # Print updated stats
    conn = get_db()
    stats = conn.execute("""
        SELECT source, COUNT(*) as cnt
        FROM problems
        GROUP BY source
        ORDER BY cnt DESC
    """).fetchall()

    print("\nDatabase now contains:")
    for row in stats:
        print(f"  {row['source']:20} | {row['cnt']:5} problems")

    total_count = conn.execute("SELECT COUNT(*) FROM problems").fetchone()[0]
    open_count = conn.execute("SELECT COUNT(*) FROM problems WHERE status='open'").fetchone()[0]
    print(f"\n  TOTAL: {total_count} problems ({open_count} open)")

    conn.close()

if __name__ == "__main__":
    main()
