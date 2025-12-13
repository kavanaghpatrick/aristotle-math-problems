#!/usr/bin/env python3
"""
Batch extract statements using simple HTTP + better parsing.
For erdosproblems.com, we need to handle the API directly.
"""

import sqlite3
import json
import time
import re
from pathlib import Path
from urllib.request import urlopen, Request
from urllib.error import URLError

DB_PATH = Path(__file__).parent / "problems.db"

def fetch_erdos_api(problem_number):
    """Fetch from erdosproblems.com API if available."""
    # Try the API endpoint
    api_url = f"https://www.erdosproblems.com/api/problem/{problem_number}"

    headers = {
        'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7)',
        'Accept': 'application/json',
    }

    try:
        req = Request(api_url, headers=headers)
        with urlopen(req, timeout=15) as response:
            data = json.loads(response.read().decode('utf-8'))
            return data
    except:
        return None

def fetch_erdos_html(problem_number):
    """Fetch and parse HTML from erdosproblems.com."""
    url = f"https://www.erdosproblems.com/{problem_number}"

    headers = {
        'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7)',
        'Accept': 'text/html',
    }

    try:
        req = Request(url, headers=headers)
        with urlopen(req, timeout=15) as response:
            html = response.read().decode('utf-8')

            # Look for the content div - this is where the problem statement is
            content_match = re.search(r'<div id="content">(.+?)</div>', html, re.DOTALL)
            if content_match:
                content = content_match.group(1)
                # Clean up HTML entities
                content = content.replace('&#62;', '>')
                content = content.replace('&#60;', '<')
                content = content.replace('&gt;', '>')
                content = content.replace('&lt;', '<')
                # Remove HTML tags but keep LaTeX
                content = re.sub(r'<[^>]+>', '', content)
                content = re.sub(r'\s+', ' ', content).strip()
                return {'statement': content}

            return None
    except Exception as e:
        return None

def extract_statement_from_data(data):
    """Extract problem statement from API/JSON data."""
    if not data:
        return None

    # Try different field names
    for field in ['statement', 'content', 'description', 'text', 'body', 'problem']:
        if field in data:
            val = data[field]
            if isinstance(val, str) and len(val) > 20:
                return val
            elif isinstance(val, dict):
                # Recurse
                result = extract_statement_from_data(val)
                if result:
                    return result

    return None

def analyze_statement(statement):
    """Analyze statement for tractability."""
    if not statement:
        return {}, 50

    text_lower = statement.lower()

    features = {
        'is_sidon': 'sidon' in text_lower,
        'is_graph': any(x in text_lower for x in ['graph', 'vertex', 'edge']),
        'is_coloring': 'color' in text_lower,
        'is_ramsey': 'ramsey' in text_lower,
        'is_bounded': any(x in text_lower for x in ['bounded', 'finite', 'n ≤', 'n <']),
        'is_combinatorial': any(x in text_lower for x in ['set', 'subset', 'sequence']),
        'has_explicit_n': bool(re.search(r'n\s*[=<≤]\s*\d+', text_lower)),
        'is_prime': 'prime' in text_lower,
        'is_asymptotic': any(x in text_lower for x in ['asymptotic', 'infinity', 'all sufficiently']),
    }

    score = 55
    if features['is_sidon']: score += 20
    if features['is_graph']: score += 15
    if features['is_coloring']: score += 10
    if features['is_ramsey']: score += 15
    if features['is_bounded']: score += 15
    if features['is_combinatorial']: score += 10
    if features['has_explicit_n']: score += 10
    if features['is_prime']: score -= 10
    if features['is_asymptotic']: score -= 10
    if len(statement) > 100: score += 5

    return features, min(100, max(0, score))

def main(limit=100):
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    print("=" * 70)
    print("BATCH STATEMENT EXTRACTION")
    print("=" * 70)

    # Get problems needing extraction
    cursor = conn.execute("""
        SELECT id, source, source_id, name, tractability_score
        FROM problems
        WHERE source = 'erdos'
        AND status = 'open'
        AND (statement IS NULL OR statement LIKE '%fetch%' OR statement LIKE '%innerHTML%')
        ORDER BY tractability_score DESC
        LIMIT ?
    """, (limit,))

    problems = list(cursor)
    print(f"\nFound {len(problems)} problems needing extraction\n")

    extracted = 0
    for i, row in enumerate(problems, 1):
        print(f"[{i}/{len(problems)}] #{row['source_id']}...", end=' ', flush=True)

        # Try API first
        data = fetch_erdos_api(row['source_id'])
        if not data:
            data = fetch_erdos_html(row['source_id'])

        statement = extract_statement_from_data(data)

        if statement and len(statement) > 30:
            features, score = analyze_statement(statement)

            conn.execute("""
                UPDATE problems
                SET statement = ?,
                    tractability_score = ?,
                    notes = ?
                WHERE id = ?
            """, (statement[:2000], score, json.dumps(features), row['id']))

            print(f"✓ ({len(statement)} chars, score: {score})")
            extracted += 1
        else:
            print("✗")

        time.sleep(0.3)

    conn.commit()

    print(f"\n{'=' * 70}")
    print(f"COMPLETE: {extracted}/{len(problems)} extracted")
    print("=" * 70)

    # Stats
    stats = conn.execute("""
        SELECT
            COUNT(*) as total,
            SUM(CASE WHEN statement IS NOT NULL AND statement NOT LIKE '%fetch%' AND length(statement) > 50 THEN 1 ELSE 0 END) as good
        FROM problems WHERE source = 'erdos'
    """).fetchone()

    print(f"\nErdős statement coverage: {stats['good']}/{stats['total']} ({stats['good']/stats['total']*100:.1f}%)")

    conn.close()
    return extracted

if __name__ == "__main__":
    import sys
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    main(limit)
