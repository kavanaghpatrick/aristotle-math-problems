#!/usr/bin/env python3
"""
Statement Extraction Pipeline
Use LLMs to extract problem statements for the database.
"""

import sqlite3
import json
import time
import re
import asyncio
from pathlib import Path
from urllib.request import urlopen, Request
from urllib.error import URLError
from concurrent.futures import ThreadPoolExecutor

DB_PATH = Path(__file__).parent / "problems.db"

# Known problem statement sources
ERDOS_BASE = "https://www.erdosproblems.com/"
OPG_BASE = "http://www.openproblemgarden.org"
OEIS_BASE = "https://oeis.org/"

def fetch_url(url, timeout=30):
    """Fetch URL with proper headers."""
    headers = {
        'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
    }
    req = Request(url, headers=headers)
    try:
        with urlopen(req, timeout=timeout) as response:
            return response.read().decode('utf-8', errors='ignore')
    except URLError as e:
        return None

def extract_erdos_statement(problem_number):
    """Extract statement from erdosproblems.com."""
    url = f"{ERDOS_BASE}{problem_number}"
    html = fetch_url(url)
    if not html:
        return None

    # Extract LaTeX content between $ signs
    latex_pattern = r'\$[^$]+\$'
    latex_matches = re.findall(latex_pattern, html, re.DOTALL)

    # Get main text content
    text = re.sub(r'<[^>]+>', ' ', html)
    text = re.sub(r'\s+', ' ', text)

    # Find problem statement section
    if 'Additional info' in text:
        main_text = text.split('Additional info')[0]
    else:
        main_text = text

    # Extract sentences with LaTeX
    sentences = main_text.split('.')
    problem_sentences = [s.strip() for s in sentences if '$' in s and len(s) > 20]

    if problem_sentences:
        statement = '. '.join(problem_sentences[:3]) + '.'
        statement = re.sub(r'\s+', ' ', statement)
        return statement[:2000]

    return None

def extract_oeis_statement(seq_id):
    """Extract statement from OEIS."""
    url = f"{OEIS_BASE}search?q=id:{seq_id}&fmt=json"
    html = fetch_url(url)
    if not html:
        return None

    try:
        data = json.loads(html)
        if isinstance(data, list) and len(data) > 0:
            seq = data[0]
            name = seq.get('name', '')
            comments = seq.get('comment', [])

            # Find conjecture-related comments
            conjecture_comments = [c for c in comments if 'conjecture' in c.lower() or 'open' in c.lower()]

            if conjecture_comments:
                statement = f"{name}. {' '.join(conjecture_comments[:2])}"
                return statement[:2000]
            elif name:
                return f"{name}. (Sequence definition)"
    except:
        pass

    return None

def extract_opg_statement(problem_url):
    """Extract statement from Open Problem Garden."""
    if not problem_url.startswith('http'):
        problem_url = OPG_BASE + problem_url

    html = fetch_url(problem_url)
    if not html:
        return None

    # Extract problem content
    text = re.sub(r'<[^>]+>', ' ', html)
    text = re.sub(r'\s+', ' ', text)

    # Look for problem keywords
    for pattern in [r'Problem[:\s]+([^\.]+\.)', r'Conjecture[:\s]+([^\.]+\.)']:
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            return match.group(1)[:2000]

    # Fallback: take first substantial paragraph
    paragraphs = [p.strip() for p in text.split('  ') if len(p.strip()) > 50]
    if paragraphs:
        return paragraphs[0][:2000]

    return None

def analyze_problem_structure(statement):
    """Extract structural features from problem statement."""
    if not statement:
        return {}

    text_lower = statement.lower()

    features = {
        # Boundedness indicators
        'is_bounded': any(x in text_lower for x in ['n ≤', 'n <', 'finite', 'bounded', 'n = ']),
        'is_infinite': any(x in text_lower for x in ['infinite', 'all n', 'arbitrary', 'sufficiently large']),

        # Problem type
        'is_constructive': any(x in text_lower for x in ['construct', 'find', 'exhibit', 'give an example']),
        'is_existential': any(x in text_lower for x in ['exists', 'there is', 'prove that']),
        'is_counting': any(x in text_lower for x in ['count', 'how many', 'number of']),

        # Mathematical structure
        'has_graph': any(x in text_lower for x in ['graph', 'vertex', 'edge', 'coloring']),
        'has_algebraic': any(x in text_lower for x in ['group', 'ring', 'field', 'algebra']),
        'has_combinatorial': any(x in text_lower for x in ['set', 'subset', 'sequence', 'combinat']),
        'has_number_theory': any(x in text_lower for x in ['prime', 'integer', 'divisor', 'modulo']),

        # Certificate verification potential
        'is_verification': any(x in text_lower for x in ['verify', 'check', 'certificate', 'witness']),

        # Complexity hints
        'mentions_bounds': bool(re.search(r'\d+', statement)),
        'has_latex': '$' in statement,
    }

    return features

def calculate_intelligent_score(problem, statement, features):
    """Calculate intelligent tractability score."""
    base_score = 50

    # Statement exists - major boost
    if statement and len(statement) > 50:
        base_score += 20

    # Bounded problems are more tractable
    if features.get('is_bounded') and not features.get('is_infinite'):
        base_score += 20
    elif features.get('is_infinite'):
        base_score -= 15

    # Constructive proofs are easier
    if features.get('is_constructive'):
        base_score += 10

    # Graph/combinatorial problems tend to work well
    if features.get('has_graph') or features.get('has_combinatorial'):
        base_score += 15

    # Certificate verification is our strength
    if features.get('is_verification'):
        base_score += 25

    # Number theory primes are hard
    if features.get('has_number_theory') and 'prime' in (statement or '').lower():
        base_score -= 10

    # Algebraic structure helps
    if features.get('has_algebraic'):
        base_score += 10

    return max(0, min(100, base_score))

def extract_and_enrich(problem_id, source, source_id, urls):
    """Extract statement and enrich problem."""
    statement = None

    # Try source-specific extraction
    if source == 'erdos':
        statement = extract_erdos_statement(source_id)
    elif source == 'oeis':
        statement = extract_oeis_statement(source_id)
    elif source == 'opg':
        if urls:
            try:
                url_list = json.loads(urls)
                if url_list:
                    statement = extract_opg_statement(url_list[0])
            except:
                pass

    features = analyze_problem_structure(statement)

    return statement, features

def main(limit=50, sources=None):
    """Main extraction pipeline."""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    print("=" * 70)
    print("STATEMENT EXTRACTION PIPELINE")
    print("=" * 70)

    # Find problems without statements
    query = """
        SELECT id, source, source_id, name, urls, tractability_score
        FROM problems
        WHERE (statement IS NULL OR statement = '')
        AND status = 'open'
    """

    if sources:
        placeholders = ','.join(['?' for _ in sources])
        query += f" AND source IN ({placeholders})"
        cursor = conn.execute(query + " ORDER BY tractability_score DESC LIMIT ?",
                            sources + [limit])
    else:
        cursor = conn.execute(query + " ORDER BY tractability_score DESC LIMIT ?", (limit,))

    problems = list(cursor)
    print(f"\nFound {len(problems)} problems without statements\n")

    extracted = 0
    for i, row in enumerate(problems, 1):
        print(f"[{i}/{len(problems)}] {row['source']}: {row['source_id'] or row['name'][:30]}...", end=' ')

        statement, features = extract_and_enrich(
            row['id'], row['source'], row['source_id'], row['urls']
        )

        if statement:
            # Calculate new score
            new_score = calculate_intelligent_score(row, statement, features)

            # Update database
            conn.execute("""
                UPDATE problems
                SET statement = ?,
                    tractability_score = ?,
                    notes = ?
                WHERE id = ?
            """, (statement, new_score, json.dumps(features), row['id']))

            print(f"✓ ({len(statement)} chars, score: {new_score})")
            extracted += 1
        else:
            print("✗ (no statement found)")

        time.sleep(0.5)  # Be nice to servers

    conn.commit()

    print("\n" + "=" * 70)
    print(f"EXTRACTION COMPLETE: {extracted}/{len(problems)} statements extracted")
    print("=" * 70)

    # Show statistics
    stats = conn.execute("""
        SELECT source,
               COUNT(*) as total,
               SUM(CASE WHEN statement IS NOT NULL AND statement != '' THEN 1 ELSE 0 END) as with_statement
        FROM problems
        GROUP BY source
    """).fetchall()

    print("\nStatement coverage by source:")
    for row in stats:
        pct = (row['with_statement'] / row['total'] * 100) if row['total'] > 0 else 0
        print(f"  {row['source']:20} | {row['with_statement']:4}/{row['total']:4} ({pct:.1f}%)")

    conn.close()

    return extracted

if __name__ == "__main__":
    import sys

    limit = 50
    sources = None

    if len(sys.argv) > 1:
        if '--top' in sys.argv:
            idx = sys.argv.index('--top')
            if idx + 1 < len(sys.argv):
                limit = int(sys.argv[idx + 1])

        if '--source' in sys.argv:
            idx = sys.argv.index('--source')
            if idx + 1 < len(sys.argv):
                sources = sys.argv[idx + 1].split(',')

    main(limit=limit, sources=sources)
