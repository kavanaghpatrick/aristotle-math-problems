#!/usr/bin/env python3
"""
Extract statements from ALL sources.
Check progress: tail -f extraction_progress.log
"""

import sqlite3
import json
import time
import re
from pathlib import Path
from urllib.request import urlopen, Request
from datetime import datetime

DB_PATH = Path(__file__).parent / "problems.db"
PROGRESS_FILE = Path(__file__).parent / "extraction_progress.log"

def log(msg):
    timestamp = datetime.now().strftime("%H:%M:%S")
    line = f"[{timestamp}] {msg}"
    print(line, flush=True)
    with open(PROGRESS_FILE, 'a') as f:
        f.write(line + '\n')

def fetch_url(url, timeout=15):
    headers = {'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7)'}
    try:
        req = Request(url, headers=headers)
        with urlopen(req, timeout=timeout) as response:
            return response.read().decode('utf-8', errors='ignore')
    except:
        return None

# ============================================================
# ERDŐS
# ============================================================
def extract_erdos(problem_id):
    html = fetch_url(f"https://www.erdosproblems.com/{problem_id}")
    if not html:
        return None
    match = re.search(r'<div id="content">(.+?)</div>', html, re.DOTALL)
    if match:
        content = match.group(1)
        content = content.replace('&#62;', '>').replace('&#60;', '<')
        content = re.sub(r'<[^>]+>', '', content)
        return re.sub(r'\s+', ' ', content).strip()
    return None

# ============================================================
# MATHOVERFLOW (Stack Exchange API)
# ============================================================
def extract_mathoverflow(question_id):
    url = f"https://api.stackexchange.com/2.3/questions/{question_id}?site=mathoverflow&filter=withbody"
    html = fetch_url(url)
    if not html:
        return None
    try:
        data = json.loads(html)
        items = data.get('items', [])
        if items:
            body = items[0].get('body', '')
            # Strip HTML
            text = re.sub(r'<[^>]+>', ' ', body)
            text = re.sub(r'\s+', ' ', text).strip()
            return text[:2000] if len(text) > 50 else None
    except:
        pass
    return None

# ============================================================
# OPEN PROBLEM GARDEN
# ============================================================
def extract_opg(urls_json):
    try:
        urls = json.loads(urls_json) if urls_json else []
        if not urls:
            return None
        url = urls[0]
        if not url.startswith('http'):
            url = 'http://www.openproblemgarden.org' + url
    except:
        return None

    html = fetch_url(url)
    if not html:
        return None

    # Look for problem statement in various patterns
    patterns = [
        r'<div class="problem-statement">(.*?)</div>',
        r'<div class="content">(.*?)</div>',
        r'<p>(.*?)</p>',
    ]

    for pattern in patterns:
        match = re.search(pattern, html, re.DOTALL | re.IGNORECASE)
        if match:
            text = match.group(1)
            text = re.sub(r'<[^>]+>', ' ', text)
            text = re.sub(r'\s+', ' ', text).strip()
            if len(text) > 50:
                return text[:2000]

    # Fallback: get body text
    body = re.sub(r'<script.*?</script>', '', html, flags=re.DOTALL)
    body = re.sub(r'<style.*?</style>', '', body, flags=re.DOTALL)
    body = re.sub(r'<[^>]+>', ' ', body)
    body = re.sub(r'\s+', ' ', body).strip()

    # Find substantial text
    if len(body) > 200:
        return body[100:600]  # Skip header, get middle content
    return None

# ============================================================
# WIKIPEDIA
# ============================================================
def extract_wikipedia(urls_json):
    try:
        urls = json.loads(urls_json) if urls_json else []
        if not urls:
            return None
        url = urls[0]
        # Convert to API URL
        if '/wiki/' in url:
            title = url.split('/wiki/')[-1]
            api_url = f"https://en.wikipedia.org/api/rest_v1/page/summary/{title}"
    except:
        return None

    html = fetch_url(api_url)
    if not html:
        return None

    try:
        data = json.loads(html)
        extract = data.get('extract', '')
        if len(extract) > 50:
            return extract[:2000]
    except:
        pass
    return None

# ============================================================
# OEIS
# ============================================================
def extract_oeis(seq_id):
    url = f"https://oeis.org/search?q=id:{seq_id}&fmt=json"
    html = fetch_url(url)
    if not html:
        return None
    try:
        data = json.loads(html)
        if isinstance(data, list) and data:
            seq = data[0]
            name = seq.get('name', '')
            comments = seq.get('comment', [])
            conj_comments = [c for c in comments if 'conjecture' in c.lower()]
            if conj_comments:
                return f"{name}. {' '.join(conj_comments[:2])}"[:2000]
            return name[:500] if name else None
    except:
        pass
    return None

# ============================================================
# SCORING
# ============================================================
def calculate_score(statement, source):
    if not statement:
        return 50

    text = statement.lower()
    score = 55

    # Positive signals
    if 'sidon' in text: score += 20
    if any(x in text for x in ['graph', 'vertex', 'edge']): score += 15
    if 'ramsey' in text: score += 15
    if 'color' in text: score += 10
    if any(x in text for x in ['bounded', 'finite']): score += 15
    if any(x in text for x in ['set', 'subset', 'sequence']): score += 10
    if len(statement) > 100: score += 5

    # Negative signals
    if 'prime' in text and 'twin' in text: score -= 15
    if any(x in text for x in ['riemann', 'zeta']): score -= 20
    if any(x in text for x in ['asymptotic', 'infinity', 'all sufficiently']): score -= 10

    return min(100, max(0, score))

# ============================================================
# MAIN
# ============================================================
def main():
    with open(PROGRESS_FILE, 'a') as f:
        f.write(f"\n{'='*60}\n")
        f.write(f"=== ALL SOURCES EXTRACTION {datetime.now()} ===\n")
        f.write(f"{'='*60}\n\n")

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    # Get problems by source
    sources = {
        'erdos': extract_erdos,
        'mathoverflow': extract_mathoverflow,
        'opg': extract_opg,
        'wikipedia': extract_wikipedia,
        'oeis': extract_oeis,
    }

    for source_name, extractor in sources.items():
        log(f"\n{'='*50}")
        log(f"SOURCE: {source_name.upper()}")
        log(f"{'='*50}")

        # Get problems needing extraction
        cursor = conn.execute("""
            SELECT id, source_id, urls, name
            FROM problems
            WHERE source = ?
            AND (statement IS NULL OR length(statement) < 50
                 OR statement LIKE '%fetch%' OR statement LIKE '%innerHTML%')
            ORDER BY tractability_score DESC
        """, (source_name,))

        problems = list(cursor)
        if not problems:
            log(f"  No problems to extract")
            continue

        log(f"  {len(problems)} problems to extract")

        extracted = 0
        for i, row in enumerate(problems, 1):
            # Extract based on source type
            if source_name == 'erdos':
                statement = extractor(row['source_id'])
            elif source_name in ['opg', 'wikipedia']:
                statement = extractor(row['urls'])
            elif source_name == 'mathoverflow':
                statement = extractor(row['source_id'])
            elif source_name == 'oeis':
                statement = extractor(row['source_id'])
            else:
                statement = None

            if statement and len(statement) > 30:
                score = calculate_score(statement, source_name)
                conn.execute("""
                    UPDATE problems SET statement = ?, tractability_score = ?
                    WHERE id = ?
                """, (statement[:2000], score, row['id']))
                extracted += 1

            # Progress every 20
            if i % 20 == 0:
                log(f"  Progress: {i}/{len(problems)} | Extracted: {extracted}")

            time.sleep(0.3)

        conn.commit()
        log(f"  DONE: {extracted}/{len(problems)} extracted")

    conn.close()

    # Final summary
    log(f"\n{'='*60}")
    log("FINAL COVERAGE")
    log(f"{'='*60}")

    conn = sqlite3.connect(DB_PATH)
    cursor = conn.execute("""
        SELECT source,
               COUNT(*) as total,
               SUM(CASE WHEN statement IS NOT NULL AND length(statement) > 50 THEN 1 ELSE 0 END) as with_stmt
        FROM problems GROUP BY source
    """)

    for row in cursor:
        pct = (row[2] / row[1] * 100) if row[1] > 0 else 0
        log(f"  {row[0]:20} | {row[2]:4}/{row[1]:4} ({pct:.1f}%)")

    conn.close()

if __name__ == "__main__":
    main()
