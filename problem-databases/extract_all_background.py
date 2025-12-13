#!/usr/bin/env python3
"""
Background statement extraction with progress tracking.
Run: python3 extract_all_background.py
Check progress: cat extraction_progress.log
"""

import sqlite3
import json
import time
import re
import sys
from pathlib import Path
from urllib.request import urlopen, Request
from datetime import datetime

DB_PATH = Path(__file__).parent / "problems.db"
PROGRESS_FILE = Path(__file__).parent / "extraction_progress.log"

def log_progress(msg):
    """Log to both console and file."""
    timestamp = datetime.now().strftime("%H:%M:%S")
    line = f"[{timestamp}] {msg}"
    print(line)
    with open(PROGRESS_FILE, 'a') as f:
        f.write(line + '\n')

def fetch_erdos_statement(problem_number):
    """Fetch from erdosproblems.com."""
    url = f"https://www.erdosproblems.com/{problem_number}"
    headers = {'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7)'}

    try:
        req = Request(url, headers=headers)
        with urlopen(req, timeout=15) as response:
            html = response.read().decode('utf-8')

            match = re.search(r'<div id="content">(.+?)</div>', html, re.DOTALL)
            if match:
                content = match.group(1)
                content = content.replace('&#62;', '>').replace('&#60;', '<')
                content = re.sub(r'<[^>]+>', '', content)
                content = re.sub(r'\s+', ' ', content).strip()
                return content if len(content) > 30 else None
    except:
        pass
    return None

def analyze_statement(statement):
    """Calculate tractability score."""
    if not statement:
        return {}, 50

    text = statement.lower()

    score = 55
    if 'sidon' in text: score += 20
    if any(x in text for x in ['graph', 'vertex', 'edge']): score += 15
    if 'ramsey' in text: score += 15
    if 'color' in text: score += 10
    if any(x in text for x in ['bounded', 'finite', 'n ≤']): score += 15
    if any(x in text for x in ['set', 'subset', 'sequence']): score += 10
    if bool(re.search(r'n\s*[=<≤]\s*\d+', text)): score += 10
    if 'prime' in text: score -= 10
    if any(x in text for x in ['asymptotic', 'infinity']): score -= 10
    if len(statement) > 100: score += 5

    return {}, min(100, max(0, score))

def main():
    # Clear progress file
    with open(PROGRESS_FILE, 'w') as f:
        f.write(f"=== EXTRACTION STARTED {datetime.now()} ===\n\n")

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    # Get all problems needing extraction
    cursor = conn.execute("""
        SELECT id, source, source_id, name, tractability_score
        FROM problems
        WHERE source = 'erdos'
        AND status = 'open'
        AND (statement IS NULL OR statement LIKE '%fetch%' OR statement LIKE '%innerHTML%' OR length(statement) < 50)
        ORDER BY tractability_score DESC
    """)

    problems = list(cursor)
    total = len(problems)

    log_progress(f"TOTAL TO EXTRACT: {total} problems")
    log_progress("-" * 50)

    extracted = 0
    failed = 0

    for i, row in enumerate(problems, 1):
        statement = fetch_erdos_statement(row['source_id'])

        if statement:
            features, score = analyze_statement(statement)
            conn.execute("""
                UPDATE problems SET statement = ?, tractability_score = ?, notes = ?
                WHERE id = ?
            """, (statement[:2000], score, json.dumps(features), row['id']))
            extracted += 1
            status = f"✓ score={score}"
        else:
            failed += 1
            status = "✗"

        # Progress update every 10 problems
        if i % 10 == 0 or i == total:
            pct = (i / total) * 100
            log_progress(f"PROGRESS: {i}/{total} ({pct:.1f}%) | Extracted: {extracted} | Failed: {failed}")

        # Commit every 50
        if i % 50 == 0:
            conn.commit()

        time.sleep(0.3)  # Rate limit

    conn.commit()
    conn.close()

    log_progress("=" * 50)
    log_progress(f"COMPLETE: {extracted}/{total} extracted ({extracted/total*100:.1f}%)")
    log_progress(f"Failed: {failed}")

    # Final stats
    conn = sqlite3.connect(DB_PATH)
    stats = conn.execute("""
        SELECT COUNT(*) as total,
               SUM(CASE WHEN statement IS NOT NULL AND length(statement) > 50 THEN 1 ELSE 0 END) as with_stmt
        FROM problems WHERE source = 'erdos'
    """).fetchone()
    conn.close()

    log_progress(f"COVERAGE: {stats[1]}/{stats[0]} ({stats[1]/stats[0]*100:.1f}%)")

if __name__ == "__main__":
    main()
