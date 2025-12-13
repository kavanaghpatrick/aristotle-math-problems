#!/usr/bin/env python3
"""
Fetch problem statements from erdosproblems.com and store in database.
"""

import sqlite3
import time
import re
from pathlib import Path
from urllib.request import urlopen, Request
from urllib.error import URLError
from html.parser import HTMLParser

DB_PATH = Path(__file__).parent / "problems.db"

class StatementParser(HTMLParser):
    """Extract problem statement from erdosproblems.com"""

    def __init__(self):
        super().__init__()
        self.in_problem = False
        self.statement_parts = []
        self.depth = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        # The problem statement is typically in a specific div
        if tag == 'div' and 'problem-statement' in attrs.get('class', ''):
            self.in_problem = True
            self.depth = 1
        elif self.in_problem:
            self.depth += 1

    def handle_endtag(self, tag):
        if self.in_problem:
            self.depth -= 1
            if self.depth == 0:
                self.in_problem = False

    def handle_data(self, data):
        if self.in_problem:
            self.statement_parts.append(data.strip())

    def get_statement(self):
        return ' '.join(self.statement_parts)

def fetch_statement(problem_number):
    """Fetch problem statement from erdosproblems.com"""
    url = f"https://www.erdosproblems.com/{problem_number}"

    headers = {
        'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36'
    }
    req = Request(url, headers=headers)

    try:
        with urlopen(req, timeout=30) as response:
            html = response.read().decode('utf-8', errors='ignore')

            # Try multiple extraction methods

            # Method 1: Look for MathJax/LaTeX content
            # The statement is usually in a specific pattern
            patterns = [
                r'<p[^>]*>(.*?)</p>',  # Paragraphs
                r'<div[^>]*problem[^>]*>(.*?)</div>',  # Problem divs
            ]

            # Simple extraction: find LaTeX-like content
            latex_pattern = r'\$[^$]+\$|\\\[.*?\\\]|\\\(.*?\\\)'
            latex_matches = re.findall(latex_pattern, html, re.DOTALL)

            # Get text content
            text = re.sub(r'<[^>]+>', ' ', html)
            text = re.sub(r'\s+', ' ', text)

            # Find the main problem text (usually after "Problem" and before "Additional info")
            if 'Additional info' in text:
                parts = text.split('Additional info')
                main_text = parts[0]
            else:
                main_text = text

            # Find sentence with "$" (LaTeX)
            sentences = main_text.split('.')
            problem_sentences = [s.strip() for s in sentences if '$' in s and len(s) > 20]

            if problem_sentences:
                statement = '. '.join(problem_sentences[:3]) + '.'
                # Clean up
                statement = re.sub(r'\s+', ' ', statement)
                return statement[:2000]  # Limit length

            return None

    except URLError as e:
        print(f"  Error fetching #{problem_number}: {e}")
        return None

def update_statements(problem_numbers=None, limit=50):
    """Fetch and update statements for problems."""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    if problem_numbers:
        # Specific problems
        placeholders = ','.join(['?' for _ in problem_numbers])
        cursor = conn.execute(f"""
            SELECT id, source_id FROM problems
            WHERE source = 'erdos' AND source_id IN ({placeholders})
            AND (statement IS NULL OR statement = '')
        """, problem_numbers)
    else:
        # High-priority problems without statements
        cursor = conn.execute("""
            SELECT id, source_id FROM problems
            WHERE source = 'erdos'
            AND (statement IS NULL OR statement = '')
            AND tractability_score >= 70
            ORDER BY tractability_score DESC
            LIMIT ?
        """, (limit,))

    problems = list(cursor)
    print(f"Fetching statements for {len(problems)} problems...")

    updated = 0
    for row in problems:
        num = row['source_id']
        print(f"  Fetching #{num}...", end=' ')

        statement = fetch_statement(num)

        if statement:
            conn.execute("""
                UPDATE problems SET statement = ? WHERE id = ?
            """, (statement, row['id']))
            print(f"OK ({len(statement)} chars)")
            updated += 1
        else:
            print("FAILED")

        time.sleep(0.5)  # Be nice to server

    conn.commit()
    conn.close()

    print(f"\n✓ Updated {updated}/{len(problems)} statements")

if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1:
        # Specific problem numbers
        nums = sys.argv[1:]
        update_statements(nums)
    else:
        # Top priority problems
        update_statements(limit=30)
