#!/usr/bin/env python3
"""
Extract problem statements using Playwright for JavaScript-rendered sites.
"""

import sqlite3
import json
import asyncio
import re
from pathlib import Path
from playwright.async_api import async_playwright

DB_PATH = Path(__file__).parent / "problems.db"

async def extract_erdos_statement(page, problem_number):
    """Extract statement from erdosproblems.com using Playwright."""
    url = f"https://www.erdosproblems.com/{problem_number}"

    try:
        await page.goto(url, timeout=30000)
        await page.wait_for_load_state('networkidle', timeout=15000)

        # Wait longer for JS rendering
        await asyncio.sleep(3)

        # Try to wait for MathJax to finish
        try:
            await page.wait_for_function('typeof MathJax !== "undefined" && MathJax.startup && MathJax.startup.promise', timeout=5000)
            await asyncio.sleep(1)
        except:
            pass

        # Get the main content
        content = await page.content()

        # Extract text, preserving LaTeX
        text = await page.evaluate('''() => {
            // Find the main problem content
            const main = document.querySelector('main') || document.body;
            return main.innerText;
        }''')

        if not text:
            return None

        # Clean up the text
        lines = [l.strip() for l in text.split('\n') if l.strip()]

        # Find the problem statement - usually contains LaTeX ($...$)
        statement_lines = []
        in_problem = False

        for line in lines:
            # Skip navigation/header stuff
            if any(skip in line.lower() for skip in ['home', 'about', 'contact', 'search', 'login']):
                continue
            if line.startswith('Problem #') or line.startswith('Erdős'):
                in_problem = True
                continue
            if 'Additional info' in line or 'References' in line:
                break
            if in_problem and len(line) > 10:
                statement_lines.append(line)
                if len(statement_lines) >= 5:  # Limit to first 5 substantial lines
                    break

        if statement_lines:
            statement = ' '.join(statement_lines)
            # Clean up
            statement = re.sub(r'\s+', ' ', statement).strip()
            return statement[:2000]

        return None

    except Exception as e:
        print(f"  Error: {e}")
        return None

def analyze_statement(statement):
    """Analyze statement for tractability features."""
    if not statement:
        return {}, 50

    text_lower = statement.lower()

    features = {
        'is_bounded': any(x in text_lower for x in ['n ≤', 'n <', 'finite', 'bounded', 'n =']),
        'is_sidon': 'sidon' in text_lower,
        'is_graph': any(x in text_lower for x in ['graph', 'vertex', 'edge', 'coloring']),
        'is_combinatorial': any(x in text_lower for x in ['set', 'subset', 'sequence']),
        'has_explicit_bound': bool(re.search(r'\d+', statement)),
        'is_asymptotic': any(x in text_lower for x in ['asymptotic', 'o(1)', 'sufficiently large']),
    }

    # Calculate score
    score = 50
    if features['is_bounded']: score += 15
    if features['is_sidon']: score += 20  # Sidon sets work well
    if features['is_graph']: score += 15
    if features['is_combinatorial']: score += 10
    if features['has_explicit_bound']: score += 10
    if features['is_asymptotic']: score -= 10
    if len(statement) > 100: score += 10  # Good statement quality

    return features, min(100, max(0, score))

async def main(limit=50):
    """Main extraction pipeline."""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    print("=" * 70)
    print("PLAYWRIGHT STATEMENT EXTRACTION")
    print("=" * 70)

    # Get Erdős problems without good statements
    cursor = conn.execute("""
        SELECT id, source_id, name, tractability_score
        FROM problems
        WHERE source = 'erdos'
        AND status = 'open'
        AND (statement IS NULL OR statement LIKE '%fetch%' OR length(statement) < 50)
        ORDER BY tractability_score DESC
        LIMIT ?
    """, (limit,))

    problems = list(cursor)
    print(f"\nFound {len(problems)} Erdős problems to extract\n")

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        page = await browser.new_page()

        extracted = 0
        for i, row in enumerate(problems, 1):
            print(f"[{i}/{len(problems)}] Erdős #{row['source_id']}...", end=' ', flush=True)

            statement = await extract_erdos_statement(page, row['source_id'])

            if statement and len(statement) > 50 and 'fetch' not in statement.lower():
                features, score = analyze_statement(statement)

                conn.execute("""
                    UPDATE problems
                    SET statement = ?,
                        tractability_score = ?,
                        notes = ?
                    WHERE id = ?
                """, (statement, score, json.dumps(features), row['id']))

                print(f"✓ ({len(statement)} chars, score: {score})")
                extracted += 1
            else:
                print("✗")

            await asyncio.sleep(0.5)  # Be nice

        await browser.close()

    conn.commit()

    print("\n" + "=" * 70)
    print(f"COMPLETE: {extracted}/{len(problems)} statements extracted")
    print("=" * 70)

    # Show top problems now
    cursor = conn.execute("""
        SELECT source_id, tractability_score, substr(statement, 1, 80) as stmt
        FROM problems
        WHERE source = 'erdos' AND statement IS NOT NULL AND length(statement) > 50
        ORDER BY tractability_score DESC
        LIMIT 10
    """)

    print("\nTop 10 Erdős problems by new score:")
    for row in cursor:
        print(f"  #{row['source_id']:4} | Score: {row['tractability_score']:3} | {row['stmt']}...")

    conn.close()
    return extracted

if __name__ == "__main__":
    import sys
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    asyncio.run(main(limit))
