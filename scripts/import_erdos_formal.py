#!/usr/bin/env python3
"""
Import formalized Erdős problems from Google DeepMind Formal Conjectures repo.
Extracts theorem statements and stores them in our tracking database.
"""

import json
import re
import sqlite3
import time
import urllib.request
from pathlib import Path

DB_PATH = Path(__file__).parent.parent / "submissions" / "tracking.db"
REPO_API = "https://api.github.com/repos/google-deepmind/formal-conjectures/contents/FormalConjectures/ErdosProblems"

def get_file_list():
    """Get list of all Erdős problem Lean files."""
    with urllib.request.urlopen(REPO_API) as response:
        data = json.load(response)
    return [(f['name'].replace('.lean', ''), f['download_url'])
            for f in data if f['name'].endswith('.lean')]

def fetch_file(url):
    """Fetch a single Lean file."""
    try:
        with urllib.request.urlopen(url) as response:
            return response.read().decode('utf-8')
    except Exception as e:
        print(f"Error fetching {url}: {e}")
        return None

def parse_lean_file(content, problem_num):
    """Extract theorem statements from Lean file."""
    theorems = []

    # Pattern to match theorem/lemma declarations with attributes
    # Matches: @[category ...] theorem name ... := by sorry
    pattern = r'''
        (?:@\[([^\]]+)\]\s*)*           # Optional attributes like @[category ...]
        (theorem|lemma)\s+               # theorem or lemma keyword
        ([\w.]+)\s*                      # theorem name (including dots for namespaces)
        ([^:]*:\s*[^:=]+)                # parameters and type signature
        \s*:=\s*by\s*                    # := by
        \s*(sorry|\{[^}]*\}|[\s\S]*?(?=\n\n|\n@|\nend|\Z))  # proof (sorry or actual)
    '''

    # Simpler pattern - just get theorem statements
    simple_pattern = r'(theorem|lemma)\s+([\w.]+)\s*([^:]*:\s*[^=]+):=\s*by'

    for match in re.finditer(simple_pattern, content, re.MULTILINE):
        kind = match.group(1)
        name = match.group(2)
        signature = match.group(3).strip()

        # Get the full statement including parameters
        full_statement = f"{kind} {name} {signature}"

        # Check for category attribute before this theorem
        # Look backwards from match start
        pre_content = content[:match.start()]
        category_match = re.search(r'@\[category\s+([^\]]+)\]', pre_content[-200:])
        category = category_match.group(1) if category_match else None

        # Check for AMS attribute
        ams_match = re.search(r'@\[AMS\s+(\d+)\]', pre_content[-200:])
        ams = ams_match.group(1) if ams_match else None

        # Check if it has sorry
        has_sorry = 'sorry' in content[match.start():match.end()+100]

        theorems.append({
            'problem_number': problem_num,
            'theorem_name': name,
            'category': category,
            'ams_code': ams,
            'statement': full_statement,
            'has_sorry': 1 if has_sorry else 0
        })

    return theorems

def import_to_db(theorems, lean_content, source_url, conn):
    """Import theorems to database."""
    cursor = conn.cursor()
    imported = 0

    for t in theorems:
        try:
            cursor.execute('''
                INSERT OR REPLACE INTO erdos_formal
                (problem_number, theorem_name, category, ams_code, statement, lean_file, source_url, has_sorry)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                t['problem_number'],
                t['theorem_name'],
                t['category'],
                t['ams_code'],
                t['statement'],
                lean_content,
                source_url,
                t['has_sorry']
            ))
            imported += 1
        except Exception as e:
            print(f"Error inserting {t['theorem_name']}: {e}")

    conn.commit()
    return imported

def main():
    print("Fetching Erdős problem file list...")
    files = get_file_list()
    print(f"Found {len(files)} Lean files")

    conn = sqlite3.connect(DB_PATH)
    total_imported = 0

    for i, (problem_num, url) in enumerate(files):
        if i % 20 == 0:
            print(f"Processing {i+1}/{len(files)}...")

        content = fetch_file(url)
        if not content:
            continue

        theorems = parse_lean_file(content, problem_num)
        if theorems:
            imported = import_to_db(theorems, content, url, conn)
            total_imported += imported

        # Rate limiting to avoid GitHub API limits
        time.sleep(0.1)

    conn.close()
    print(f"\nDone! Imported {total_imported} theorem statements from {len(files)} files")

if __name__ == "__main__":
    main()
