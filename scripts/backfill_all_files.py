#!/usr/bin/env python3
"""Backfill ALL missing lean files (≤slot330) into tracking.db"""

import os
import re
import sqlite3

DB_PATH = "/Users/patrickkavanagh/math/submissions/tracking.db"
SUBMISSIONS_DIR = "/Users/patrickkavanagh/math/submissions/nu4_final"

def count_sorry_proven(filepath):
    """Count sorry and proven (theorem/lemma without sorry) in a lean file."""
    try:
        with open(filepath, 'r') as f:
            content = f.read()
    except:
        return None, None, ""

    sorry_count = len(re.findall(r'\bsorry\b', content))

    # Split by theorem/lemma boundaries and count blocks without sorry
    blocks = re.split(r'(?=\b(?:theorem|lemma)\s)', content)
    proven = 0
    for block in blocks:
        if re.search(r'\b(theorem|lemma)\s+\w+', block):
            if not re.search(r'\bsorry\b', block):
                proven += 1

    return sorry_count, proven, content

def extract_notes(content):
    """Extract notes from file header comments."""
    m = re.match(r'/[-*](.+?)[-*]/', content, re.DOTALL)
    if m:
        return m.group(1).strip()[:200]
    return None

def extract_fin_size(content):
    m = re.search(r'Fin\s+(\d+)', content)
    return int(m.group(1)) if m else None

def get_slot_num(filename):
    """Extract slot number from filename, or None."""
    m = re.match(r'slot(\d+)', filename)
    return int(m.group(1)) if m else None

def main():
    conn = sqlite3.connect(DB_PATH)

    # Get all filenames already in DB
    existing = set()
    for (fname,) in conn.execute("SELECT filename FROM submissions"):
        existing.add(fname)

    # Scan all lean files
    inserted = 0
    skipped = 0
    for fname in sorted(os.listdir(SUBMISSIONS_DIR)):
        if not fname.endswith('.lean'):
            continue

        if fname in existing:
            skipped += 1
            continue

        # Filter: only slots ≤ 330, or non-slot files
        slot_num = get_slot_num(fname)
        if slot_num is not None and slot_num > 330:
            continue

        filepath = os.path.join(SUBMISSIONS_DIR, fname)
        sorry_count, proven_count, content = count_sorry_proven(filepath)
        if content is None or content == "":
            continue

        pattern = 'scaffolded' if '_aristotle' in fname else None
        notes = extract_notes(content)
        fin_size = extract_fin_size(content)
        has_axiom = bool(re.search(r'^axiom\s', content, re.MULTILINE))

        # Determine status
        if sorry_count == 0 and proven_count and proven_count > 0 and not has_axiom:
            status = 'compiled_clean'
            verified = 1
        else:
            status = 'completed'
            verified = None
            if has_axiom:
                verified = 0
                notes = f"HAS AXIOMS. {notes}" if notes else "HAS AXIOMS"

        problem_id = fname.replace('.lean', '').replace('_aristotle', '')

        try:
            conn.execute("""
                INSERT INTO submissions
                (filename, problem_id, pattern, status,
                 sorry_count, proven_count, fin_size, frontier_id,
                 notes, verified)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                fname, problem_id, pattern, status,
                sorry_count, proven_count, fin_size, 'nu_4',
                notes, verified
            ))
            inserted += 1
            print(f"  {fname} [{status}] sorry={sorry_count} proven={proven_count}")
        except sqlite3.IntegrityError as e:
            print(f"  {fname} FAILED: {e}")

    conn.commit()
    total = conn.execute("SELECT COUNT(*) FROM submissions").fetchone()[0]
    print(f"\nInserted: {inserted}, Skipped (already exists): {skipped}")
    print(f"Total submissions in DB: {total}")
    conn.close()

if __name__ == '__main__':
    main()
