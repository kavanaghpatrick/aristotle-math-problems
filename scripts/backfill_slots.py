#!/usr/bin/env python3
"""Backfill missing slot entries into tracking.db"""

import os
import re
import sqlite3
import glob

DB_PATH = "/Users/patrickkavanagh/math/submissions/tracking.db"
SUBMISSIONS_DIR = "/Users/patrickkavanagh/math/submissions/nu4_final"

def get_existing_slots(conn):
    """Get set of slot numbers already in DB."""
    cursor = conn.execute(
        "SELECT DISTINCT filename FROM submissions WHERE filename LIKE 'slot%'"
    )
    existing = set()
    for (fname,) in cursor:
        m = re.match(r'slot(\d+)', fname)
        if m:
            existing.add(int(m.group(1)))
    return existing

def get_file_slots():
    """Get dict of slot_num -> list of files."""
    slots = {}
    for f in os.listdir(SUBMISSIONS_DIR):
        m = re.match(r'slot(\d+)', f)
        if m:
            slot_num = int(m.group(1))
            if slot_num not in slots:
                slots[slot_num] = []
            slots[slot_num].append(f)
    return slots

def count_sorry_proven(filepath):
    """Count sorry and proven (theorem/lemma without sorry) in a lean file."""
    try:
        with open(filepath, 'r') as f:
            content = f.read()
    except:
        return None, None

    sorry_count = len(re.findall(r'\bsorry\b', content))

    # Count theorem/lemma declarations
    declarations = re.findall(r'\b(theorem|lemma|def)\s+\w+', content)
    total_decls = len(declarations)

    # A rough proven count: total declarations minus sorry count
    # More accurate: count blocks that don't contain sorry
    # Split by theorem/lemma boundaries
    blocks = re.split(r'(?=\b(?:theorem|lemma)\s)', content)
    proven = 0
    for block in blocks:
        if re.search(r'\b(theorem|lemma)\s+\w+', block):
            if not re.search(r'\bsorry\b', block):
                proven += 1

    return sorry_count, proven

def extract_uuid(slot_num, files):
    """Try to find UUID from ID.txt file."""
    for f in files:
        if f.endswith('_ID.txt') or f.endswith('ID.txt'):
            try:
                path = os.path.join(SUBMISSIONS_DIR, f)
                with open(path) as fh:
                    content = fh.read().strip()
                    # UUID pattern
                    m = re.search(r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}', content)
                    if m:
                        return m.group(0)
            except:
                pass
    return None

def extract_problem_id(lean_content, slot_num, filename):
    """Extract problem_id from file content or filename."""
    # Try to extract from filename
    base = filename.replace('.lean', '').replace('_aristotle', '')
    return base

def extract_pattern(filename, lean_content):
    """Determine submission pattern."""
    if '_aristotle' in filename:
        return 'scaffolded'
    if 'safe_discard' in filename.lower():
        return 'safe_discard'
    if 'multi_agent' in lean_content.lower():
        return 'multi_agent_optimized'
    return None

def extract_notes(lean_content, filename):
    """Extract notes from file header comments."""
    # Get first comment block
    m = re.match(r'/[-*](.+?)[-*]/', lean_content, re.DOTALL)
    if m:
        header = m.group(1).strip()
        # Take first 200 chars
        return header[:200]
    return None

def determine_status(sorry_count, proven_count, has_uuid, lean_content):
    """Determine submission status."""
    if sorry_count is not None:
        if sorry_count == 0 and proven_count and proven_count > 0:
            # Check for axiom
            if re.search(r'^axiom\s', lean_content, re.MULTILINE):
                return 'completed'
            return 'proven'
        elif has_uuid:
            return 'completed'
        else:
            return 'completed'
    return 'draft'

def extract_fin_size(lean_content):
    """Extract Fin n size from content."""
    m = re.search(r'Fin\s+(\d+)', lean_content)
    if m:
        return int(m.group(1))
    return None

def main():
    conn = sqlite3.connect(DB_PATH)
    existing = get_existing_slots(conn)
    file_slots = get_file_slots()

    # Find missing slots <= 330
    missing = sorted([s for s in file_slots if s <= 330 and s not in existing])
    print(f"Found {len(missing)} missing slots to backfill")

    inserted = 0
    for slot_num in missing:
        files = file_slots[slot_num]
        lean_files = [f for f in files if f.endswith('.lean')]
        txt_files = [f for f in files if f.endswith('.txt') and not f.endswith('_ID.txt')]
        id_files = [f for f in files if f.endswith('_ID.txt') or f == f'slot{slot_num}_ID.txt']

        uuid = extract_uuid(slot_num, files)

        if not lean_files:
            # Only txt/ID files, skip or create minimal entry
            print(f"  Slot {slot_num}: no .lean files, skipping")
            continue

        # Process each lean file for this slot
        for lean_file in lean_files:
            lean_path = os.path.join(SUBMISSIONS_DIR, lean_file)
            try:
                with open(lean_path) as f:
                    content = f.read()
            except:
                print(f"  Slot {slot_num}: could not read {lean_file}")
                continue

            sorry_count, proven_count = count_sorry_proven(lean_path)
            pattern = extract_pattern(lean_file, content)
            notes = extract_notes(content, lean_file)
            fin_size = extract_fin_size(content)
            status = determine_status(sorry_count, proven_count, uuid is not None, content)
            problem_id = extract_problem_id(content, slot_num, lean_file)

            # Check for axioms - mark as incomplete
            has_axiom = bool(re.search(r'^axiom\s', content, re.MULTILINE))
            if has_axiom and status == 'proven':
                status = 'completed'
                if notes:
                    notes = f"HAS AXIOMS. {notes}"
                else:
                    notes = "HAS AXIOMS"

            # Determine verified status
            verified = None
            if status == 'proven' and sorry_count == 0:
                verified = 1
            elif has_axiom:
                verified = 0

            try:
                conn.execute("""
                    INSERT INTO submissions
                    (filename, uuid, problem_id, pattern, status,
                     sorry_count, proven_count, fin_size, frontier_id,
                     notes, verified)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    lean_file, uuid, problem_id, pattern, status,
                    sorry_count, proven_count, fin_size, 'nu_4',
                    notes, verified
                ))
                inserted += 1
                sorry_str = f"sorry={sorry_count}" if sorry_count is not None else "sorry=?"
                proven_str = f"proven={proven_count}" if proven_count is not None else "proven=?"
                print(f"  Slot {slot_num}: {lean_file} [{status}] {sorry_str} {proven_str}")
            except sqlite3.IntegrityError as e:
                # UUID conflict - set uuid to None and retry
                if 'uuid' in str(e).lower():
                    conn.execute("""
                        INSERT INTO submissions
                        (filename, problem_id, pattern, status,
                         sorry_count, proven_count, fin_size, frontier_id,
                         notes, verified)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, (
                        lean_file, problem_id, pattern, status,
                        sorry_count, proven_count, fin_size, 'nu_4',
                        notes, verified
                    ))
                    inserted += 1
                    print(f"  Slot {slot_num}: {lean_file} [{status}] (uuid conflict, inserted without)")
                else:
                    print(f"  Slot {slot_num}: {lean_file} FAILED: {e}")

    conn.commit()
    print(f"\nInserted {inserted} entries")

    # Summary
    total = conn.execute("SELECT COUNT(*) FROM submissions").fetchone()[0]
    print(f"Total submissions in DB: {total}")

    conn.close()

if __name__ == '__main__':
    main()
