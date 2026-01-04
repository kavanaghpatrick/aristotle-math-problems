#!/usr/bin/env python3
"""
Batch prepare ALL Erdős problem submissions, organized by priority tier.

Tier 1: Prize + falsifiable/verifiable (highest value, quick feedback)
Tier 2: Prize + any status (money on the table)
Tier 3: Falsifiable/verifiable + high tractability (Aristotle sweet spot)
Tier 4: Already proved/disproved in Lean (formalization tasks)
Tier 5: Research open + high tractability
Tier 6: Everything else

Usage:
    python3 batch_prepare_erdos.py --tier 1        # Prepare tier 1 only
    python3 batch_prepare_erdos.py --all           # Prepare all tiers
    python3 batch_prepare_erdos.py --stats         # Show tier statistics
"""

import argparse
import json
import os
import sqlite3
import urllib.request
from datetime import datetime
from pathlib import Path

DB_PATH = Path(__file__).parent.parent / "submissions" / "tracking.db"
OUTPUT_BASE = Path(__file__).parent.parent / "submissions" / "erdos"

TIER_QUERIES = {
    1: """
        -- Tier 1: Prize + falsifiable/verifiable
        SELECT DISTINCT ef.problem_number, ef.theorem_name, ef.category,
               ef.source_url, ef.lean_file, efu.status, efu.prize, efu.tractability_score
        FROM erdos_formal ef
        JOIN erdos_full efu ON ef.problem_number = efu.number
        WHERE ef.has_sorry = 1
          AND efu.prize IS NOT NULL AND efu.prize != 'no'
          AND efu.status IN ('falsifiable', 'verifiable')
        ORDER BY efu.tractability_score DESC
    """,
    2: """
        -- Tier 2: Prize + any status (excluding tier 1)
        SELECT DISTINCT ef.problem_number, ef.theorem_name, ef.category,
               ef.source_url, ef.lean_file, efu.status, efu.prize, efu.tractability_score
        FROM erdos_formal ef
        JOIN erdos_full efu ON ef.problem_number = efu.number
        WHERE ef.has_sorry = 1
          AND efu.prize IS NOT NULL AND efu.prize != 'no'
          AND efu.status NOT IN ('falsifiable', 'verifiable')
        ORDER BY efu.tractability_score DESC
    """,
    3: """
        -- Tier 3: Falsifiable/verifiable + high tractability (no prize, excluding already done)
        SELECT DISTINCT ef.problem_number, ef.theorem_name, ef.category,
               ef.source_url, ef.lean_file, efu.status, efu.prize, efu.tractability_score
        FROM erdos_formal ef
        JOIN erdos_full efu ON ef.problem_number = efu.number
        WHERE ef.has_sorry = 1
          AND (efu.prize IS NULL OR efu.prize = 'no')
          AND efu.status IN ('falsifiable', 'verifiable')
          AND efu.tractability_score >= 90
        ORDER BY efu.tractability_score DESC
    """,
    4: """
        -- Tier 4: Already proved/disproved (formalization tasks)
        SELECT DISTINCT ef.problem_number, ef.theorem_name, ef.category,
               ef.source_url, ef.lean_file, efu.status, efu.prize, efu.tractability_score
        FROM erdos_formal ef
        JOIN erdos_full efu ON ef.problem_number = efu.number
        WHERE ef.has_sorry = 1
          AND (efu.status LIKE '%proved%' OR efu.status LIKE '%Lean%')
        ORDER BY
            CASE WHEN efu.prize != 'no' THEN 0 ELSE 1 END,
            efu.tractability_score DESC
    """,
    5: """
        -- Tier 5: Research open + high tractability
        SELECT DISTINCT ef.problem_number, ef.theorem_name, ef.category,
               ef.source_url, ef.lean_file, efu.status, efu.prize, efu.tractability_score
        FROM erdos_formal ef
        JOIN erdos_full efu ON ef.problem_number = efu.number
        WHERE ef.has_sorry = 1
          AND ef.category LIKE '%research open%'
          AND efu.tractability_score >= 80
          AND efu.status NOT IN ('falsifiable', 'verifiable')
          AND efu.status NOT LIKE '%proved%'
        ORDER BY efu.tractability_score DESC
    """,
    6: """
        -- Tier 6: Everything else
        SELECT DISTINCT ef.problem_number, ef.theorem_name, ef.category,
               ef.source_url, ef.lean_file,
               COALESCE(efu.status, 'unknown') as status,
               COALESCE(efu.prize, 'no') as prize,
               COALESCE(efu.tractability_score, 50) as tractability_score
        FROM erdos_formal ef
        LEFT JOIN erdos_full efu ON ef.problem_number = efu.number
        WHERE ef.has_sorry = 1
          AND ef.problem_number NOT IN (
              SELECT DISTINCT problem_number FROM erdos_formal ef2
              JOIN erdos_full efu2 ON ef2.problem_number = efu2.number
              WHERE efu2.prize IS NOT NULL AND efu2.prize != 'no'
          )
          AND ef.problem_number NOT IN (
              SELECT DISTINCT problem_number FROM erdos_formal ef3
              JOIN erdos_full efu3 ON ef3.problem_number = efu3.number
              WHERE efu3.status IN ('falsifiable', 'verifiable')
                 OR efu3.status LIKE '%proved%'
                 OR efu3.status LIKE '%Lean%'
          )
        ORDER BY COALESCE(efu.tractability_score, 50) DESC
    """
}

TIER_DESCRIPTIONS = {
    1: "Prize + Falsifiable/Verifiable (HIGHEST VALUE)",
    2: "Prize + Other Status",
    3: "Falsifiable/Verifiable + High Tractability",
    4: "Already Proved/Disproved (Formalization)",
    5: "Research Open + High Tractability",
    6: "Everything Else"
}

def get_tier_stats(conn):
    """Get statistics for each tier."""
    stats = {}
    for tier, query in TIER_QUERIES.items():
        cursor = conn.cursor()
        cursor.execute(query)
        rows = cursor.fetchall()

        problems = set(r[0] for r in rows)
        prizes = [r[6] for r in rows if r[6] and r[6] != 'no']

        # Calculate total prize value
        prize_total = 0
        for p in prizes:
            if '$10000' in str(p): prize_total += 10000
            elif '$5000' in str(p): prize_total += 5000
            elif '$1000' in str(p): prize_total += 1000
            elif '$500' in str(p): prize_total += 500
            elif '$250' in str(p): prize_total += 250
            elif '$100' in str(p): prize_total += 100
            elif '£25' in str(p): prize_total += 25
            elif '$10' in str(p): prize_total += 10

        stats[tier] = {
            'description': TIER_DESCRIPTIONS[tier],
            'theorems': len(rows),
            'problems': len(problems),
            'prize_total': prize_total,
            'rows': rows
        }

    return stats

def add_informal_sketch(content: str, theorem_name: str, status: str) -> str:
    """Add informal proof sketch based on problem status."""

    if status in ('falsifiable', 'verifiable'):
        sketch_type = "VERIFICATION" if status == 'verifiable' else "FALSIFICATION"
        sketch = f"""/-
{sketch_type} SKETCH for {theorem_name}:
Status: {status} - Aristotle should {"verify this directly" if status == 'verifiable' else "find a counterexample on Fin 5-7"}

1. [If verifiable: describe why the statement is true]
2. [If falsifiable: describe expected counterexample structure]
3. [Key properties to check]
-/
"""
    elif 'proved' in status.lower() or 'lean' in status.lower():
        sketch = f"""/-
FORMALIZATION SKETCH for {theorem_name}:
Status: {status} - Proof exists, needs Lean formalization

1. [Reference the known proof]
2. [Key lemmas needed]
3. [Main proof technique]
-/
"""
    else:
        sketch = f"""/-
PROOF SKETCH for {theorem_name}:
Status: {status}

1. [Mathematical approach]
2. [Key lemmas or techniques]
3. [Why this leads to the result]
-/
"""

    # Insert before theorem/lemma declaration
    lines = content.split('\n')
    result = []
    inserted = False
    for line in lines:
        if not inserted and (f'theorem {theorem_name}' in line or f'lemma {theorem_name}' in line):
            result.append(sketch)
            inserted = True
        result.append(line)

    return '\n'.join(result)

def prepare_tier(conn, tier: int, dry_run: bool = False):
    """Prepare all submissions for a tier."""
    cursor = conn.cursor()
    cursor.execute(TIER_QUERIES[tier])
    rows = cursor.fetchall()

    if not rows:
        print(f"  No theorems in tier {tier}")
        return 0

    tier_dir = OUTPUT_BASE / f"tier{tier}"
    tier_dir.mkdir(parents=True, exist_ok=True)

    prepared = 0
    for row in rows:
        problem_num, theorem_name, category, source_url, lean_file, status, prize, tractability = row

        safe_name = theorem_name.replace('.', '_').replace(' ', '_')
        filename = f"erdos_{problem_num}_{safe_name}.lean"
        filepath = tier_dir / filename

        if filepath.exists():
            continue  # Skip already prepared

        if dry_run:
            print(f"    Would create: {filename}")
            prepared += 1
            continue

        # Use stored content
        content = lean_file
        if not content:
            print(f"    SKIP (no content): {theorem_name}")
            continue

        # Add sketch
        content = add_informal_sketch(content, theorem_name, status or 'unknown')

        # Write file
        header = f"""/-
Erdős Problem #{problem_num}: {theorem_name}
Tier: {tier} - {TIER_DESCRIPTIONS[tier]}
Status: {status} | Prize: {prize} | Tractability: {tractability}
Generated: {datetime.now().isoformat()}
-/

"""
        with open(filepath, 'w') as f:
            f.write(header + content)

        prepared += 1

    return prepared

def main():
    parser = argparse.ArgumentParser(description='Batch prepare Erdős submissions')
    parser.add_argument('--tier', '-t', type=int, choices=[1,2,3,4,5,6],
                       help='Prepare specific tier')
    parser.add_argument('--all', '-a', action='store_true',
                       help='Prepare all tiers')
    parser.add_argument('--stats', '-s', action='store_true',
                       help='Show tier statistics')
    parser.add_argument('--dry-run', '-n', action='store_true',
                       help='Show what would be created')
    args = parser.parse_args()

    conn = sqlite3.connect(DB_PATH)

    if args.stats or (not args.tier and not args.all):
        stats = get_tier_stats(conn)
        print("\n" + "="*70)
        print("ERDŐS PROBLEM SUBMISSION TIERS")
        print("="*70)

        total_theorems = 0
        total_problems = set()
        total_prize = 0

        for tier, data in stats.items():
            print(f"\nTier {tier}: {data['description']}")
            print(f"  Theorems: {data['theorems']:3d} | Problems: {data['problems']:3d} | Prize: ${data['prize_total']:,}")
            total_theorems += data['theorems']
            total_prize += data['prize_total']

        print("\n" + "-"*70)
        print(f"TOTAL: {total_theorems} theorems | ${total_prize:,} in prizes")
        print("="*70)

        if not args.tier and not args.all:
            print("\nUsage:")
            print("  python3 batch_prepare_erdos.py --tier 1     # Prepare tier 1")
            print("  python3 batch_prepare_erdos.py --all        # Prepare all")
            print("  python3 batch_prepare_erdos.py --dry-run -a # Preview all")
            conn.close()
            return

    if args.tier:
        print(f"\nPreparing Tier {args.tier}: {TIER_DESCRIPTIONS[args.tier]}")
        count = prepare_tier(conn, args.tier, args.dry_run)
        print(f"  {'Would prepare' if args.dry_run else 'Prepared'}: {count} files")
        print(f"  Output: submissions/erdos/tier{args.tier}/")

    if args.all:
        print("\nPreparing ALL tiers:")
        total = 0
        for tier in range(1, 7):
            print(f"\n  Tier {tier}: {TIER_DESCRIPTIONS[tier]}")
            count = prepare_tier(conn, tier, args.dry_run)
            print(f"    {'Would prepare' if args.dry_run else 'Prepared'}: {count} files")
            total += count
        print(f"\n  Total: {total} files")

    conn.close()

if __name__ == "__main__":
    main()
