#!/usr/bin/env python3
"""
Query tools for the unified problems database.

Usage:
    python query_db.py stats                    # Show statistics
    python query_db.py top [N]                  # Top N candidates (default 20)
    python query_db.py search "term"            # Search problems
    python query_db.py domain "graph theory"    # Filter by domain
    python query_db.py export csv               # Export to CSV
    python query_db.py ready                    # Ready to submit
    python query_db.py lean "erdos-124"         # Get Lean content
"""

import sqlite3
import sys
import json
import csv
from pathlib import Path

DB_PATH = Path(__file__).parent / "problems.db"

def connect():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn

def stats():
    """Show database statistics."""
    conn = connect()

    print("="*60)
    print("DATABASE STATISTICS")
    print("="*60)

    # Overall counts
    total = conn.execute("SELECT COUNT(*) FROM problems").fetchone()[0]
    open_count = conn.execute("SELECT COUNT(*) FROM problems WHERE status='open'").fetchone()[0]
    lean4 = conn.execute("SELECT COUNT(*) FROM problems WHERE has_lean4=1").fetchone()[0]
    open_lean4 = conn.execute("SELECT COUNT(*) FROM problems WHERE status='open' AND has_lean4=1").fetchone()[0]
    submitted = conn.execute("SELECT COUNT(*) FROM problems WHERE submitted_to_aristotle=1").fetchone()[0]

    print(f"\nTotal problems: {total}")
    print(f"Open problems: {open_count}")
    print(f"With Lean 4: {lean4}")
    print(f"Open + Lean 4: {open_lean4} ⭐")
    print(f"Already submitted: {submitted}")

    # By source
    print("\nBy source:")
    for row in conn.execute("""
        SELECT source,
               COUNT(*) as total,
               SUM(CASE WHEN status='open' THEN 1 ELSE 0 END) as open,
               SUM(CASE WHEN has_lean4=1 THEN 1 ELSE 0 END) as lean4
        FROM problems GROUP BY source ORDER BY total DESC
    """):
        print(f"  {row['source']:20} | Total: {row['total']:5} | Open: {row['open']:5} | Lean4: {row['lean4']:4}")

    # By domain
    print("\nBy domain (top 10):")
    for row in conn.execute("""
        SELECT domain, COUNT(*) as cnt
        FROM problems
        WHERE domain IS NOT NULL AND domain != ''
        GROUP BY domain ORDER BY cnt DESC LIMIT 10
    """):
        print(f"  {row['domain']:20} | {row['cnt']:5}")

    # Tractability distribution
    print("\nTractability distribution:")
    for row in conn.execute("""
        SELECT
            CASE
                WHEN tractability_score >= 90 THEN '90-100'
                WHEN tractability_score >= 80 THEN '80-89'
                WHEN tractability_score >= 70 THEN '70-79'
                WHEN tractability_score >= 60 THEN '60-69'
                ELSE '<60'
            END as bracket,
            COUNT(*) as cnt
        FROM problems
        WHERE status='open' AND has_lean4=1
        GROUP BY bracket
        ORDER BY bracket DESC
    """):
        print(f"  {row['bracket']:10} | {row['cnt']:4}")

    conn.close()

def top(n=20):
    """Show top N candidates."""
    conn = connect()

    print(f"\nTOP {n} CANDIDATES (Open + Lean 4)")
    print("="*80)
    print(f"{'#':3} {'Source':8} {'ID':10} {'Score':5} {'Prize':7} {'Domain':15} {'Name':30}")
    print("-"*80)

    cursor = conn.execute("""
        SELECT source, source_id, name, tractability_score, prize_amount, domain
        FROM problems
        WHERE status = 'open' AND has_lean4 = 1 AND submitted_to_aristotle = 0
        ORDER BY tractability_score DESC, prize_amount ASC
        LIMIT ?
    """, (n,))

    for i, row in enumerate(cursor, 1):
        prize = f"${row['prize_amount']}" if row['prize_amount'] else "-"
        name = (row['name'] or '')[:30]
        print(f"{i:3} {row['source']:8} {row['source_id'] or '-':10} "
              f"{row['tractability_score']:5} {prize:7} {(row['domain'] or '-')[:15]:15} {name}")

    conn.close()

def search(term):
    """Search problems by name or content."""
    conn = connect()

    print(f"\nSEARCH RESULTS: '{term}'")
    print("="*60)

    cursor = conn.execute("""
        SELECT source, source_id, name, status, has_lean4, tractability_score
        FROM problems
        WHERE name LIKE ? OR statement LIKE ? OR notes LIKE ?
        ORDER BY tractability_score DESC
        LIMIT 50
    """, (f'%{term}%', f'%{term}%', f'%{term}%'))

    results = list(cursor)
    print(f"Found {len(results)} results\n")

    for row in results:
        lean = "✓" if row['has_lean4'] else " "
        print(f"[{row['source']}] {row['source_id'] or row['name'][:30]:30} "
              f"| {row['status']:10} | Lean4:{lean} | Score:{row['tractability_score']}")

    conn.close()

def by_domain(domain):
    """Filter by domain."""
    conn = connect()

    print(f"\nPROBLEMS IN DOMAIN: '{domain}'")
    print("="*60)

    cursor = conn.execute("""
        SELECT source, source_id, name, status, has_lean4, tractability_score
        FROM problems
        WHERE domain LIKE ?
        ORDER BY tractability_score DESC
        LIMIT 50
    """, (f'%{domain}%',))

    results = list(cursor)
    print(f"Found {len(results)} results\n")

    for row in results:
        lean = "✓" if row['has_lean4'] else " "
        print(f"[{row['source']}] {row['source_id'] or row['name'][:30]:30} "
              f"| {row['status']:10} | Lean4:{lean} | Score:{row['tractability_score']}")

    conn.close()

def export_csv(filename="problems_export.csv"):
    """Export to CSV."""
    conn = connect()

    cursor = conn.execute("""
        SELECT source, source_id, name, status, has_lean4, tractability_score,
               domain, prize_amount, lean_file_path
        FROM problems
        ORDER BY tractability_score DESC
    """)

    output_path = Path(__file__).parent / filename

    with open(output_path, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['source', 'source_id', 'name', 'status', 'has_lean4',
                        'tractability_score', 'domain', 'prize_amount', 'lean_file_path'])
        for row in cursor:
            writer.writerow(list(row))

    print(f"✓ Exported to {output_path}")
    conn.close()

def ready():
    """Show problems ready to submit."""
    conn = connect()

    print("\nREADY TO SUBMIT (Open + Lean 4 + Not Submitted)")
    print("="*60)

    cursor = conn.execute("""
        SELECT source, source_id, name, tractability_score, lean_file_path
        FROM problems
        WHERE status = 'open'
          AND has_lean4 = 1
          AND submitted_to_aristotle = 0
        ORDER BY tractability_score DESC
        LIMIT 30
    """)

    results = list(cursor)
    print(f"Found {len(results)} problems ready to submit\n")

    for i, row in enumerate(results[:20], 1):
        path = Path(row['lean_file_path']).name if row['lean_file_path'] else '-'
        print(f"{i:3}. [{row['source']}] {row['source_id'] or row['name'][:25]:25} "
              f"| Score:{row['tractability_score']:3} | {path}")

    conn.close()

def get_lean(slug):
    """Get Lean content for a problem."""
    conn = connect()

    cursor = conn.execute("""
        SELECT name, lean_content, lean_file_path
        FROM problems
        WHERE slug = ? OR source_id = ?
    """, (slug, slug))

    row = cursor.fetchone()
    if row:
        print(f"\n=== {row['name']} ===")
        print(f"File: {row['lean_file_path']}")
        print("\n" + "="*60 + "\n")
        print(row['lean_content'] or "No Lean content available")
    else:
        print(f"Problem not found: {slug}")

    conn.close()

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return

    cmd = sys.argv[1]

    if cmd == 'stats':
        stats()
    elif cmd == 'top':
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 20
        top(n)
    elif cmd == 'search':
        search(sys.argv[2] if len(sys.argv) > 2 else '')
    elif cmd == 'domain':
        by_domain(sys.argv[2] if len(sys.argv) > 2 else '')
    elif cmd == 'export':
        fmt = sys.argv[2] if len(sys.argv) > 2 else 'csv'
        if fmt == 'csv':
            export_csv()
    elif cmd == 'ready':
        ready()
    elif cmd == 'lean':
        get_lean(sys.argv[2] if len(sys.argv) > 2 else '')
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)

if __name__ == "__main__":
    main()
