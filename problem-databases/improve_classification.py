#!/usr/bin/env python3
"""
Improve problem classification using statement analysis.
"""

import sqlite3
import re
from pathlib import Path

DB_PATH = Path(__file__).parent / "problems.db"

# Domain detection patterns
DOMAIN_PATTERNS = {
    'graph theory': [
        r'\bgraph\b', r'\bvertex\b', r'\bedge\b', r'\bchromatic\b',
        r'\bclique\b', r'\bindependent set\b', r'\btree\b', r'\bcycle\b',
        r'\bpath\b', r'\bcolou?ring\b', r'\bdegree\b', r'\bplanar\b'
    ],
    'number theory': [
        r'\bprime\b', r'\bdivisor\b', r'\binteger\b', r'\bmod(ulo)?\b',
        r'\bcongruence\b', r'\bdiophantine\b', r'\barithmetic\b',
        r'\bfactorization\b', r'\bgcd\b', r'\blcm\b'
    ],
    'combinatorics': [
        r'\bsidon\b', r'\bramsey\b', r'\bset\b', r'\bsubset\b',
        r'\bsequence\b', r'\bpermutation\b', r'\bcombination\b',
        r'\bpartition\b', r'\bcounting\b', r'\bbinomial\b',
        r'\bextremal\b', r'\bturán\b'
    ],
    'geometry': [
        r'\bpoint\b', r'\bline\b', r'\bplane\b', r'\bdistance\b',
        r'\bangle\b', r'\bconvex\b', r'\bpolygon\b', r'\bcircle\b',
        r'\bsphere\b', r'\btriangle\b', r'euclidean'
    ],
    'algebra': [
        r'\bgroup\b', r'\bring\b', r'\bfield\b', r'\bvector\b',
        r'\bmatrix\b', r'\blinear\b', r'\bpolynomial\b', r'\balgebra\b'
    ],
    'analysis': [
        r'\blimit\b', r'\bcontinuous\b', r'\bderivative\b', r'\bintegral\b',
        r'\bconvergence\b', r'\bseries\b', r'\bfunction\b', r'\bmeasure\b'
    ]
}

def classify_domain(statement):
    """Determine domain from statement text."""
    if not statement:
        return None

    text = statement.lower()
    scores = {}

    for domain, patterns in DOMAIN_PATTERNS.items():
        score = sum(1 for p in patterns if re.search(p, text, re.IGNORECASE))
        if score > 0:
            scores[domain] = score

    if not scores:
        return None

    # Return highest scoring domain
    return max(scores, key=scores.get)

def main():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    print("=" * 60)
    print("IMPROVING DOMAIN CLASSIFICATION")
    print("=" * 60)

    # Find problems with vague domains
    cursor = conn.execute("""
        SELECT id, source, source_id, domain, statement
        FROM problems
        WHERE domain IN ('various', 'research', '')
        AND statement IS NOT NULL
        AND length(statement) > 50
    """)

    problems = list(cursor)
    print(f"\nFound {len(problems)} problems with vague domains\n")

    updated = 0
    domain_counts = {}

    for row in problems:
        new_domain = classify_domain(row['statement'])

        if new_domain and new_domain != row['domain']:
            conn.execute("UPDATE problems SET domain = ? WHERE id = ?",
                        (new_domain, row['id']))
            domain_counts[new_domain] = domain_counts.get(new_domain, 0) + 1
            updated += 1

    conn.commit()

    print(f"Updated {updated} problems:")
    for domain, count in sorted(domain_counts.items(), key=lambda x: -x[1]):
        print(f"  {domain}: {count}")

    # Show remaining unclassified
    remaining = conn.execute("""
        SELECT COUNT(*) FROM problems
        WHERE domain IN ('various', 'research', '')
    """).fetchone()[0]

    print(f"\nRemaining unclassified: {remaining}")

    conn.close()

if __name__ == "__main__":
    main()
