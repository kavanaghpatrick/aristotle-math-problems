#!/usr/bin/env python3
"""
Analyze problem TYPES to identify Aristotle's sweet spot.

Key insight: Boris used --informal mode (English → Lean → Solve)
So we should focus on PROBLEM TYPE matching Aristotle's strengths, not just existing formalizations.

Aristotle's proven strengths:
1. SAT/Certificate verification (SAT LRAT: SUCCESS)
2. Bounded combinatorics (Erdős #124: SUCCESS)
3. Well-founded recursion (HOMFLY v4: SUCCESS)
4. Algebraic structures

What failed:
1. Huge search spaces (Quantum Collision: TIMEOUT)
2. Over-specified approaches (HOMFLY v3: FAILED)
"""

import sqlite3
import json
from pathlib import Path
from collections import defaultdict

DB_PATH = Path(__file__).parent / "problems.db"

# Problem type indicators
STRONG_INDICATORS = {
    'sat_compatible': [
        'combinatorics', 'graph', 'coloring', 'clique', 'independent set',
        'ramsey', 'turán', 'extremal', 'covering', 'partition', 'matching',
        'hamiltonian', 'latin square', 'steiner', 'design'
    ],
    'bounded_search': [
        'finite', 'bounded', 'small', 'fixed parameter', 'polynomial',
        'n ≤', 'n <', 'order n', 'size k'
    ],
    'algebraic': [
        'sidon', 'additive', 'sumset', 'sum-free', 'arithmetic progression',
        'sequence', 'basis', 'representation', 'polynomial', 'algebraic'
    ],
    'certificate_verification': [
        'verify', 'certificate', 'witness', 'check', 'validation',
        'unsat', 'satisfiability'
    ]
}

WEAK_INDICATORS = {
    'potentially_intractable': [
        'prime', 'twin prime', 'goldbach', 'riemann', 'zeta',
        'infinity', 'asymptotic', 'all sufficiently large',
        'transcendental', 'irrational'
    ],
    'may_require_deep_theory': [
        'conjecture', 'fundamental', 'general', 'arbitrary',
        'continuous', 'analytic', 'holomorphic'
    ]
}

def calculate_type_score(problem_text, tags):
    """Calculate problem type compatibility score."""
    text = (problem_text or '').lower()
    tags_lower = [t.lower() for t in (tags or [])]
    combined = text + ' ' + ' '.join(tags_lower)

    score = 50  # Base score

    # Strong positive indicators
    for category, indicators in STRONG_INDICATORS.items():
        matches = sum(1 for ind in indicators if ind in combined)
        score += matches * 8

    # Weak/negative indicators
    for category, indicators in WEAK_INDICATORS.items():
        matches = sum(1 for ind in indicators if ind in combined)
        score -= matches * 5

    # Bonus for specific patterns
    if 'sidon' in combined:
        score += 15  # Sidon sets are very tractable
    if 'graph' in combined and ('color' in combined or 'chromatic' in combined):
        score += 10
    if 'distance' in combined and 'unit' in combined:
        score += 10
    if 'ramsey' in combined and any(f'r({i}' in combined for i in range(3, 7)):
        score += 15  # Small Ramsey numbers

    # Penalties
    if 'prime' in combined and 'twin' in combined:
        score -= 20
    if 'riemann' in combined or 'zeta' in combined:
        score -= 30

    return max(0, min(100, score))

def analyze_database():
    """Analyze all problems for type compatibility."""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    print("="*70)
    print("ANALYZING PROBLEM TYPES FOR ARISTOTLE COMPATIBILITY")
    print("="*70)
    print("\nBased on proven successes:")
    print("  ✓ SAT LRAT (certificate verification)")
    print("  ✓ Erdős #124 (bounded combinatorics)")
    print("  ✓ HOMFLY v4 (algebraic structures)")
    print()

    # Get all open problems
    cursor = conn.execute("""
        SELECT id, source, source_id, name, status, has_lean4,
               tractability_score, domain, statement, notes
        FROM problems
        WHERE status = 'open'
    """)

    # Get tags for each problem
    def get_tags(problem_id):
        tag_cursor = conn.execute("""
            SELECT t.name FROM tags t
            JOIN problem_tags pt ON t.id = pt.tag_id
            WHERE pt.problem_id = ?
        """, (problem_id,))
        return [row[0] for row in tag_cursor]

    results = []
    for row in cursor:
        tags = get_tags(row['id'])
        text = f"{row['name']} {row['statement'] or ''} {row['notes'] or ''}"

        type_score = calculate_type_score(text, tags)

        results.append({
            'id': row['id'],
            'source': row['source'],
            'source_id': row['source_id'],
            'name': row['name'],
            'has_lean4': row['has_lean4'],
            'old_score': row['tractability_score'],
            'type_score': type_score,
            'domain': row['domain'],
            'tags': tags
        })

    # Sort by type score
    results.sort(key=lambda x: -x['type_score'])

    # Print top candidates
    print("TOP 30 BY PROBLEM TYPE (regardless of formalization):")
    print("-"*70)
    print(f"{'#':3} {'Source':8} {'ID':10} {'Type':4} {'Lean':4} {'Domain':15} {'Name':25}")
    print("-"*70)

    for i, r in enumerate(results[:30], 1):
        lean = "✓" if r['has_lean4'] else " "
        name = (r['name'] or '')[:25]
        print(f"{i:3} {r['source']:8} {r['source_id'] or '-':10} "
              f"{r['type_score']:4} {lean:4} {(r['domain'] or '-')[:15]:15} {name}")

    # Analysis by category
    print("\n" + "="*70)
    print("TYPE SCORE DISTRIBUTION")
    print("="*70)

    brackets = defaultdict(lambda: {'total': 0, 'with_lean': 0, 'without_lean': 0})
    for r in results:
        if r['type_score'] >= 80:
            bracket = '80+'
        elif r['type_score'] >= 70:
            bracket = '70-79'
        elif r['type_score'] >= 60:
            bracket = '60-69'
        else:
            bracket = '<60'

        brackets[bracket]['total'] += 1
        if r['has_lean4']:
            brackets[bracket]['with_lean'] += 1
        else:
            brackets[bracket]['without_lean'] += 1

    for bracket in ['80+', '70-79', '60-69', '<60']:
        b = brackets[bracket]
        print(f"  {bracket:6} | Total: {b['total']:4} | With Lean: {b['with_lean']:4} | WITHOUT Lean: {b['without_lean']:4} ⭐")

    # Highlight non-formalized high-type-score problems
    print("\n" + "="*70)
    print("HIDDEN GEMS: High Type Score WITHOUT Lean 4 (prime targets for --informal)")
    print("="*70)

    hidden_gems = [r for r in results if not r['has_lean4'] and r['type_score'] >= 70]

    print(f"\nFound {len(hidden_gems)} high-potential problems without Lean files!\n")

    for i, r in enumerate(hidden_gems[:20], 1):
        tags_str = ', '.join(r['tags'][:3]) if r['tags'] else '-'
        print(f"{i:3}. [{r['source']}] {r['source_id'] or r['name'][:30]:30} "
              f"| Type: {r['type_score']} | Tags: {tags_str}")

    # Update database with type scores
    print("\n" + "="*70)
    print("UPDATING DATABASE WITH TYPE SCORES")
    print("="*70)

    for r in results:
        # Combine old tractability with type score
        # Type score is more important for non-formalized problems
        if r['has_lean4']:
            new_score = (r['old_score'] + r['type_score']) // 2
        else:
            new_score = r['type_score']  # Type score is primary for non-formalized

        conn.execute("""
            UPDATE problems
            SET tractability_score = ?
            WHERE id = ?
        """, (new_score, r['id']))

    conn.commit()
    conn.close()

    print("✓ Database updated with type-based tractability scores")

    return results

if __name__ == "__main__":
    analyze_database()
