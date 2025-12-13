#!/usr/bin/env python3
"""
Score problems for Aristotle tractability based on proven success patterns.

Success factors (from Boris pattern analysis, Dec 2025):
- Sidon sets: 90% success (Erdős #124)
- Bounded/finite parameters: 85% success
- Graph/Ramsey combinatorics: 80% success
- Certificate verification: 90% success
- Clear formal statement available: +10%

Failure factors:
- Huge state spaces (>2^30): 90% failure
- Asymptotic/infinite problems: 70% failure
- Famous long-standing (>50 years): likely intractable
- No statement extracted: can't formalize
"""

import sqlite3
import re
from pathlib import Path

DB_PATH = Path(__file__).parent / "problems.db"

# Positive signals (add points)
POSITIVE_PATTERNS = {
    # Sidon sets - proven 90% success
    'sidon': (25, [r'\bsidon\b', r'\bB_h\b', r'\bb_h\b']),

    # Bounded/finite - 85% success
    'bounded': (20, [r'\bbounded\b', r'\bfinite\b', r'\bat most\b', r'\bexactly\b',
                     r'for all n\s*[<≤]\s*\d+', r'\bn\s*=\s*\d+']),

    # Graph theory - 80% success
    'graph': (15, [r'\bgraph\b', r'\bvertex\b', r'\bedge\b', r'\bclique\b',
                   r'\bchromatic\b', r'\bplanar\b']),

    # Ramsey theory - 80% success
    'ramsey': (15, [r'\bramsey\b', r'\bmonochromatic\b', r'\bcolou?ring\b',
                    r'\banti-ramsey\b']),

    # Extremal combinatorics - good structure
    'extremal': (12, [r'\bextremal\b', r'\bturán\b', r'\bex\(n', r'\bforbidden\b']),

    # Sequences with structure
    'sequence': (10, [r'\bsequence\b', r'\bprogression\b', r'\barithmetic progression\b']),

    # Polynomial/algebraic - tractable
    'algebraic': (10, [r'\bpolynomial\b', r'\balgebraic\b', r'\bdegree\b']),

    # Verification problems - 90% success
    'verify': (15, [r'\bverify\b', r'\bcheck\b', r'\bcertificate\b', r'\bwitness\b']),

    # Recent progress indicator
    'recent': (10, [r'\brecent\b', r'\b202[3-5]\b', r'\bprogress\b']),
}

# Negative signals (subtract points)
NEGATIVE_PATTERNS = {
    # Asymptotic - hard to formalize
    'asymptotic': (-15, [r'\basymptotic\b', r'\bas n\s*→\s*∞', r'\blim\b',
                         r'\bO\(', r'\bo\(', r'\bΘ\(']),

    # Infinite/unbounded - intractable
    'infinite': (-20, [r'\binfinite\b', r'\bunbounded\b', r'\ball n\b',
                       r'\bfor all\b.*\bintegers\b']),

    # Dense primes - historically hard
    'prime_dense': (-10, [r'\btwin prime\b', r'\bgoldbach\b', r'\bprime gap\b']),

    # Transcendental/analytic - hard for ATP
    'analytic': (-15, [r'\btranscendental\b', r'\birrational\b', r'\bcontinuous\b',
                       r'\bintegral\b', r'\bderivative\b']),

    # Computational complexity - usually intractable
    'complexity': (-20, [r'\bNP-hard\b', r'\bNP-complete\b', r'\bundecidable\b',
                         r'\bPSPACE\b']),

    # Famous conjectures - likely too hard
    'famous': (-25, [r'\bRiemann\b', r'\bCollatz\b', r'\bGoldbach\b',
                     r'\bP\s*=\s*NP\b', r'\bMillennium\b']),
}

# Domain-based adjustments
DOMAIN_SCORES = {
    'combinatorics': 15,
    'graph theory': 12,
    'number theory': 0,  # neutral - depends on specific problem
    'geometry': 5,
    'algebra': 5,
    'analysis': -5,
    'topology': -10,
    'logic': -5,
}

def score_problem(statement, domain, name=''):
    """Calculate tractability score for a problem."""
    if not statement:
        return 10  # Can't score without statement

    text = (statement + ' ' + (name or '')).lower()
    score = 50  # Base score
    reasons = []

    # Apply positive patterns
    for signal, (points, patterns) in POSITIVE_PATTERNS.items():
        for pattern in patterns:
            if re.search(pattern, text, re.IGNORECASE):
                score += points
                reasons.append(f"+{points} {signal}")
                break

    # Apply negative patterns
    for signal, (points, patterns) in NEGATIVE_PATTERNS.items():
        for pattern in patterns:
            if re.search(pattern, text, re.IGNORECASE):
                score += points  # points are already negative
                reasons.append(f"{points} {signal}")
                break

    # Domain adjustment
    if domain:
        domain_lower = domain.lower()
        for d, pts in DOMAIN_SCORES.items():
            if d in domain_lower:
                score += pts
                if pts != 0:
                    reasons.append(f"{'+' if pts > 0 else ''}{pts} domain:{d}")
                break

    # Clamp to 0-100
    score = max(0, min(100, score))

    return score, reasons

def main():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row

    print("=" * 70)
    print("TRACTABILITY SCORING - Based on Aristotle Success Patterns")
    print("=" * 70)

    # Score all open problems with statements
    cursor = conn.execute("""
        SELECT id, source, source_id, name, domain, statement
        FROM problems
        WHERE status = 'open'
        AND statement IS NOT NULL
        AND length(statement) > 50
    """)

    problems = list(cursor)
    print(f"\nScoring {len(problems)} open problems with statements...\n")

    scored = []
    for row in problems:
        score, reasons = score_problem(row['statement'], row['domain'], row['name'])
        scored.append({
            'id': row['id'],
            'source': row['source'],
            'source_id': row['source_id'],
            'name': row['name'],
            'domain': row['domain'],
            'score': score,
            'reasons': reasons
        })

        # Update database
        conn.execute("UPDATE problems SET tractability_score = ? WHERE id = ?",
                    (score, row['id']))

    conn.commit()

    # Sort by score
    scored.sort(key=lambda x: -x['score'])

    # Show top 20
    print("=" * 70)
    print("TOP 20 CANDIDATES FOR ARISTOTLE")
    print("=" * 70)

    for i, p in enumerate(scored[:20], 1):
        source_id = f"#{p['source_id']}" if p['source_id'] else ""
        print(f"\n{i}. [{p['score']:3d}] {p['source'].upper()} {source_id}")
        print(f"   {p['name'][:60]}")
        print(f"   Domain: {p['domain']}")
        print(f"   Signals: {', '.join(p['reasons'][:5])}")

    # Distribution stats
    print("\n" + "=" * 70)
    print("SCORE DISTRIBUTION")
    print("=" * 70)

    buckets = {'90-100': 0, '80-89': 0, '70-79': 0, '60-69': 0, '50-59': 0, '<50': 0}
    for p in scored:
        if p['score'] >= 90: buckets['90-100'] += 1
        elif p['score'] >= 80: buckets['80-89'] += 1
        elif p['score'] >= 70: buckets['70-79'] += 1
        elif p['score'] >= 60: buckets['60-69'] += 1
        elif p['score'] >= 50: buckets['50-59'] += 1
        else: buckets['<50'] += 1

    for bucket, count in buckets.items():
        bar = '█' * (count // 5)
        print(f"  {bucket:>7}: {count:4d} {bar}")

    conn.close()

    return scored[:20]

if __name__ == "__main__":
    main()
