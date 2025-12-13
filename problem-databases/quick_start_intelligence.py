#!/usr/bin/env python3
"""
Quick Start: Problem Selection Intelligence
Demonstrate immediate value with 10 test problems
"""

import sqlite3
import json
import subprocess
import os
from pathlib import Path

# Database path
DB_PATH = Path(__file__).parent / "problems.db"

# Known success patterns from Aristotle outcomes
SUCCESS_PATTERNS = {
    'boris_pure': {
        'keywords': ['bounded', 'finite', 'combinatorial', 'graph', 'explicit'],
        'anti_keywords': ['infinite', 'asymptotic', 'prime', 'riemann'],
        'success_rate': 0.90,
        'description': 'Pure Boris pattern - minimal intervention',
    },
    'certificate_verification': {
        'keywords': ['verify', 'certificate', 'witness', 'SAT', 'proof'],
        'anti_keywords': ['find', 'construct', 'search'],
        'success_rate': 0.90,
        'description': 'Verify certificate, not find solution',
    },
    'bounded_combinatorics': {
        'keywords': ['n=', 'n ≤', 'small', 'explicit', 'finite'],
        'anti_keywords': ['all n', 'arbitrary n', 'infinitely'],
        'success_rate': 0.85,
        'description': 'Bounded parameters, finite search space',
    },
    'algebraic_structure': {
        'keywords': ['group', 'ring', 'algebra', 'lattice', 'well-founded'],
        'anti_keywords': ['transcendental', 'analytic'],
        'success_rate': 0.80,
        'description': 'Rich algebraic constraints',
    },
}

# Known Aristotle successes
KNOWN_SUCCESSES = [
    {
        'name': 'Erdős #124',
        'pattern': 'boris_pure',
        'success_rate': 0.90,
        'features': ['bounded', 'combinatorial', 'sidon_sets'],
    },
    {
        'name': 'Jones polynomial',
        'pattern': 'certificate_verification',
        'success_rate': 1.00,  # 983 lines, 0 sorries
        'features': ['verify', 'computational_witness', 'algebraic'],
    },
    {
        'name': 'SAT LRAT',
        'pattern': 'certificate_verification',
        'success_rate': 1.00,
        'features': ['verify', 'certificate', 'boolean_logic'],
    },
    {
        'name': 'HOMFLY v4',
        'pattern': 'algebraic_structure',
        'success_rate': 1.00,
        'features': ['algebraic', 'well_founded', 'knot_theory'],
    },
]

# Known failures
KNOWN_FAILURES = [
    {
        'name': 'Quantum Collision',
        'reason': 'Search space 16^16 = 2^64 too large',
        'features': ['huge_state_space'],
    },
    {
        'name': 'HOMFLY v2',
        'reason': 'Over-prescribed 17 theorems, 4 were false',
        'features': ['prescriptive', 'buggy_foundation'],
    },
]


def match_pattern(problem_text, pattern):
    """Check if problem matches a success pattern."""
    if not problem_text:
        return 0.0

    text_lower = problem_text.lower()

    # Count keyword matches
    keyword_matches = sum(1 for kw in pattern['keywords'] if kw.lower() in text_lower)
    anti_matches = sum(1 for kw in pattern['anti_keywords'] if kw.lower() in text_lower)

    # Score
    if anti_matches > 0:
        return 0.0  # Disqualified

    if keyword_matches > 0:
        return pattern['success_rate'] * (keyword_matches / len(pattern['keywords']))

    return 0.0


def analyze_problem_intelligent(problem):
    """Intelligent analysis of a problem."""

    problem_text = f"{problem['name']} {problem.get('statement', '')} {problem.get('domain', '')}"

    # Pattern matching
    pattern_scores = {}
    for pattern_name, pattern in SUCCESS_PATTERNS.items():
        score = match_pattern(problem_text, pattern)
        if score > 0:
            pattern_scores[pattern_name] = score

    # Best pattern match
    best_pattern = max(pattern_scores.items(), key=lambda x: x[1]) if pattern_scores else (None, 0.0)

    # Structural features (heuristic for now)
    features = {
        'is_bounded': any(kw in problem_text.lower() for kw in ['n=', 'n ≤', 'bounded', 'finite']),
        'is_combinatorial': any(kw in problem_text.lower() for kw in ['graph', 'combinat', 'sidon']),
        'has_certificate': any(kw in problem_text.lower() for kw in ['verify', 'certificate', 'witness']),
        'is_algebraic': any(kw in problem_text.lower() for kw in ['group', 'ring', 'algebra']),
        'is_huge_space': any(kw in problem_text.lower() for kw in ['infinite', 'all n', 'arbitrary']),
    }

    # Calculate intelligent score
    base_score = best_pattern[1] * 100 if best_pattern[0] else 30

    # Feature bonuses
    if features['is_bounded']:
        base_score += 20
    if features['is_combinatorial']:
        base_score += 10
    if features['has_certificate']:
        base_score += 25
    if features['is_algebraic']:
        base_score += 10
    if features['is_huge_space']:
        base_score -= 40

    # Clamp
    intelligent_score = max(0, min(100, base_score))

    return {
        'intelligent_score': intelligent_score,
        'best_pattern': best_pattern[0],
        'pattern_confidence': best_pattern[1],
        'features': features,
        'pattern_scores': pattern_scores,
    }


def get_test_problems():
    """Get 10 test problems from database."""

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()

    # Get diverse sample
    problems = []

    # 1. Top scored by current system
    cursor.execute("""
        SELECT * FROM problems
        WHERE status = 'open' AND tractability_score >= 80
        LIMIT 3
    """)
    problems.extend([dict(row) for row in cursor.fetchall()])

    # 2. Has Lean4
    cursor.execute("""
        SELECT * FROM problems
        WHERE status = 'open' AND has_lean4 = 1 AND tractability_score >= 70
        LIMIT 3
    """)
    problems.extend([dict(row) for row in cursor.fetchall()])

    # 3. Random sample
    cursor.execute("""
        SELECT * FROM problems
        WHERE status = 'open' AND length(statement) > 100
        ORDER BY RANDOM()
        LIMIT 4
    """)
    problems.extend([dict(row) for row in cursor.fetchall()])

    conn.close()

    # Deduplicate
    seen = set()
    unique = []
    for p in problems:
        if p['id'] not in seen:
            seen.add(p['id'])
            unique.append(p)

    return unique[:10]


def compare_scoring():
    """Compare old vs new scoring."""

    print("=" * 80)
    print("PROBLEM SELECTION INTELLIGENCE - QUICK START")
    print("=" * 80)
    print()

    # Get test problems
    problems = get_test_problems()

    print(f"Analyzing {len(problems)} test problems...")
    print()

    results = []

    for i, problem in enumerate(problems, 1):
        print(f"\n{i}. {problem['name']}")
        print(f"   Source: {problem['source']}")
        print(f"   Domain: {problem.get('domain', 'N/A')}")
        print(f"   Old Score: {problem.get('tractability_score', 0)}")

        # New intelligent analysis
        analysis = analyze_problem_intelligent(problem)

        print(f"   New Score: {analysis['intelligent_score']}")
        print(f"   Best Pattern: {analysis['best_pattern']} (confidence: {analysis['pattern_confidence']:.2f})")

        features_list = [k for k, v in analysis['features'].items() if v]
        if features_list:
            print(f"   Features: {', '.join(features_list)}")

        # Change
        old_score = problem.get('tractability_score', 0) or 0
        new_score = analysis['intelligent_score']
        delta = new_score - old_score

        print(f"   Change: {int(delta):+d}")

        if delta > 20:
            print(f"   ⬆️ SIGNIFICANTLY UPGRADED")
        elif delta < -20:
            print(f"   ⬇️ SIGNIFICANTLY DOWNGRADED")

        results.append({
            'problem': problem,
            'old_score': old_score,
            'new_score': new_score,
            'delta': delta,
            'analysis': analysis,
        })

    # Summary
    print()
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)

    # Sort by new score
    results_sorted = sorted(results, key=lambda x: -x['new_score'])

    print("\nTOP 5 CANDIDATES (by new scoring):")
    for i, r in enumerate(results_sorted[:5], 1):
        print(f"  {i}. {r['problem']['name']}")
        print(f"     Score: {r['old_score']} → {r['new_score']} ({int(r['delta']):+d})")
        print(f"     Pattern: {r['analysis']['best_pattern']}")
        print()

    # Biggest changes
    biggest_upgrades = sorted(results, key=lambda x: -x['delta'])[:3]
    print("\nBIGGEST UPGRADES:")
    for r in biggest_upgrades:
        if r['delta'] > 0:
            print(f"  • {r['problem']['name']}: +{r['delta']} points")
            print(f"    Why: {r['analysis']['best_pattern']} pattern detected")

    biggest_downgrades = sorted(results, key=lambda x: x['delta'])[:3]
    print("\nBIGGEST DOWNGRADES:")
    for r in biggest_downgrades:
        if r['delta'] < 0:
            print(f"  • {r['problem']['name']}: {r['delta']} points")
            features = [k for k, v in r['analysis']['features'].items() if v and 'huge' in k]
            if features:
                print(f"    Why: Detected {features}")

    # Statistics
    print()
    print("STATISTICS:")
    avg_old = sum(r['old_score'] for r in results) / len(results)
    avg_new = sum(r['new_score'] for r in results) / len(results)
    print(f"  Average old score: {avg_old:.1f}")
    print(f"  Average new score: {avg_new:.1f}")
    print(f"  Average change: {avg_new - avg_old:+.1f}")

    pattern_detected = sum(1 for r in results if r['analysis']['best_pattern'] is not None)
    print(f"  Patterns detected: {pattern_detected}/{len(results)}")

    # Save results
    output_path = Path(__file__).parent / "intelligent_scoring_results.json"
    with open(output_path, 'w') as f:
        json.dump([{
            'name': r['problem']['name'],
            'source': r['problem']['source'],
            'old_score': r['old_score'],
            'new_score': r['new_score'],
            'delta': r['delta'],
            'pattern': r['analysis']['best_pattern'],
            'features': r['analysis']['features'],
        } for r in results], f, indent=2)

    print()
    print(f"Results saved to: {output_path}")


def suggest_next_submissions():
    """Suggest problems for next Aristotle submissions."""

    print()
    print("=" * 80)
    print("SUGGESTED NEXT SUBMISSIONS")
    print("=" * 80)
    print()

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()

    # Find high-value targets
    cursor.execute("""
        SELECT * FROM problems
        WHERE status = 'open'
          AND has_lean4 = 1
        ORDER BY tractability_score DESC
        LIMIT 20
    """)

    candidates = [dict(row) for row in cursor.fetchall()]
    conn.close()

    # Re-score with intelligence
    for candidate in candidates:
        analysis = analyze_problem_intelligent(candidate)
        candidate['intelligent_score'] = analysis['intelligent_score']
        candidate['best_pattern'] = analysis['best_pattern']
        candidate['pattern_confidence'] = analysis['pattern_confidence']

    # Sort by intelligent score
    candidates_sorted = sorted(candidates, key=lambda x: -x['intelligent_score'])

    print("Top 10 by intelligent scoring:")
    for i, c in enumerate(candidates_sorted[:10], 1):
        print(f"\n{i}. {c['name']}")
        print(f"   Score: {c['intelligent_score']}")
        print(f"   Pattern: {c['best_pattern']} ({c['pattern_confidence']:.2f})")
        print(f"   Lean file: {c.get('lean_file_path', 'N/A')}")

        if c['best_pattern'] == 'boris_pure':
            print(f"   ⭐ PRIME CANDIDATE for Boris pattern submission")


if __name__ == "__main__":
    compare_scoring()
    suggest_next_submissions()
