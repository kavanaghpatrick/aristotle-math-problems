#!/usr/bin/env python3
"""
Extract Boris Pattern scores from Formal Conjectures Erdős problem files.

Scoring:
  +10 per @[category research solved]
  +5  per @[category undergraduate]
  +5  per @[category test]
  +5  if "by decide" or "by native" present (decidable)
  +3  if SimpleGraph/graph theory keywords
  -5  if has asymptotics (atTop, Tendsto, liminf, limsup, ∀ᶠ)
  -3  if prize mentioned > $500
"""

import os
import re
from pathlib import Path
from dataclasses import dataclass
from typing import List
import json

FC_DIR = Path("/Users/patrickkavanagh/math/problem-databases/formal-conjectures/FormalConjectures/ErdosProblems")

@dataclass
class ProblemAnalysis:
    problem_num: int
    filename: str
    solved_count: int = 0
    undergraduate_count: int = 0
    test_count: int = 0
    open_count: int = 0
    has_decide: bool = False
    has_asymptotics: bool = False
    has_graph_theory: bool = False
    has_sidon: bool = False
    has_prime: bool = False
    prize_amount: int = 0
    boris_score: int = 0
    theorem_names: List[str] = None

    def __post_init__(self):
        if self.theorem_names is None:
            self.theorem_names = []

def extract_problem_number(filename: str) -> int:
    """Extract problem number from filename like '707.lean'"""
    match = re.match(r'(\d+)\.lean', filename)
    return int(match.group(1)) if match else 0

def analyze_file(filepath: Path) -> ProblemAnalysis:
    """Analyze a single Lean file for Boris pattern indicators."""
    content = filepath.read_text()
    filename = filepath.name
    problem_num = extract_problem_number(filename)

    analysis = ProblemAnalysis(
        problem_num=problem_num,
        filename=filename
    )

    # Count categories
    analysis.solved_count = len(re.findall(r'@\[category research solved', content))
    analysis.undergraduate_count = len(re.findall(r'@\[category undergraduate', content))
    analysis.test_count = len(re.findall(r'@\[category test', content))
    analysis.open_count = len(re.findall(r'@\[category research open', content))

    # Check for decidable proofs
    analysis.has_decide = bool(re.search(r'by\s+(decide|native)', content))

    # Check for asymptotics (NEGATIVE indicator)
    async_patterns = [
        r'∀ᶠ',
        r'atTop',
        r'Tendsto',
        r'liminf',
        r'limsup',
        r'Filter\.atTop',
        r'eventually',
    ]
    analysis.has_asymptotics = any(re.search(p, content) for p in async_patterns)

    # Check for graph theory (POSITIVE indicator)
    graph_patterns = [
        r'SimpleGraph',
        r'chromaticNumber',
        r'CliqueFree',
        r'girth',
        r'edgeSet',
        r'Subgraph',
    ]
    analysis.has_graph_theory = any(re.search(p, content) for p in graph_patterns)

    # Check for Sidon sets
    analysis.has_sidon = bool(re.search(r'IsSidon|Sidon', content))

    # Check for prime/number theory
    analysis.has_prime = bool(re.search(r'\.Prime|Nat\.Prime|prime', content, re.IGNORECASE))

    # Extract prize amount if mentioned
    prize_match = re.search(r'\$(\d+)', content)
    if prize_match:
        analysis.prize_amount = int(prize_match.group(1))

    # Extract theorem names for solved variants
    theorem_matches = re.findall(r'theorem\s+([\w\.]+)', content)
    analysis.theorem_names = theorem_matches

    # Calculate Boris score
    score = 0
    score += analysis.solved_count * 10
    score += analysis.undergraduate_count * 5
    score += analysis.test_count * 5
    if analysis.has_decide:
        score += 5
    if analysis.has_graph_theory:
        score += 3
    if analysis.has_asymptotics:
        score -= 5
    if analysis.prize_amount >= 500:
        score -= 3

    analysis.boris_score = score

    return analysis

def main():
    analyses = []

    for lean_file in FC_DIR.glob("*.lean"):
        if lean_file.name == "Basic.lean":
            continue
        analysis = analyze_file(lean_file)
        analyses.append(analysis)

    # Sort by Boris score descending
    analyses.sort(key=lambda x: x.boris_score, reverse=True)

    # Print summary table
    print("=" * 100)
    print("BORIS PATTERN RANKING - ALL 261 ERDŐS PROBLEMS")
    print("=" * 100)
    print(f"{'#':<6} {'Score':<7} {'Solved':<7} {'UGrad':<7} {'Test':<6} {'Dec':<5} {'Asym':<6} {'Graph':<6} {'Prize':<7}")
    print("-" * 100)

    for a in analyses[:50]:  # Top 50
        print(f"{a.problem_num:<6} {a.boris_score:<7} {a.solved_count:<7} {a.undergraduate_count:<7} "
              f"{a.test_count:<6} {'Y' if a.has_decide else 'N':<5} "
              f"{'Y' if a.has_asymptotics else 'N':<6} "
              f"{'Y' if a.has_graph_theory else 'N':<6} "
              f"${a.prize_amount:<6}" if a.prize_amount else
              f"{a.problem_num:<6} {a.boris_score:<7} {a.solved_count:<7} {a.undergraduate_count:<7} "
              f"{a.test_count:<6} {'Y' if a.has_decide else 'N':<5} "
              f"{'Y' if a.has_asymptotics else 'N':<6} "
              f"{'Y' if a.has_graph_theory else 'N':<6} $0")

    print("\n" + "=" * 100)
    print("TOP 20 CANDIDATES (Highest Boris Score)")
    print("=" * 100)

    for i, a in enumerate(analyses[:20], 1):
        flags = []
        if a.has_decide: flags.append("DECIDE")
        if a.has_graph_theory: flags.append("GRAPH")
        if a.has_sidon: flags.append("SIDON")
        if a.has_asymptotics: flags.append("ASYNC")

        print(f"\n{i:2}. #{a.problem_num} - Score: {a.boris_score}")
        print(f"    Solved: {a.solved_count}, Undergrad: {a.undergraduate_count}, Test: {a.test_count}")
        print(f"    Flags: {', '.join(flags) if flags else 'None'}")
        if a.solved_count > 0:
            solved_theorems = [t for t in a.theorem_names if 'variant' in t.lower() or 'solved' in t.lower()]
            if solved_theorems:
                print(f"    Theorems: {', '.join(solved_theorems[:3])}")

    # Save full results to JSON
    output_data = []
    for a in analyses:
        output_data.append({
            'problem_num': a.problem_num,
            'boris_score': a.boris_score,
            'solved_count': a.solved_count,
            'undergraduate_count': a.undergraduate_count,
            'test_count': a.test_count,
            'has_decide': a.has_decide,
            'has_asymptotics': a.has_asymptotics,
            'has_graph_theory': a.has_graph_theory,
            'has_sidon': a.has_sidon,
            'prize_amount': a.prize_amount,
            'theorem_names': a.theorem_names,
        })

    output_path = Path("/Users/patrickkavanagh/math/boris_scores.json")
    output_path.write_text(json.dumps(output_data, indent=2))
    print(f"\n\nFull results saved to: {output_path}")

    # Statistics
    print("\n" + "=" * 100)
    print("STATISTICS")
    print("=" * 100)
    print(f"Total problems analyzed: {len(analyses)}")
    print(f"Problems with SOLVED variants: {sum(1 for a in analyses if a.solved_count > 0)}")
    print(f"Problems with UNDERGRADUATE: {sum(1 for a in analyses if a.undergraduate_count > 0)}")
    print(f"Problems with TEST cases: {sum(1 for a in analyses if a.test_count > 0)}")
    print(f"Problems with DECIDE proofs: {sum(1 for a in analyses if a.has_decide)}")
    print(f"Problems with ASYMPTOTICS: {sum(1 for a in analyses if a.has_asymptotics)}")
    print(f"Problems with GRAPH THEORY: {sum(1 for a in analyses if a.has_graph_theory)}")

    # Best candidates summary
    print("\n" + "=" * 100)
    print("BEST BORIS CANDIDATES (Score >= 20, No Asymptotics)")
    print("=" * 100)
    best = [a for a in analyses if a.boris_score >= 20 and not a.has_asymptotics]
    for a in best:
        print(f"  #{a.problem_num}: Score {a.boris_score} | {a.solved_count}S {a.undergraduate_count}U {a.test_count}T")

if __name__ == "__main__":
    main()
