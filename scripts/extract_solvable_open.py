#!/usr/bin/env python3
"""
Extract GENUINELY OPEN problems that might be SOLVABLE by Aristotle.

Key insight: We want problems that are:
1. OPEN (not solved)
2. Have decidable/finite structure
3. Ask for True/False answer
4. Have concrete small bounds
5. Are in domains with good Mathlib support
"""

import os
import re
from pathlib import Path
from dataclasses import dataclass, field
from typing import List
import json

FC_DIR = Path("/Users/patrickkavanagh/math/problem-databases/formal-conjectures/FormalConjectures/ErdosProblems")

@dataclass
class OpenProblem:
    problem_num: int
    filename: str
    open_count: int = 0
    solved_count: int = 0
    has_answer_sorry: bool = False  # ↔ answer(sorry) pattern
    has_decide: bool = False
    has_norm_num: bool = False
    has_native_decide: bool = False
    has_finite_type: bool = False  # Fin, Finset, Finite
    has_concrete_numbers: bool = False  # Specific numbers in statement
    has_asymptotics: bool = False
    is_true_false: bool = False  # Asking for True/False
    prize_amount: int = 0
    open_theorems: List[str] = field(default_factory=list)
    solvability_score: int = 0

def analyze_file(filepath: Path) -> OpenProblem:
    content = filepath.read_text()
    filename = filepath.name
    match = re.match(r'(\d+)\.lean', filename)
    problem_num = int(match.group(1)) if match else 0

    prob = OpenProblem(problem_num=problem_num, filename=filename)

    # Count categories
    prob.open_count = len(re.findall(r'@\[category research open', content))
    prob.solved_count = len(re.findall(r'@\[category research solved', content))

    # Check for answer(sorry) pattern - these are True/False questions!
    prob.has_answer_sorry = bool(re.search(r'↔\s*answer\s*\(\s*sorry\s*\)', content))

    # Check for decidability indicators
    prob.has_decide = bool(re.search(r'by\s+decide', content))
    prob.has_norm_num = bool(re.search(r'norm_num', content))
    prob.has_native_decide = bool(re.search(r'native_decide', content))

    # Check for finite types (good for computation)
    finite_patterns = [r'Fin\s+\d+', r'Finset', r'Finite', r'\.card', r'\.ncard']
    prob.has_finite_type = any(re.search(p, content) for p in finite_patterns)

    # Check for concrete numbers in theorem statements
    # Look for specific bounds like n ≤ 10, k = 5, etc.
    prob.has_concrete_numbers = bool(re.search(r'[≤≥=]\s*\d+', content))

    # Check for asymptotics (bad)
    async_patterns = [r'∀ᶠ', r'atTop', r'Tendsto', r'liminf', r'limsup', r'Filter\.atTop']
    prob.has_asymptotics = any(re.search(p, content) for p in async_patterns)

    # Extract prize
    prize_match = re.search(r'\$(\d+)', content)
    if prize_match:
        prob.prize_amount = int(prize_match.group(1))

    # Extract open theorem names
    # Find theorems marked as open
    open_sections = re.finditer(r'@\[category research open.*?\].*?theorem\s+([\w\.]+)', content, re.DOTALL)
    prob.open_theorems = [m.group(1) for m in open_sections]

    # Calculate solvability score for OPEN problems
    if prob.open_count > 0:
        score = 0

        # Strong positive signals
        if prob.has_answer_sorry:
            score += 20  # True/False question - finite answer space!
        if prob.has_decide or prob.has_native_decide:
            score += 15  # Decidable structure exists
        if prob.has_norm_num:
            score += 10  # Numeric computation possible
        if prob.has_finite_type:
            score += 10  # Finite domain
        if prob.has_concrete_numbers:
            score += 5   # Concrete bounds

        # Negative signals
        if prob.has_asymptotics:
            score -= 15  # Asymptotics = hard
        if prob.prize_amount >= 500:
            score -= 10  # Big prize = hard problem
        if prob.prize_amount >= 1000:
            score -= 10  # Extra penalty for $1000+

        # Penalty if mostly solved (less interesting)
        if prob.solved_count > prob.open_count:
            score -= 5

        prob.solvability_score = score

    return prob

def main():
    problems = []

    for lean_file in FC_DIR.glob("*.lean"):
        if lean_file.name == "Basic.lean":
            continue
        prob = analyze_file(lean_file)
        if prob.open_count > 0:  # Only include problems with OPEN theorems
            problems.append(prob)

    # Sort by solvability score
    problems.sort(key=lambda x: x.solvability_score, reverse=True)

    print("=" * 100)
    print("SOLVABLE OPEN PROBLEMS - Ranked by Tractability")
    print("=" * 100)
    print(f"\nTotal problems with OPEN theorems: {len(problems)}")
    print(f"Problems with answer(sorry) pattern: {sum(1 for p in problems if p.has_answer_sorry)}")
    print(f"Problems with decide: {sum(1 for p in problems if p.has_decide)}")
    print()

    print("=" * 100)
    print("TOP 30 MOST SOLVABLE OPEN PROBLEMS")
    print("=" * 100)
    print(f"{'#':<6} {'Score':<7} {'Open':<5} {'T/F':<4} {'Dec':<4} {'Fin':<4} {'Num':<4} {'Asym':<5} {'Prize':<7}")
    print("-" * 100)

    for p in problems[:30]:
        print(f"{p.problem_num:<6} {p.solvability_score:<7} {p.open_count:<5} "
              f"{'Y' if p.has_answer_sorry else 'N':<4} "
              f"{'Y' if p.has_decide else 'N':<4} "
              f"{'Y' if p.has_finite_type else 'N':<4} "
              f"{'Y' if p.has_concrete_numbers else 'N':<4} "
              f"{'Y' if p.has_asymptotics else 'N':<5} "
              f"${p.prize_amount}")

    print("\n" + "=" * 100)
    print("BEST CANDIDATES: OPEN + True/False + Decidable + No Asymptotics")
    print("=" * 100)

    best = [p for p in problems
            if p.has_answer_sorry
            and not p.has_asymptotics
            and p.solvability_score >= 20]

    for p in best:
        print(f"\n#{p.problem_num} - Score: {p.solvability_score}")
        print(f"  Open theorems: {p.open_count}")
        print(f"  Has decide: {p.has_decide}, Finite: {p.has_finite_type}")
        print(f"  Prize: ${p.prize_amount}")
        if p.open_theorems:
            print(f"  Theorems: {', '.join(p.open_theorems[:3])}")

    # Also show problems with decide that are open
    print("\n" + "=" * 100)
    print("OPEN PROBLEMS WITH DECIDABLE STRUCTURE")
    print("=" * 100)

    decidable = [p for p in problems if p.has_decide or p.has_native_decide]
    for p in decidable:
        print(f"#{p.problem_num}: Score {p.solvability_score}, "
              f"Open: {p.open_count}, Dec: Y, Asym: {'Y' if p.has_asymptotics else 'N'}")

    # Save to JSON
    output = [{
        'num': p.problem_num,
        'score': p.solvability_score,
        'open': p.open_count,
        'answer_sorry': p.has_answer_sorry,
        'decide': p.has_decide,
        'finite': p.has_finite_type,
        'asymptotics': p.has_asymptotics,
        'prize': p.prize_amount,
        'theorems': p.open_theorems
    } for p in problems]

    Path("/Users/patrickkavanagh/math/solvable_open.json").write_text(json.dumps(output, indent=2))
    print(f"\n\nSaved to /Users/patrickkavanagh/math/solvable_open.json")

if __name__ == "__main__":
    main()
