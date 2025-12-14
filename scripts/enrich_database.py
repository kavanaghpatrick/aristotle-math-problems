#!/usr/bin/env python3
"""
Enrich the Erdős problems database with formalization gap analysis.

Adds fields:
- solved_theorems: List of theorems marked as "solved"
- open_theorems: List of theorems marked as "open"
- has_solved_variants: Boolean - are there proved theorems we can target?
- needs_custom_defs: Does it need FormalConjectures custom definitions?
- mathlib_imports: What Mathlib modules beyond base are used?
- decidable_tests: Are there decidable test cases (decide, norm_num)?
- gap_score: Composite score for formalization gap potential
"""

import json
import re
from pathlib import Path
from collections import defaultdict

FORMAL_CONJECTURES_PATH = Path("problem-databases/formal-conjectures/FormalConjectures/ErdosProblems")

def parse_lean_file(filepath: Path) -> dict:
    """Extract metadata from a Lean file."""
    try:
        content = filepath.read_text()
    except:
        return None

    result = {
        "filepath": str(filepath),
        "solved_theorems": [],
        "open_theorems": [],
        "undergraduate_theorems": [],
        "test_theorems": [],
        "high_school_theorems": [],
        "has_norm_num": "norm_num" in content,
        "has_decide": "decide" in content,
        "has_native_decide": "native_decide" in content,
        "has_aesop": "aesop" in content,
        "uses_answer_sorry": "answer(sorry)" in content,
        "custom_defs": [],
        "mathlib_specific": [],
    }

    # Extract theorem categories
    # Pattern: @[category X Y, AMS N] theorem name
    category_pattern = r'@\[category\s+([^,\]]+).*?\]\s*(?:theorem|def|lemma)\s+(\S+)'
    for match in re.finditer(category_pattern, content):
        category = match.group(1).strip()
        theorem_name = match.group(2).strip()

        if "solved" in category:
            result["solved_theorems"].append(theorem_name)
        elif "open" in category:
            result["open_theorems"].append(theorem_name)
        elif "undergraduate" in category:
            result["undergraduate_theorems"].append(theorem_name)
        elif "test" in category:
            result["test_theorems"].append(theorem_name)
        elif "high_school" in category:
            result["high_school_theorems"].append(theorem_name)

    # Check for custom definitions in file
    def_pattern = r'(?:def|abbrev)\s+(\S+)'
    for match in re.finditer(def_pattern, content):
        def_name = match.group(1)
        if not def_name.startswith("_"):
            result["custom_defs"].append(def_name)

    # Check for specific Mathlib imports (beyond basic)
    mathlib_patterns = [
        ("SimpleGraph", "graph_theory"),
        ("chromaticNumber", "chromatic"),
        ("Sidon", "sidon"),
        ("primeFactors", "prime_factors"),
        ("centralBinom", "central_binom"),
        ("Filter.atTop", "asymptotics"),
        ("Asymptotics", "asymptotics"),
        ("BigO", "asymptotics"),
        ("IsTheta", "asymptotics"),
        ("ENat", "extended_nat"),
        ("Finset.Icc", "finset_intervals"),
        ("Set.Infinite", "infinite_sets"),
        ("Set.Finite", "finite_sets"),
        ("IsGreatest", "order_theory"),
        ("Multiset", "multiset"),
    ]

    for pattern, tag in mathlib_patterns:
        if pattern in content:
            result["mathlib_specific"].append(tag)

    return result


def compute_gap_score(data: dict) -> int:
    """
    Compute a formalization gap score.
    Higher = more likely to have exploitable gaps.

    Factors:
    - Has solved variants (can target those)
    - Has decidable/computable test cases
    - Uses simple Mathlib (not graph theory, asymptotics)
    - Self-contained definitions
    - Has undergraduate/high_school theorems (simpler)
    """
    score = 0

    # Solved variants are prime targets (+30)
    if data.get("solved_theorems"):
        score += 30

    # Decidable tests suggest tractable problem (+20)
    if data.get("has_decide") or data.get("has_native_decide"):
        score += 20
    if data.get("has_norm_num"):
        score += 10

    # Undergraduate/high school = simpler (+15)
    if data.get("undergraduate_theorems"):
        score += 15
    if data.get("high_school_theorems"):
        score += 15

    # Self-contained defs = can submit standalone (+10)
    if data.get("custom_defs"):
        score += 10

    # Penalize complex dependencies
    mathlib = data.get("mathlib_specific", [])
    if "asymptotics" in mathlib:
        score -= 15
    if "graph_theory" in mathlib or "chromatic" in mathlib:
        score -= 20
    if "sidon" in mathlib:
        score -= 10

    # Simple structures bonus
    if "finset_intervals" in mathlib or "prime_factors" in mathlib:
        score += 5

    return max(0, score)


def main():
    # Load existing databases
    with open("boris_scores.json") as f:
        boris_data = json.load(f)

    boris_by_num = {p["problem_num"]: p for p in boris_data}

    # Analyze all Lean files
    enriched = []

    for lean_file in sorted(FORMAL_CONJECTURES_PATH.glob("*.lean")):
        # Extract problem number from filename
        try:
            problem_num = int(lean_file.stem)
        except ValueError:
            continue

        file_data = parse_lean_file(lean_file)
        if not file_data:
            continue

        # Merge with existing boris data
        existing = boris_by_num.get(problem_num, {})

        enriched_entry = {
            "problem_num": problem_num,
            "boris_score": existing.get("boris_score", 0),
            "solved_theorems": file_data["solved_theorems"],
            "open_theorems": file_data["open_theorems"],
            "undergraduate_theorems": file_data["undergraduate_theorems"],
            "test_theorems": file_data["test_theorems"],
            "high_school_theorems": file_data["high_school_theorems"],
            "has_solved_variants": len(file_data["solved_theorems"]) > 0,
            "has_decidable": file_data["has_decide"] or file_data["has_native_decide"],
            "has_norm_num": file_data["has_norm_num"],
            "uses_answer_sorry": file_data["uses_answer_sorry"],
            "custom_defs": file_data["custom_defs"],
            "mathlib_deps": file_data["mathlib_specific"],
            "has_asymptotics": "asymptotics" in file_data["mathlib_specific"],
            "has_graph_theory": "graph_theory" in file_data["mathlib_specific"] or "chromatic" in file_data["mathlib_specific"],
            "gap_score": compute_gap_score(file_data),
            "prize_amount": existing.get("prize_amount", 0),
        }

        enriched.append(enriched_entry)

    # Sort by gap_score descending
    enriched.sort(key=lambda x: (-x["gap_score"], -x["boris_score"]))

    # Save enriched database
    with open("enriched_problems.json", "w") as f:
        json.dump(enriched, f, indent=2)

    print(f"Enriched {len(enriched)} problems")
    print(f"\nTop 20 by gap_score:")
    print("-" * 80)
    print(f"{'#':<6} {'Gap':<5} {'Boris':<6} {'Solved':<8} {'Decidable':<10} {'Dependencies'}")
    print("-" * 80)

    for entry in enriched[:20]:
        deps = ", ".join(entry["mathlib_deps"][:3]) if entry["mathlib_deps"] else "minimal"
        print(f"{entry['problem_num']:<6} {entry['gap_score']:<5} {entry['boris_score']:<6} "
              f"{len(entry['solved_theorems']):<8} {'Yes' if entry['has_decidable'] else 'No':<10} {deps}")

    # Also output problems with solved variants
    with_solved = [e for e in enriched if e["has_solved_variants"]]
    print(f"\n\nProblems with SOLVED variants ({len(with_solved)} total):")
    print("-" * 80)
    for entry in with_solved[:15]:
        solved = ", ".join(entry["solved_theorems"][:2])
        if len(entry["solved_theorems"]) > 2:
            solved += f" (+{len(entry['solved_theorems'])-2} more)"
        print(f"#{entry['problem_num']}: {solved}")


if __name__ == "__main__":
    main()
