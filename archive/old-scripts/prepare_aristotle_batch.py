#!/usr/bin/env python3
"""
Prepare Aristotle batch for Jones polynomial verification.
Part of Jones Unknotting Conjecture project.
"""

import json
from pathlib import Path


def select_knots(json_file: Path, crossing_number: int, count: int) -> list:
    """Select knots with specific crossing number."""
    with open(json_file) as f:
        knots = json.load(f)

    # Filter by crossing number
    matching = [k for k in knots if k['crossings'] == crossing_number]

    # Prioritize non-alternating (these are the ones we need to verify)
    non_alternating = [k for k in matching if not k.get('alternating', True)]
    alternating = [k for k in matching if k.get('alternating', False)]

    # Return mix: prioritize non-alternating
    selected = non_alternating[:count]
    if len(selected) < count:
        selected.extend(alternating[:count - len(selected)])

    return selected[:count]


def generate_aristotle_input(knots: list, context_file: Path, output_file: Path):
    """Generate Aristotle input with full context."""

    # Read the full Jones polynomial framework
    with open(context_file) as f:
        context = f.read()

    # Build the task description
    task = """
CONTEXT - EXISTING JONES POLYNOMIAL FRAMEWORK:
========================================

The code below provides a complete Lean 4 formalization of the Jones polynomial via the Kauffman bracket algorithm.
It includes LinkDiagram definitions, crossing structures, bracket computation, and Jones polynomial calculation.
This framework has been verified on 8 knots (3_1, 4_1, 5_1, 5_2, 6_1, 6_2, 6_3, 7_1).

"""

    # Add all 626 lines of context
    task += context

    task += """

TASK - PROVE JONES ≠ 1 FOR NEW KNOTS:
=====================================

We are working on the Jones Unknotting Conjecture: Does any non-trivial knot have Jones polynomial = 1?

For EACH knot in the list below, please:
1. Define the LinkDiagram from the PD code
2. Compute the Jones polynomial using the existing framework
3. Prove that jones_polynomial ≠ 1 using native_decide

"""

    task += f"KNOT LIST ({len(knots)} knots at {knots[0]['crossings']} crossings):\n"
    task += "-" * 70 + "\n\n"

    for i, knot in enumerate(knots, 1):
        task += f"{i}. Knot {knot['name']} ({knot['crossings']} crossings)\n"
        task += f"   PD code: {knot['pd_notation']}\n"
        task += f"   Known Jones: {knot.get('jones_polynomial', 'unknown')}\n"
        task += f"   Alternating: {knot.get('alternating', 'unknown')}\n"
        task += f"\n"

    task += """
STRATEGY:
---------
1. For each knot, define the LinkDiagram using the PD code (similar to existing examples)
2. Determine the correct crossing signs to match the known Jones polynomial
3. Compute jones_polynomial using the existing framework
4. Prove jones_polynomial K ≠ 1 using native_decide
5. Output one theorem per knot

EXPECTED OUTPUT:
---------------
For each knot K, produce a theorem:

theorem jones_neq_one_K : jones_polynomial K ≠ 1 := by native_decide

NOTES:
------
- The Jones polynomial framework includes writhe normalization (A^(-3*writhe))
- You may need to adjust crossing signs to match the known polynomials
- Use native_decide for automatic verification
- All 8 existing knots have been verified this way

"""

    # Write output
    with open(output_file, 'w') as f:
        f.write(task)

    print(f"✅ Aristotle input prepared: {output_file}")
    print(f"   {len(knots)} knots selected")
    print(f"   Crossing number: {knots[0]['crossings']}")
    print(f"   File size: {len(task):,} characters")
    print(f"\nKnots included:")
    for knot in knots:
        alt_status = "ALT" if knot.get('alternating', False) else "NON-ALT"
        print(f"   - {knot['name']} ({alt_status})")


def main():
    math_dir = Path("/Users/patrickkavanagh/math")

    # Select 10 knots at 9 crossings
    knots = select_knots(
        json_file=math_dir / "knots_database_10.json",
        crossing_number=9,
        count=10
    )

    if not knots:
        print("❌ No knots found at 9 crossings")
        return

    # Generate Aristotle input with FULL context
    generate_aristotle_input(
        knots=knots,
        context_file=math_dir / "ad54d62b-5420-423c-b1da-4ecb46438de7-output.lean",
        output_file=math_dir / "unknotting" / "aristotle_batch_9crossing_test.txt"
    )

    print("\n✅ Ready to launch!")
    print("\nNext step:")
    print("   aristotle prove-from-file --informal unknotting/aristotle_batch_9crossing_test.txt")


if __name__ == "__main__":
    main()
