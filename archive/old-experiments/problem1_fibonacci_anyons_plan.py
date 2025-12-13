#!/usr/bin/env python3
"""Problem 1: Fibonacci Anyon Braid Verification - Detailed Plan"""

import subprocess

prompt = """You are an expert in topological quantum computing and AI-assisted theorem proving. Help design the OPTIMAL Aristotle submission for Fibonacci anyon braid verification.

PROBLEM BACKGROUND:
Fibonacci anyons are quasi-particles used in topological quantum computing. Their braiding operations must satisfy specific algebraic constraints (unitarity, Yang-Baxter equations).

RECENT BREAKTHROUGH (2024):
Explicit braid matrices for Fibonacci anyons were published. We need to formally verify these satisfy the required constraints.

WHY THIS IS PERFECT FOR ARISTOTLE:
- ✅ Decidable: Matrix multiplication + equality checks
- ✅ Concrete instances: Specific braid matrices provided
- ✅ Batchable: Multiple braid sequences
- ✅ Like our proven Jones work: Algebraic verification
- ✅ Clear success criterion: Verify constraints satisfied

WHAT WE NEED TO DESIGN:

1. **EXACT PROBLEM SPECIFICATION**
   - What are the Fibonacci anyon braid matrices? (Find exact 2024 paper)
   - What constraints must they satisfy?
     - Unitarity: B^† B = I
     - Yang-Baxter: B_i B_{i+1} B_i = B_{i+1} B_i B_{i+1}
     - Pentagon equation?
   - What representation (dimension, field)?

2. **CONCRETE INSTANCES TO VERIFY**
   - How many braid generators? (σ_1, σ_2, ...)
   - Which braid sequences to test?
   - Should we test compositions?
   - Suggested batch size: 10-20 instances

3. **LEAN FORMALIZATION STRATEGY**
   - How to represent matrices in Lean?
   - Matrix library: Mathlib.LinearAlgebra.Matrix?
   - Finite fields or complex numbers?
   - How to express unitarity/Yang-Baxter in Lean?

4. **ARISTOTLE PROMPT DESIGN**
   - Informal vs formal input?
   - How much context about anyons?
   - Should we provide explicit matrices or matrix generation rules?
   - Reference to Jones polynomial connection?

5. **VALIDATION STRATEGY**
   - How to cross-check results?
   - Independent computation (SageMath, Mathematica)?
   - What would constitute success?

6. **EXPECTED CHALLENGES**
   - Complex number arithmetic in Lean?
   - Matrix size/complexity?
   - Timeout risks?

DELIVERABLES NEEDED:

A. **Exact constraint equations** (mathematical formulation)
B. **List of 10-20 test instances** (specific braids)
C. **Lean template** (how to represent problem)
D. **Aristotle prompt** (draft submission text)
E. **Validation plan** (how to verify results)
F. **Success criteria** (what constitutes passing)

BE MAXIMALLY SPECIFIC. Provide:
- Exact paper references (2024 Fibonacci anyon matrices)
- Concrete matrix dimensions
- Specific braid sequences to test
- Exact Lean syntax for constraints

This is the HIGHEST PRIORITY problem (80-90% success estimate).

Make it bulletproof.
"""

print("=" * 70)
print("PROBLEM 1: FIBONACCI ANYON BRAID VERIFICATION")
print("=" * 70)
print()
print("Phase 1: Gemini Detailed Design")
print("-" * 70)
print()

result = subprocess.run(
    ['gemini', '-p', prompt],
    capture_output=True, text=True, timeout=300
)

if result.returncode == 0:
    analysis = result.stdout

    print(analysis)
    print()

    with open('/Users/patrickkavanagh/math/PROBLEM1_FIBONACCI_ANYONS_PLAN.md', 'w') as f:
        f.write("# Problem 1: Fibonacci Anyon Braid Verification - Detailed Plan\n\n")
        f.write("**Date**: December 12, 2025\n")
        f.write("**Designer**: Gemini\n")
        f.write("**Priority**: HIGHEST (80-90% success estimate)\n\n")
        f.write("---\n\n")
        f.write(analysis)

    print("✅ Plan saved to PROBLEM1_FIBONACCI_ANYONS_PLAN.md")
    print()
    print("=" * 70)
    print("Next: Review with Grok for validation...")
    print("=" * 70)
else:
    print(f"❌ Error: {result.stderr}")
