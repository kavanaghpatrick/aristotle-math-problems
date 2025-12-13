#!/usr/bin/env python3
"""Systematically plan and validate all 5 focused problems"""

import subprocess
import time

print("=" * 70)
print("SYSTEMATIC PLANNING: THE FOCUSED FIVE")
print("=" * 70)
print()

# Problem definitions
problems = [
    {
        "id": 1,
        "name": "Fibonacci Anyon Braid Verification",
        "priority": "HIGHEST",
        "success_rate": "80-90%",
        "prompt": """Design COMPLETE plan for Fibonacci anyon braid verification.

REQUIREMENTS:
1. Exact matrices (F-matrix, R-matrix) from 2024 papers
2. Specific constraints: Unitarity, Yang-Baxter, Pentagon
3. 10-20 test instances (specific braid sequences)
4. Lean formalization strategy (exact libraries)
5. Aristotle prompt (complete submission text)
6. Validation plan (how to verify results)

BE MAXIMALLY SPECIFIC with exact mathematics."""
    },
    {
        "id": 2,
        "name": "Resolution/LRAT Proof Verification",
        "priority": "HIGH",
        "success_rate": "70-85%",
        "prompt": """Design COMPLETE plan for SAT resolution proof verification.

REQUIREMENTS:
1. Identify LRAT proof databases (specific sources)
2. Which SAT formulas to test (10-20 instances)
3. Lean LRAT verification libraries (do they exist?)
4. Proof format (how to provide to Aristotle)
5. Aristotle prompt (submission text)
6. Validation (how to verify Lean checked proofs correctly)

BE SPECIFIC about data sources and formats."""
    },
    {
        "id": 3,
        "name": "F-Matrix Pentagon Equation Verification",
        "priority": "HIGH",
        "success_rate": "70-80%",
        "prompt": """Design COMPLETE plan for fusion category F-matrix verification.

REQUIREMENTS:
1. Pentagon equation exact formulation
2. Use SageMath to generate candidate F-matrices (10-20 instances)
3. Which fusion categories to test
4. Lean formalization of pentagon equation
5. Aristotle prompt
6. Validation strategy

BE SPECIFIC about SageMath commands and matrix dimensions."""
    },
    {
        "id": 4,
        "name": "Spectral Gap Eigenvalue Verification",
        "priority": "MEDIUM-HIGH",
        "success_rate": "60-75%",
        "prompt": """Design COMPLETE plan for graph spectral gap verification.

REQUIREMENTS:
1. How to generate candidate graphs (specific algorithms)
2. Which graphs to test (10-20 instances)
3. Spectral gap bounds to verify
4. Lean eigenvalue computation (library support?)
5. Aristotle prompt
6. Validation (independent eigenvalue computation)

BE SPECIFIC about graph generation and bounds."""
    },
    {
        "id": 5,
        "name": "PCR Space Lower Bounds (n≤15)",
        "priority": "MEDIUM",
        "success_rate": "60-70%",
        "prompt": """Design COMPLETE plan for Polynomial Calculus Resolution space bounds.

REQUIREMENTS:
1. Specific instances (n=10, 12, 15)
2. Pebbling principles formulation
3. How to represent in Lean
4. Aristotle prompt
5. Validation strategy

BE SPECIFIC about which pebbling instances."""
    }
]

print(f"Planning {len(problems)} problems systematically...")
print()

for prob in problems:
    print("=" * 70)
    print(f"PROBLEM {prob['id']}: {prob['name']}")
    print(f"Priority: {prob['priority']} | Success Rate: {prob['success_rate']}")
    print("=" * 70)
    print()

    print(f"Phase 1: Gemini Initial Design")
    print("-" * 70)

    result = subprocess.run(
        ['gemini', '-p', prob['prompt']],
        capture_output=True, text=True, timeout=300
    )

    if result.returncode == 0:
        design = result.stdout

        # Save to file
        filename = f'/Users/patrickkavanagh/math/PROBLEM{prob["id"]}_PLAN.md'
        with open(filename, 'w') as f:
            f.write(f"# Problem {prob['id']}: {prob['name']}\n\n")
            f.write(f"**Priority**: {prob['priority']}\n")
            f.write(f"**Success Rate**: {prob['success_rate']}\n\n")
            f.write("---\n\n")
            f.write("## Gemini Initial Design\n\n")
            f.write(design)

        print(f"✅ Initial design saved to {filename}")
        print()

        # Show summary (first 500 chars)
        print("DESIGN SUMMARY:")
        print(design[:800] + "...\n" if len(design) > 800 else design)
        print()

    else:
        print(f"❌ Error: {result.stderr}")
        print()

    # Brief pause between problems
    if prob['id'] < len(problems):
        print("⏸️  Pausing 2 seconds before next problem...")
        time.sleep(2)
        print()

print("=" * 70)
print("✅ INITIAL DESIGNS COMPLETE FOR ALL 5 PROBLEMS")
print("=" * 70)
print()
print("Next steps:")
print("1. Review each plan")
print("2. Validate with Grok (cross-check designs)")
print("3. Refine based on feedback")
print("4. Create Aristotle submission files")
print("5. Get final consensus")
print("6. Submit!")
