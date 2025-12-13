#!/usr/bin/env python3
"""Grok Optimization Round 1: Detailed plan for optimal 25-crossing submission."""

import json
import subprocess
import os

prompt = """You are an expert in Lean 4, knot theory, and AI-assisted theorem proving. Help design the OPTIMAL submission for 25-crossing knots to Aristotle AI.

CONTEXT:
- We submitted 20 knots with suboptimal framing (batch, braid words, 7.5KB context)
- Both Codex and Grok-2 recommended canceling and optimizing
- Key issues: Too large batch, wrong format, too much context, no scaffolding

YOUR TASK:
Design the OPTIMAL submission strategy from scratch. Be MAXIMALLY SPECIFIC.

CRITICAL DESIGN QUESTIONS:

1. KNOT SELECTION & REPRESENTATION:
   - How do we generate ACTUAL 25-crossing knots (not just braid words)?
   - Should we use SnapPy, Mathematica, or something else?
   - Exact commands to generate PD codes from braid words?
   - How to verify crossing count is exactly 25?
   - How to verify knot is non-trivial?

2. JONES POLYNOMIAL PRECOMPUTATION:
   - Should we precompute Jones polynomials?
   - Use SnapPy? KnotTheory (Mathematica)? Both for validation?
   - Exact format for polynomial (Laurent, standard, SparsePoly)?
   - How to convert to Lean-compatible format?

3. LEAN SCAFFOLDING DESIGN:
   - Exact template structure for Lean file?
   - What imports are needed?
   - How to represent PD codes in Lean?
   - How to represent Jones polynomial in Lean?
   - What theorem statement format?
   - How much to leave as "sorry" vs. fill in?

4. CONTEXT DESIGN:
   - Exact wording for minimal context?
   - 1-2 paragraphs - what should they say?
   - Should we reference our successful 9-crossing batch?
   - How to frame the difficulty without biasing toward failure?

5. SUBMISSION STRATEGY:
   - Submit ONE knot first as test?
   - Which knot (simplest, most complex, median)?
   - Sequential submission or small batches?
   - How to parallelize without overwhelming queue?

6. REFERENCE EXAMPLE:
   - Should we extract one 9-crossing proof as template?
   - If yes, which knot (9_1, 9_42, etc.)?
   - How to annotate it for clarity?
   - Should we include it inline or as separate file?

7. VALIDATION BEFORE SUBMISSION:
   - How to validate PD codes are correct?
   - How to validate Jones polynomials are correct?
   - How to validate Lean syntax is correct?
   - Cross-checking strategy?

8. EXPECTED CHALLENGES:
   - What could still go wrong with optimized approach?
   - How to detect if a knot is too hard?
   - Timeout threshold before marking as infeasible?
   - Fallback strategy if 25-crossing proves too hard?

DELIVERABLES NEEDED:

Please provide EXACT specifications:

A. Python script to generate PD codes from braid words using SnapPy
   - Include exact SnapPy commands
   - Include validation steps
   - Include error handling

B. Python script to compute Jones polynomials
   - Using SnapPy
   - Convert to Lean format
   - Cross-validate with Mathematica if possible

C. Lean template file structure
   - Exact imports
   - Exact representation of PD code
   - Exact representation of Jones polynomial
   - Exact theorem statement
   - Exact proof structure with strategic "sorry"s

D. Minimal context template (1-2 paragraphs)
   - Exact wording
   - What to include, what to exclude

E. Submission order
   - Which knot to test first?
   - How to proceed after first result?

F. Success criteria
   - What success rate constitutes breakthrough?
   - When to pivot vs. persist?

BE MAXIMALLY SPECIFIC. Give actual code, exact Lean syntax, exact SnapPy commands.

This is Round 1 of optimization. We'll refine based on your recommendations.
"""

print("🔄 OPTIMIZATION ROUND 1: Detailed Design")
print("=" * 70)
print()

request = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-2-latest",
    "temperature": 0.2,  # Lower for precise technical recommendations
    "max_tokens": 4096
}

with open('/tmp/grok_opt_round1_request.json', 'w') as f:
    json.dump(request, f, indent=2)

result = subprocess.run(
    ['curl', '-X', 'POST', 'https://api.x.ai/v1/chat/completions',
     '-H', f'Authorization: Bearer {os.environ.get("GROK_API_KEY")}',
     '-H', 'Content-Type: application/json',
     '-d', '@/tmp/grok_opt_round1_request.json'],
    capture_output=True, text=True, timeout=300
)

if result.returncode == 0:
    response = json.loads(result.stdout)
    analysis = response['choices'][0]['message']['content']

    print("GROK ROUND 1: DETAILED DESIGN")
    print("=" * 70)
    print()
    print(analysis)
    print()

    with open('/Users/patrickkavanagh/math/GROK_OPT_ROUND1.md', 'w') as f:
        f.write("# Grok Optimization Round 1: Detailed Design\n\n")
        f.write("**Date**: December 12, 2025\n")
        f.write("**Model**: grok-2-latest (temperature 0.2)\n\n")
        f.write("---\n\n")
        f.write(analysis)

    print("✅ Round 1 saved to GROK_OPT_ROUND1.md")
else:
    print(f"❌ Error: {result.stderr}")
