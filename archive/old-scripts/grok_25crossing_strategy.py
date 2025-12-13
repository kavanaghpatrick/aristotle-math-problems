#!/usr/bin/env python3
"""Consult Grok on optimal 25-crossing strategy for Aristotle submission."""

import json
import subprocess
import os

prompt = """You are an expert in knot theory and computational topology. Help design the optimal strategy for formally verifying 25-crossing knots using Aristotle AI + Lean 4.

CONTEXT:
We're blasting past the computational state-of-the-art (24 crossings) to formally verify knots at 25 crossings using Aristotle AI.

CRITICAL CHALLENGE: 25-crossing knots are NOT enumerated in standard databases.

STRATEGIC QUESTIONS:

1. KNOT GENERATION STRATEGY:
   - How do we identify/generate 25-crossing knots?
   - Should we use braid closures? Which braid indices?
   - Random knot generation? Specific algorithms?
   - How to ensure they're actually 25-crossing (not fewer)?
   - How to ensure non-trivial (not unknots)?

2. INITIAL BATCH SIZE:
   - Start with 10 knots? 20? 50?
   - What's the right balance between "test feasibility" and "enough for breakthrough"?
   - If we only get 5-10 successful, is that enough for Nature paper?

3. COMPUTATIONAL FEASIBILITY:
   - Which 25-crossing knots are most likely to succeed?
   - Prioritize by: braid index, genus, hyperbolic volume?
   - Should we start with 4-strand braids (simpler) or go directly to 5-strand?
   - What's the expected Jones polynomial complexity at 25 crossings?

4. ARISTOTLE CONTEXT:
   - What context should we provide to Aristotle in the informal problem statement?
   - Should we mention the conjecture background?
   - Should we provide hints about computational strategy?
   - How detailed should the problem description be?

5. VALIDATION STRATEGY:
   - How do we validate 25-crossing results (no database to cross-check)?
   - Independent computation with SnapPy/Mathematica?
   - Multiple independent braid representations?
   - What confidence level do we need?

6. RISK MITIGATION:
   - What if Aristotle times out on all 25-crossing knots?
   - Should we have a fallback batch at 20-crossing (known feasible)?
   - What's the minimum success rate to still claim breakthrough?

7. PRIORITIZATION:
   - If we can only formally verify 5 knots at 25-crossing, is that enough?
   - Should we aim for diversity (different knot types) or simplicity (all 4-strand braids)?
   - What would make the strongest Nature paper?

8. LEAN 4 REPRESENTATION:
   - How should we represent 25-crossing knots in Lean?
   - PD codes? Braid words? DT codes?
   - What format is most likely to succeed with Aristotle?

BE SPECIFIC AND PRACTICAL. We're submitting to Aristotle in the next hour.

Give concrete recommendations:
- Exact braid words for first 10-20 test knots
- Problem statement template for Aristotle
- Success criteria for proceeding vs pivoting

This is a GO/NO-GO decision point. Be brutally honest about feasibility.
"""

print("🤖 Consulting Grok on 25-Crossing Strategy...")
print("=" * 70)
print()

request = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-2-latest",
    "temperature": 0.3,
    "max_tokens": 4000
}

with open('/tmp/grok_25crossing_request.json', 'w') as f:
    json.dump(request, f, indent=2)

result = subprocess.run(
    ['curl', '-X', 'POST', 'https://api.x.ai/v1/chat/completions',
     '-H', f'Authorization: Bearer {os.environ.get("GROK_API_KEY")}',
     '-H', 'Content-Type: application/json',
     '-d', '@/tmp/grok_25crossing_request.json'],
    capture_output=True, text=True, timeout=300
)

if result.returncode == 0:
    response = json.loads(result.stdout)
    analysis = response['choices'][0]['message']['content']

    print("GROK STRATEGIC RECOMMENDATIONS")
    print("=" * 70)
    print()
    print(analysis)
    print()

    with open('/Users/patrickkavanagh/math/GROK_25CROSSING_STRATEGY.md', 'w') as f:
        f.write("# Grok 25-Crossing Strategy\n\n")
        f.write("**Date**: December 12, 2025\n")
        f.write("**Model**: grok-2-latest (temperature 0.3)\n\n")
        f.write("---\n\n")
        f.write(analysis)

    print("✅ Strategy saved to GROK_25CROSSING_STRATEGY.md")
else:
    print(f"❌ Error: {result.stderr}")
