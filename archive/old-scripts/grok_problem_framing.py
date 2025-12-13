#!/usr/bin/env python3
"""Ask Grok about optimal problem framing for Aristotle."""

import json
import subprocess
import os

prompt = """You are an expert in AI-assisted theorem proving, Lean 4, and proof assistant optimization. Analyze the problem framing for our 25-crossing knot verification.

CONTEXT:
We just submitted 20 knots at 25-crossing to Aristotle AI for formal verification. Our submission uses an informal problem statement with rich context about the Jones conjecture.

CURRENT FRAMING:
- Informal problem statement (~7.5KB text)
- Background on Jones Unknotting Conjecture
- 20 braid words provided (e.g., "(σ₁σ₂σ₁⁻¹σ₂⁻¹)⁶")
- Instructions to convert to PD codes and verify Jones ≠ 1
- Hints about Kauffman bracket algorithm
- Expected polynomial complexity warnings

CRITICAL QUESTIONS:

1. PROBLEM DECOMPOSITION:
   - Should we submit 20 knots at once vs. 1 knot at a time?
   - Does Aristotle handle batch problems better or worse?
   - Could batching cause it to fail on all if one is too hard?

2. FORMALIZATION LEVEL:
   - Informal text (what we did) vs. partial Lean definitions?
   - Should we provide explicit PD codes instead of braid words?
   - Should we provide the full Kauffman bracket expansion?
   - How much "work" should we do vs. let Aristotle figure out?

3. CONTEXT AMOUNT:
   - Is 7.5KB too much context (information overload)?
   - Or is rich context helpful for AI reasoning?
   - Should we strip to bare minimum: "Prove Jones ≠ 1 for these knots"?

4. REPRESENTATION FORMAT:
   - Braid words (what we used) - requires conversion
   - PD codes (planar diagram) - direct knot representation
   - DT codes (Dowker-Thistlethwaite) - more compact
   - Gauss codes - alternative representation
   Which format is easiest for Aristotle to work with?

5. PROOF STRATEGY HINTS:
   - Should we specify exact tactics to use?
   - Or let Aristotle explore freely?
   - Does "native_decide" hint help or constrain?
   - Should we reference our successful 9-crossing framework explicitly?

6. INCREMENTAL APPROACH:
   - Could we submit ONE hard 25-crossing knot first?
   - Then if successful, submit the batch?
   - Or is the batch submission already optimal?

7. COMPUTATIONAL HINTS:
   - Should we provide polynomial degree estimates?
   - Should we mention timeout expectations?
   - Does warning about complexity help or hurt?

8. ALTERNATIVE FRAMING:
   - Frame as "extend this pattern from 9-crossing to 25-crossing"?
   - Frame as "here's a successful proof, now do this harder case"?
   - Frame as pure mathematical challenge without context?
   - Which framing maximizes success probability?

9. LEAN 4 SCAFFOLDING:
   - Should we provide partial Lean definitions?
   - Should we give the full framework and just leave "sorry"s?
   - Would that be easier than informal text?

10. DECISION POINT:
    - Have we already optimized the framing?
    - Or should we CANCEL and resubmit with better framing?
    - Is it worth resubmitting if we can improve success rate?

BE BRUTALLY HONEST:
- Did we frame this optimally for Aristotle?
- What would you change?
- Is it worth canceling and resubmitting?
- Or should we let it run and learn from the results?

Give specific recommendations with concrete examples of better framings if you have them.
"""

print("🤖 Consulting Grok on Problem Framing Optimization...")
print("=" * 70)
print()

request = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-2-latest",
    "temperature": 0.3,
    "max_tokens": 4000
}

with open('/tmp/grok_framing_request.json', 'w') as f:
    json.dump(request, f, indent=2)

result = subprocess.run(
    ['curl', '-X', 'POST', 'https://api.x.ai/v1/chat/completions',
     '-H', f'Authorization: Bearer {os.environ.get("GROK_API_KEY")}',
     '-H', 'Content-Type: application/json',
     '-d', '@/tmp/grok_framing_request.json'],
    capture_output=True, text=True, timeout=300
)

if result.returncode == 0:
    response = json.loads(result.stdout)
    analysis = response['choices'][0]['message']['content']

    print("GROK ANALYSIS: PROBLEM FRAMING OPTIMIZATION")
    print("=" * 70)
    print()
    print(analysis)
    print()

    with open('/Users/patrickkavanagh/math/GROK_FRAMING_ANALYSIS.md', 'w') as f:
        f.write("# Grok Analysis: Problem Framing Optimization\n\n")
        f.write("**Date**: December 12, 2025\n")
        f.write("**Model**: grok-2-latest (temperature 0.3)\n\n")
        f.write("---\n\n")
        f.write(analysis)

    print("✅ Analysis saved to GROK_FRAMING_ANALYSIS.md")
else:
    print(f"❌ Error: {result.stderr}")
