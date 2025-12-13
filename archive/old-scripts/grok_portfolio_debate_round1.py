#!/usr/bin/env python3
"""Debate Round 1 with Grok: Are we focusing on the right problems?"""

import json
import subprocess
import os

prompt = """You are a strategic advisor for AI-assisted theorem proving research. Engage in a BRUTALLY HONEST debate about problem selection.

CONTEXT:
We have ~70 unsolved problems identified across multiple domains (quantum complexity, coding theory, expander graphs, statistical physics, etc.). We also have deep experience with Aristotle AI from our Jones polynomial project.

ARISTOTLE'S PROVEN STRENGTHS (from our experience):
- ✅ Decidable problems (native_decide tactics)
- ✅ Computational verification (check if X = Y)
- ✅ Batch processing (10+ similar instances)
- ✅ Moderate complexity (not too hard, not trivial)
- ✅ Well-specified problems (clear success criteria)

ARISTOTLE'S PROVEN PERFORMANCE:
- 10 knots at 9-crossing: 3-4 minutes, 100% success
- Jones ≠ 1 verification: native_decide worked perfectly
- 0 sorries, 96 theorems proved
- 10-40x faster than expected

ARISTOTLE'S SUSPECTED WEAKNESSES (not tested):
- ❌ Creative mathematical insights required
- ❌ Non-decidable problems
- ❌ Extremely complex state spaces
- ❌ Ambiguous specifications

OUR CURRENT PROBLEM PORTFOLIO (~70 problems):

**Top Tier (30-45% success):**
1. Spectral Gap Bounds for Odd-Diameter Graphs (30-45%)
2. Sorting Network Size Optimality n=18 (35%)
3. Jones Polynomial Certifiable Cases (30-40%)
4. Polar Codes Finite Blocklength Scaling (30-35%)
5. Resolution Complexity for Specific SAT Formulas (35%)
6. Quantum Query Complexity of Collision Problem (30%)
7. Quantum Communication Complexity of Disjointness (30%)

**High Value (20-30% success):**
8. Two-Sided Vertex Expansion Beyond 60% (25-40%)
9. Antiferromagnetic Potts Model Partition Function Bounds (25-35%)
10. F-Matrix Solvability for Fusion Rules (25-35%)
11. Type I [56,28,12] Self-Dual Code Existence (25-30%)
12. Online Bipartite Matching (degree d=3) (25%)
13. LIS Streaming Lower Bound (25%)
14. Polynomial Calculus Resolution Space Lower Bounds (25%)
15-20: Several more in 20-25% range

**Medium Value (15-20% success):**
21+: ~30 more problems

**Lower Tier (5-15% success):**
~20 more problems in quantum complexity, physics, etc.

CRITICAL STRATEGIC QUESTION:

**Are we chasing the WRONG problems?**

Our Jones polynomial project:
- Perfect Aristotle fit (decidable, systematic, verifiable)
- 100% success rate
- 10-40x faster than expected
- Could complete 1,126 knots this week
- Guaranteed Tier 2-3 publication
- 25-crossing attempt: Nature-level if it works

Contrast with our ~70 problem portfolio:
- Success rates: 5-45% (much lower!)
- Many not obviously decidable
- May require creative insights
- Formalizability: MEDIUM to HARD
- Most are one-off problems (not systematic)

**DEBATE POINTS:**

1. **Are we spreading too thin?**
   - Should we focus on Jones (proven winner) vs 70 uncertain problems?
   - Is portfolio diversification smart or wasteful?

2. **Do these problems leverage Aristotle's strengths?**
   - How many are decidable vs creative?
   - How many can be batched vs one-off?
   - How many have clear verification paths?

3. **Are success rates realistic?**
   - Jones: 100% success (proven)
   - Portfolio: 5-45% success (estimated)
   - Are we overestimating chances on these problems?

4. **What's the opportunity cost?**
   - Time spent on 70 problems vs finishing Jones 12-crossing
   - Time spent on 25-crossing optimization
   - Could we publish Jones THIS WEEK if we focused?

5. **What makes sense strategically?**
   Option A: Double down on Jones (1,126 knots, guaranteed win)
   Option B: Diversify to 70 problems (higher risk, potentially higher reward?)
   Option C: Focus on TOP 5-10 problems that best match Aristotle's strengths

6. **Which problems actually match Aristotle's profile?**
   - Decidable core
   - Systematic/batchable
   - Moderate complexity
   - Well-specified
   - Verifiable

**YOUR TASK:**

BRUTALLY evaluate our portfolio. Tell us:
1. Are we pursuing the right strategy?
2. Which problems (if any) from our 70 are actually good Aristotle fits?
3. Should we abandon most of these and focus on Jones?
4. Or is diversification actually smart?
5. What's the HIGHEST IMPACT path forward?

Be SPECIFIC. Name problems. Rank them. Challenge our assumptions.

DON'T BE NICE. Be strategically ruthless. What should we ACTUALLY be working on?
"""

print("⚔️  DEBATE ROUND 1: Portfolio Strategic Evaluation")
print("=" * 70)
print()

request = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-2-latest",
    "temperature": 0.5,  # Balanced for debate
    "max_tokens": 4096
}

with open('/tmp/grok_debate_r1_request.json', 'w') as f:
    json.dump(request, f, indent=2)

result = subprocess.run(
    ['curl', '-X', 'POST', 'https://api.x.ai/v1/chat/completions',
     '-H', f'Authorization: Bearer {os.environ.get("GROK_API_KEY")}',
     '-H', 'Content-Type: application/json',
     '-d', '@/tmp/grok_debate_r1_request.json'],
    capture_output=True, text=True, timeout=300
)

if result.returncode == 0:
    response = json.loads(result.stdout)
    analysis = response['choices'][0]['message']['content']

    print("GROK ROUND 1: BRUTAL STRATEGIC EVALUATION")
    print("=" * 70)
    print()
    print(analysis)
    print()

    with open('/Users/patrickkavanagh/math/GROK_DEBATE_ROUND1.md', 'w') as f:
        f.write("# Grok Debate Round 1: Portfolio Strategic Evaluation\n\n")
        f.write("**Date**: December 12, 2025\n")
        f.write("**Model**: grok-2-latest (temperature 0.5)\n\n")
        f.write("---\n\n")
        f.write(analysis)

    print("✅ Round 1 saved to GROK_DEBATE_ROUND1.md")
else:
    print(f"❌ Error: {result.stderr}")
