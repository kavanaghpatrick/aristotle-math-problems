#!/usr/bin/env python3
"""
Comprehensive audit: Failed attempts + Top tier-1/tier-2 issues to launch.
"""

import json
import subprocess
import sys
import os

api_key = os.environ.get('GROK_API_KEY')
if not api_key:
    print("❌ GROK_API_KEY not set", file=sys.stderr)
    sys.exit(1)

# Read the summary
with open('ARISTOTLE_RESULTS_SUMMARY.md', 'r') as f:
    summary = f.read()

question = f"""COMPREHENSIVE AUDIT: Failed Attempts + Best New Problems to Launch

You are conducting a comprehensive audit to prepare for a mass launch of Aristotle problems.

---

## PART 1: FAILED ATTEMPTS - HOW TO FIX

### Issue #25: PHP Resolution Width (TIMEOUT)

**What was attempted:**
- Prove PHP_10 resolution width lower bounds
- 231 lines of partial formalization
- Aristotle timeout - couldn't complete

**Problem:** Width problems are harder than size problems.

**Question:** How should we reformulate this to succeed?
- Simpler target (PHP_5 instead of PHP_10)?
- Different approach (width-size tradeoff)?
- Concrete computational verification instead of general proof?
- Or abandon width entirely and focus on tighter size bounds?

**Your task:** Provide improved problem statement for PHP width/size.

---

### Issue #23: Sorting Networks (FALSE CLAIM)

**What happened:**
- Proved C(18) ≤ 82 using Batcher's algorithm
- Claimed "improves upon 86" (false - current best is 77)
- Just formalized 1960s algorithm

**Question:** Should we retry sorting networks?
- Option A: Prove C(18) = 77 is OPTIMAL (lower bound)
- Option B: Formalize known network with 77 comparators
- Option C: Abandon (too hard for Aristotle)

**Your task:** If retrying, provide improved formulation. If not, explain why.

---

## PART 2: BEST UNTRIED TIER-1/TIER-2 ISSUES

**Available issues (never attempted):**

### Tier-1 Highest (35-45% success):
1. **Issue #21**: Spectral Gap Bounds for Odd-Diameter Graphs
2. **Issue #26**: Polar Codes Finite Blocklength Scaling Constants
3. **Issue #27**: Quantum Query Complexity - Collision Problem Lower Bound
4. **Issue #28**: Quantum Communication Complexity - Set Disjointness Gap
5. **Issue #29**: Two-Sided Vertex Expansion Beyond 60%

### Tier-2 High (20-40% success):
6. **Issue #30**: Antiferromagnetic Potts Model - Partition Function Bounds
7. **Issue #31**: F-Matrix Solvability for Fusion Rules
8. **Issue #32**: Type I [56,28,12] Self-Dual Code Existence
9. **Issue #33**: Online Bipartite Matching for d=3 Graphs
10. **Issue #34**: Longest Increasing Subsequence Streaming Lower Bound
11. **Issue #35**: Polynomial Calculus Resolution Space Lower Bounds
12. **Issue #36**: Lossless Bipartite Expanders - Unbalanced Settings
13. **Issue #37**: Topological Entanglement Entropy Lower Bound
14. **Issue #38**: Ingleton Inequality Maximum Violation
15. **Issue #39**: Boolean Promise Constraint Satisfaction Dichotomy
16. **Issue #40**: Linear Programming Bound Improvement for Binary Codes
17. **Issue #41**: QAOA Depth-2 Optimality for MaxCut on 3-Regular Graphs

---

## YOUR COMPREHENSIVE TASK

### 1. Failed Attempts Analysis

For **Issue #25 (PHP Width/Size)** and **Issue #23 (Sorting Networks)**:

**Provide:**
- Should we retry? YES/NO
- If YES: Improved problem statement following HQC v3 pattern (concrete, forces structure exploitation)
- If NO: Brief explanation why

### 2. Top 5 Tier-1/Tier-2 Issues to Launch

**Select the 5 BEST issues from the list above based on:**
- Formalizability in Lean 4
- Concrete parameters available
- Can follow successful patterns (HQC v3, Jones v2)
- Genuine novelty potential (not just formalization)
- Success probability >25%

**For each of the 5:**
1. **Issue number and title**
2. **Why this is a good target** (1-2 sentences)
3. **Key challenge** (what makes it hard)
4. **Success strategy** (how to formulate for Aristotle)
5. **Concrete parameters** (specific values to use)
6. **Success probability** (1-100%)

### 3. Problem Formulation Patterns

**Based on our successes (HQC v3, Jones v2), what patterns should ALL problems follow?**

**Provide:**
- ✅ Must have (concrete parameters, quantitative bounds, etc.)
- ❌ Must avoid (binary questions, abstract types, etc.)
- 📋 Template structure for Aristotle input files

---

## CRITICAL LESSONS LEARNED

**From HQC v3 success:**
- FORCE structure exploitation (don't make it optional)
- Specific goals (FFT eigenvalues, automorphism groups)
- Red flags prevent reverting to generic approaches

**From Jones v2 improvement:**
- Concrete instances (trefoil knot) not abstract (alternating knots)
- Quantitative bounds (O(c^3)) not binary (polynomial-time?)
- Verification component (known polynomials)

**From past failures:**
- v2 formalized known bounds (no novelty)
- Jones v1 used abstract types (framework only)
- Sorting networks claimed false improvement

**Apply these lessons to your recommendations!**

---

## OUTPUT FORMAT

```
## PART 1: FAILED ATTEMPTS

### Issue #25: PHP Width/Size
Retry: YES/NO
Rationale: ...
[If YES] Improved Problem Statement:
...

### Issue #23: Sorting Networks
Retry: YES/NO
Rationale: ...
[If YES] Improved Problem Statement:
...

## PART 2: TOP 5 TIER-1/TIER-2 ISSUES

### #1: [Issue #XX - Title]
Why: ...
Challenge: ...
Strategy: ...
Parameters: ...
Success Probability: XX%
Problem Statement Preview:
...

[Repeat for #2-5]

## PART 3: UNIVERSAL PROBLEM FORMULATION TEMPLATE

[Provide template structure that all problems should follow]

## PART 4: LAUNCH PRIORITY

[Rank all problems (failed retries + top 5) by launch priority 1-7]
```

Be brutally honest about success probabilities. Use lessons from HQC v3 and Jones v2!
"""

request = {
    "messages": [{"role": "user", "content": question}],
    "model": "grok-2-1212",
    "temperature": 0.3  # Balanced creativity + rigor
}

with open('/tmp/grok_comprehensive_audit_request.json', 'w') as f:
    json.dump(request, f)

print("🔍 Asking Grok for comprehensive audit...")
print("🎯 Failed attempts + Top 5 tier-1/tier-2 issues")
print("🌡️  Temperature: 0.3 (balanced mode)")
print()

result = subprocess.run(
    [
        'curl', '-X', 'POST',
        'https://api.x.ai/v1/chat/completions',
        '-H', 'Content-Type: application/json',
        '-H', f'Authorization: Bearer {api_key}',
        '-d', '@/tmp/grok_comprehensive_audit_request.json',
        '--max-time', '300'
    ],
    capture_output=True,
    text=True
)

if result.returncode != 0:
    print(f"❌ Error: {result.stderr}", file=sys.stderr)
    sys.exit(1)

try:
    response = json.loads(result.stdout)
    audit = response['choices'][0]['message']['content']
    print(audit)
    print()

    with open('/tmp/grok_comprehensive_audit.txt', 'w') as f:
        f.write(audit)

    print("💾 Saved to: /tmp/grok_comprehensive_audit.txt")

except Exception as e:
    print(f"❌ Error: {e}", file=sys.stderr)
    print(f"Raw: {result.stdout}", file=sys.stderr)
    sys.exit(1)
