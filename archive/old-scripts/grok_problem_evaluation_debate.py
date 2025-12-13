#!/usr/bin/env python3
"""Debate with Grok: Which of our 70 problems are ACTUALLY good Aristotle fits?"""

import json
import subprocess
import os

prompt = """You are an expert in AI-assisted theorem proving. Evaluate our problem portfolio against Aristotle's PROVEN capabilities.

ARISTOTLE'S PROVEN PROFILE (from Jones polynomial project):

✅ **STRENGTHS:**
- Decidable problems (native_decide tactics work perfectly)
- Computational verification (checking if computed_value ≠ target)
- Batch processing (10 similar instances in 3-4 minutes)
- Moderate complexity (9-crossing knots, 15-25 term polynomials)
- Well-specified problems (clear boolean success criteria)
- **Success rate: 18/18 (100%)**

❓ **UNKNOWNS (currently testing):**
- High complexity (25-crossing, currently IN PROGRESS)
- Very large batches (20 knots at once)

❌ **SUSPECTED WEAKNESSES:**
- Creative mathematical insights required
- Non-decidable theorem proving
- Ambiguous specifications
- Optimization (finding "best" vs verifying correctness)

---

OUR 70 INTERDISCIPLINARY PROBLEMS - EVALUATE THESE:

**TOP TIER (claimed 30-45% success):**

1. **Spectral Gap Bounds for Odd-Diameter Graphs**
   - Compute eigenvalues, prove bounds
   - Is this decidable via native_decide?
   - Can we batch test multiple graph instances?
   - **Aristotle fit: ???**

2. **Sorting Network Size Optimality (n=18)**
   - Prove 77-comparator network is optimal
   - Lower bound = prove 76 is impossible (negative search!)
   - Upper bound = verify 77 works (trivial)
   - **Aristotle fit: ???**

3. **Jones Polynomial Certifiable Cases**
   - Topological quantum computing application
   - Verify explicit Fibonacci anyon braid matrices
   - Is this similar to our Jones work?
   - **Aristotle fit: ???**

4. **Polar Codes Finite Blocklength Scaling**
   - Prove bounds on code performance
   - Is this decidable?
   - **Aristotle fit: ???**

5. **Resolution Complexity for Specific SAT Formulas**
   - Verify LRAT proofs
   - Resolution proofs are decidable
   - Can batch different formulas?
   - **Aristotle fit: ???**

6. **Quantum Query Complexity of Collision Problem**
   - Discrete query complexity
   - Is this decidable or requires creative insight?
   - **Aristotle fit: ???**

**HIGH VALUE (claimed 20-30% success):**

7. **F-Matrix Solvability for Fusion Rules**
   - Pentagon equation solvers exist (SageMath)
   - Could we verify solutions?
   - **Aristotle fit: ???**

8. **Type I [56,28,12] Self-Dual Code Existence**
   - Finite concrete problem
   - Search vs verification?
   - **Aristotle fit: ???**

9. **Online Bipartite Matching (degree d=3)**
   - Prove competitive ratio bounds
   - Decidable or creative?
   - **Aristotle fit: ???**

10. **Polynomial Calculus Resolution Space Lower Bounds**
    - Can verify for pebbling principles (n ≤ 15)
    - Small finite cases
    - **Aristotle fit: ???**

**OTHERS:**
- ~60 more problems across quantum complexity, statistical physics, coding theory, etc.

---

YOUR TASK - BE BRUTALLY ANALYTICAL:

For EACH problem above (at minimum the top 10):

1. **Is it decidable?**
   - Can native_decide solve it?
   - Or requires creative proof strategy?

2. **Is it well-specified?**
   - Clear boolean success criterion?
   - Or ambiguous "prove bounds" without concrete target?

3. **Is it batchable?**
   - Multiple similar instances?
   - Or one-off problem?

4. **Does it match Jones profile?**
   - Computational verification?
   - Moderate complexity?
   - Systematic structure?

5. **HONEST success estimate**
   - Given Aristotle's profile, what's REAL probability?
   - Not theoretical, but practical given our evidence

6. **Recommendation**
   - PURSUE (good fit)
   - TEST (worth trying but risky)
   - ABANDON (bad fit for Aristotle)

**CRITICAL EVALUATION:**

Which problems (if ANY) are actually as good a fit as Jones was?

Which are we fooling ourselves about?

Which have the "decidable core" that Aristotle needs?

Which require creative insights Aristotle probably can't do?

**Be SPECIFIC. Name problems. Give concrete yes/no on decidability. Challenge the success estimates.**

Don't tell me what I want to hear. Tell me what will actually work with Aristotle.
"""

print("⚔️  PROBLEM EVALUATION DEBATE")
print("=" * 70)
print()

request = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-2-latest",
    "temperature": 0.3,  # Lower for analytical rigor
    "max_tokens": 4096
}

with open('/tmp/grok_problem_eval_request.json', 'w') as f:
    json.dump(request, f, indent=2)

# Use gemini instead for reliability
print("Consulting Gemini for problem evaluation...")
import tempfile
with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as f:
    f.write(prompt)
    prompt_file = f.name

result = subprocess.run(
    ['gemini', '-p', prompt],
    capture_output=True, text=True, timeout=300
)

if result.returncode == 0:
    analysis = result.stdout

    print("GEMINI: PROBLEM PORTFOLIO EVALUATION")
    print("=" * 70)
    print()
    print(analysis)
    print()

    with open('/Users/patrickkavanagh/math/PROBLEM_EVALUATION_DEBATE.md', 'w') as f:
        f.write("# Problem Portfolio Evaluation - Aristotle Fit Analysis\n\n")
        f.write("**Date**: December 12, 2025\n")
        f.write("**Evaluator**: Gemini\n\n")
        f.write("---\n\n")
        f.write(analysis)

    print("✅ Evaluation saved to PROBLEM_EVALUATION_DEBATE.md")
else:
    print(f"❌ Error: {result.stderr}")

os.unlink(prompt_file)
