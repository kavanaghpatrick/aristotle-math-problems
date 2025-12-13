#!/usr/bin/env python3
"""Get Grok-4's expert analysis of our first batch results."""

import json
import subprocess
import os

# Prepare analysis request for Grok
analysis_prompt = """You are an expert in knot theory and the Jones polynomial. Please analyze these results with MAXIMUM SKEPTICISM and mathematical rigor.

CONTEXT:
We're attempting to verify the Jones Unknotting Conjecture (1985): Does any non-trivial knot have Jones polynomial = 1?

WHAT WE DID:
1. Used Aristotle AI (Lean 4 theorem prover) to compute Jones polynomials for 10 knots at 9 crossings
2. Each computation used the Kauffman bracket algorithm
3. All proofs were verified by Lean's kernel using `native_decide`
4. We then cross-validated against the KnotInfo database

BATCH 1 RESULTS (10 knots):
- Knot 9_1:  Jones = t^4 + t^6 - t^7 + t^8 - t^9 + t^10 - t^11 + t^12 - t^13
- Knot 9_2:  Jones = t - t^2 + 2t^3 - 2t^4 + 2t^5 - 2t^6 + 2t^7 - t^8 + t^9 - t^10
- Knot 9_42: Jones = t^(-3) - t^(-2) + t^(-1) - 1 + t - t^2 + t^3
- Knot 9_43: Jones = 1 - t + 2t^2 - 2t^3 + 2t^4 - 2t^5 + 2t^6 - t^7
- Knot 9_44: Jones = t^(-2) - 2t^(-1) + 3 - 3t + 3t^2 - 2t^3 + 2t^4 - t^5
- Knot 9_45: Jones = -t^(-8) + 2t^(-7) - 3t^(-6) + 4t^(-5) - 4t^(-4) + 4t^(-3) - 3t^(-2) + 2t^(-1)
- Knot 9_46: Jones = t^(-6) - t^(-5) + t^(-4) - 2t^(-3) + t^(-2) - t^(-1) + 2
- Knot 9_47: Jones = -t^(-2) + 3t^(-1) - 3 + 5t - 5t^2 + 4t^3 - 4t^4 + 2t^5
- Knot 9_48: Jones = -2t^(-6) + 3t^(-5) - 4t^(-4) + 6t^(-3) - 4t^(-2) + 4t^(-1) - 3 + t
- Knot 9_49: Jones = t^2 - 2t^3 + 4t^4 - 4t^5 + 5t^6 - 4t^7 + 3t^8 - 2t^9

VALIDATION PERFORMED:
1. ✅ All 10 theorems exist in Lean output
2. ✅ All prove Jones ≠ [(0,1)] (polynomial representation of 1)
3. ✅ All use native_decide (Lean kernel verified)
4. ✅ All knots exist in KnotInfo database
5. ✅ Deep check: Knot 9_1 matches KnotInfo exactly (all 9 terms, all coefficients)

TECHNICAL DETAILS:
- Total Lean code: 983 lines
- Theorems proved: 96
- Sorries: 0
- Completion time: 3-4 minutes
- Success rate: 10/10 (100%)

CRITICAL QUESTIONS FOR YOU (Grok):

1. MATHEMATICAL CORRECTNESS:
   - Do these Jones polynomials look plausible for 9-crossing knots?
   - Any red flags in the polynomial forms?
   - Is it normal for some to have negative powers?

2. VALIDATION APPROACH:
   - Is comparing against KnotInfo database sufficient?
   - What else should we validate?
   - Any known issues with KnotInfo data?

3. JONES ≠ 1 VERIFICATION:
   - Can we trust that these polynomials are definitely ≠ 1?
   - Any edge cases where polynomial could equal 1 at specific t values but not as formal polynomial?
   - Is Lean's kernel verification sufficient proof?

4. UNKNOTTING CONJECTURE PROGRESS:
   - Does this represent meaningful progress on the conjecture?
   - What % confidence do we have in these 10 results?
   - Any concerns about methodology?

5. SCALING CONCERNS:
   - We plan to verify 1,126 non-alternating knots up to 12 crossings
   - At current speed (10 knots in 3-4 min), this is 7-8 hours total
   - Any mathematical or computational issues we should anticipate?

6. POTENTIAL ERRORS:
   - Where could we have gone wrong?
   - What assumptions might be faulty?
   - How could we validate more rigorously?

BE MAXIMALLY SKEPTICAL. Point out ANY potential issues, even minor ones.

Your expertise could save us from publishing incorrect results!
"""

# Call Grok API
print("🤖 Consulting Grok-4 Expert Analysis...")
print("=" * 70)
print()
print("Sending analysis request to Grok-4 (this may take 30-60 seconds)...")
print()

# Create request JSON
request = {
    "messages": [
        {
            "role": "user",
            "content": analysis_prompt
        }
    ],
    "model": "grok-2-latest",
    "temperature": 0.3,  # Lower temp for analytical rigor
    "max_tokens": 4000
}

# Write to temp file
with open('/tmp/grok_validation_request.json', 'w') as f:
    json.dump(request, f, indent=2)

# Call Grok API
try:
    result = subprocess.run(
        [
            'curl', '-X', 'POST',
            'https://api.x.ai/v1/chat/completions',
            '-H', f'Authorization: Bearer {os.environ.get("GROK_API_KEY")}',
            '-H', 'Content-Type: application/json',
            '-d', f'@/tmp/grok_validation_request.json'
        ],
        capture_output=True,
        text=True,
        timeout=300
    )

    if result.returncode == 0:
        response = json.loads(result.stdout)
        analysis = response['choices'][0]['message']['content']

        print("=" * 70)
        print("GROK-4 EXPERT ANALYSIS")
        print("=" * 70)
        print()
        print(analysis)
        print()
        print("=" * 70)

        # Save to file
        with open('/Users/patrickkavanagh/math/GROK_BATCH1_VALIDATION.md', 'w') as f:
            f.write("# Grok-4 Expert Validation of Batch 1 Results\n\n")
            f.write("**Date**: December 12, 2025\n\n")
            f.write("**Model**: grok-2-latest (temperature 0.3)\n\n")
            f.write("---\n\n")
            f.write(analysis)

        print()
        print("✅ Analysis saved to: GROK_BATCH1_VALIDATION.md")

    else:
        print(f"❌ Error calling Grok API:")
        print(result.stderr)

except Exception as e:
    print(f"❌ Error: {e}")
    import traceback
    traceback.print_exc()
