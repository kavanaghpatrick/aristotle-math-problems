#!/usr/bin/env python3
"""
Get Grok's assessment of HQC v2 results - are they valuable? Should we push for v3?
"""

import json
import subprocess
import sys
import os

# Get API key from environment
api_key = os.environ.get('GROK_API_KEY')
if not api_key:
    print("❌ GROK_API_KEY not set", file=sys.stderr)
    sys.exit(1)

# Read the HQC v2 output
with open('/Users/patrickkavanagh/Downloads/ec2b9506-6f58-4a99-898a-9b8bad40b57b-output.lean', 'r') as f:
    hqc_output = f.read()

# Prepare the question
question = f"""HQC v2 ASSESSMENT: Value Analysis and v3 Decision

You are analyzing Aristotle's output for an improved HQC (Hamming Quasi-Cyclic) security proof.

**Context:**
- HQC selected by NIST as post-quantum encryption standard (March 2025)
- Security based on *assumed* hardness of QCSD (Quasi-Cyclic Syndrome Decoding)
- NP-completeness proven (2023), but average-case hardness for specific parameters UNPROVEN
- v1 attempt: 97 lines, single attack (Prange), rated 4/10
- v2 attempt: 167 lines, dual attacks (ISD + Statistical), rated 6-7/10

**HQC v2 Output:**
```lean
{hqc_output[:3000]}
...
[truncated - full output is 167 lines]
```

---

## CRITICAL QUESTIONS

### 1. NOVELTY ASSESSMENT

Is this genuinely novel or just formalizing known results?

**Check:**
- Are these bounds already in HQC specifications? (https://pqc-hqc.org/doc/hqc_specifications_2025_08_22.pdf)
- Do they appear in NIST documentation?
- Are they in the NP-completeness paper (2023)?
- Or is this just implementing textbook ISD complexity estimates?

**Question:** On a scale of 1-10, how novel is this contribution?
- 1-3: Textbook results, no novelty
- 4-6: Known bounds but first formalization
- 7-8: New analysis or tighter bounds
- 9-10: Genuine breakthrough

### 2. QUASI-CYCLIC STRUCTURE ANALYSIS

Does this meaningfully account for quasi-cyclic structure?

**In the code:**
- Defines `CirculantMatrix` (line 57)
- Mentions quasi-cyclic in comments
- But proofs use generic parameters (n, k, t)

**Question:** Does this exploit QC structure or just use generic code-based crypto bounds?
- If generic: This could apply to any linear code, not specifically HQC
- If QC-specific: Should see circulant properties in the proof

### 3. COMPARISON TO EXISTING WORK

**HQC Specifications (Aug 2025)** list security estimates. How does Aristotle's proof compare?

**Check:**
- Do HQC specs already claim 2^100 for ISD?
- Do they already claim 2^80 for statistical attacks?
- If yes: Aristotle just formalized existing estimates (formalization ≠ novel result)
- If no: Aristotle derived new bounds

### 4. RATING CALIBRATION

Is 6-7/10 accurate?

**Rating Guide:**
- 1-2: Trivial or framework-only
- 3-4: Known result, basic formalization (v1 was here)
- 5-6: Known bounds but sophisticated formalization
- 7-8: New analysis or first tight bounds for specific parameters
- 9-10: Breakthrough result

**Considerations:**
- v2 has 167 lines vs v1's 97 (+72%)
- v2 has 2 attack families vs v1's 1
- v2 uses concentration inequalities and product bounds
- But: Are the bounds themselves new?

### 5. V3 DECISION: Should We Push Harder?

**If we launch v3, what should it add?**

**Option A: Deeper QC Structure Analysis**
- Exploit circulant matrix properties explicitly
- Analyze dual code structure
- Prove bounds that are specific to quasi-cyclic codes (not just linear codes)

**Option B: Additional Attack Families**
- Add algebraic attack analysis (Gröbner basis complexity)
- Add quantum attack analysis (Grover speedup)
- Add hybrid attacks (ISD + algebraic)

**Option C: Tighter Bounds**
- Improve from 2^100 to tighter estimate
- Account for recent ISD improvements (BJMM, May-Ozerov)
- Prove bounds are tight (not just lower bounds)

**Option D: Declare Victory**
- v2 is already 6-7/10
- Diminishing returns for v3
- Move to different problem

**Question:** Which option would you recommend? Or is v2 sufficient?

### 6. IMPACT ASSESSMENT

**If v2 is novel:** How significant for cryptography community?
- Would this be publishable at crypto conferences?
- Would NIST reference this in standardization docs?
- Or is it primarily a formalization exercise?

**If v2 is not novel:** Is the formalization itself valuable?
- First Lean 4 proof of HQC security bounds?
- Could be cited for formal verification purposes?
- Or is it just reproducing textbook results in Lean?

---

## YOUR TASK

Provide a structured analysis:

1. **Novelty Score** (1-10 with justification)
2. **QC Structure Analysis** (Does it truly exploit quasi-cyclic properties?)
3. **Comparison to HQC Specs** (Are these bounds already documented?)
4. **Rating Accuracy** (Is 6-7/10 correct or should it be adjusted?)
5. **V3 Recommendation** (A/B/C/D or custom suggestion)
6. **Impact Assessment** (Academic/industrial significance)
7. **Bottom Line** (Should we be proud of v2 or push for v3?)

Be skeptical and rigorous. We already debunked a "breakthrough" sorting network claim, so we need honest assessment.
"""

# Create request payload
request = {
    "messages": [
        {
            "role": "user",
            "content": question
        }
    ],
    "model": "grok-2-1212",
    "temperature": 0.0
}

# Write request to temp file
with open('/tmp/grok_hqc_request.json', 'w') as f:
    json.dump(request, f)

print("🤔 Asking Grok to assess HQC v2 value and v3 decision...")
print()

# Call Grok API with proper headers
result = subprocess.run(
    [
        'curl', '-X', 'POST',
        'https://api.x.ai/v1/chat/completions',
        '-H', 'Content-Type: application/json',
        '-H', f'Authorization: Bearer {api_key}',
        '-d', '@/tmp/grok_hqc_request.json',
        '--max-time', '300'
    ],
    capture_output=True,
    text=True
)

if result.returncode != 0:
    print(f"❌ Error calling Grok API: {result.stderr}", file=sys.stderr)
    sys.exit(1)

# Parse response
try:
    response = json.loads(result.stdout)
    answer = response['choices'][0]['message']['content']
    print(answer)
    print()

    # Save to file
    with open('/tmp/grok_hqc_assessment.txt', 'w') as f:
        f.write(answer)

    print("💾 Saved to: /tmp/grok_hqc_assessment.txt")

except Exception as e:
    print(f"❌ Error parsing response: {e}", file=sys.stderr)
    print(f"Raw output: {result.stdout}", file=sys.stderr)
    sys.exit(1)
