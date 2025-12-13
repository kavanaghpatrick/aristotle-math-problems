#!/usr/bin/env python3
"""
Get Grok's review of HQC v3 input - is it ready to launch?
"""

import json
import subprocess
import sys
import os

api_key = os.environ.get('GROK_API_KEY')
if not api_key:
    print("❌ GROK_API_KEY not set", file=sys.stderr)
    sys.exit(1)

# Read the v3 input
with open('hqc_v3_input.txt', 'r') as f:
    v3_input = f.read()

question = f"""HQC v3 FINAL REVIEW: Ready to Launch?

Review the HQC v3 problem statement below and assess if it's ready to launch to Aristotle.

---

## HQC v3 PROBLEM STATEMENT

{v3_input}

---

## CRITICAL REVIEW QUESTIONS

### 1. Does it FORCE QC exploitation?

**Check:**
- Can Aristotle revert to generic C(n,t)/C(m,t) bounds?
- Are the goals specific enough to require circulant properties?
- Will Aristotle HAVE to use eigenvalues, automorphisms, or polynomial rings?

**Verdict:** YES/NO with explanation

### 2. Are the goals achievable for Aristotle?

**Check:**
- Is FFT eigenvalue computation formalizable in Lean 4?
- Can automorphism groups be reasoned about formally?
- Are Gröbner basis bounds too advanced?
- Is 250-400 lines realistic?

**Verdict:** Which goals are achievable (1-5)? Success probability for each?

### 3. Are the success criteria clear?

**Check:**
- Will we be able to verify if QC structure was used?
- Are the red flags concrete enough?
- Can we objectively rate the output 7-8/10 vs 5-6/10?

**Verdict:** Clarity rating 1-10

### 4. Missing anything critical?

**Check:**
- Are HQC parameters complete (n, k, t, r)?
- Any undefined notation?
- Need more background on circulant matrices?
- Any contradictions or ambiguities?

**Verdict:** List any missing elements

### 5. Comparison to v2 failures

**v2 Failed Because:**
- Used generic bounds (no QC exploitation)
- Defined CirculantMatrix but never used it
- Could apply to any linear code

**Does v3 avoid these failures?**

**Verdict:** How is v3 different? Will it force genuine QC analysis?

### 6. Launch Readiness

**Final Decision:**
- ✅ READY TO LAUNCH - Go ahead
- ⚠️ NEEDS MINOR FIXES - List specific changes
- ❌ MAJOR ISSUES - Redesign required

---

## YOUR TASK

Provide:

1. **QC Exploitation Assessment** (Does it force QC analysis? YES/NO)
2. **Achievability Rating** (1-5 for each goal, with success probability)
3. **Success Criteria Clarity** (1-10 rating)
4. **Missing Elements** (list anything critical that's missing)
5. **v2 Failure Avoidance** (how does v3 prevent reverting to generic bounds?)
6. **Launch Decision** (✅ READY / ⚠️ MINOR FIXES / ❌ MAJOR ISSUES)
7. **If Minor Fixes:** Specific changes needed before launch
8. **Expected Outcome:** Predicted novelty rating (1-10) if successful

Be brutally honest. We've already had v2 fail at QC exploitation - we cannot afford to fail again.
"""

request = {
    "messages": [{"role": "user", "content": question}],
    "model": "grok-2-1212",
    "temperature": 0.0  # Maximum rigor for review
}

with open('/tmp/grok_review_v3_request.json', 'w') as f:
    json.dump(request, f)

print("🔍 Asking Grok for final review of HQC v3...")
print("🌡️  Temperature: 0.0 (maximum rigor)")
print()

result = subprocess.run(
    [
        'curl', '-X', 'POST',
        'https://api.x.ai/v1/chat/completions',
        '-H', 'Content-Type: application/json',
        '-H', f'Authorization: Bearer {api_key}',
        '-d', '@/tmp/grok_review_v3_request.json',
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
    review = response['choices'][0]['message']['content']
    print(review)
    print()

    with open('/tmp/grok_hqc_v3_review.txt', 'w') as f:
        f.write(review)

    print("💾 Saved to: /tmp/grok_hqc_v3_review.txt")

except Exception as e:
    print(f"❌ Error: {e}", file=sys.stderr)
    print(f"Raw: {result.stdout}", file=sys.stderr)
    sys.exit(1)
