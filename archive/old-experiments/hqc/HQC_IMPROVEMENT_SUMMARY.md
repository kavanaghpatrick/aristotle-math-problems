# HQC/QCSD Improvement Strategy - Summary

**Date:** 2025-12-11
**Issue:** #22 - QC Syndrome Decoding Complexity (NIST HQC Standard)

---

## 🎯 CURRENT STATUS

**Aristotle Result v1:**
- UUID: `79336407-4142-49c0-bba0-c8daa0d8cdf4`
- Lines: 97 (very brief)
- Proved: Prange's algorithm ≥ 2^100 for HQC parameters
- Rating: **4/10** - Partial success, known security analysis

**What's Missing:**
- Only analyzes ONE specific attack (Prange)
- Doesn't account for quasi-cyclic structure
- No general complexity characterization
- Doesn't address the open problem

---

## 🎓 KEY RESEARCH FINDINGS

### 1. **The Open Problem** (Confirmed Unsolved)

**Gap identified:**
- ✅ NP-completeness proven (2023) - worst-case hardness
- ❌ Average-case hardness UNPROVEN - needed for cryptography
- ❌ No tight bounds accounting for quasi-cyclic structure

### 2. **Recent Developments (2023-2025)**

**[Decoding Quasi-Cyclic codes is NP-complete](https://eprint.iacr.org/2023/1064.pdf)** (2023)
- First formal complexity result for QC-SDP
- Proves worst-case NP-hardness
- **Limitation:** Doesn't address average-case or structural exploitation

**[On Independence Assumptions in QC Codes](https://arxiv.org/html/2501.02626)** (January 2025)
- Analyzes whether QC codes are as hard as random codes
- **Key open question:** Does structure reduce security?

**[HQC Specifications](https://pqc-hqc.org/doc/hqc_specifications_2025_08_22.pdf)** (August 2025)
- NIST selected HQC in March 2025
- Security based on *assumed* hardness (not proven)
- Defines 3-QCSD-PT problem formally

### 3. **Critical Gap**

**Cryptographic security requires:** Average-case hardness
**Current knowledge:** Only worst-case NP-completeness
**Open problem:** Bridge this gap for HQC parameters

---

## 💡 GROK'S BRAINSTORMING RECOMMENDATIONS

### Approach 1: LPN Reduction (Most Ambitious)
**Goal:** Prove average-case QCSD hardness via reduction to Learning Parity with Noise (LPN)

**Challenge:** Requires constructing non-trivial reduction
**Success probability:** 20-30%
**Impact if successful:** Major breakthrough

### Approach 2: Structural Analysis (Recommended)
**Goal:** Analyze ALL major attack families accounting for QC structure

**Components:**
1. Information Set Decoding lower bound
2. Statistical attacks exploiting circulant structure
3. Algebraic attacks using polynomial representation
4. Union bound combining all families

**Success probability:** 40-60%
**Impact:** Genuine novel contribution

### Approach 3: Information-Theoretic (Most Novel)
**Goal:** Prove fundamental lower bounds independent of algorithms

**Approach:** Entropy-based arguments
**Success probability:** 30-40%
**Impact:** Complementary perspective to computational hardness

---

## 📋 IMPROVED PROBLEM STATEMENT

### Recommended: **Structural Analysis Approach**

**Why this choice?**
- More feasible than full LPN reduction
- More substantial than current single-attack analysis
- Achieves genuine novelty
- Aligns with Aristotle's strengths (formalization, case analysis)

### Three-Tier Goal Structure

**Goal 1: ISD Lower Bound** (Core)
- Prove: ISD requires ≥ 2^100 operations even exploiting QC structure
- Key insight: QC structure doesn't significantly reduce search space
- Expected: 80-120 lines of Lean

**Goal 2: Statistical Attack Lower Bound** (Important)
- Prove: Statistical attacks require ≥ 2^80 operations
- Use concentration inequalities to show weak statistical signals
- Expected: 80-120 lines of Lean

**Goal 3: Algebraic Attack Lower Bound** (Stretch)
- Prove: Polynomial attacks require ≥ 2^80 operations
- Analyze Gröbner basis complexity
- Expected: 60-100 lines of Lean

**Goal 4: Union Bound** (Synthesis)
- Combine all attack families
- Prove: Overall security ≥ 2^80
- Expected: 40-60 lines of Lean

**Total: 250-400 lines** (vs. current 97)

---

## 📊 COMPARISON: CURRENT VS. IMPROVED

| Metric | Current | Improved | Gain |
|--------|---------|----------|------|
| **Scope** | 1 attack (Prange) | 3-4 attack families | 3-4x broader |
| **Structure** | Ignores QC | Explicitly analyzes | Novel angle |
| **Lines** | 97 | 250-400 | 2.5-4x deeper |
| **Novelty** | Known bound | Structural analysis | Genuine contribution |
| **Rating** | 4/10 | **7-8/10 target** | Major improvement |

---

## 📁 CREATED FILES

1. **`HQC_IMPROVED_PROBLEM_STATEMENT.md`**
   - Full analysis (3000+ words)
   - Three problem versions
   - Implementation strategy
   - Risk assessment

2. **`hqc_improved_input.txt`**
   - Clean Aristotle input
   - Focused on Approach 2 (Structural Analysis)
   - Goals 1-4 clearly specified
   - Technical requirements detailed

3. **`HQC_IMPROVEMENT_SUMMARY.md`** (this file)
   - Executive summary
   - Key findings
   - Recommendation

---

## 🎯 SUCCESS METRICS

### Minimum Success (Still Valuable):
- ✅ Formalize quasi-cyclic structure in Lean
- ✅ Prove ISD lower bound (Goal 1)
- ✅ ~150-200 lines
- **Rating: 5-6/10**

### Target Success:
- ✅ Goals 1-2 complete (ISD + statistical)
- ✅ Concrete bounds: ISD ≥ 2^100, Statistical ≥ 2^80
- ✅ ~250-350 lines
- **Rating: 7-8/10**

### Stretch Success:
- ✅ Goals 1-3 complete (ISD + statistical + algebraic)
- ✅ Union bound (Goal 4)
- ✅ Overall security ≥ 2^80 proven
- ✅ ~350-450 lines
- **Rating: 8-9/10**

---

## 🚀 NEXT STEPS

### Ready to Launch Aristotle:

**Input file:** `hqc_improved_input.txt`

**Command:**
```bash
aristotle prove-from-file --informal hqc_improved_input.txt
```

**Or via Python API:**
```python
import asyncio
from aristotlelib import Project, ProjectInputType, set_api_key

async def prove_hqc():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    solution = await Project.prove_from_file(
        input_file_path="hqc_improved_input.txt",
        project_input_type=ProjectInputType.INFORMAL,
        wait_for_completion=True
    )
    print(f"Solution: {solution}")

asyncio.run(prove_hqc())
```

### Expected Timeline:
- **Fast path:** 30 minutes - 2 hours (if it clicks)
- **Typical:** 2-6 hours
- **Complex:** 6-12 hours
- **Timeout:** 24 hours max

### Monitoring:
- Check https://aristotle.harmonic.fun/projects
- Poll for completion status
- Download results when ready

---

## 💪 WHY THIS COULD SUCCEED

### Aristotle's Strengths (Demonstrated):
1. ✅ Can formalize complex cryptographic primitives (HQC v1)
2. ✅ Handles large computations via `native_decide` (2^100 calculations)
3. ✅ Produces 100-400 lines of Lean successfully
4. ✅ Can structure multi-part proofs (PHP had 377 lines)

### Problem Alignment:
1. ✅ Concrete parameters (not asymptotic)
2. ✅ Well-defined attack models
3. ✅ Combinatorial calculations (Aristotle's forte)
4. ✅ Modular structure (can succeed on subgoals)

### Success Probability Estimate:
- **Goal 1 (ISD):** 70-80% (similar to current work)
- **Goal 2 (Statistical):** 50-60% (new but structured)
- **Goal 3 (Algebraic):** 30-40% (stretch goal)
- **Overall (Goals 1-2):** **40-60%** ← Realistic target

---

## 🎓 LEARNING FROM SORTING NETWORK FAILURE

### Mistakes to Avoid:

1. **❌ Don't accept claims at face value**
   - Verify "improvement" claims against literature
   - Check current state-of-art BEFORE celebrating

2. **❌ Don't confuse formalization with novelty**
   - First Lean proof ≠ new mathematical result
   - Need to advance actual knowledge

3. **✅ Do set clear novelty criteria**
   - Define what would count as genuine contribution
   - Check against recent papers (2023-2025)

### Applied to HQC:

**Novelty criteria defined:**
- Must go beyond single-attack analysis (Prange)
- Must explicitly account for quasi-cyclic structure
- Must provide concrete bounds for HQC parameters
- Must advance beyond NP-completeness result

**Verification plan:**
- Check ePrint archive for similar results
- Compare to HQC specifications and NIST analysis
- Validate bounds against known attacks

---

## 📚 SOURCES

### Research Papers:
1. [NP-completeness of QC decoding (2023)](https://eprint.iacr.org/2023/1064.pdf)
2. [Independence assumptions (Jan 2025)](https://arxiv.org/html/2501.02626)
3. [HQC specifications (Aug 2025)](https://pqc-hqc.org/doc/hqc_specifications_2025_08_22.pdf)
4. [NIST HQC presentation (2024)](https://csrc.nist.gov/csrc/media/Presentations/2024/hqc/images-media/gaborit-hqc-pqc2024.pdf)
5. [Decoding Challenge - QCSD](https://decodingchallenge.org/q-c)

### AI Consultation:
- **Grok API:** Brainstorming session (temperature 0.7)
- **Web Search:** Literature verification
- **Claude Analysis:** Synthesis and strategy

---

## 🎯 FINAL RECOMMENDATION

**GO FOR IT!**

Launch Aristotle with the improved problem statement (`hqc_improved_input.txt`).

**Rationale:**
1. Problem is genuinely open and important (NIST standard)
2. Improved scope significantly more substantial than v1
3. Realistic success probability (40-60%)
4. Even partial success (Goal 1 only) is valuable
5. Clear novelty criteria defined upfront

**Expected outcome:**
- **Best case:** 7-8/10 result, genuine contribution
- **Realistic case:** 5-6/10 result, solid formalization
- **Worst case:** Similar to v1, but we tried something harder

**Risk:** Low - even failure provides learning about Aristotle's limits

---

**Ready to proceed?** The improved input file is ready at:
`/Users/patrickkavanagh/math/hqc_improved_input.txt`

**Estimated improvement:** 4/10 → 7-8/10 (if successful)
**Success probability:** 40-60%
**Time investment:** 2-12 hours of Aristotle runtime
**Value proposition:** Genuine shot at novel contribution to NIST PQC security analysis
