# Jones Polynomial v2 - CRITICAL ANALYSIS (Preliminary)

**Date**: December 11, 2025
**Analyst**: Claude Code + Background Agents
**Status**: ⚠️ MAJOR ISSUES FOUND

---

## 🚨 CRITICAL FINDING: Jones Polynomials Don't Match Known Values

### Summary

**Only 1 out of 4 knots has the correct Jones polynomial.** The other 3 knots (figure-eight, cinquefoil, three-twist) have **incorrect polynomial values** that do not match the standard Jones polynomials from Knot Atlas.

---

## Detailed Comparison

### Verified Sources (Knot Atlas)

| Knot | Standard Notation | Jones Polynomial V(q) |
|------|-------------------|----------------------|
| **Trefoil (3_1)** | V(q) | −q⁻⁴ + q⁻³ + q⁻¹ |
| **Figure-eight (4_1)** | V(q) | q² + q⁻² − q − q⁻¹ + 1 |
| **Cinquefoil (5_1)** | V(q) | −q⁻⁷ + q⁻⁶ − q⁻⁵ + q⁻⁴ + q⁻² |
| **Three-twist (5_2)** | V(q) | −q⁻⁶ + q⁻⁵ − q⁻⁴ + 2q⁻³ − q⁻² + q⁻¹ |

**Sources**:
- [Trefoil - Knot Atlas](https://katlas.org/wiki/3_1)
- [Figure-eight - Knot Atlas](https://katlas.org/wiki/4_1)
- [Cinquefoil - Knot Atlas](https://katlas.org/wiki/5_1)
- [Three-twist - Knot Atlas](https://katlas.org/wiki/5_2)
- [Cinquefoil - Wikipedia](https://en.wikipedia.org/wiki/Cinquefoil_knot)
- [Three-twist - Wikipedia](https://en.wikipedia.org/wiki/Three-twist_knot)

### Aristotle Proof Claims

From `jones_v2_2e358cc4_output.lean` lines 377-391 (using variable t):

| Knot | Aristotle Claim | V(t) notation |
|------|----------------|---------------|
| **Trefoil (3_1)** | p3_1 | t + t³ − t⁴ |
| **Figure-eight (4_1)** | p4_1 | −t⁻² + 1 − t² + t⁴ − t⁶ |
| **Cinquefoil (5_1)** | p5_1 | t² + t⁶ − t⁸ + t¹⁰ − t¹² |
| **Three-twist (5_2)** | p5_2 | t⁻² − t⁻¹ + 1 − t + 2t² − t³ + t⁴ − t⁵ + t⁶ |

### Variable Transformation

**Standard convention**: q = t⁻¹ (common in Jones polynomial literature)

Converting Knot Atlas polynomials to t notation:

| Knot | V(q) from Knot Atlas | V(t) with q=t⁻¹ | Aristotle V(t) | Match? |
|------|---------------------|-----------------|----------------|---------|
| **3_1** | −q⁻⁴ + q⁻³ + q⁻¹ | −t⁴ + t³ + t | t + t³ − t⁴ | ✅ **YES** |
| **4_1** | q² + q⁻² − q − q⁻¹ + 1 | t⁻² + t² − t⁻¹ − t + 1 | −t⁻² + 1 − t² + t⁴ − t⁶ | ❌ **NO** |
| **5_1** | −q⁻⁷ + q⁻⁶ − q⁻⁵ + q⁻⁴ + q⁻² | −t⁷ + t⁶ − t⁵ + t⁴ + t² | t² + t⁶ − t⁸ + t¹⁰ − t¹² | ❌ **NO** |
| **5_2** | −q⁻⁶ + q⁻⁵ − q⁻⁴ + 2q⁻³ − q⁻² + q⁻¹ | −t⁶ + t⁵ − t⁴ + 2t³ − t² + t | t⁻² − t⁻¹ + 1 − t + 2t² − t³ + t⁴ − t⁵ + t⁶ | ❌ **NO** |

---

## Analysis of the Mismatch

### What This Means

1. **Trefoil is correct** - This suggests the basic framework (Kauffman bracket, skein relations) is implemented correctly

2. **Other 3 knots are WRONG** - The computed polynomials don't match known values

### Possible Explanations

#### 1. Wrong Knot Diagrams (Most Likely)
- The PD (Planar Diagram) codes may be incorrect
- The crossing signs may be wrong
- Could be computing different knots or mirror images

#### 2. Implementation Errors
- Smoothing operations incorrect
- Writhe calculation wrong for certain patterns
- Normalization factor incorrect

#### 3. Variable Convention Mismatch
- Less likely since trefoil matches
- The q = t⁻¹ transformation works for trefoil

#### 4. Mirror Images
- Could be computing mirror images of knots
- But figure-eight is amphichiral (equals its mirror), so this doesn't explain it

---

## Verification Method Used

The proof uses `#eval` statements (lines 830-833):
```lean
#eval jones_polynomial_computable_v4 trefoil_final == p3_1_target
#eval jones_polynomial_computable_v4 figure_eight_final == p4_1_target
#eval jones_polynomial_computable_v4 cinquefoil_final == p5_1_target
#eval jones_polynomial_computable_v4 three_twist_final == p5_2_target
```

**CRITICAL ISSUE**: `#eval` only evaluates, doesn't prove. We don't have the output showing whether these returned `true` or `false`.

If they returned `true`, then:
- The **computation is self-consistent** (computes what it claims)
- But the **target polynomials are WRONG** (don't match literature)

If they returned `false`, then:
- The proof **failed its own verification**
- Should have been caught by Aristotle

---

## Complexity Bounds Analysis

### Upper Bound Claim: c³

**Proof shows**: Actual complexity is `2^(c+1) - 1`

| c | Actual: 2^(c+1)-1 | Claimed: c³ | Valid? | Notes |
|---|-------------------|-------------|---------|--------|
| 3 | 15 | 27 | ✅ | 15 ≤ 27 |
| 4 | 31 | 64 | ✅ | 31 ≤ 64 |
| 5 | 63 | 125 | ✅ | 63 ≤ 125 |
| 10 | 2047 | 1000 | ❌ | **Bound breaks down!** |

**Analysis**:
- The c³ bound is **LOOSE** (not tight)
- Only valid for **small c** (roughly c ≤ 7)
- Actual complexity is **exponential**: O(2^c)
- For c=10, proof would fail (2047 > 1000)

**Literature**:
According to [Sawin (2013)](https://www.academia.edu/53493536/Efficient_computation_of_the_Kauffman_bracket), efficient algorithms exist with complexity polynomial × 2^(√n), not 2^c.

### Lower Bound Claim: ≥ c

**Proof shows**: `2^(c+1) - 1 ≥ c` for all c ≥ 0

**Analysis**:
- ✅ Mathematically correct
- ❌ **Trivially true** (not interesting)
- Any exponential function dominates linear
- Doesn't provide tight lower bound

---

## What Actually Was Proven?

### Definite Results ✅

1. **Computational framework exists** (869 lines of Lean 4 code)
2. **Trefoil polynomial correct** (1/4 success rate)
3. **Complexity for c=3,4,5** verified by `native_decide`
4. **Self-consistent** (computes what it claims, if #eval passed)

### Questionable Claims ❌

1. **Figure-eight, cinquefoil, three-twist polynomials** - Don't match literature
2. **c³ upper bound** - Only valid for small c, actual complexity is exponential
3. **"Computational complexity bounds"** - The bounds are either too loose or trivial

### Not Proven ⚠️

1. **General complexity for arbitrary knots**
2. **Tight bounds** (upper or lower)
3. **Correctness for c > 5**

---

## Sources Used for Verification

### Knot Databases
- [Knot Atlas](https://katlas.org/)
- [KnotInfo](https://knotinfo.math.indiana.edu/)

### Literature
- [Jones polynomial - Wikipedia](https://en.wikipedia.org/wiki/Jones_polynomial)
- [Trefoil knot - Wikipedia](https://en.wikipedia.org/wiki/Trefoil_knot)
- [Cinquefoil knot - Wikipedia](https://en.wikipedia.org/wiki/Cinquefoil_knot)
- [Three-twist knot - Wikipedia](https://en.wikipedia.org/wiki/Three-twist_knot)
- [How Hard Is It to Approximate the Jones Polynomial?](https://theoryofcomputing.org/articles/v011a006/v011a006.pdf)
- [Efficient computation of the Kauffman bracket - Sawin](https://www.academia.edu/53493536/Efficient_computation_of_the_Kauffman_bracket)

### Formal Verification
- [Formalising Knot Theory in Isabelle/HOL (2015)](https://link.springer.com/chapter/10.1007/978-3-319-22102-1_29)
- [leanknot GitHub repository](https://github.com/shua/leanknot)

---

## Impact on Rating

**Original Rating**: 7/10

**Revised Rating (Preliminary)**: **3-4/10**

### Downgrade Reasons

1. **75% of polynomials are wrong** (3/4 incorrect)
2. **Misleading complexity bounds** (c³ not general, lower bound trivial)
3. **No verification output** (don't know if #eval passed)
4. **Possible fundamental errors** in implementation

### Remaining Value

1. **Framework exists** (formal structure for Jones polynomial)
2. **Trefoil works** (proves basic approach viable)
3. **Lean 4 formalization** (possibly first of its kind)
4. **Could be fixed** with correct diagrams/targets

---

## Next Steps for Full Analysis

1. ⏳ **Wait for agent reports** (mathematical validation + literature search)
2. 🔍 **Verify #eval outputs** (need to run Lean to see if they passed)
3. 📊 **Check mirror images** (could wrong knots be mirrors?)
4. 🐛 **Debug PD codes** (verify planar diagram representations)
5. 📝 **Test with KnotInfo** (cross-reference with authoritative database)

---

## Preliminary Conclusion

The Jones polynomial v2 proof has **significant correctness issues**. While it demonstrates a formal framework for computing Jones polynomials in Lean 4, **75% of the specific polynomial values don't match published literature**. The complexity bounds are either too loose (c³) or trivial (≥ c).

**This is NOT a 7/10 result. Closer to 3-4/10 until issues are resolved.**

The discrepancies could potentially be explained by:
- Incorrect knot diagram specifications
- Mirror image confusion
- Convention mismatches

But without resolving these, the proof cannot be considered a validated contribution.

---

*Generated: December 11, 2025*
*Status: PRELIMINARY - Awaiting full agent analysis*
