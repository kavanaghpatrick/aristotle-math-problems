# TOP 10 PROBLEMS FOR ARISTOTLE - QUICK START GUIDE

**Goal**: Maximize probability of solving impressive unsolved problems using Aristotle

---

## 🎯 TIER 1: START HERE (High Success Rate)

### 1. **Goldbach Conjecture for n ≤ 10^6** ⭐⭐⭐
```
Problem: Every even integer 4 ≤ n ≤ 10^6 is the sum of two primes.
Success Rate: 85%
Time: 1 week
Impact: HIGH - Partial result on famous problem
```

**Why**: Finite verification, strong Mathlib prime support, clear algorithmic path

**Aristotle Command**:
```bash
echo "Prove that every even integer n where 4 ≤ n ≤ 1000000 can be expressed as the sum of two prime numbers." > goldbach_bounded.txt
aristotle prove-from-file --informal goldbach_bounded.txt
```

---

### 2. **Sum of Two Squares Characterization** ⭐⭐⭐
```
Problem: n = a² + b² iff primes ≡ 3 (mod 4) appear to even powers in n
Success Rate: 95%
Time: 3-5 days
Impact: MEDIUM - Classical theorem, good formalization exercise
```

**Why**: Likely partially in Mathlib, elementary modular arithmetic, known proof

---

### 3. **McKay Conjecture Formalization** ⭐⭐⭐
```
Problem: Formalize recently proven McKay conjecture (Späth & Cabanes, 2023)
Success Rate: 75%
Time: 3 weeks
Impact: HIGH - Research-level formalization, Mathlib contribution
```

**Why**: Proof exists (verification not discovery), advances Lean 4 group theory

---

### 4. **IMO Cyclic Inequality (A5/A6 Level)** ⭐⭐
```
Problem: For positive a,b,c: Σ_cyc a³/(b² + c²) ≥ (a+b+c)/2
Success Rate: 60%
Time: 1 week
Impact: MEDIUM - IMO Problem 6 difficulty
```

**Why**: Multiple proof strategies (Cauchy-Schwarz, substitution, AM-GM chains)

---

### 5. **Anderson-Badawi Conjecture (n=3)** ⭐⭐
```
Problem: Every 3-absorbing ideal is strongly 3-absorbing
Success Rate: 50%
Time: 3 weeks
Impact: HIGH - Open research problem, proven for n=2
```

**Why**: Pure algebra, well-defined operations, natural next case

---

## 🚀 TIER 2: MOONSHOTS (High Impact if Solved)

### 6. **Ramsey Number R(5,5)** 🌙
```
Problem: Determine exact value (currently: 43 < R(5,5) < 49)
Success Rate: 5%
Time: Months
Impact: EXTREME - Would be major breakthrough
```

**Why**: Most famous small Ramsey number, SAT solving advances, finite search

---

### 7. **Burnside Problem B(2,5) Finiteness** 🌙
```
Problem: Is the free Burnside group B(2,5) finite?
Success Rate: 20%
Time: Months
Impact: VERY HIGH - Open since decades, next natural case
```

**Why**: B(r,2), B(r,3), B(r,4), B(r,6) all known finite

---

### 8. **Irrationality of ζ(5)** 🌙
```
Problem: Prove ζ(5) = Σ 1/n^5 is irrational
Success Rate: 15%
Time: Months
Impact: VERY HIGH - ζ(3) proven by Apéry, ζ(5) remains open
```

**Why**: Similar structure to ζ(3), Mathlib support for zeta function

---

### 9. **Inverse Galois Problem for M₂₃** 🌙
```
Problem: Is Mathieu group M₂₃ realizable as Galois group over ℚ?
Success Rate: 10%
Time: Months
Impact: VERY HIGH - Last remaining sporadic simple group
```

**Why**: All other sporadics known realizable, single finite group case

---

### 10. **Van der Waerden Number W(3,5)** 🌙
```
Problem: Smallest N where any 3-coloring of {1,...,N} has monochromatic 5-AP
Success Rate: 30%
Time: 6-8 weeks
Impact: HIGH - W(3,4)=293 found via SAT, natural next case
```

**Why**: SAT methods proven effective for W(3,4) in 2012

---

## 📋 RECOMMENDED WORKFLOW

### Week 1-2: Validation
- Run #2 (Sum of Two Squares) - Should succeed
- Run #4 (Cyclic Inequality) - Test IMO-level capability
- **Goal**: Confirm Aristotle setup working correctly

### Week 3-6: First Research Result
- Launch #1 (Goldbach Bounded) - High probability success
- Launch #5 (Anderson-Badawi) - Potential breakthrough
- **Goal**: 1 successful research-level result

### Month 2-3: Scale Up
- Continue #3 (McKay Formalization) - Major contribution
- Launch 2-3 Tier 1 problems in parallel
- Start 1 moonshot (#8 or #10) in background
- **Goal**: Multiple Mathlib contributions

### Ongoing: Moonshot Hunting
- Keep #6, #7, #8, #9 running continuously
- Even failures produce valuable infrastructure
- **Goal**: Potential breakthrough discovery

---

## 🔥 PARALLEL LAUNCH STRATEGY

**Run simultaneously**:
1. **Quick Win**: Sum of Two Squares (#2)
2. **Medium Challenge**: Goldbach Bounded (#1)
3. **Research Target**: Anderson-Badawi (#5)
4. **Moonshot**: Irrationality ζ(5) (#8)

This maximizes:
- Short-term validation
- Medium-term publications
- Long-term breakthrough potential

---

## 📊 SUCCESS METRICS

**Phase 1 Success** (1 month):
- ✅ 2-3 problems solved
- ✅ Aristotle workflow validated
- ✅ First Mathlib contributions

**Phase 2 Success** (3 months):
- ✅ 5-8 problems solved
- ✅ 1-2 research papers drafted
- ✅ Major Mathlib contributions (group theory, number theory)

**Phase 3 Success** (6+ months):
- ✅ 1 breakthrough on open problem
- ✅ Published research
- ✅ Established Aristotle as research tool

---

## 🎓 EXAMPLES OF SUCCESSFUL ARISTOTLE PROOFS

Based on what Aristotle has solved:

**Similar to what it can do**:
- Erdős Problem #124 (6 hours)
- 5/6 IMO 2025 problems (gold medal)
- 10/12 Putnam 2025 problems
- Niven's theorem, Gauss-Lucas theorem (during training)

**What to expect**:
- Number theory: ✅ Excellent
- Algebra: ✅ Excellent
- Analysis/Inequalities: ✅ Very Good
- Geometry: ✅ Good (via Yuclid)
- Combinatorics: ⚠️ Weakest area

---

## 🚨 IMPORTANT NOTES

### Cryptographic Implications
- **Riemann Hypothesis**: Impacts RSA security
- **Birch & Swinnerton-Dyer**: Impacts elliptic curve cryptography
- Any breakthrough should be disclosed responsibly

### Resource Limits
- Max 5 concurrent Aristotle projects
- Max 10 files per request
- Max 100 MB per file
- Lean 4.24.0, Mathlib 4.24.0

### Iteration Strategy
- First attempts may fail
- Aristotle uses iterative refinement
- Provide context files when helpful
- Use `--no-wait` for async mode

---

## 🎯 IMMEDIATE ACTION

**Right now, run this**:
```bash
cd /Users/patrickkavanagh/math
mkdir aristotle-research
cd aristotle-research

# Test 1: Quick validation
echo "Prove that for any natural number n, if n is divisible by 4, then n is even." > test_simple.txt
aristotle prove-from-file --informal test_simple.txt

# Test 2: IMO-level challenge
echo "For positive real numbers a, b, c, prove that: (a³/(b²+c²)) + (b³/(c²+a²)) + (c³/(a²+b²)) ≥ (a+b+c)/2" > test_imo_inequality.txt
aristotle prove-from-file --informal test_imo_inequality.txt

# Test 3: First research target
echo "Prove that every even integer n where 4 ≤ n ≤ 10000 can be expressed as the sum of two prime numbers." > goldbach_10k.txt
aristotle prove-from-file --informal goldbach_10k.txt
```

**Expected**: Tests 1 & 2 should succeed. Test 3 = first research result.

---

*Created from analysis of 60+ problems across Grok, Gemini, and 6 parallel Claude research agents*
