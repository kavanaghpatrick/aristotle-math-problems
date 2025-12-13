# Mass Launch Status - 7 Improved Problems

**Date**: December 11, 2025
**Grok Analysis**: Comprehensive audit with improved formulations

---

## Launch Status

| # | Issue | Problem | Status | Project ID |
|---|-------|---------|--------|------------|
| 1 | #27 | Quantum Query Collision (n=16) | ✅ LAUNCHED | cd691d07-ed92-4e2e-902f-5d9d0c3d1103 |
| 2 | #28 | Quantum Communication Disjointness (n=8) | ⏳ PENDING | Waiting for slot |
| 3 | #25 | PHP Width (PHP_5 improved) | ⏳ PENDING | Waiting for slot |
| 4 | #32 | Self-Dual Code [56,28,12] | ⏳ PENDING | Waiting for slot |
| 5 | #23 | Sorting Network C(18)=77 | ⏳ PENDING | Waiting for slot |
| 6 | #35 | PC Space (PHP_6) | ⏳ PENDING | Waiting for slot |
| 7 | #41 | QAOA MaxCut 3-Regular | ⏳ PENDING | Waiting for slot |

**Current Limit**: 5 concurrent projects
**Currently Running**:
- Jones v2 (2e358cc4)
- HQC v3 (4c28f37f)
- Quantum Query #27 (cd691d07)

**Available Slots**: 2 (will launch next 2 when current ones complete)

---

## Grok's Priority Ranking

1. **#27** - Quantum Query Collision (40% success) ✅ LAUNCHED
2. **#28** - Quantum Communication (35% success) ⏳ NEXT
3. **#25** - PHP Width/Size (30-35% success) ⏳ NEXT
4. **#32** - Self-Dual Code (30% success)
5. **#23** - Sorting Networks (20-25% success)
6. **#35** - PC Space (25% success)
7. **#41** - QAOA MaxCut (25% success)

---

## Success Criteria (All Problems)

**Must Have:**
✅ Concrete parameters (specific n, not just asymptotic)
✅ Quantitative bounds (≥ X, not just Ω notation)
✅ Structure exploitation (force use of specific techniques)
✅ Verification component (native_decide where applicable)

**Must Avoid:**
❌ Binary yes/no questions
❌ Abstract types without instances
❌ Generic arguments that work for any n
❌ Only asymptotic bounds

---

## Problem Summaries

### #27: Quantum Query Collision (LAUNCHED)
- **Target**: Prove T ≥ 3 queries for n=16
- **Methods**: Adversary matrix + Polynomial method + BHT verification
- **Novelty**: 7-8/10 (first formal verification for specific n)
- **File**: `mass_launch/01_quantum_query_collision.txt`

### #28: Quantum Communication Disjointness (PENDING)
- **Target**: Classical ≥ 5 bits, Quantum ≤ 3 qubits, Gap ≥ 2
- **Methods**: Fooling set (32 pairs) + Quantum fingerprinting
- **Novelty**: 7-8/10 (concrete gap for n=8)
- **File**: `mass_launch/02_quantum_communication_disjointness.txt`

### #25: PHP Width (PENDING - Improved v2)
- **Target**: Width w ≥ 3 for PHP_5 with size s ≤ 1024
- **Methods**: Width-size tradeoff + Pigeon expansion
- **Improvement**: Smaller instance (PHP_5 vs PHP_10), explicit bounds
- **File**: `mass_launch/03_php_width_improved.txt`

### #32: Self-Dual Code (PENDING)
- **Target**: Construct [56,28,12] Type I self-dual code
- **Methods**: Double circulant + Weight enumerator
- **Novelty**: 7-8/10 if code exists (open problem)
- **File**: `mass_launch/04_self_dual_code.txt`

### #23: Sorting Networks (PENDING - Improved v2)
- **Target**: Prove C(18) = 77 is optimal (lower bound ≥ 77)
- **Methods**: Info theory + Depth-width + Computational search
- **Improvement**: Focus on optimality, not just construction
- **File**: `mass_launch/05_sorting_network_optimal.txt`

### #35: PC Space (PENDING)
- **Target**: Polynomial Calculus space ≥ 6 for PHP_6
- **Methods**: Degree-space tradeoff + Resolution simulation
- **Novelty**: 6-7/10 (first formal PC space bound)
- **File**: `mass_launch/06_polynomial_calculus_space.txt`

### #41: QAOA MaxCut (PENDING)
- **Target**: QAOA depth-2 optimal for 3-regular 12-vertex graphs
- **Methods**: Explicit angle optimization + Classical comparison
- **Novelty**: 6-7/10 (quantum advantage verification)
- **File**: `mass_launch/07_qaoa_maxcut.txt`

---

## Launch Strategy

### Immediate (Slots Available)
- ✅ #27 Quantum Query Collision - LAUNCHED
- ⏳ Waiting for 2 slots to free up

### Next Wave (When 2 Slots Free)
- #28 Quantum Communication (highest priority pending)
- #25 PHP Width (improved retry)

### Final Wave (When 2 More Slots Free)
- #32 Self-Dual Code
- #23 Sorting Networks (improved retry)
- #35 PC Space
- #41 QAOA MaxCut

---

## Lessons Applied (From HQC v3 & Jones v2)

**What Works:**
✅ Concrete parameters (n=16, not just asymptotic)
✅ Force structure use (adversary matrix, fooling sets)
✅ Multiple goals (partial success valuable)
✅ Computational verification (native_decide)

**What to Avoid:**
❌ Optional structure (must be forced)
❌ Binary questions (enables trivial proofs)
❌ Generic formulations (revert to known bounds)

---

## Monitoring

**All projects:**
🔗 https://aristotle.harmonic.fun/projects

**Launched:**
- #27 Quantum Query: https://aristotle.harmonic.fun/projects/cd691d07-ed92-4e2e-902f-5d9d0c3d1103

**Pending:** Will launch as slots become available

---

## GitHub Issue Updates

All 7 issues updated with:
- Full problem statements (sourced in GitHub)
- Success criteria
- Expected novelty ratings
- File references

**Following user instruction:** "All primarily sourced in github - don't modify once they are out"

---

**Next Update:** When slots free up and remaining problems launch
**Expected Timeline:** 3-16 hours per problem

*Generated: December 11, 2025*
