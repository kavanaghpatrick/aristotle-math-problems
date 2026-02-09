# Target Ranking — February 9, 2026

## Strategic Shift

After 46 days on Tuza (978 submissions, 127 proven, 43 false lemmas), the evidence says:

**STOP attacking open problems that require novel mathematics.**
**START formalizing solved results in NT/algebra and extending decidable computations.**

### Why

| What we tried | Result |
|--------------|--------|
| Open combinatorics (Tuza) | 3.7/10 score, 6/7 sub-cases, blocked on PATH_4 |
| Open NT (Erdos 364, 677) | Both require novel math nobody has |
| Solved NT with decide infra | Already-proven test cases in repo |

AI tools (Aristotle, DeepSeek-Prover, HILBERT) achieve:
- Algebra: 85-100% success
- Number Theory: 75-97% success
- Combinatorics: 7-50% success

Our best track record: sorry=0 + native_decide → 77% proven.

---

## BATCH 1: First Submissions (Highest Confidence)

### 1. Feit-Thompson Prime Conjecture — Bounded Cases
**Score: 7.8/10** | Track 1: native_decide
- Statement: For primes p < q, (q^p-1)/(q-1) does NOT divide (p^q-1)/(p-1)
- Source: `formal-conjectures/Wikipedia/FeitThompsonPrimeConjecture.lean`
- Approach: Verify for specific (p,q) pairs using native_decide on ℕ
- Budget: 1-2 slots
- WHY: Pure computation, zero mathematical insight needed

### 2. Erdos #1059 — Extend Factorial Subtraction Verification
**Score: 7.3/10** | Track 1: decide +kernel
- Statement: For prime p, verify p - k! is composite for all k with k! < p
- Source: `formal-conjectures/ErdosProblems/1059.lean`
- Approach: Copy existing pattern (`norm_num + decide +kernel`) for primes 307, 401, 503
- Budget: 1 slot per prime
- WHY: Infrastructure already built and working. Extend existing proofs.

### 3. Leinster Groups — cyclic_of_perfect_is_leinster
**Score: 7.5/10** | Track 2: Boris INFORMAL
- Statement: Cyclic group with perfect number order is a Leinster group
- Source: `formal-conjectures/Wikipedia/LeinsterGroup.lean`
- Approach: Proof sketch: cyclic → all subgroups normal and correspond to divisors → sum of orders = σ(n) = 2n
- Budget: 2 slots (sorry=0 attempt + INFORMAL fallback)
- WHY: Clean algebra, well-supported in Mathlib

### 4. Leinster Groups — exists_nonabelian_leinster_group
**Score: 7.4/10** | Track 1+2: Concrete witness
- Statement: S₃ × C₅ (order 30) is a nonabelian Leinster group
- Source: same file
- Approach: Enumerate normal subgroups of S₃ × C₅, verify sum of orders = 60
- Budget: 2-3 slots
- WHY: Concrete computation, specific group

### 5. Erdos #541 — answer(True), Graham's Conjecture on Zero-Sum
**Score: 7.0/10** | Track 2: Boris INFORMAL
- Statement: If residues mod prime p have unique zero-sum length, at most 2 distinct residues
- Source: `formal-conjectures/ErdosProblems/541.lean`
- answer(True) is KNOWN. Solved by Gao-Hamidoune-Wang 2010
- Uses Fin p, ZMod p — good Mathlib types
- Budget: 3-5 slots (complex proof but known solution)

---

## BATCH 2: Medium Confidence

### 6. Erdos #402 — Graham's gcd Conjecture
**Score: 6.8/10** | Track 2: Boris INFORMAL
- For finite A ⊂ ℕ, ∃ a,b ∈ A with gcd(a,b) ≤ a/|A|
- Known proof (Szegedy/Zaharescu). Uses Finset, gcd.

### 7. Leinster Groups — abelian_is_leinster_iff_cyclic_perfect
**Score: 7.0/10** | Track 2
- Iff direction: abelian Leinster ↔ cyclic with perfect order
- Published proof (Leinster 2001 Thm 2.1)

### 8. Leinster Groups — dihedral_is_leinster_iff_odd_perfect
**Score: 7.1/10** | Track 2
- Dihedral Leinster ↔ odd perfect number
- High interest (connects to famous open problem)

### 9. Erdos #1052 — even_of_isUnitaryPerfect
**Score: 6.6/10** | Track 2
- All unitary perfect numbers are even
- Known result

### 10. Erdos #379 — limsup S(n) = ∞
**Score: 6.0/10** | Track 2
- Has existing Lean proof on GitHub (Tao's analysis repo)
- Could potentially port/adapt

---

## REJECTED (Do Not Attempt)

| Problem | Why |
|---------|-----|
| Erdos #364 (powerful triples) | Open 50 years, no finite reduction, requires algebraic NT |
| Erdos #677 (lcmInterval full) | Open, requires new math about p-adic structure |
| Catalan's conjecture | Proof uses class field theory (~100 pages) |
| Bounded Burnside | answer(sorry) + complex group theory |
| Erdos #952 (Gaussian moat) | Infinite domain, very deep |

---

## Portfolio Allocation

| Track | Allocation | Problems |
|-------|-----------|----------|
| Track 1: native_decide / decide | 40% | Feit-Thompson bounded, Erdos 1059 extend, Leinster witness |
| Track 2: Boris INFORMAL | 40% | Leinster algebra proofs, Erdos 541, 402, 1052 |
| Track 3: Falsification | 10% | Test negations of sub-claims before investing |
| Tuza maintenance | 10% | Only if new math idea for PATH_4 emerges |

## Key Metric

**Tuza after 46 days: 127 proven out of 978 submissions (13%)**
**Target for Batch 1: ≥3 proven out of 10-12 submissions (25%+)**

The shift to easier domains should roughly DOUBLE our success rate.
