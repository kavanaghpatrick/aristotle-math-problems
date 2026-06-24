# Infrastructure-Only Results: Mathlib-Formalization Audit

**Date:** 2026-05-30
**Scope:** Audit of 6 infrastructure-only submissions for upstream value.
**Method:** Direct grep against `Mathlib4` (vendored copy under `.lake/packages/mathlib`) and `FormalConjecturesForMathlib` (FC's pending-upstream layer). Cross-checked against `formal-conjectures/FormalConjectures/ErdosProblems/*.lean`.

## Key upstream finding

`FormalConjecturesForMathlib` is FC's **staging library** for Mathlib-bound definitions. Anything already living there is *not* a fresh contribution; it is FC's own house-keeping. Mathlib upstream itself has none of the six definitions surveyed here.

---

## Per-result classification

### L1 — E944 `IsVertexCritical` / `IsEdgeCritical` — **DUPLICATE**
- Status: **already in `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring.lean`** as `SimpleGraph.IsCritical`, `SimpleGraph.IsCriticalEdges`, `SimpleGraph.IsCriticalEdge`, `Subgraph.IsCriticalVertex`.
- The FC E944 file (`FormalConjectures/ErdosProblems/944.lean`) ALREADY uses these via `G.IsCritical k` / `G.IsCriticalEdges edges`.
- L1's local redefinitions use different signatures (`∀ v, (G.induce ({v}ᶜ)).chromaticNumber < k`) but are equivalent. **No upstream value.**
- Mathlib has `chromaticNumber` but no critical-graph predicates.

### L5 — E1055 `selfridgeClass` / `leastPrimeOfClass` / `selfridgeClass_eq_one_iff` — **FC-WORTHY (alternative formulation)**
- Status: NOT in Mathlib. NOT in `FormalConjecturesForMathlib`.
- FC's existing E1055 already has `IsOfClass : ℕ+ → ℕ → Prop` (via `PNat.caseStrongInductionOn`) and `p (r : ℕ+) : ℕ`. L5 introduces a simpler `noncomputable def selfridgeClass (p : ℕ) : ℕ` with structural recursion.
- The simpler signature is friendlier for computation; the existing FC signature is friendlier for inductive proofs. Not a clean drop-in replacement.
- The proven helper `selfridgeClass_eq_one_iff` (3-smoothness characterization at class 1) is genuinely useful.
- **Verdict:** Could be merged into FC's `1055.lean` as an alternative characterization. Too narrow for Mathlib upstream.

### R8 — E938 `Nat.Powerful` / `Set.IsAPOfLength` / `sq_powerful` / `powerful_infinite` — **DUPLICATE**
- `Nat.Powerful`: **already defined** in `FormalConjecturesForMathlib/Data/Nat/Full.lean` as `abbrev Powerful : ℕ → Prop := (2).Full`. The FC files (E137, E364, E936, E938, E942, E943, OEIS/63880) ALL use this existing definition method-style as `n.Powerful` / `Powerful n`.
- `Set.IsAPOfLength`: **already defined** in `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` (ℕ∞ length, with companion `IsAPOfLengthWith`). R8's local version uses ℕ — different signature.
- `sq_powerful`, `powerful_infinite`: trivial corollaries; worth ~5 lines each. Could be PR'd into FC's `Full.lean` but not Mathlib-grade.
- **Verdict:** Definitions are duplicates; the two lemmas are FC-worthy at best.

### E373 Surányi bounds (`n < 2a`, `a + 2 ≤ n`) — **FC-WORTHY**
- Status: NOT in Mathlib. NOT in FC ForMathlib.
- These are problem-specific Bertrand-style constraints on the Surányi equation `n! = a!·b!`. They are tight to this open problem and have no obvious reuse.
- Proofs use `Nat.factorial_le`, `Nat.factorial_mul_factorial_dvd_factorial_add`, `nlinarith` — clean Mathlib-style tactics, but the *statements* themselves are problem-local.
- **Verdict:** Belongs as helper lemmas inside `FormalConjectures/ErdosProblems/373.lean` as a `helpers` namespace. Not Mathlib material.

### E1052 — 8 helper theorems (`unitarySigma`, `unitaryDivisors`, `unitarySigma_prime_pow`, `unitarySigma_mul_coprime`, `unitarySigma_eq_prod_one_add_pow`, `not_isUnitaryPerfect_prime_pow`, `wall_k2`, `IsUnitaryPerfect.even`) — **PARTIAL DUPLICATE / FC-WORTHY**
- The CURRENT FC `ErdosProblems/1052.lean` ALREADY contains `properUnitaryDivisors`, `IsUnitaryPerfect`, `unitaryDivisors`, `unitarySigma`, `isUnitaryPerfect_iff_unitarySigma_eq_two_mul`, `unitarySigma_eq_prod_prime_factors`, `two_pow_card_primeFactors_dvd_unitarySigma`, `card_primeFactors_le_one_of_odd_isUnitaryPerfect`, `even_of_isUnitaryPerfect` — credited to Aristotle in the docstring.
- The submission's `IsUnitaryPerfect.even` is a re-proof of the existing `even_of_isUnitaryPerfect`. `unitarySigma_mul_coprime`, `unitarySigma_eq_prod_one_add_pow`, `unitarySigma_prime_pow` are NEW formulations (the existing file goes straight to the prime-factor product without an explicit multiplicativity lemma).
- `not_isUnitaryPerfect_prime_pow` and `wall_k2` (case k=2) ARE NEW and substantive: Wall's 1972 theorem for k=2 prime factors.
- `unitarySigma` belongs in Mathlib as a sibling to `ArithmeticFunction.sigma 1`, but with the additional unitary structure it is a reasonable PR target.
- **Verdict:** `unitarySigma` + multiplicativity + Wall k=2 are FC-worthy and *potentially* Mathlib-PR-able (sigma functions are well-established Mathlib territory). The rest duplicates existing FC content.

### R10 — `erdos_647_residual_bounded_iter2` — **TOO SPECIFIC**
- Statement: bounded verification for `n ∈ [3000, 10^6]` with `6 ∣ n` plus a 4-prime-tower condition, closed via `native_decide` over `Finset.Icc 3000 1000000`.
- The lemma name embeds `iter2` (project version marker). The hypotheses are bespoke to a specific Cunningham-chain residual closure attack on E647. This is project bookkeeping, not a general result.
- Not even a candidate for FC's `647.lean` — it's a witness table for an ongoing project lane, not a general theorem about τ(n).
- **Verdict:** Stays in `submissions/`. No FC value, no Mathlib value.

---

## Top 3 PR candidates (in priority order)

1. **`unitarySigma` family** → could open as **Mathlib PR**: define `Nat.unitaryDivisors`, `Nat.unitarySigma` as a sibling to existing `ArithmeticFunction.sigma`, prove multiplicativity on coprime arguments and the prime-power formula. Wall k=2 as a corollary. Real upstream value (unitary divisors are a standard arithmetic function).
2. **`sq_powerful` + `powerful_infinite`** → small **FC PR** into `FormalConjecturesForMathlib/Data/Nat/Full.lean`. Two 1-line lemmas saying every square ≥ 1 is powerful and the set of powerful numbers is infinite.
3. **E373 Surányi bounds** (`n < 2a` and `a + 2 ≤ n`) → **FC PR** as a private `helpers` namespace inside `FormalConjectures/ErdosProblems/373.lean`.

## Realistic contribution count

- **Mathlib PR-ready today:** 0–1 (the `unitarySigma` family, but it needs cleanup; the submitted proofs use `simp_all +decide` and aesop-heavy tactics that Mathlib reviewers reject; needs a rewrite in idiomatic Mathlib style)
- **FC-worthy PR-ready today:** 2 (sq_powerful/powerful_infinite micro-lemmas; E373 Surányi bounds)
- **Duplicates / no value:** 3 (L1 E944 critical defs, R8 IsAPOfLength duplicate, L5 selfridgeClass alternative — keep as project notes)
- **Too specific:** 1 (R10 R647 bounded witness table)

**Net upstream output: 0 immediate Mathlib PRs, 2 small FC PRs.** The `unitarySigma` family is a real 30–60 minute cleanup task before it could be submitted to either FC or Mathlib.

The deeper lesson: when FC's E944 file already imports definitions that L1 redefines locally, the submission pipeline is not pulling in the existing FC ecosystem context. R8's `Nat.Powerful` duplication is the clearest example — six sibling FC problems use `Nat.Powerful` from `Full.lean`, but the submission template doesn't surface it.
