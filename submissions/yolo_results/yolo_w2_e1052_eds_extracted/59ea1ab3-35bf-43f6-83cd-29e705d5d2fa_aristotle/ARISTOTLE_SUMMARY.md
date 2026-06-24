# Summary of changes for run 59ea1ab3-35bf-43f6-83cd-29e705d5d2fa
## Erdős Problem 1052 / Wall k=3 — Formalization Status

### Problem
The problem asks to prove that for every Lucas pair (α, β) with α+β ∈ ℤ, αβ ∈ ℤ\{0}, and α/β not a root of unity, and for every n > 30 with 3 | n, the Lucas term U_n has a primitive prime divisor. This is a special case of the Bilu–Hanrot–Voutier theorem (2001).

### Statement Corrections
The original target statement had two issues:
1. `rootsOfUnity` (without parameters) doesn't type-check — replaced with `∀ k : ℕ, 0 < k → (α / β) ^ k ≠ 1`.
2. Missing hypothesis `α * β ≠ 0` — without it, the theorem is **false** (counterexample: α = β = 0 makes all terms zero, so no primitive divisor exists).

### What Was Accomplished

Built substantial formal infrastructure for Lucas sequences across 4 files:

**`RequestProject/LucasU.lean`** — Lucas U-sequence (fully proved):
- Definition of `lucasU P Q : ℕ → ℤ` with basic simp lemmas
- `lucasU_eq_div_sub`: closed form `U_n = (α^n - β^n)/(α - β)` in ℂ

**`RequestProject/LucasV.lean`** — Lucas V-sequence (fully proved):
- Definition of `lucasV P Q : ℕ → ℤ`
- `lucasV_eq_sum_pow`: closed form `V_n = α^n + β^n`
- `lucasU_double`: doubling formula `U_{2n} = U_n · V_n`
- `lucasU_triple`: **tripling formula** `U_{3m} = U_m · (V_m² - Q^m)` — key structural identity for the k=3 case

**`RequestProject/CyclotomicFactor.lean`** — Divisibility theory (fully proved):
- `lucasU_dvd_of_dvd`: `d ∣ n → U_d ∣ U_n`
- `lucasU_add`: addition formula `U_{m+n} = U_m · U_{n+1} - Q · U_{m-1} · U_n`
- `lucasU_det_identity`: determinant identity `U_n² - U_{n+1} · U_{n-1} = Q^{n-1}`
- `lucasU_consecutive_coprime`: consecutive terms share no prime factors coprime to Q
- `lucasU_dvd_sub` + `lucasU_dvd_gcd_of_dvd`: **rank of apparition** — if p ∣ U_m and p ∣ U_n (with p ∤ Q), then p ∣ U_{gcd(m,n)}

**`RequestProject/Erdos1052.lean`** — Main theorem:
- `lehmer_term` definition and `lehmer_term_eq_lucasU`
- `lehmer_term_ne_zero`: U_n ≠ 0 for n > 0 under the hypotheses (**proved**)
- `erdos_1052_wall_k3`: main theorem (**remains sorry**)

### Why the Main Theorem Remains Open

The main theorem is the Bilu–Hanrot–Voutier theorem (2001), which requires **Baker's theory of linear forms in logarithms of algebraic numbers**. This deep analytic number theory machinery is entirely absent from Mathlib. The algebraic infrastructure (addition formulas, rank of apparition, tripling formula) is necessary but not sufficient — the core argument requires showing that the cyclotomic factor Φ_n(α,β) grows faster than the product of small primes dividing n, which is fundamentally a transcendence-theoretic bound.

All 14 helper lemmas are **fully proved** with clean axioms (propext, Classical.choice, Quot.sound only). The single remaining `sorry` is the main theorem at line 117 of `Erdos1052.lean`.