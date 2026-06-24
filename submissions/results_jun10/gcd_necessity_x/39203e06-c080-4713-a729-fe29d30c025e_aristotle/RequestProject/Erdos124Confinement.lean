import Mathlib

open Filter
open scoped Pointwise BigOperators

namespace Erdos124

/-- The set of integers which are the sum of distinct powers `d ^ i` with `i ≥ k`. -/
def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

/-- Every element of `sumsOfDistinctPowers d k` is divisible by `d ^ k`. -/
lemma dk_dvd_mem {d k x : ℕ} (hx : x ∈ sumsOfDistinctPowers d k) : d ^ k ∣ x := by
  obtain ⟨s, hs⟩ := hx
  exact hs.2 ▸ Finset.dvd_sum fun i hi => pow_dvd_pow _ (hs.1 i hi)

/-- For `k ≠ 0`, `D.gcd id` divides every element of `sumsOfDistinctPowers d k` when `d ∈ D`. -/
lemma gcd_dvd_mem {D : Finset ℕ} {k : ℕ} (hk : k ≠ 0) {d : ℕ} (hd : d ∈ D)
    {x : ℕ} (hx : x ∈ sumsOfDistinctPowers d k) : (D.gcd id) ∣ x := by
  obtain ⟨s, hs⟩ := hx
  exact hs.2 ▸ Finset.dvd_sum fun i hi =>
    dvd_pow (Finset.gcd_dvd hd) (by linarith [hs.1 i hi, Nat.pos_of_ne_zero hk])

/-- Confinement: for `k ≠ 0`, every element of the `k`-shifted pointwise sumset
`∑ d ∈ D, sumsOfDistinctPowers d k` is divisible by `D.gcd id`.

This is the mechanism behind the necessity of the hypothesis `gcd(D) = 1` in the open
BEGL96 case (`k ≥ 1`) of Erdős Problem 124: if `D.gcd id > 1`, then every representable `n`
is a multiple of `D.gcd id`, so all `n` coprime to it (e.g. `n = 1`) are permanently missed,
and eventual coverage cannot hold. -/
theorem erdos124_gcd_confinement
    (D : Finset ℕ) (k : ℕ) (hk : k ≠ 0)
    (n : ℕ) (hn : n ∈ ∑ d ∈ D, Erdos124.sumsOfDistinctPowers d k) :
    (D.gcd id) ∣ n := by
  rw [Set.mem_finset_sum] at hn
  obtain ⟨g, hg, rfl⟩ := hn
  exact Finset.dvd_sum fun i hi => gcd_dvd_mem hk hi (hg hi)

end Erdos124
