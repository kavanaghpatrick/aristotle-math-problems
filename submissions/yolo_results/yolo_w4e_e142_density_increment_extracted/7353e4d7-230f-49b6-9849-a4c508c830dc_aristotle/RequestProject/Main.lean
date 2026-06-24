import Mathlib

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 8000000

/-!
# Erdős Problem 142 — Explicit threshold for r₃(N) < N / log N

We formalize the statement that there exists a finite threshold N₀ such that
the Roth number r₃(N) satisfies r₃(N) · log(N) < N for all N in [N₀, N₀ + 10⁶].

## Mathematical background

The Roth number r₃(N) is the maximum size of a subset of {0, …, N-1} containing
no non-trivial 3-term arithmetic progression. Mathlib defines this as `rothNumberNat N`.

**Available in Mathlib:** `rothNumberNat_isLittleO_id` proves r₃(N) = o(N) via the
corners theorem and Szemerédi regularity. This is *insufficient* for our goal since
r₃(N) = o(N) does NOT imply r₃(N) = o(N/log N).

**Not yet in Mathlib:** The Bloom–Sisask (2020) bound r₃(N) ≤ C·N/(log N)^{1+c},
or the stronger Kelley–Meka (2023) bound r₃(N) ≤ C·N·exp(-c·(log N)^{1/12}).
Either of these implies r₃(N)·log(N) < N for sufficiently large N.

## Proof structure

1. Define `Set.IsAPOfLengthFree.maxCard` via `rothNumberNat` for k = 3.
2. State the deep unformalized bound as `rothNumberNat_times_log_eventually_lt` (sorry).
3. Derive the main theorem from it.
-/

namespace Set.IsAPOfLengthFree

/-- The maximum cardinality of a k-AP-free subset of {0, …, N-1}.
For k = 3 this equals `rothNumberNat N` (the additive Roth number).
For k ≠ 3, we use a trivial upper bound `N` as a placeholder. -/
noncomputable def maxCard (k N : ℕ) : ℕ :=
  if k = 3 then rothNumberNat N else N

end Set.IsAPOfLengthFree

lemma IsAPOfLengthFree_maxCard_three (N : ℕ) :
    Set.IsAPOfLengthFree.maxCard 3 N = rothNumberNat N := by
  simp [Set.IsAPOfLengthFree.maxCard]

/-- **Bloom–Sisask 2020 / Kelley–Meka 2023 (unformalized in Mathlib).**
For sufficiently large N, r₃(N) · log(N) < N.

This follows from the Bloom–Sisask bound r₃(N) ≤ C·N/(log N)^{1+c} (c > 0),
which gives r₃(N)·log(N) ≤ C·N/(log N)^c → 0 as N → ∞.
The Kelley–Meka (2023) bound r₃(N) ≤ C·N·exp(-c·(log N)^{1/12}) is even stronger.

Neither bound is currently formalized in Mathlib (the Roth/Kelley-Meka upper bound
is listed as a TODO in `Mathlib.Combinatorics.Additive.AP.Three.Defs`). -/
lemma rothNumberNat_times_log_eventually_lt :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (rothNumberNat N : ℝ) * Real.log N < (N : ℝ) := by sorry

/-- **Erdős Problem 142 (finite threshold version).**
There exists N₀ such that for all N in [N₀, N₀ + 10⁶],
the Roth number satisfies r₃(N) · log(N) < N. -/
theorem erdos_142_finite_threshold :
    ∃ N₀ : ℕ, ∀ N ∈ Finset.Icc N₀ (N₀ + 10^6),
      (Set.IsAPOfLengthFree.maxCard 3 N : ℝ) * Real.log N < (N : ℝ) := by
  obtain ⟨N₁, hN₁⟩ := rothNumberNat_times_log_eventually_lt
  exact ⟨N₁, fun N hN => by
    rw [IsAPOfLengthFree_maxCard_three]
    exact hN₁ N (Finset.mem_Icc.mp hN).1⟩
