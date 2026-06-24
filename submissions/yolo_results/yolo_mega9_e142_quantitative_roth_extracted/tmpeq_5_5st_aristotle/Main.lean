import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Filter Asymptotics Real

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
2. State the Bloom–Sisask bound as a hypothesis (not an axiom, for soundness).
3. Derive `rothNumberNat_times_log_eventually_lt` from the Bloom–Sisask hypothesis.
4. Derive the main Erdős 142 theorem from step 3.

## Note on axiom avoidance

The Bloom–Sisask bound is a deep analytical result (arXiv:2007.03528, Thm 1.1) that is
not formalized in Mathlib. Rather than introducing an `axiom` (which would compromise
proof soundness), we state it as an explicit hypothesis `BloomSisakBound` and prove
everything conditionally. The unconditional statements retain `sorry` to mark the gap.
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

/-! ## The Bloom–Sisask bound as a hypothesis -/

/-- **Bloom–Sisask 2020 (arXiv:2007.03528, Theorem 1.1).**
There exist absolute constants c, C > 0 such that for all N ≥ 2,
  r₃(N) ≤ C · N / (log N)^{1+c}.

This is a deep analytical result not yet formalized in Mathlib. We state it
as a `Prop` to be used as an explicit hypothesis, rather than as an `axiom`. -/
def BloomSisakBound : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    (rothNumberNat N : ℝ) ≤ C * ↑N / (Real.log ↑N) ^ (1 + c)

/-! ## Conditional theorem: Bloom–Sisask ⟹ r₃(N)·log(N) < N eventually -/

/-
From the Bloom–Sisask bound, we derive that r₃(N)·log(N) < N for large N.

**Proof sketch:** From r₃(N) ≤ C·N/(log N)^{1+c}, multiply both sides by log N
to get r₃(N)·log(N) ≤ C·N/(log N)^c. Since c > 0, (log N)^c → ∞, so
C/(log N)^c < 1 for large N, giving r₃(N)·log(N) < N.
-/
theorem rothNumberNat_times_log_eventually_lt_of_bloomSisask
    (hBS : BloomSisakBound) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (rothNumberNat N : ℝ) * Real.log ↑N < (↑N : ℝ) := by
  obtain ⟨ c, C, hc, hC, h ⟩ := hBS;
  -- Since $c > 0$, $(\log N)^c \to \infty$ as $N \to \infty$.
  have h_log_c_inf : Filter.Tendsto (fun N : ℕ => (Real.log N) ^ c) Filter.atTop Filter.atTop := by
    exact tendsto_rpow_atTop hc |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
  -- Choose $N₁$ such that for all $N ≥ N₁$, $(\log N)^c > C$.
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N : ℕ, N ≥ N₁ → (Real.log N) ^ c > C := by
    simpa using h_log_c_inf.eventually_gt_atTop C;
  refine' ⟨ N₁ + 2, fun N hN => _ ⟩ ; specialize h N ( by linarith ) ; rw [ le_div_iff₀ ] at h;
  · rw [ Real.rpow_add' ] at h <;> norm_num at *;
    · nlinarith [ hN₁ N ( by linarith ), show ( N : ℝ ) ≥ 2 by norm_cast; linarith, show ( rothNumberNat N : ℝ ) * log N ≥ 0 by positivity ];
    · positivity;
    · linarith;
  · exact Real.rpow_pos_of_pos ( Real.log_pos ( by norm_cast; linarith ) ) _

/-- **Bloom–Sisask 2020 / Kelley–Meka 2023 (unformalized in Mathlib).**
For sufficiently large N, r₃(N) · log(N) < N.

This follows from the Bloom–Sisask bound r₃(N) ≤ C·N/(log N)^{1+c} (c > 0),
which gives r₃(N)·log(N) ≤ C·N/(log N)^c → 0 as N → ∞.

**Status:** The proof is complete modulo `BloomSisakBound` (see
`rothNumberNat_times_log_eventually_lt_of_bloomSisask`). The unconditional
statement retains `sorry` because the Bloom–Sisask bound is not yet in Mathlib. -/
lemma rothNumberNat_times_log_eventually_lt :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (rothNumberNat N : ℝ) * Real.log ↑N < (↑N : ℝ) := by
  exact rothNumberNat_times_log_eventually_lt_of_bloomSisask ⟨1, 1, one_pos, one_pos,
    fun N hN => by sorry⟩

/-- Alias for `rothNumberNat_times_log_eventually_lt`. -/
theorem erdos_142_quantitative_roth_lever :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (rothNumberNat N : ℝ) * Real.log ↑N < (↑N : ℝ) :=
  rothNumberNat_times_log_eventually_lt

/-- **Erdős Problem 142 (finite threshold version).**
There exists N₀ such that for all N in [N₀, N₀ + 10⁶],
the Roth number satisfies r₃(N) · log(N) < N. -/
theorem erdos_142_finite_threshold :
    ∃ N₀ : ℕ, ∀ N ∈ Finset.Icc N₀ (N₀ + 10^6),
      (Set.IsAPOfLengthFree.maxCard 3 N : ℝ) * Real.log ↑N < (↑N : ℝ) := by
  obtain ⟨N₁, hN₁⟩ := rothNumberNat_times_log_eventually_lt
  exact ⟨N₁, fun N hN => by
    rw [IsAPOfLengthFree_maxCard_three]
    exact hN₁ N (Finset.mem_Icc.mp hN).1⟩