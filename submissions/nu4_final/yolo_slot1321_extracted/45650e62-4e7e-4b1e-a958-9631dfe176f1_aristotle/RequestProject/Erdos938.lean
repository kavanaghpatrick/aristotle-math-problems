/-
# Erdős Problem 938: Finitely many 3-APs of consecutive powerful numbers

A natural number n ≥ 1 is **powerful** if p ∣ n ⟹ p² ∣ n for every prime p.
The powerful numbers form an infinite strictly increasing sequence
  n₁ < n₂ < n₃ < ⋯ = 1, 4, 8, 9, 16, 25, 27, 32, …

**Erdős 938** asks: are there only finitely many indices k such that
nₖ, nₖ₊₁, nₖ₊₂ form a three-term arithmetic progression?

**Status**: OPEN. Up to 10¹⁴ only 18 such triples are known.

We provide:
- Definition of powerful numbers and proof the set is infinite.
- A reformulation of the problem using `Nat.nth`.
- A conditional proof: if a *kernel-uniformity* hypothesis holds
  together with *bounded-kernel finiteness*, Erdős 938 follows.
- The main theorem is stated with `sorry` since it is an open problem.

**Falsification note**: van Doorn (2026, arXiv:2605.06697, Conjecture 5) conjectures
infinitely many consecutive powerful 3-APs via the Pell family x² − 7³y² = 2.
If true, the problem has a *negative* answer.
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

/-! ## Definition of powerful numbers -/

/-- A natural number `n` is **powerful** (also called squareful) if every
prime factor of `n` appears with multiplicity at least 2. We require `n ≥ 1`
so that 0 is excluded. -/
def Nat.IsPowerful (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-! ## Basic properties of powerful numbers -/

/-- 1 is powerful (vacuously). -/
theorem Nat.IsPowerful.one : Nat.IsPowerful 1 := by
  exact ⟨le_refl 1, fun p hp hpd => by
    have := Nat.le_of_dvd one_pos hpd; interval_cases p <;> simp_all [Nat.Prime] ⟩

/-- Every perfect square ≥ 1 is powerful. -/
theorem Nat.IsPowerful.sq {m : ℕ} (hm : 1 ≤ m) : Nat.IsPowerful (m ^ 2) := by
  refine ⟨Nat.one_le_pow 2 m hm, fun p hp hpdvd => ?_⟩
  have hpm : p ∣ m := by
    rw [pow_two, hp.dvd_mul] at hpdvd
    exact hpdvd.elim id id
  calc p ^ 2 = p * p := by ring
    _ ∣ m * m := Nat.mul_dvd_mul hpm hpm
    _ = m ^ 2 := by ring

/-- The set of powerful numbers is infinite (contains all perfect squares). -/
theorem Nat.IsPowerful_infinite : Set.Infinite {n : ℕ | Nat.IsPowerful n} := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n + 1) ^ 2)
  · intro a b hab
    have := Nat.pow_left_injective (by omega : (2 : ℕ) ≠ 0) hab
    omega
  · intro n
    exact Nat.IsPowerful.sq (by omega)

/-! ## Enumeration via `Nat.nth` -/

/-- The k-th powerful number in increasing order. -/
noncomputable def powerfulNth (k : ℕ) : ℕ := Nat.nth Nat.IsPowerful k

theorem powerfulNth_isPowerful (k : ℕ) : Nat.IsPowerful (powerfulNth k) :=
  Nat.nth_mem_of_infinite Nat.IsPowerful_infinite k

theorem powerfulNth_strictMono : StrictMono powerfulNth :=
  Nat.nth_strictMono Nat.IsPowerful_infinite

/-! ## Consecutive powerful 3-APs -/

/-- Index `k` witnesses a consecutive powerful 3-AP when nₖ, nₖ₊₁, nₖ₊₂
are in arithmetic progression: nₖ + nₖ₊₂ = 2 · nₖ₊₁. -/
def IsConsecutivePowerful3AP (k : ℕ) : Prop :=
  powerfulNth k + powerfulNth (k + 2) = 2 * powerfulNth (k + 1)

/-! ## Conditional proof framework -/

/-- **Bounded-kernel finiteness**: for any fixed bound `B`, there are only
finitely many indices `k` witnessing a consecutive powerful 3-AP whose
three members all have squarefree kernel at most `B` in the Golomb
decomposition n = a² · b³ with b squarefree.

This follows from the theory of integral points on ternary quadratic forms
(Mordell–Siegel), but the proof requires deep number theory not yet in Mathlib. -/
def BoundedKernelFiniteness : Prop :=
  ∀ B : ℕ, Set.Finite {k : ℕ | IsConsecutivePowerful3AP k ∧
    ∀ i : Fin 3, ∃ a b : ℕ, Squarefree b ∧ b ≤ B ∧
      powerfulNth (k + i) = a ^ 2 * b ^ 3}

/-- **Kernel-uniformity hypothesis** (the open core of the conditional approach):
there exist absolute constants `B₀` and `K₀` such that for every consecutive
powerful 3-AP starting at index k with powerfulNth k ≥ K₀, the squarefree
kernels of all three members are bounded by `B₀`.

**Warning**: This hypothesis may be FALSE — van Doorn (2026, arXiv:2605.06697)
conjectures infinitely many consecutive powerful 3-APs from the Pell family
x² − 343y² = 2, in which one kernel is always 7 but others may grow. -/
def KernelUniformity : Prop :=
  ∃ B₀ K₀ : ℕ, ∀ k : ℕ, IsConsecutivePowerful3AP k → K₀ ≤ powerfulNth k →
    ∀ i : Fin 3, ∃ a b : ℕ, Squarefree b ∧ b ≤ B₀ ∧
      powerfulNth (k + i) = a ^ 2 * b ^ 3

/-
**Conditional implication**: Kernel-uniformity + bounded-kernel finiteness
together imply Erdős 938.

Proof sketch: By kernel-uniformity, all but finitely many (those with
powerfulNth k < K₀) consecutive powerful 3-APs have kernels bounded by B₀.
By bounded-kernel finiteness with B = B₀, those contribute finitely many.
The indices with powerfulNth k < K₀ are themselves finite (since powerfulNth
is strictly monotone, there are at most finitely many k with
powerfulNth k < K₀). So the total set is finite.
-/
theorem erdos_938_conditional
    (hKU : KernelUniformity) (hBKF : BoundedKernelFiniteness) :
    Set.Finite {k : ℕ | IsConsecutivePowerful3AP k} := by
  cases' hKU with B₀ K₀ hK₀;
  cases' K₀ with K₀ hK₀;
  contrapose! hBKF;
  -- Fix an arbitrary $B$.
  intro hB
  have := hB (B₀ + 1);
  exact hBKF <| Set.Finite.subset ( this.union <| Set.finite_le_nat K₀ ) fun k hk => if hk' : K₀ ≤ powerfulNth k then Or.inl ⟨ hk, fun i => by obtain ⟨ a, b, hb₁, hb₂, hb₃ ⟩ := hK₀ k hk hk' i; exact ⟨ a, b, hb₁, by linarith, hb₃ ⟩ ⟩ else Or.inr <| Set.mem_setOf.mpr <| le_of_not_ge fun hk'' => hk' <| hk''.trans <| powerfulNth_strictMono.id_le _

/-! ## Main theorem (OPEN PROBLEM) -/

/--
**Erdős Problem 938** (open): there are only finitely many indices `k`
such that the `k`-th, `(k+1)`-th, and `(k+2)`-th powerful numbers form
a three-term arithmetic progression.

This is an **open problem** as of 2026. The `sorry` reflects genuinely
unknown mathematics, not a gap in formalization effort.
-/
theorem erdos_938 : Set.Finite {k : ℕ | IsConsecutivePowerful3AP k} := by
  sorry