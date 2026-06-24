import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Erdős Problem 938: Finitely many 3-APs of consecutive powerful numbers

A natural number `n ≥ 1` is **powerful** (also called squarefull) if every prime
factor of `n` appears with exponent at least 2.

**Erdős 938** asks: Are there only finitely many indices `k` such that
`n_k, n_{k+1}, n_{k+2}` (three consecutive powerful numbers) form a
three-term arithmetic progression?

## Status

This is an **open problem**. No proof of finiteness is known in the literature.
The only known conditional result is under the abc conjecture (Chan 2022,
arXiv:2210.00281). The informal proof outline in the problem source relies on
the Bombieri–Lang conjecture for surfaces of general type, which is itself
unproven. The theorem is therefore stated but left as `sorry`.

## Known 3-AP triples of consecutive powerful numbers

- (1728, 1764, 1800)   with common difference 36
- (6912, 7056, 7200)   with common difference 144
- (729000, 729316, 729632) with common difference 316

No others have been found computationally.
-/

/-- A natural number `n` is **powerful** if `n ≥ 1` and every prime factor
of `n` divides `n` with multiplicity at least 2 (equivalently, `p ∣ n → p² ∣ n`
for every prime `p`). -/
def Nat.Powerful (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- A set `S ⊆ ℕ` is an **arithmetic progression of length `l`** if there exist
`a, d ∈ ℕ` with `d > 0` such that `S = {a, a + d, a + 2d, …, a + (l-1)d}`. -/
def Set.IsAPOfLength (S : Set ℕ) (l : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ S = (fun i => a + i * d) '' (Finset.range l : Set ℕ)

/-!
## Basic facts about powerful numbers
-/

/-
1 is powerful (vacuously: no prime divides 1).
-/
theorem Nat.Powerful.one : Nat.Powerful 1 := by
  exact ⟨ by norm_num, fun p pp dp => by have := Nat.le_of_dvd ( by norm_num ) dp; interval_cases p <;> trivial ⟩

/-
Every perfect square `n² ≥ 1` is powerful.
-/
theorem Nat.Powerful.sq {n : ℕ} (hn : 1 ≤ n) : Nat.Powerful (n ^ 2) := by
  refine' ⟨ by nlinarith, fun p pp dp => _ ⟩;
  exact pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) 2

/-
The set of powerful numbers is infinite (it contains all perfect squares).
-/
theorem Nat.Powerful.setOf_infinite : (setOf Nat.Powerful).Infinite := by
  exact Set.infinite_of_forall_exists_gt fun n => ⟨ ( n + 1 ) ^ 2, Nat.Powerful.sq ( Nat.le_add_left _ _ ), by nlinarith ⟩

/-!
## Main theorem (OPEN)
-/

/-- **Erdős 938** (OPEN). The set of indices `k` for which the three consecutive
powerful numbers `n_k, n_{k+1}, n_{k+2}` form a 3-term AP is finite.

This is an open problem. No proof is known; the statement is left as `sorry`. -/
theorem erdos_938 :
    {P : Finset ℕ | Set.IsAPOfLength (↑P) 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)}}.Finite := by
  sorry