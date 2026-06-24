import Mathlib

open Filter Asymptotics

namespace Erdos208

/-- The set of squarefree natural numbers is infinite (e.g. it contains all primes). -/
lemma infinite_setOf_squarefree : ({n : ℕ | Squarefree n} : Set ℕ).Infinite := by
  have hpr : ({p : ℕ | Nat.Prime p} : Set ℕ).Infinite := by
    simpa using Nat.infinite_setOf_prime
  refine hpr.mono ?_
  intro p hp
  simpa using hp.squarefree

/-- `s n` is the `n`-th squarefree natural number (0-indexed). -/
noncomputable def s (n : ℕ) : ℕ := Nat.nth (fun k : ℕ => Squarefree k) n

lemma s_squarefree (n : ℕ) : Squarefree (s n) := by
  classical
  have hinf : ({k : ℕ | Squarefree k} : Set ℕ).Infinite := infinite_setOf_squarefree
  simpa [s] using Nat.nth_mem_of_infinite (p := fun k : ℕ => Squarefree k) hinf n

lemma strictMono_s : StrictMono s := by
  classical
  have hinf : ({k : ℕ | Squarefree k} : Set ℕ).Infinite := infinite_setOf_squarefree
  simpa [s] using (Nat.nth_strictMono (p := fun k : ℕ => Squarefree k) hinf)

/--
Erdős problem 208 (squarefree gaps): if `s n` enumerates the squarefree naturals in increasing order,
then for every `ε > 0` we have

`(s (n+1) - s n) = O((s n)^ε)` as `n → ∞`.

This statement is not currently available in Mathlib.
-/
theorem erdos_208_squarefree_gaps_bigO :
    ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ => ((s (n + 1) : ℝ) - (s n : ℝ)))
        =O[atTop] (fun n : ℕ => (s n : ℝ) ^ ε) := by
  intro ε hε
  sorry

end Erdos208
