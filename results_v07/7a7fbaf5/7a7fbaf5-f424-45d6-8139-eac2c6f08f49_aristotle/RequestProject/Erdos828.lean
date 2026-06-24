import Mathlib

/-!
# Erdős Problem 828

For every integer `a`, there are infinitely many `n` with `φ(n) ∣ (n + a)`.

**Status**: OPEN. This generalizes Lehmer's conjecture (case `a = -1`).

## Known easy cases
- `a = -1`: Every prime `p` satisfies `φ(p) = p - 1 ∣ p - 1`. Since there are
  infinitely many primes, the set is infinite.
- `a = 0`: Every `n = 2^k` satisfies `φ(2^k) = 2^{k-1} ∣ 2^k`. Since there are
  infinitely many powers of 2, the set is infinite.

## Difficulty of the general case

For a fixed template `n = c · p` with `c` fixed and `p` prime, the condition
`φ(c)(p-1) ∣ cp + a` reduces to `φ(c)(p-1) ∣ c + a`, yielding only finitely
many primes. Similarly, using two varying primes in `n = c · p · q` does not
overcome the growth rate mismatch. The general case appears to require either
sieve-theoretic methods or a fundamentally different construction, and remains
open as of 2024.
-/

/-- For `a = -1`, every prime satisfies `φ(p) ∣ p - 1`, giving infinitely many solutions. -/
lemma erdos_828_neg_one :
    Set.Infinite {n : ℕ | ↑(Nat.totient n) ∣ (n : ℤ) + (-1)} := by
  refine Set.infinite_iff_exists_gt.mpr ?_
  intro a
  obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ a < p :=
    Exists.imp (by tauto) (Nat.exists_infinite_primes (a + 1))
  use p
  rcases p with (_ | _ | p) <;> simp_all +decide [Nat.totient_prime]

/-- For `a = 0`, every `2^k` satisfies `φ(2^k) ∣ 2^k`, giving infinitely many solutions. -/
lemma erdos_828_zero :
    Set.Infinite {n : ℕ | ↑(Nat.totient n) ∣ (n : ℤ) + 0} := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro n
  use 2 ^ (n + 1)
  norm_num [Nat.totient_prime_pow]
  exact ⟨pow_dvd_pow _ (Nat.le_succ _),
    Nat.recOn n (by norm_num) fun n _ => by
      norm_num [Nat.pow_succ'] at *; linarith⟩

/-- **Erdős Problem 828** (OPEN): For every integer `a`, there are infinitely many `n`
with `φ(n) ∣ (n + a)`. -/
theorem erdos_828 :
    ∀ a : ℤ, Set.Infinite {n : ℕ | ↑(Nat.totient n) ∣ n + a} := by
  sorry
