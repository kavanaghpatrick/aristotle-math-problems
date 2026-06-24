import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000

/-!
# Erdős Problem 779 — Deaconescu's prime conjecture on primorials

For n ≥ 1, let P = ∏ i ∈ Finset.range (n+1), Nat.nth Nat.Prime i (the product of the
first n+1 primes). Does there always exist a prime p with p_n < p < P such that P + p
is prime?

**Status**: Open conjecture (Deaconescu, Math. Mag., 1982). Verified computationally
for n ≤ 1000. Erdős expected the least such p satisfies p ≤ n^{O(1)}.

We verify the conjecture for n ≤ 10 by providing explicit witnesses.
The general case remains open.
-/

/-! ## Helper: computing Nat.nth Nat.Prime values -/

/-- Helper to prove `Nat.nth Nat.Prime k = p` using `Nat.nth_count`. -/
private lemma nth_prime_eq {k p : ℕ} (hp : Nat.Prime p) (hc : Nat.count Nat.Prime p = k) :
    Nat.nth Nat.Prime k = p := by
  rw [← hc]; exact Nat.nth_count hp

lemma nth_prime_0 : Nat.nth Nat.Prime 0 = 2 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_1 : Nat.nth Nat.Prime 1 = 3 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_2 : Nat.nth Nat.Prime 2 = 5 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_3 : Nat.nth Nat.Prime 3 = 7 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_4 : Nat.nth Nat.Prime 4 = 11 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_5 : Nat.nth Nat.Prime 5 = 13 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_6 : Nat.nth Nat.Prime 6 = 17 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_7 : Nat.nth Nat.Prime 7 = 19 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_8 : Nat.nth Nat.Prime 8 = 23 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_9 : Nat.nth Nat.Prime 9 = 29 :=
  nth_prime_eq (by norm_num) (by native_decide)

lemma nth_prime_10 : Nat.nth Nat.Prime 10 = 31 :=
  nth_prime_eq (by norm_num) (by native_decide)

/-! ## Case-by-case verification

Witnesses (OEIS A005235 adjusted for the constraint p > p_n):
- n=1: P=6, p=5, P+p=11
- n=2: P=30, p=7, P+p=37
- n=3: P=210, p=13, P+p=223
- n=4: P=2310, p=23, P+p=2333
- n=5: P=30030, p=17, P+p=30047
- n=6: P=510510, p=19, P+p=510529
- n=7: P=9699690, p=23, P+p=9699713
- n=8: P=223092870, p=37, P+p=223092907
- n=9: P=6469693230, p=61, P+p=6469693291
- n=10: P=200560490130, p=67, P+p=200560490197
-/

macro "simp_primes" : tactic =>
  `(tactic| simp only [Finset.prod_range_succ, Finset.prod_range_zero,
    nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3, nth_prime_4,
    nth_prime_5, nth_prime_6, nth_prime_7, nth_prime_8, nth_prime_9, nth_prime_10])

lemma erdos_779_n1 :
    let P := ∏ i ∈ Finset.range 2, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 1 < p ∧ p < P := by
  simp_primes; exact ⟨5, by norm_num, by norm_num, by omega, by omega⟩

lemma erdos_779_n2 :
    let P := ∏ i ∈ Finset.range 3, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 2 < p ∧ p < P := by
  simp_primes; exact ⟨7, by norm_num, by norm_num, by omega, by omega⟩

lemma erdos_779_n3 :
    let P := ∏ i ∈ Finset.range 4, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 3 < p ∧ p < P := by
  simp_primes; exact ⟨13, by norm_num, by norm_num, by omega, by omega⟩

lemma erdos_779_n4 :
    let P := ∏ i ∈ Finset.range 5, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 4 < p ∧ p < P := by
  simp_primes; exact ⟨23, by norm_num, by norm_num, by omega, by omega⟩

lemma erdos_779_n5 :
    let P := ∏ i ∈ Finset.range 6, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 5 < p ∧ p < P := by
  simp_primes; exact ⟨17, by norm_num, by norm_num, by omega, by omega⟩

lemma erdos_779_n6 :
    let P := ∏ i ∈ Finset.range 7, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 6 < p ∧ p < P := by
  simp_primes; exact ⟨19, by norm_num, by norm_num, by omega, by omega⟩

lemma erdos_779_n7 :
    let P := ∏ i ∈ Finset.range 8, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 7 < p ∧ p < P := by
  simp_primes; exact ⟨23, by norm_num, by norm_num, by omega, by omega⟩

lemma erdos_779_n8 :
    let P := ∏ i ∈ Finset.range 9, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 8 < p ∧ p < P := by
  simp_primes; exact ⟨37, by norm_num, by norm_num, by omega, by omega⟩

lemma erdos_779_n9 :
    let P := ∏ i ∈ Finset.range 10, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 9 < p ∧ p < P := by
  simp_primes; exact ⟨61, by native_decide, by native_decide, by omega, by omega⟩

lemma erdos_779_n10 :
    let P := ∏ i ∈ Finset.range 11, Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime 10 < p ∧ p < P := by
  simp_primes; exact ⟨67, by native_decide, by native_decide, by omega, by omega⟩

/-! ## Main theorem (open conjecture) -/

/--
Erdős Problem 779 (Deaconescu's conjecture):
For n ≥ 1, if P is the product of the first (n+1) primes, then there exists a prime p
with p_n < p < P such that P + p is prime.

This is an open conjecture. We verify it for n ≤ 10 by providing explicit witnesses
and leave the general case as sorry.
-/
theorem erdos_779 (n : ℕ) (hn : n ≥ 1) :
    let P := ∏ i ∈ Finset.range (n + 1), Nat.nth Nat.Prime i
    ∃ p, p.Prime ∧ (P + p).Prime ∧ Nat.nth Nat.Prime n < p ∧ p < P := by
  sorry
