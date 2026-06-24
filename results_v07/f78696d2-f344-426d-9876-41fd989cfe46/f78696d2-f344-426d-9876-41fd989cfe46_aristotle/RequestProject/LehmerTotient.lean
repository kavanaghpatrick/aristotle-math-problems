import Mathlib

/-!
# Lehmer's Totient Problem

**Conjecture (Lehmer, 1932):** If `φ(n) ∣ (n - 1)` and `n > 1`, then `n` is prime.

**Status:** OPEN. No counterexample is known. It has been shown that any composite
counterexample must be:
- odd
- squarefree
- have at least 15 prime factors
- exceed 10^30

We prove the known partial results:
- Any counterexample must be squarefree (`lehmer_squarefree`)
- Any counterexample must be odd (`lehmer_odd_or_prime`)
- The Carmichael condition: for every prime factor `p` of `n`, `(p - 1) ∣ (n - 1)`
  (`lehmer_carmichael`)

The main conjecture remains open and is stated with `sorry`.
-/

/-- Consecutive natural numbers are coprime. -/
lemma coprime_pred (n : ℕ) (hn : n > 1) : Nat.Coprime n (n - 1) := by
  cases n <;> simp_all +decide [Nat.succ_eq_add_one]

/-- If `φ(n) ∣ (n - 1)` and `n > 1`, then `n` is squarefree.
    Proof: if `p² ∣ n` then `p ∣ φ(n) ∣ (n-1)`, but `p ∣ n`, so `p ∣ gcd(n, n-1) = 1`. -/
lemma lehmer_squarefree (n : ℕ) (hn : n > 1)
    (hdvd : Nat.totient n ∣ (n - 1)) :
    Squarefree n := by
  by_contra h_not_squarefree
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ n := by
    simpa only [pow_two] using by rw [Nat.squarefree_iff_prime_squarefree] at h_not_squarefree; aesop
  have h_div_phi : p ∣ Nat.totient n := by
    refine' Nat.dvd_trans _ (Nat.totient_dvd_of_dvd hp.2)
    norm_num [Nat.totient_prime_pow hp.1]
  exact absurd (Nat.dvd_trans h_div_phi hdvd) (by
    intro h
    have := Nat.dvd_sub' (dvd_of_mul_left_dvd hp.2) h
    rcases n with (_ | _ | n) <;> simp_all +arith +decide [Nat.prime_dvd_prime_iff_eq])

/-- For `n > 2`, `φ(n)` is even. -/
lemma even_totient_of_even_gt_two (n : ℕ) (hn : n > 2) (heven : Even n) :
    2 ∣ Nat.totient n := by
  exact even_iff_two_dvd.mp (Nat.totient_even <| by linarith)

/-- If `φ(n) ∣ (n - 1)` and `n > 1`, then `n` is odd or `n` is prime.
    If `n` is even and `n > 2`, then `φ(n)` is even but `n - 1` is odd, contradiction.
    So `n = 2`, which is prime. -/
lemma lehmer_odd_or_prime (n : ℕ) (hn : n > 1)
    (hdvd : Nat.totient n ∣ (n - 1)) :
    Odd n ∨ Nat.Prime n := by
  by_cases h_even : Even n ∧ n > 2;
  · exact absurd ( even_iff_two_dvd.mp ( Nat.totient_even <| by linarith ) ) ( by intro t; exact absurd ( dvd_trans t hdvd ) ( by rw [ Nat.dvd_iff_mod_eq_zero ] ; rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Nat.even_iff, Nat.add_mod, Nat.mod_eq_zero_of_dvd ] ) );
  · rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ parity_simps ]

/-- If `p` is prime and `p ∣ n`, then `(p - 1) ∣ φ(n)`. -/
lemma prime_sub_one_dvd_totient (n p : ℕ) (hp : Nat.Prime p) (hpn : p ∣ n) :
    (p - 1) ∣ Nat.totient n := by
  exact Nat.totient_prime hp ▸ Nat.totient_dvd_of_dvd hpn

/-- **Carmichael condition:** if `φ(n) ∣ (n - 1)` and `p` is a prime divisor of `n`,
    then `(p - 1) ∣ (n - 1)`. -/
lemma lehmer_carmichael (n p : ℕ) (hn : n > 1)
    (hdvd : Nat.totient n ∣ (n - 1))
    (hp : Nat.Prime p) (hpn : p ∣ n) :
    (p - 1) ∣ (n - 1) := by
  exact Nat.dvd_trans (prime_sub_one_dvd_totient n p hp hpn) hdvd

/-- **Lehmer's Totient Conjecture** (Open Problem, 1932).
    If `φ(n) ∣ (n - 1)` and `n > 1`, then `n` is prime.

    This is an open problem. No proof or counterexample is known.
    Any composite counterexample must be odd, squarefree, have ≥ 15 prime factors,
    and exceed 10^30. -/
theorem lehmer_totient (n : ℕ) (hn : n > 1)
    (hdvd : Nat.totient n ∣ (n - 1)) :
    Nat.Prime n := by sorry
