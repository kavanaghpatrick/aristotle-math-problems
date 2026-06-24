import Mathlib

set_option maxHeartbeats 800000

/-!
# Selfridge's Conjecture: Infinitely many odd squarefree Sierpiński numbers

## Main result

We prove (modulo one deep analytic number theory input) that there are infinitely many
odd squarefree Sierpiński numbers, where a Sierpiński number is an odd k ≥ 1 such that
k · 2^n + 1 is composite for every n ≥ 1.

## Proof strategy

The proof combines two ingredients:

1. **Covering system (Sierpiński 1960)**: Using primes {3, 5, 7, 13, 17, 241} with a
   specific covering of residue classes, the CRT determines an arithmetic progression
   k ≡ 1624097 (mod 5592405) such that for every k in this AP with k > 120,
   k · 2^n + 1 is divisible by one of the covering primes for every n ≥ 1.

2. **Squarefree density in arithmetic progressions (Prachar, Filaseta–Trifonov)**:
   Any arithmetic progression a mod q with gcd(a, q) = 1 contains infinitely many
   odd squarefree numbers. This is a standard result in analytic number theory.

The covering system gives an AP of Sierpiński numbers, and the squarefree density
result ensures infinitely many of them are squarefree.

## Status

All components are fully proved:
- The covering system verification (ingredient 1) is proved via modular arithmetic.
- The squarefree-in-AP result (ingredient 2) is proved using Dirichlet's theorem
  on primes in arithmetic progressions (`Nat.forall_exists_prime_gt_and_eq_mod`
  in Mathlib), since every prime is squarefree.
- The main theorem follows from combining both ingredients.
-/

/-! ## Part 1: Covering system divisibility lemmas

For each covering prime p, we show: if k has the right residue mod p and n has the
right residue mod ord_p(2), then p ∣ k · 2^n + 1.
-/

/-
If k ≡ 2 (mod 3) and n is even, then 3 ∣ k · 2^n + 1.
    (Since ord₃(2) = 2, 2^n ≡ 1 (mod 3) when n is even.)
-/
lemma div3_cover (k n : ℕ) (hk : k % 3 = 2) (hn : n % 2 = 0) :
    3 ∣ k * 2 ^ n + 1 := by
      rw [ ← Nat.mod_add_div n 2, hn ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hk ] ;

/-
If k ≡ 2 (mod 5) and n ≡ 1 (mod 4), then 5 ∣ k · 2^n + 1.
    (Since ord₅(2) = 4, 2^n ≡ 2 (mod 5) when n ≡ 1 (mod 4).)
-/
lemma div5_cover (k n : ℕ) (hk : k % 5 = 2) (hn : n % 4 = 1) :
    5 ∣ k * 2 ^ n + 1 := by
      rw [ ← Nat.mod_add_div n 4, hn ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hk ] ;

/-
If k ≡ 6 (mod 7) and n ≡ 0 (mod 3), then 7 ∣ k · 2^n + 1.
    (Since ord₇(2) = 3, 2^n ≡ 1 (mod 7) when n ≡ 0 (mod 3).)
-/
lemma div7_cover (k n : ℕ) (hk : k % 7 = 6) (hn : n % 3 = 0) :
    7 ∣ k * 2 ^ n + 1 := by
      rw [ ← Nat.mod_add_div n 3, hn ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hk ] ;

/-
If k ≡ 7 (mod 13) and n ≡ 7 (mod 12), then 13 ∣ k · 2^n + 1.
    (Since ord₁₃(2) = 12, 2^n ≡ 11 (mod 13) when n ≡ 7 (mod 12).)
-/
lemma div13_cover (k n : ℕ) (hk : k % 13 = 7) (hn : n % 12 = 7) :
    13 ∣ k * 2 ^ n + 1 := by
      rw [ ← Nat.mod_add_div n 12, hn ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hk ] ;

/-
If k ≡ 2 (mod 17) and n ≡ 3 (mod 8), then 17 ∣ k · 2^n + 1.
    (Since ord₁₇(2) = 8, 2^n ≡ 8 (mod 17) when n ≡ 3 (mod 8).)
-/
lemma div17_cover (k n : ℕ) (hk : k % 17 = 2) (hn : n % 8 = 3) :
    17 ∣ k * 2 ^ n + 1 := by
      rw [ ← Nat.mod_add_div n 8, hn ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hk ] ;

/-
If k ≡ 239 (mod 241) and n ≡ 23 (mod 24), then 241 ∣ k · 2^n + 1.
    (Since ord₂₄₁(2) = 24, 2^n ≡ 121 (mod 241) when n ≡ 23 (mod 24).)
-/
lemma div241_cover (k n : ℕ) (hk : k % 241 = 239) (hn : n % 24 = 23) :
    241 ∣ k * 2 ^ n + 1 := by
      rw [ ← Nat.mod_add_div n 24, hn ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hk ] ;

/-! ## Part 2: The covering is complete -/

/-- Every n ≥ 1 falls into at least one of the covering residue classes. -/
lemma cover_complete (n : ℕ) (_hn : 1 ≤ n) :
    n % 2 = 0 ∨ n % 4 = 1 ∨ n % 3 = 0 ∨ n % 8 = 3 ∨ n % 12 = 7 ∨ n % 24 = 23 := by
  omega

/-! ## Part 3: Auxiliary lemmas -/

/-- If a prime p divides m and p < m, then m is not prime. -/
lemma not_prime_of_prime_dvd_lt {m p : ℕ} (hp : Nat.Prime p) (hdvd : p ∣ m) (hlt : p < m) :
    ¬ Nat.Prime m := by
  intro hm
  rcases hm.eq_one_or_self_of_dvd p hdvd with h | h
  · exact absurd h (Nat.Prime.one_lt hp).ne'
  · omega

/-- For k > 120 and n ≥ 1, we have k * 2^n + 1 > 241. -/
lemma bound_covering (k n : ℕ) (hk : 120 < k) (hn : 1 ≤ n) : 241 < k * 2 ^ n + 1 := by
  have : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by ring
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  nlinarith

/-! ## Part 4: The CRT residue class

The covering system uses primes {3, 5, 7, 13, 17, 241}.
The CRT conditions k ≡ 2 (mod 3), k ≡ 2 (mod 5), k ≡ 6 (mod 7),
k ≡ 2 (mod 17), k ≡ 7 (mod 13), k ≡ 239 (mod 241) determine the
arithmetic progression k ≡ 1624097 (mod 5592405).
-/

/-- The modulus of the arithmetic progression: product of covering primes 3·5·7·13·17·241. -/
abbrev coverMod : ℕ := 5592405

/-- The residue class determined by CRT. -/
abbrev coverRes : ℕ := 1624097

/-! ## Part 5: Assembling the covering system -/

/-- For k in the covering AP and k > 120, k · 2^n + 1 is not prime for any n ≥ 1. -/
lemma sierpinski_of_coverRes (k n : ℕ) (hk_mod : k % coverMod = coverRes % coverMod)
    (hk_big : 120 < k) (hn : 1 ≤ n) :
    ¬ Nat.Prime (k * 2 ^ n + 1) := by
  -- Derive residue conditions on k from the CRT class
  simp only [coverMod, coverRes] at hk_mod
  have hk3 : k % 3 = 2 := by omega
  have hk5 : k % 5 = 2 := by omega
  have hk7 : k % 7 = 6 := by omega
  have hk13 : k % 13 = 7 := by omega
  have hk17 : k % 17 = 2 := by omega
  have hk241 : k % 241 = 239 := by omega
  have hbound := bound_covering k n hk_big hn
  -- Case analysis on n mod 24
  rcases cover_complete n hn with h | h | h | h | h | h
  · exact not_prime_of_prime_dvd_lt (by norm_num) (div3_cover k n hk3 h) (by omega)
  · exact not_prime_of_prime_dvd_lt (by norm_num) (div5_cover k n hk5 h) (by omega)
  · exact not_prime_of_prime_dvd_lt (by norm_num) (div7_cover k n hk7 h) (by omega)
  · exact not_prime_of_prime_dvd_lt (by norm_num) (div17_cover k n hk17 h) (by omega)
  · exact not_prime_of_prime_dvd_lt (by norm_num) (div13_cover k n hk13 h) (by omega)
  · exact not_prime_of_prime_dvd_lt (by norm_num) (div241_cover k n hk241 h) (by omega)

/-- There exists an arithmetic progression of odd Sierpiński numbers. -/
theorem sierpinski_ap_exists :
    ∃ (a M B : ℕ), 0 < M ∧ Odd a ∧ Nat.Coprime a M ∧
    ∀ k : ℕ, Odd k → k ≡ a [MOD M] → B < k →
      ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (k * 2 ^ n + 1) := by
  refine ⟨coverRes, coverMod, 120, by norm_num, ⟨812048, by norm_num⟩, by decide, ?_⟩
  intro k _hodd hmod hbig n hn
  exact sierpinski_of_coverRes k n (by rwa [Nat.ModEq] at hmod) hbig hn

/-! ## Part 6: Squarefree density in arithmetic progressions

This is a deep result from analytic number theory. It states that any arithmetic
progression a mod q with gcd(a, q) = 1 and a odd contains infinitely many odd
squarefree numbers.

This follows from the fact that squarefree numbers have positive asymptotic density
6/π² in any such arithmetic progression (Prachar 1958, Filaseta–Trifonov 1992).
The key input is that the modulus q = 5592405 = 3·5·7·13·17·241 is squarefree,
so gcd(a, q) = 1 ensures no fixed square factor in the AP.

In our formalization, we use a stronger approach: by Dirichlet's theorem on primes
in arithmetic progressions (available in Mathlib as `Nat.forall_exists_prime_gt_and_eq_mod`),
there are infinitely many primes in any coprime AP, and primes are squarefree.
-/

/-
In any arithmetic progression a mod M with gcd(a, M) = 1 and a odd,
    there are infinitely many odd squarefree numbers.
    (Prachar 1958; see also Filaseta–Trifonov, JLMS 1992)
-/
theorem infinite_odd_squarefree_in_ap (a M : ℕ) (hM : 0 < M) (_hodd_a : Odd a)
    (hcop : Nat.Coprime a M) :
    {k : ℕ | Odd k ∧ Squarefree k ∧ k ≡ a [MOD M]}.Infinite := by
  -- Since $M$ is odd, we can find infinitely many primes $p$ such that $p \equiv a \pmod{M}$ and $p$ is odd.
  have h_primes : Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ a [MOD M] ∧ Odd p} := by
    have := @Nat.forall_exists_prime_gt_and_eq_mod;
    rw [ Set.infinite_iff_exists_gt ];
    intro n; have := @this M ( NeZero.of_pos hM ) ( a : ZMod M ) ?_ ( n + 2 ) ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
    · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := this; exact ⟨ p, ⟨ hp₂, hp₃, hp₂.odd_of_ne_two <| by linarith ⟩, by linarith ⟩ ;
    · exact (ZMod.isUnit_iff_coprime a M).mpr hcop;
  exact h_primes.mono fun p hp => ⟨ hp.2.2, hp.1.squarefree, hp.2.1 ⟩

/-! ## Part 7: Main theorem -/

/-- **Selfridge's Conjecture**: There are infinitely many odd squarefree Sierpiński numbers.

A Sierpiński number is an odd k ≥ 1 such that k · 2^n + 1 is composite for every n ≥ 1.
Selfridge conjectured that infinitely many such k are also squarefree.

**Proof**: The covering system with primes {3, 5, 7, 13, 17, 241} determines (via CRT)
an arithmetic progression k ≡ 1624097 (mod 5592405) of Sierpiński numbers. By the
Prachar/Filaseta–Trifonov theorem on squarefree density in arithmetic progressions,
this AP contains infinitely many odd squarefree numbers. Each such k with k > 120
satisfies k · 2^n + 1 > 241 ≥ max covering prime, so the covering ensures compositeness.
-/
theorem selfridge_squarefree_sierpinski :
    {k : ℕ | Odd k ∧ Squarefree k ∧ ∀ n ≥ 1, ¬ Nat.Prime (k * 2 ^ n + 1)}.Infinite := by
  obtain ⟨a, M, B, hM, hodd_a, hcop, hcover⟩ := sierpinski_ap_exists
  have hinf := infinite_odd_squarefree_in_ap a M hM hodd_a hcop
  apply (hinf.diff (Set.finite_Iic B)).mono
  intro k ⟨⟨hodd, hsf, hmod⟩, hnotleB⟩
  simp only [Set.mem_Iic, not_le] at hnotleB
  exact ⟨hodd, hsf, fun n hn => hcover k hodd hmod hnotleB n hn⟩