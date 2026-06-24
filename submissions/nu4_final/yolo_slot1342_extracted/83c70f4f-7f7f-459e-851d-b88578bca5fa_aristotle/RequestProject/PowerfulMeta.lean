import Mathlib

/-! # Powerful Numbers Chapter — Joint mod-44100 + coprimality META

A natural number `n` is *powerful* if every prime factor of `n` appears with exponent ≥ 2.
This file proves a three-conjunct meta-theorem about powerful numbers in arithmetic progressions.
-/

/-- A natural number is *powerful* if for every prime `p` dividing it, `p²` also divides it. -/
def Nat.Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-! ## Atomic obstruction lemmas

These lemmas establish that certain residues modulo prime squares are incompatible
with being a powerful number. -/

/-
If x ≡ 2 (mod 4), then x is not powerful (2 | x but 4 ∤ x).
-/
lemma not_powerful_of_mod4_eq2 (x : ℕ) (h : x % 4 = 2) : ¬ Nat.Powerful x := by
  exact fun H => by have := H 2 Nat.prime_two ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ; omega;

/-
If x ≡ 3 (mod 9), then x is not powerful (3 | x but 9 ∤ x).
-/
lemma not_powerful_of_mod9_eq3 (x : ℕ) (h : x % 9 = 3) : ¬ Nat.Powerful x := by
  exact fun H => by have := H 3 Nat.prime_three ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ; omega;

/-
If x ≡ 6 (mod 9), then x is not powerful (3 | x but 9 ∤ x).
-/
lemma not_powerful_of_mod9_eq6 (x : ℕ) (h : x % 9 = 6) : ¬ Nat.Powerful x := by
  exact fun H => absurd ( H 3 Nat.prime_three ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
If x ≡ 5 (mod 25), then x is not powerful (5 | x but 25 ∤ x).
-/
lemma not_powerful_of_mod25_eq5 (x : ℕ) (h : x % 25 = 5) : ¬ Nat.Powerful x := by
  -- By definition, $x$ is powerful if for every prime $p$, $p^2 \mid x$ whenever $p \mid x$.
  unfold Nat.Powerful
  intro hp
  exact absurd (hp 5 (by norm_num) (Nat.dvd_of_mod_eq_zero (by omega))) (by omega)

/-
If x ≡ 10 (mod 25), then x is not powerful.
-/
lemma not_powerful_of_mod25_eq10 (x : ℕ) (h : x % 25 = 10) : ¬ Nat.Powerful x := by
  exact fun H => absurd ( H 5 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
If x ≡ 15 (mod 25), then x is not powerful.
-/
lemma not_powerful_of_mod25_eq15 (x : ℕ) (h : x % 25 = 15) : ¬ Nat.Powerful x := by
  exact fun h' => absurd ( h' 5 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
If x ≡ 20 (mod 25), then x is not powerful.
-/
lemma not_powerful_of_mod25_eq20 (x : ℕ) (h : x % 25 = 20) : ¬ Nat.Powerful x := by
  rintro hx;
  exact absurd ( hx 5 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
If x ≡ 7 (mod 49), then x is not powerful (7 | x but 49 ∤ x).
-/
lemma not_powerful_of_mod49_eq7 (x : ℕ) (h : x % 49 = 7) : ¬ Nat.Powerful x := by
  exact fun H => absurd ( H 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
If x ≡ 14 (mod 49), then x is not powerful.
-/
lemma not_powerful_of_mod49_eq14 (x : ℕ) (h : x % 49 = 14) : ¬ Nat.Powerful x := by
  intro hx; have := hx 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, h ] at this;

/-
If x ≡ 21 (mod 49), then x is not powerful.
-/
lemma not_powerful_of_mod49_eq21 (x : ℕ) (h : x % 49 = 21) : ¬ Nat.Powerful x := by
  exact fun H => absurd ( H 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
If x ≡ 28 (mod 49), then x is not powerful.
-/
lemma not_powerful_of_mod49_eq28 (x : ℕ) (h : x % 49 = 28) : ¬ Nat.Powerful x := by
  exact fun H => absurd ( H 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
If x ≡ 35 (mod 49), then x is not powerful.
-/
lemma not_powerful_of_mod49_eq35 (x : ℕ) (h : x % 49 = 35) : ¬ Nat.Powerful x := by
  -- Since $x \equiv 35 \pmod{49}$, we have $7 \mid x$ but $49 \nmid x$.
  have h7 : 7 ∣ x := by
    lia
  have h49 : ¬49 ∣ x := by
    omega
  exact fun h_powerful => by have := h_powerful 7 (by norm_num) h7; exact h49 this;

/-
If x ≡ 42 (mod 49), then x is not powerful.
-/
lemma not_powerful_of_mod49_eq42 (x : ℕ) (h : x % 49 = 42) : ¬ Nat.Powerful x := by
  exact fun h' => by have := h' 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ; omega;

/-! ## Conjunct (a): mod-44100 closure for consecutive powerful triples -/

private lemma consec_powerful_mod4 (n : ℕ)
    (hn : Nat.Powerful n) (hn1 : Nat.Powerful (n+1)) (hn2 : Nat.Powerful (n+2)) :
    n % 4 = 3 := by
  have := Nat.mod_lt n zero_lt_four; interval_cases _ : n % 4 <;> simp_all +decide;
  · exact absurd ( hn2 2 Nat.prime_two ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega );
  · exact not_powerful_of_mod4_eq2 _ ( by norm_num [ *, Nat.add_mod ] ) hn1;
  · exact not_powerful_of_mod4_eq2 _ ( by omega ) hn

private lemma consec_powerful_mod9 (n : ℕ)
    (hn : Nat.Powerful n) (hn1 : Nat.Powerful (n+1)) (hn2 : Nat.Powerful (n+2)) :
    n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
  have := Nat.mod_lt n ( by decide : 0 < 9 ) ; interval_cases _ : n % 9 <;> simp_all +decide;
  all_goals have := hn1 3 Nat.prime_three; have := hn2 3 Nat.prime_three; norm_num at *;
  bv_omega;
  · lia;
  · exact absurd ( hn 3 Nat.prime_three ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega );
  · exact absurd ( this ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega );
  · exact absurd ( this ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega );
  · exact absurd ( hn 3 Nat.prime_three ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

private lemma consec_powerful_mod25 (n : ℕ)
    (hn : Nat.Powerful n) (hn1 : Nat.Powerful (n+1)) (hn2 : Nat.Powerful (n+2)) :
    n % 25 ∈ ({0,1,2,6,7,11,12,16,17,21,22,23,24} : Finset ℕ) := by
  by_contra h_contra;
  -- Since $n$ is powerful, $n+1$ and $n+2$ must also be powerful.
  have h_mod25_cases : (n + 1) % 25 ∈ ({5, 10, 15, 20} : Finset ℕ) ∨ (n + 2) % 25 ∈ ({5, 10, 15, 20} : Finset ℕ) ∨ n % 25 ∈ ({5, 10, 15, 20} : Finset ℕ) := by
    norm_num [ Nat.add_mod ] ; have := Nat.mod_lt n ( by decide : 0 < 25 ) ; interval_cases n % 25 <;> trivial;
  rcases h_mod25_cases with ( h | h | h ) <;> simp_all +decide [ Nat.add_mod ];
  · exact absurd ( hn1 5 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( show ( n + 1 ) % 5 = 0 by omega ) ) ) ( by omega );
  · have := Nat.mod_lt n ( by decide : 0 < 25 ) ; interval_cases _ : n % 25 <;> simp_all +decide ;
    · exact not_powerful_of_mod25_eq5 ( n + 2 ) ( by norm_num [ *, Nat.add_mod ] ) hn2;
    · exact not_powerful_of_mod25_eq10 ( n + 2 ) ( by norm_num [ *, Nat.add_mod ] ) hn2;
    · exact not_powerful_of_mod25_eq15 ( n + 2 ) ( by norm_num [ *, Nat.add_mod ] ) hn2;
    · exact not_powerful_of_mod25_eq20 ( n + 2 ) ( by norm_num [ *, Nat.add_mod ] ) hn2;
  · rcases h with ( h | h | h | h ) <;> have := not_powerful_of_mod25_eq5 n <;> have := not_powerful_of_mod25_eq10 n <;> have := not_powerful_of_mod25_eq15 n <;> have := not_powerful_of_mod25_eq20 n <;> simp_all +decide

private lemma consec_powerful_mod49 (n : ℕ)
    (hn : Nat.Powerful n) (hn1 : Nat.Powerful (n+1)) (hn2 : Nat.Powerful (n+2)) :
    n % 49 ∈ ({0,1,2,3,4,8,9,10,11,15,16,17,18,22,23,24,25,
              29,30,31,32,36,37,38,39,43,44,45,46,47,48} : Finset ℕ) := by
  by_contra h_contra;
  have h_n_mod_49 : n % 49 ∈ ({7, 14, 21, 28, 35, 42} : Finset ℕ) ∨ (n + 1) % 49 ∈ ({7, 14, 21, 28, 35, 42} : Finset ℕ) ∨ (n + 2) % 49 ∈ ({7, 14, 21, 28, 35, 42} : Finset ℕ) := by
    norm_num [ Nat.add_mod ] ; have := Nat.mod_lt n ( by decide : 0 < 49 ) ; interval_cases n % 49 <;> trivial;
  rcases h_n_mod_49 with ( h | h | h ) <;> simp_all +decide [ Nat.add_mod ];
  · rcases h with ( h | h | h | h | h | h ) <;> have := hn 7 <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, h ] at this;
    all_goals omega;
  · exact absurd ( hn1 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( show ( n + 1 ) % 7 = 0 from by omega ) ) ) ( by omega );
  · exact absurd ( hn2 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( show ( n + 2 ) % 7 = 0 from by omega ) ) ) ( by omega )

/-! ## Conjunct (c): squarefree-d coprimality -/

/-
Key structural lemma: if p is prime with p ∣ d but p² ∤ d, and both n and n+d
are powerful, then p ∤ n.
-/
lemma powerful_pair_prime_not_dvd (p n d : ℕ) (hp : p.Prime) (hpd : p ∣ d)
    (hpd2 : ¬ (p ^ 2 ∣ d)) (hn : Nat.Powerful n) (hnd : Nat.Powerful (n + d)) :
    ¬ (p ∣ n) := by
  exact fun h => hpd2 <| by simpa [ Nat.dvd_add_right ( hn p hp h ) ] using hnd p hp ( dvd_add h hpd ) ;

/-
If d is squarefree and n, n+d, n+2d are all powerful, then gcd(n,d) = 1.
-/
lemma powerful_3ap_squarefree_coprime (n d : ℕ) (_hd : 0 < d) (hsq : Squarefree d)
    (hn : Nat.Powerful n) (hnd : Nat.Powerful (n + d)) (_hn2d : Nat.Powerful (n + 2 * d)) :
    Nat.Coprime n d := by
  by_contra h_contra;
  -- Then there exists a prime p dividing gcd(n,d), so� p� | � n� and p | d.
  obtain ⟨p, hp_prime, hp_div_n, hp_div_d⟩ : ∃ p, Nat.Prime p ∧ p ∣ n ∧ p ∣ d := by
    exact Nat.Prime.not_coprime_iff_dvd.mp h_contra;
  exact powerful_pair_prime_not_dvd p n d hp_prime hp_div_d ( fun h => hp_prime.not_isUnit <| hsq _ <| by simpa [ sq ] using h ) hn hnd hp_div_n

/-! ## Main META theorem -/

theorem powerful_chapter_meta :
    (∀ n : ℕ, Nat.Powerful n → Nat.Powerful (n+1) → Nat.Powerful (n+2) →
       n % 4 = 3 ∧ (n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8) ∧
       (n % 25 ∈ ({0,1,2,6,7,11,12,16,17,21,22,23,24} : Finset ℕ)) ∧
       (n % 49 ∈ ({0,1,2,3,4,8,9,10,11,15,16,17,18,22,23,24,25,
                   29,30,31,32,36,37,38,39,43,44,45,46,47,48} : Finset ℕ)))
    ∧ (∀ n d : ℕ, 0 < d → Nat.Powerful n → Nat.Powerful (n+d) → Nat.Powerful (n+2*d) →
       n % 4 ≠ 2 ∧ (n+d) % 4 ≠ 2 ∧ (n+2*d) % 4 ≠ 2 ∧
       n % 9 ∉ ({3,6} : Finset ℕ) ∧
       (n+d) % 9 ∉ ({3,6} : Finset ℕ) ∧ (n+2*d) % 9 ∉ ({3,6} : Finset ℕ))
    ∧ (∀ n d : ℕ, 0 < d → Squarefree d → Nat.Powerful n →
       Nat.Powerful (n+d) → Nat.Powerful (n+2*d) → Nat.Coprime n d) := by
  constructor;
  · grind +suggestions;
  · simp +zetaDelta at *;
    grind +suggestions