import Mathlib

set_option maxHeartbeats 800000

/-- A natural number is *powerful* if every prime dividing it also has its square dividing it. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-
Obstruction lemmas: if x has a specific residue mod p^2 that is divisible by p but not p^2,
then x is not powerful.
-/
lemma not_powerful_of_mod4_eq2 (x : ℕ) (h : x % 4 = 2) : ¬Powerful x := by
  exact fun H => by have := H 2 Nat.prime_two ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ; omega;

lemma not_powerful_of_mod9_eq3 (x : ℕ) (h : x % 9 = 3) : ¬Powerful x := by
  exact fun h' => absurd ( h' 3 Nat.prime_three ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod9_eq6 (x : ℕ) (h : x % 9 = 6) : ¬Powerful x := by
  exact fun H => absurd ( H 3 Nat.prime_three ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod25_eq5 (x : ℕ) (h : x % 25 = 5) : ¬Powerful x := by
  exact fun h' => absurd ( h' 5 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod25_eq10 (x : ℕ) (h : x % 25 = 10) : ¬Powerful x := by
  exact fun hP => absurd ( hP 5 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod25_eq15 (x : ℕ) (h : x % 25 = 15) : ¬Powerful x := by
  exact fun hP => by have := hP 5 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ; omega;

lemma not_powerful_of_mod25_eq20 (x : ℕ) (h : x % 25 = 20) : ¬Powerful x := by
  exact fun hP => absurd ( hP 5 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod49_eq7 (x : ℕ) (h : x % 49 = 7) : ¬Powerful x := by
  exact fun H => absurd ( H 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod49_eq14 (x : ℕ) (h : x % 49 = 14) : ¬Powerful x := by
  exact fun hP => absurd ( hP 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod49_eq21 (x : ℕ) (h : x % 49 = 21) : ¬Powerful x := by
  exact fun hP => absurd ( hP 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod49_eq28 (x : ℕ) (h : x % 49 = 28) : ¬Powerful x := by
  exact fun hP => absurd ( hP 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod49_eq35 (x : ℕ) (h : x % 49 = 35) : ¬Powerful x := by
  exact fun hP => absurd ( hP 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

lemma not_powerful_of_mod49_eq42 (x : ℕ) (h : x % 49 = 42) : ¬Powerful x := by
  exact fun hP => absurd ( hP 7 ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega )

/-
Main theorem components
-/
lemma powerful_triple_mod4 (n : ℕ) (hn : Powerful n) (hn1 : Powerful (n + 1))
    (hn2 : Powerful (n + 2)) : n % 4 = 3 := by
  by_contra! h_contra;
  -- By examining each case, we � can� see that for any natural number n, at least one of n, n+1, or n+2 is not powerful. We will consider each case where n mod 4 is 0, 1, or 2.
  by_cases h_mod4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2;
  · rcases h_mod4 with ( h | h | h );
    · exact not_powerful_of_mod4_eq2 ( n + 2 ) ( by norm_num [ Nat.add_mod, h ] ) hn2;
    · exact absurd ( hn1 2 Nat.prime_two ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ( by omega );
    · exact not_powerful_of_mod4_eq2 n h hn;
  · have := Nat.mod_lt n zero_lt_four; interval_cases n % 4 <;> contradiction;

lemma powerful_triple_mod9 (n : ℕ) (hn : Powerful n) (hn1 : Powerful (n + 1))
    (hn2 : Powerful (n + 2)) : n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
  have := @not_powerful_of_mod9_eq3 ( n+2 ) ; have := @not_powerful_of_mod9_eq6 ( n+2 ) ; have := @not_powerful_of_mod9_eq3 ( n+1 ) ; have := @not_powerful_of_mod9_eq6 ( n+1 ) ; have := @not_powerful_of_mod9_eq3 n ; have := @not_powerful_of_mod9_eq6 n ; norm_num [ Nat.add_mod ] at *;
  have := Nat.mod_lt n ( by decide : 0 < 9 ) ; interval_cases _ : n % 9 <;> simp_all +decide ;

lemma powerful_triple_mod25 (n : ℕ) (hn : Powerful n) (hn1 : Powerful (n + 1))
    (hn2 : Powerful (n + 2)) :
    n % 25 ∈ ({0,1,2,6,7,11,12,16,17,21,22,23,24} : Finset ℕ) := by
  have := @not_powerful_of_mod25_eq5 ( n + 2 ) ; have := @not_powerful_of_mod25_eq10 ( n + 2 ) ; have := @not_powerful_of_mod25_eq15 ( n + 2 ) ; have := @not_powerful_of_mod25_eq20 ( n + 2 ) ; have := @not_powerful_of_mod25_eq5 ( n + 1 ) ; have := @not_powerful_of_mod25_eq10 ( n + 1 ) ; have := @not_powerful_of_mod25_eq15 ( n + 1 ) ; have := @not_powerful_of_mod25_eq20 ( n + 1 ) ; have := @not_powerful_of_mod25_eq5 n ; have := @not_powerful_of_mod25_eq10 n ; have := @not_powerful_of_mod25_eq15 n ; have := @not_powerful_of_mod25_eq20 n ; simp_all +arith +decide ;
  grind +ring

lemma powerful_triple_mod49 (n : ℕ) (hn : Powerful n) (hn1 : Powerful (n + 1))
    (hn2 : Powerful (n + 2)) :
    n % 49 ∈ ({0,1,2,3,4,8,9,10,11,15,16,17,18,22,23,24,25,
              29,30,31,32,36,37,38,39,43,44,45,46,47,48} : Finset ℕ) := by
  contrapose! hn1; contrapose! hn2; simp_all +decide ;
  intro h; have := h 7; norm_num at this;
  have := hn2 7; norm_num at this;
  have := hn 7; norm_num at this; omega;

theorem erdos_364_mod44100
    (n : ℕ) (hn : Powerful n) (hn1 : Powerful (n + 1)) (hn2 : Powerful (n + 2)) :
    n % 4 = 3 ∧ (n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8) ∧
      (n % 25 ∈ ({0,1,2,6,7,11,12,16,17,21,22,23,24} : Finset ℕ)) ∧
      (n % 49 ∈ ({0,1,2,3,4,8,9,10,11,15,16,17,18,22,23,24,25,
                  29,30,31,32,36,37,38,39,43,44,45,46,47,48} : Finset ℕ)) := by
  exact ⟨powerful_triple_mod4 n hn hn1 hn2,
         powerful_triple_mod9 n hn hn1 hn2,
         powerful_triple_mod25 n hn hn1 hn2,
         powerful_triple_mod49 n hn hn1 hn2⟩