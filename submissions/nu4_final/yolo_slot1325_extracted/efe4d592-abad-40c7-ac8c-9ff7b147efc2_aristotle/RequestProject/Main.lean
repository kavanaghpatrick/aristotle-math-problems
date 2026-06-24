import Mathlib

/-!
# Erdős Problem 364 — mod-36 closure for consecutive powerful triples

A natural number `n` is **powerful** iff for every prime `p` dividing `n`, `p²` also divides `n`.

We prove that if `n`, `n+1`, and `n+2` are all powerful, then `n % 36 ∈ {7, 27, 35}`.

This is an unconditional elementary modular partial result toward the full Erdős conjecture
that no three consecutive powerful numbers exist (open for `n < 10²²`).
-/

/-- A natural number is *powerful* if every prime factor occurs with exponent at least 2. -/
def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- If `x ≡ 2 (mod 4)` then `x` is not powerful: `2 ∣ x` but `4 ∤ x`. -/
lemma not_powerful_of_mod4_eq2 (x : ℕ) (h : x % 4 = 2) : ¬ Powerful x := by
  intro hpow
  have : 4 ∣ x := by
    have := hpow 2 (by norm_num) (by omega : 2 ∣ x)
    norm_num at this; exact this
  omega

/-- If `x ≡ 3 (mod 9)` then `x` is not powerful: `3 ∣ x` but `9 ∤ x`. -/
lemma not_powerful_of_mod9_eq3 (x : ℕ) (h : x % 9 = 3) : ¬ Powerful x := by
  intro hpow
  have : 9 ∣ x := by
    have := hpow 3 (by norm_num) (by omega : 3 ∣ x)
    norm_num at this; exact this
  omega

/-- If `x ≡ 6 (mod 9)` then `x` is not powerful: `3 ∣ x` but `9 ∤ x`. -/
lemma not_powerful_of_mod9_eq6 (x : ℕ) (h : x % 9 = 6) : ¬ Powerful x := by
  intro hpow
  have : 9 ∣ x := by
    have := hpow 3 (by norm_num) (by omega : 3 ∣ x)
    norm_num at this; exact this
  omega

/--
**Erdős 364 (mod-36 closure).**
If `n`, `n + 1`, and `n + 2` are all powerful, then `n ≡ 7, 27, or 35 (mod 36)`.

*Proof outline.* Among three consecutive integers one is `≡ 2 (mod 4)` unless `n ≡ 3 (mod 4)`;
a residue-2 number is not powerful (prime factor 2 with `4 ∤ x`). Similarly, among three
consecutive integers one is `≡ 3` or `≡ 6 (mod 9)` unless `n % 9 ∈ {0, 7, 8}`, and those
residues are not powerful (prime factor 3 with `9 ∤ x`). The Chinese Remainder Theorem
combines `n % 4 = 3` with `n % 9 ∈ {0, 7, 8}` to yield `n % 36 ∈ {7, 27, 35}`.
-/
theorem erdos_364_mod36
    (n : ℕ) (hn : Powerful n) (hn1 : Powerful (n + 1)) (hn2 : Powerful (n + 2)) :
    n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35 := by
  -- Step 1: n ≡ 3 (mod 4)
  have hmod4 : n % 4 = 3 := by
    have h4 := Nat.mod_lt n (show 0 < 4 by norm_num)
    by_contra hne
    have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 := by omega
    rcases this with h | h | h
    · exact not_powerful_of_mod4_eq2 (n + 2) (by omega) hn2
    · exact not_powerful_of_mod4_eq2 (n + 1) (by omega) hn1
    · exact not_powerful_of_mod4_eq2 n (by omega) hn
  -- Step 2: n % 9 ∈ {0, 7, 8}
  have hmod9 : n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
    have h9 := Nat.mod_lt n (show 0 < 9 by norm_num)
    by_contra hne
    push_neg at hne
    have : n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 := by omega
    rcases this with h | h | h | h | h | h
    · exact not_powerful_of_mod9_eq3 (n + 2) (by omega) hn2
    · exact not_powerful_of_mod9_eq3 (n + 1) (by omega) hn1
    · exact not_powerful_of_mod9_eq3 n h hn
    · exact not_powerful_of_mod9_eq6 (n + 2) (by omega) hn2
    · exact not_powerful_of_mod9_eq6 (n + 1) (by omega) hn1
    · exact not_powerful_of_mod9_eq6 n h hn
  -- Step 3: CRT gives n % 36 ∈ {7, 27, 35}
  omega
