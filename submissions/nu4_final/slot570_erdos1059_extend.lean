/-
Erdős Problem 1059: Extensions to primes 367, 461, 557

Are there infinitely many primes p such that p - k! is composite for each k
with 1 ≤ k! < p?

Known examples: p = 101, p = 211 (verified in formal-conjectures repo).
We extend to p = 367, 461, 557 using the same decidable infrastructure.

Reference: https://www.erdosproblems.com/1059
-/

import Mathlib

namespace Erdos1059

def IsFactorial (d : ℕ) : Prop :=
  d ∈ Set.range Nat.factorial

def factorialsLessThanN (n : ℕ) : Set ℕ :=
  { d | d < n ∧ IsFactorial d }

def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀d ∈ factorialsLessThanN n, (n - d).Composite

abbrev DecidableIsFactorial (d : ℕ) : Prop :=
  ((Finset.Icc 0 d).filter (λ k => Nat.factorial k = d)).Nonempty

def decidableFactorialsLessThanN (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter DecidableIsFactorial

def DecidableAllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ d ∈ decidableFactorialsLessThanN n, (n - d).Composite

lemma isFactorial_equivalent (d : ℕ) :
  IsFactorial d ↔ DecidableIsFactorial d := by
  unfold IsFactorial DecidableIsFactorial
  simp
  constructor
  · rintro ⟨k, hk⟩
    use k
    rw [Finset.mem_filter]
    constructor
    · have hk : k <= d := by
        rw [← hk]
        apply Nat.self_le_factorial
      rw [Finset.mem_Icc]
      exact ⟨Nat.zero_le k, hk⟩
    · exact hk
  · rintro ⟨k, hk⟩
    use k
    rw [Finset.mem_filter] at hk
    exact hk.2

lemma factorialsLessThanN_equivalent (n : ℕ) :
  factorialsLessThanN n = ↑(decidableFactorialsLessThanN n) := by
  ext d
  unfold factorialsLessThanN decidableFactorialsLessThanN
  simp
  exact λ _ => isFactorial_equivalent d

lemma allFactorialSubtractionsComposite_equivalent (d : ℕ) :
    DecidableAllFactorialSubtractionsComposite d ↔ AllFactorialSubtractionsComposite d := by
  unfold AllFactorialSubtractionsComposite DecidableAllFactorialSubtractionsComposite
  rw [factorialsLessThanN_equivalent d]
  simp

/-- p = 367 is a prime where p - k! is composite for all k with 1 ≤ k! < p.
Factorials less than 367: 1, 2, 6, 24, 120.
367 - 1 = 366 = 2 × 3 × 61
367 - 2 = 365 = 5 × 73
367 - 6 = 361 = 19²
367 - 24 = 343 = 7³
367 - 120 = 247 = 13 × 19
-/
theorem allFactorialSubtractionsComposite_367 : AllFactorialSubtractionsComposite 367 := by
  have h : DecidableAllFactorialSubtractionsComposite 367 := by
    norm_num [DecidableAllFactorialSubtractionsComposite, decidableFactorialsLessThanN]
    decide +kernel
  exact (allFactorialSubtractionsComposite_equivalent 367).mp h

/-- p = 461 is a prime where p - k! is composite for all k with 1 ≤ k! < p.
Factorials less than 461: 1, 2, 6, 24, 120.
461 - 1 = 460 = 4 × 5 × 23
461 - 2 = 459 = 3³ × 17
461 - 6 = 455 = 5 × 7 × 13
461 - 24 = 437 = 19 × 23
461 - 120 = 341 = 11 × 31
-/
theorem allFactorialSubtractionsComposite_461 : AllFactorialSubtractionsComposite 461 := by
  have h : DecidableAllFactorialSubtractionsComposite 461 := by
    norm_num [DecidableAllFactorialSubtractionsComposite, decidableFactorialsLessThanN]
    decide +kernel
  exact (allFactorialSubtractionsComposite_equivalent 461).mp h

/-- p = 557 is a prime where p - k! is composite for all k with 1 ≤ k! < p.
Factorials less than 557: 1, 2, 6, 24, 120.
557 - 1 = 556 = 4 × 139
557 - 2 = 555 = 3 × 5 × 37
557 - 6 = 551 = 19 × 29
557 - 24 = 533 = 13 × 41
557 - 120 = 437 = 19 × 23
-/
theorem allFactorialSubtractionsComposite_557 : AllFactorialSubtractionsComposite 557 := by
  have h : DecidableAllFactorialSubtractionsComposite 557 := by
    norm_num [DecidableAllFactorialSubtractionsComposite, decidableFactorialsLessThanN]
    decide +kernel
  exact (allFactorialSubtractionsComposite_equivalent 557).mp h

end Erdos1059
