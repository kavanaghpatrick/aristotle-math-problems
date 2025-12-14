/-
Erdős Problem #418 - Integers not of the form n - φ(n)
SOLVED by Browkin-Schinzel (1995)

BORIS PATTERN MATCH:
- Pre-formalized in FC: ✅
- SOLVED: ✅ (4 solved variants!)
- HAS COMPLETE PROOF: ✅ (conditional variant is PROVEN in FC!)
- No asymptotics: ✅

PROBLEM: Are there infinitely many integers not of the form n - φ(n)?

ANSWER: YES - Browkin-Schinzel proved 2^(k+1) × 509203 is never n - φ(n).
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped ArithmeticFunction

namespace Erdos418

/--
Main theorem: There are infinitely many integers not of the form n - φ(n).
SOLVED by Browkin-Schinzel (1995).
-/
theorem erdos_418 : { (n - n.totient : ℕ) | n }ᶜ.Infinite := by
  sorry

/--
The Browkin-Schinzel construction: Any integer of the form 2^(k+1) × 509203
is NOT of the form n - φ(n).
-/
theorem erdos_418_browkin_schinzel :
    { 2 ^ (k + 1) * 509203 | k : ℕ } ⊆ { (n - n.totient : ℕ) | n }ᶜ := by
  sorry

/--
Conditional result: Assuming a slight strengthening of Goldbach's conjecture
(every even n > 6 is sum of two DISTINCT primes), every odd number can be
written as n - φ(n).

THIS HAS A COMPLETE PROOF IN FC!
-/
theorem erdos_418_conditional
    (goldbach : ∀ (n : ℕ), 6 < n → Even n → ∃ p q, p ≠ q ∧ p.Prime ∧ q.Prime ∧ n = p + q)
    (m : ℕ) (h : Odd m) :
    ∃ n, m + n.totient = n := by
  -- Small cases
  obtain rfl | rfl | rfl | h7m : m = 1 ∨ m = 3 ∨ m = 5 ∨ 7 ≤ m := by
    obtain ⟨m, rfl⟩ := h
    omega
  · exact ⟨2, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨25, rfl⟩
  -- General case using Goldbach
  obtain ⟨p, q, hpq, hp, hq, hm⟩ := goldbach (m + 1) (by omega) (by simpa [Nat.even_add_one] using h)
  use p * q
  have h2p : 2 ≤ p := hp.two_le
  have h2q : 2 ≤ q := hq.two_le
  rw [Nat.totient_mul (Nat.coprime_primes hp hq |>.mpr hpq),
      Nat.totient_prime hp, Nat.totient_prime hq]
  omega

/--
Erdős showed that a positive density set of integers cannot be written as
σ(n) - n (sum of divisors minus n).
-/
theorem erdos_418_sigma :
    ∃ (S : Set ℕ), S.ncard = ⊤ ∧
      S ⊆ { (Nat.divisors n |>.sum id - n : ℕ) | n }ᶜ := by
  sorry

end Erdos418
