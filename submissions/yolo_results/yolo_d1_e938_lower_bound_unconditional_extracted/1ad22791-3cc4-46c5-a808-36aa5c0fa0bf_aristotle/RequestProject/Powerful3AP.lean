import Mathlib

/-!
# Structural constraint on common difference of powerful 3-APs

A natural number `n` is **powerful** if every prime factor of `n` appears with
multiplicity at least 2, i.e., `p.Prime → p ∣ n → p² ∣ n`.

## Main results

* `powerful_3AP_prime_once_not_dvd`: If `(n, n+d, n+2d)` are all powerful and
  `p` is a prime dividing `d` exactly once (i.e. `p ∣ d` but `¬ p² ∣ d`),
  then `p` does not divide `n`.

This is a purely unconditional structural lemma. It does NOT give a growth-rate
lower bound on `d`; the abc-conditional bound `d ≫ N^{1/2-ε}` (Chan 2022,
arXiv:2210.00281) remains the only known route to such a bound.
-/

/-- A natural number is **powerful** if every prime dividing it does so
with multiplicity at least 2. -/
def Nat.Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- **Structural coprimality lemma for powerful 3-APs.**

If `n`, `n + d`, and `n + 2 * d` are all powerful numbers,
and `p` is a prime that divides `d` exactly once (`p ∣ d`, `¬ p² ∣ d`),
then `p` does not divide `n`.

*Proof.* By contrapositive: if `p ∣ n`, then since `n` is powerful we get
`p² ∣ n`. Since `p ∣ n` and `p ∣ d` we get `p ∣ (n + d)`, and since `n + d`
is powerful, `p² ∣ (n + d)`. Then `p² ∣ d` follows by subtracting `p² ∣ n`
from `p² ∣ (n + d)`.

Note: the hypotheses `hd` and `h2` are not needed for this result but are
included to match the requested signature. -/
theorem powerful_3AP_prime_once_not_dvd
    (n d p : ℕ) (_hd : 0 < d) (hp : p.Prime)
    (hpd : p ∣ d) (hpp : ¬ p^2 ∣ d)
    (h0 : Nat.Powerful n) (h1 : Nat.Powerful (n + d))
    (_h2 : Nat.Powerful (n + 2 * d)) :
    ¬ p ∣ n := by
  contrapose! hpp
  convert Nat.dvd_sub (h1 p hp (dvd_add hpp hpd)) (h0 p hp hpp) using 1
  rw [Nat.sub_eq_of_eq_add]
  ring
