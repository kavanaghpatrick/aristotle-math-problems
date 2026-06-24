/-
Structural proof of the Feit-Thompson prime conjecture for the family
of primes q ≡ 71 (mod 72) with q ≤ 1000.

The proof uses Fermat's little theorem to reduce modular exponentiation:
for each prime q in the family, we find a small prime factor p of A(q) = q²+q+1,
then show 3^q ≢ 1 (mod p) by reducing 3^q mod p via 3^(p-1) ≡ 1 (mod p).

This is a structural argument — no native_decide on 3^q for q > 100.
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 1000

/-! ## Enumeration of primes in the family -/

/-
The primes q ≤ 1000 with q > 3 and q ≡ 71 (mod 72) are exactly
    {71, 359, 431, 503, 647, 719, 863}.
-/
lemma primes_71_mod_72_le_1000 (q : ℕ) (hq : q.Prime) (hq3 : 3 < q)
    (hmod : q ≡ 71 [MOD 72]) (hle : q ≤ 1000) :
    q = 71 ∨ q = 359 ∨ q = 431 ∨ q = 503 ∨ q = 647 ∨ q = 719 ∨ q = 863 := by
  interval_cases q <;> norm_num at *

/-! ## Key structural lemmas -/

/-
If p is a prime > 3, p ∣ (q²+q+1), q ≥ 2, q is odd,
    and 3^(q % (p-1)) ≢ 1 [MOD p],
    then ¬ (q³-1)/(q-1) ∣ (3^q-1)/2.

    Proof sketch: (q³-1)/(q-1) = q²+q+1 (since q ≥ 2).
    q²+q+1 is odd (since q is odd). 3^q-1 is even. So if (q²+q+1) ∣ (3^q-1)/2,
    then (q²+q+1) ∣ (3^q-1). Since p ∣ (q²+q+1), we get p ∣ (3^q-1),
    i.e. 3^q ≡ 1 [MOD p]. By Fermat's little theorem, 3^(p-1) ≡ 1 [MOD p],
    so 3^q ≡ 3^(q%(p-1)) [MOD p]. This gives 3^(q%(p-1)) ≡ 1 [MOD p],
    contradicting the hypothesis.
-/
lemma not_dvd_via_fermat_factor (q p : ℕ) (hq : q ≥ 2) (hq_odd : q % 2 = 1)
    (hp : p.Prime) (hp3 : p > 3) (hpA : p ∣ (q ^ 2 + q + 1))
    (hres : ¬ 3 ^ (q % (p - 1)) ≡ 1 [MOD p]) :
    ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 := by
  -- By Fermat's little theorem, since p is prime and p > 3, we have 3^(p-1) ≡ 1 [MOD p].
  have h_fermat : 3^(p-1) ≡ 1 [MOD p] := by
    exact Nat.totient_prime hp ▸ Nat.ModEq.pow_totient ( Nat.coprime_comm.mp <| hp.coprime_iff_not_dvd.mpr fun h => by have := Nat.le_of_dvd ( by linarith ) h; interval_cases p );
  -- By assumption, $p \mid (q^3 - 1)/(q - 1)$, so $p \mid (3^q - 1)/2$.
  by_contra h_contra
  have hp_div : p ∣ (3^q - 1) / 2 := by
    refine dvd_trans ?_ h_contra;
    convert hpA using 1;
    exact Nat.div_eq_of_eq_mul_left ( Nat.sub_pos_of_lt hq ) ( Nat.sub_eq_of_eq_add <| by cases q <;> norm_num at * ; linarith );
  -- Since $p \mid (3^q - 1)/2$, we have $3^q \equiv 1 \pmod{p}$.
  have h_mod : 3^q ≡ 1 [MOD p] := by
    refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_;
    simpa [ hp.pos ] using Int.natCast_dvd_natCast.mpr ( hp_div.trans ( Nat.div_dvd_of_dvd ( show 2 ∣ 3 ^ q - 1 from even_iff_two_dvd.mp ( by simp +decide [ Nat.one_le_iff_ne_zero, parity_simps ] ) ) ) );
  rw [ ← Nat.mod_add_div q ( p - 1 ) ] at *; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, pow_add, pow_mul ] ;

/-! ## Main theorem -/

theorem feit_thompson_p3_q71_family :
    ∀ q : ℕ, q.Prime → 3 < q → q ≡ 71 [MOD 72] → q ≤ 1000 →
      ¬ (q ^ 3 - 1) / (q - 1) ∣ (3 ^ q - 1) / 2 := by
  intro q hprime hgt3 hmod hle
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :=
    primes_71_mod_72_le_1000 q hprime hgt3 hmod hle
  · -- q = 71: direct computation (q ≤ 100, native_decide allowed)
    native_decide
  · -- q = 359: p = 7 | A(359) = 129241, 359 % 6 = 5, 3^5 % 7 = 5 ≠ 1
    exact not_dvd_via_fermat_factor 359 7 (by omega) (by omega)
      (by decide) (by omega) (by native_decide) (by native_decide)
  · -- q = 431: p = 7 | A(431) = 186193, 431 % 6 = 5, 3^5 % 7 = 5 ≠ 1
    exact not_dvd_via_fermat_factor 431 7 (by omega) (by omega)
      (by decide) (by omega) (by native_decide) (by native_decide)
  · -- q = 503: p = 13 | A(503) = 253513, 503 % 12 = 11, 3^11 % 13 = 9 ≠ 1
    exact not_dvd_via_fermat_factor 503 13 (by omega) (by omega)
      (by decide) (by omega) (by native_decide) (by native_decide)
  · -- q = 647: p = 211 | A(647) = 419257, 647 % 210 = 17, 3^17 % 211 ≠ 1
    exact not_dvd_via_fermat_factor 647 211 (by omega) (by omega)
      (by native_decide) (by omega) (by native_decide) (by native_decide)
  · -- q = 719: p = 487 | A(719) = 517681, 719 % 486 = 233, 3^233 % 487 ≠ 1
    exact not_dvd_via_fermat_factor 719 487 (by omega) (by omega)
      (by native_decide) (by omega) (by native_decide) (by native_decide)
  · -- q = 863: p = 7 | A(863) = 745633, 863 % 6 = 5, 3^5 % 7 = 5 ≠ 1
    exact not_dvd_via_fermat_factor 863 7 (by omega) (by omega)
      (by decide) (by omega) (by native_decide) (by native_decide)