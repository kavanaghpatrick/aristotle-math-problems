import Mathlib

open scoped BigOperators Nat
open Finset Nat

set_option maxHeartbeats 800000

/-!
# Erdős Problem 1052: Finitely Many Unitary Perfect Numbers

A unitary perfect number n satisfies σ*(n) = 2n where
σ*(n) = ∑_{d|n, gcd(d, n/d) = 1} d.

Only five are known: 6, 60, 90, 87360, 146361946186458562560000.

This is an **open problem** since the 1960s.
-/

/-- The answer marker: `answer p` is definitionally equal to `p`. -/
@[reducible] def answer (p : Prop) : Prop := p

/-- The set of unitary divisors of n: divisors d of n such that gcd(d, n/d) = 1. -/
def Nat.unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- The unitary divisor sum σ*(n) = ∑_{d|n, gcd(d, n/d) = 1} d. -/
def unitarySigma (n : ℕ) : ℕ :=
  (n.unitaryDivisors).sum id

/-- A natural number n is unitary perfect if σ*(n) = 2n. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  n ≥ 1 ∧ unitarySigma n = 2 * n

/-! ## Verification of known examples -/

example : unitarySigma 6 = 12 := by native_decide
example : unitarySigma 60 = 120 := by native_decide
example : unitarySigma 90 = 180 := by native_decide
example : unitarySigma 87360 = 174720 := by native_decide

example : IsUnitaryPerfect 6 := by unfold IsUnitaryPerfect; constructor <;> native_decide
example : IsUnitaryPerfect 60 := by unfold IsUnitaryPerfect; constructor <;> native_decide
example : IsUnitaryPerfect 90 := by unfold IsUnitaryPerfect; constructor <;> native_decide
example : IsUnitaryPerfect 87360 := by unfold IsUnitaryPerfect; constructor <;> native_decide

/-! ## Basic properties of unitary divisors -/

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ n.unitaryDivisors ↔ d ∣ n ∧ Nat.Coprime d (n / d) ∧ n ≠ 0 := by
  simp [Nat.unitaryDivisors, Finset.mem_filter, Nat.mem_divisors]
  tauto

lemma one_mem_unitaryDivisors {n : ℕ} (hn : n ≥ 1) :
    1 ∈ n.unitaryDivisors := by
  rw [mem_unitaryDivisors]
  refine ⟨one_dvd n, ?_, by omega⟩
  simp [Nat.Coprime]

lemma self_mem_unitaryDivisors {n : ℕ} (hn : n ≥ 1) :
    n ∈ n.unitaryDivisors := by
  rw [mem_unitaryDivisors]
  refine ⟨dvd_refl n, ?_, by omega⟩
  simp [Nat.div_self (by omega : 0 < n), Nat.Coprime]

/-- Every unitary perfect number is at least 2. -/
lemma IsUnitaryPerfect.two_le {n : ℕ} (h : IsUnitaryPerfect n) : n ≥ 2 := by
  obtain ⟨h1, h2⟩ := h
  by_contra hlt
  push_neg at hlt
  interval_cases n
  · revert h2; native_decide

/-- σ*(n) ≥ n + 1 for n ≥ 2. -/
lemma unitarySigma_ge_one_plus_self {n : ℕ} (hn : n ≥ 2) :
    unitarySigma n ≥ n + 1 := by
  have h_subset : ({1, n} : Finset ℕ) ⊆ n.unitaryDivisors := by
    grind +suggestions;
  exact le_trans (by rw [Finset.sum_pair (by linarith)]; simp +arith +decide)
    (Finset.sum_le_sum_of_subset h_subset)

/-! ## σ* for prime powers -/

/-
σ*(p^a) = 1 + p^a for p prime and a ≥ 1.
-/
lemma unitarySigma_prime_pow {p a : ℕ} (hp : Nat.Prime p) (ha : a ≥ 1) :
    unitarySigma (p ^ a) = 1 + p ^ a := by
  unfold unitarySigma;
  rw [ Finset.sum_eq_add ( 1 : ℕ ) ( p ^ a : ℕ ) ] <;> norm_num;
  · linarith [ Nat.Prime.one_lt hp, Nat.pow_le_pow_right hp.one_lt.le ha ];
  · simp +decide [ Nat.unitaryDivisors, hp.ne_zero, hp.ne_one, Nat.divisors_prime_pow hp ];
    intro k hk₁ hk₂ hk; contrapose! hk₂; simp_all +decide [ Nat.Coprime, Nat.gcd_comm ] ;
    rw [ show p ^ a / p ^ k = p ^ ( a - k ) by rw [ Nat.div_eq_of_eq_mul_left ( pow_pos hp.pos _ ) ] ; rw [ ← pow_add, Nat.sub_add_cancel hk₁ ] ] ; exact fun h => hp.not_dvd_one <| h ▸ Nat.dvd_gcd ( dvd_pow_self _ hk ) ( dvd_pow_self _ <| Nat.sub_ne_zero_of_lt <| lt_of_le_of_ne hk₁ hk₂ );
  · exact one_mem_unitaryDivisors ( Nat.one_le_pow _ _ hp.pos );
  · exact fun h => False.elim <| h <| self_mem_unitaryDivisors <| pow_pos hp.pos _

/-! ## Multiplicativity of σ* -/

/-
σ* is multiplicative: if gcd(m, n) = 1 then σ*(mn) = σ*(m) · σ*(n).
-/
lemma unitarySigma_mul_coprime {m n : ℕ} (hm : m ≥ 1) (hn : n ≥ 1)
    (hcop : Nat.Coprime m n) :
    unitarySigma (m * n) = unitarySigma m * unitarySigma n := by
  -- By definition of unitary divisors, we know that every unitary divisor of $mn$ can be written as $d_1d_2$ where $d_1$ is a unitary divisor of $m$ and $d_2$ is a unitary divisor of $n$.
  have h_unitary_divisors : (Nat.unitaryDivisors (m * n)) = Finset.image (fun (d : ℕ × ℕ) => d.1 * d.2) (Nat.unitaryDivisors m ×ˢ Nat.unitaryDivisors n) := by
    ext d;
    constructor;
    · simp +decide [ Nat.unitaryDivisors ];
      intro hd hm hn hcop
      obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b, a ∣ m ∧ b ∣ n ∧ d = a * b := by
        exact Exists.imp ( by aesop ) ( Nat.dvd_mul.mp hd );
      refine' ⟨ a, b, _, _ ⟩ <;> simp_all +decide [ Nat.mul_div_mul_comm ];
      exact ⟨ Nat.Coprime.coprime_dvd_left ( dvd_mul_right _ _ ) <| Nat.Coprime.coprime_dvd_right ( dvd_mul_right _ _ ) hcop, Nat.Coprime.coprime_dvd_left ( dvd_mul_left _ _ ) <| Nat.Coprime.coprime_dvd_right ( dvd_mul_left _ _ ) hcop ⟩;
    · simp +contextual [ Nat.unitaryDivisors ];
      rintro x y hx hm hx' hy hn hy' rfl;
      refine' ⟨ mul_dvd_mul hx hy, _ ⟩;
      rw [ Nat.mul_div_mul_comm hx hy ];
      apply_rules [ Nat.Coprime.mul_left, Nat.Coprime.symm ];
      · exact Nat.Coprime.coprime_dvd_left hx <| Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd hy ) hcop;
      · refine' Nat.Coprime.mul_right _ _;
        · exact Nat.Coprime.coprime_dvd_left hy <| Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd hx ) hcop.symm;
        · assumption;
  simp_all +decide [ unitarySigma ];
  rw [ Finset.sum_image ];
  · erw [ Finset.sum_product, Finset.sum_mul_sum ];
  · intros x hx y hy; simp_all +decide [ Set.InjOn ];
    intro hxy
    have h1 : x.1 = y.1 := by
      exact Nat.dvd_antisymm ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( x.1 ) ( y.2 ) from Nat.Coprime.coprime_dvd_left ( Nat.dvd_of_mem_divisors <| Finset.filter_subset _ _ hx.1 ) <| Nat.Coprime.coprime_dvd_right ( Nat.dvd_of_mem_divisors <| Finset.filter_subset _ _ hy.2 ) hcop ) <| hxy.symm ▸ dvd_mul_right _ _ ) ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( y.1 ) ( x.2 ) from Nat.Coprime.coprime_dvd_left ( Nat.dvd_of_mem_divisors <| Finset.filter_subset _ _ hy.1 ) <| Nat.Coprime.coprime_dvd_right ( Nat.dvd_of_mem_divisors <| Finset.filter_subset _ _ hx.2 ) hcop ) <| hxy.symm ▸ dvd_mul_right _ _ )
    have h2 : x.2 = y.2 := by
      nlinarith [ Nat.pos_of_mem_divisors ( Finset.mem_filter.mp hx.1 |>.1 ), Nat.pos_of_mem_divisors ( Finset.mem_filter.mp hy.1 |>.1 ) ]
    exact Prod.ext h1 h2

/-! ## Evenness of unitary perfect numbers -/

/-
If n is odd and unitary perfect, then n has at least 2 odd prime factors,
    so 4 | σ*(n) = 2n, contradicting v₂(2n) = 1.
    More precisely: n = ∏ pᵢ^aᵢ with pᵢ odd primes, so
    σ*(n) = ∏(1 + pᵢ^aᵢ) and each factor is even.
-/
theorem IsUnitaryPerfect.even {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  -- By contradiction, assume n is � odd�.
  by_contra h_odd;
  -- Since n is odd, we � can� write n as a product of its prime factors.
  have h_prime_factors : n = ∏ p ∈ Nat.primeFactors n, p ^ (Nat.factorization n p) := by
    exact Eq.symm ( Nat.factorization_prod_pow_eq_self ( by rintro rfl; exact absurd h.1 ( by decide ) ) );
  -- Since n is odd, each factor 1 + p^a� ∢� is even. If n has k ≥ 2 odd prime factors, then 4 | σ*(n) = 2n. But n � is� odd, so v₂(2n) = 1, contradicting 4 | 2n.
  have h_even_factors : (∏ p ∈ Nat.primeFactors n, (1 + p ^ (Nat.factorization n p))) = 2 * n := by
    have h_even_factors : unitarySigma n = ∏ p ∈ Nat.primeFactors n, unitarySigma (p ^ (Nat.factorization n p)) := by
      have h_unitarySigma_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → unitarySigma (∏ p ∈ S, p ^ (Nat.factorization n p)) = ∏ p ∈ S, unitarySigma (p ^ (Nat.factorization n p)) := by
        intros S hS_prime
        induction' S using Finset.induction with p S hpS ih;
        · simp +decide [ unitarySigma ];
        · rw [ Finset.prod_insert hpS, unitarySigma_mul_coprime ];
          · rw [ Finset.prod_insert hpS, ih fun q hq => hS_prime q <| Finset.mem_insert_of_mem hq ];
          · exact Nat.one_le_pow _ _ ( Nat.Prime.pos ( hS_prime p ( Finset.mem_insert_self _ _ ) ) );
          · exact Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos ( hS_prime q ( Finset.mem_insert_of_mem hq ) ) ) _;
          · exact Nat.Coprime.prod_right fun q hq => Nat.coprime_pow_primes _ _ ( hS_prime p ( Finset.mem_insert_self p S ) ) ( hS_prime q ( Finset.mem_insert_of_mem hq ) ) ( by rintro rfl; exact hpS hq );
      rw [ ← h_unitarySigma_prod fun p hp => Nat.prime_of_mem_primeFactors hp, ← h_prime_factors ];
    convert h.2 using 1;
    convert h_even_factors.symm using 2;
    rw [ unitarySigma_prime_pow ( Nat.prime_of_mem_primeFactors ‹_› ) ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ‹_› ) ) ];
  -- Each factor 1 + p^a is even, so 2 �^�k | σ*(n) = 2n. Since n is odd, 2^k | 2, so k ≤ 1.
  have h_k_le_one : (Nat.primeFactors n).card ≤ 1 := by
    have h_k_le_one : 2 ^ (Nat.primeFactors n).card ∣ 2 * n := by
      rw [ ← h_even_factors, ← Finset.prod_const ];
      refine' Finset.prod_dvd_prod_of_dvd _ _ fun p hp => _;
      norm_num [ ← even_iff_two_dvd, parity_simps ];
      exact fun h => False.elim <| h_odd <| even_iff_two_dvd.mpr <| dvd_trans ( even_iff_two_dvd.mp h ) <| Nat.dvd_of_mem_primeFactors hp;
    contrapose! h_k_le_one;
    rw [ Nat.Prime.pow_dvd_iff_le_factorization ] <;> norm_num;
    · rw [ Nat.factorization_mul ] <;> norm_num;
      · rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> norm_num [ Nat.even_iff ] at * ; linarith;
        exact h_odd;
      · rintro rfl; contradiction;
    · rintro rfl; contradiction;
  interval_cases _ : Finset.card n.primeFactors;
  · rcases n with ( _ | _ | n ) <;> simp +decide at *;
  · rw [ Finset.card_eq_one ] at *;
    grind +suggestions

/-! ## No prime power is unitary perfect (Wall's theorem, k=1 case) -/

/-
No prime power is unitary perfect.
-/
theorem not_isUnitaryPerfect_prime_pow {p a : ℕ} (hp : Nat.Prime p) (ha : a ≥ 1) :
    ¬IsUnitaryPerfect (p ^ a) := by
  intro h
  have h_sum : 1 + p ^ a = 2 * p ^ a := by
    rw [ ← unitarySigma_prime_pow hp ha, h.2 ];
  linarith [ pow_lt_pow_right₀ hp.one_lt ha ]

/-
For n with exactly 2 prime factors, the only unitary perfect number is 6.
    This follows from the identity (p^a - 1)(q^b - 1) = 2.
-/
theorem wall_k2 {n : ℕ} (hn : IsUnitaryPerfect n) (hk : n.primeFactors.card = 2) :
    n = 6 := by
  -- Since n has exactly � �2 prime factors, write n = p^a * q^b with p, q distinct primes and a, b ≥ 1.
  obtain ⟨p, a, q, b, hp, hq, ha, hb, hn_eq⟩ : ∃ p a q b : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ a ≥ 1 ∧ b ≥ 1 ∧ n = p^a * q^b := by
    obtain ⟨p, q, hpq⟩ : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ n.primeFactors = {p, q} := by
      -- Since the cardinality of n.primeFactors is 2, we can extract two distinct primes p and q such that n.primeFactors = {p, q}.
      obtain ⟨p, q, hpq⟩ : ∃ p q : ℕ, p ∈ n.primeFactors ∧ q ∈ n.primeFactors ∧ p ≠ q ∧ n.primeFactors = {p, q} := by
        rw [ Finset.card_eq_two ] at hk; obtain ⟨ p, q, hpq ⟩ := hk; use p, q; aesop;
      grind;
    exact ⟨ p, Nat.factorization n p, q, Nat.factorization n q, hpq.1, hpq.2.1, hpq.2.2.1, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp <| by aesop ), Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp <| by aesop ), by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self ( show n ≠ 0 by rintro rfl; exact absurd hn.1 ( by norm_num ) ) ] ; rw [ Finsupp.prod ] ; aesop ⟩;
  -- By unitarySigma_eq_prod_one_add_pow, σ*(n) = (1 + p^a)(1 + q^b). Since n is unitary perfect, (1 + p^a)(1 + q^b) = 2 * p^a * q^b.
  have h_sigma : (1 + p^a) * (1 + q^b) = 2 * p^a * q^b := by
    have h_sigma : unitarySigma n = (1 + p^a) * (1 + q^b) := by
      rw [ hn_eq.2, unitarySigma_mul_coprime ];
      · rw [ unitarySigma_prime_pow hp hb, unitarySigma_prime_pow hq hn_eq.1 ];
      · exact Nat.one_le_pow _ _ hp.pos;
      · exact Nat.one_le_pow _ _ hq.pos;
      · exact Nat.coprime_pow_primes _ _ hp hq ha;
    linarith [ hn.2 ];
  -- This means p^a * q^b - p^a - q^b + 1 = 2, i.e. (p^a - 1)(q^b - 1) = 2.
  have h_fact : (p^a - 1) * (q^b - 1) = 2 := by
    nlinarith only [ Nat.sub_add_cancel ( Nat.one_le_pow a p hp.pos ), Nat.sub_add_cancel ( Nat.one_le_pow b q hq.pos ), h_sigma ];
  rcases x : p ^ a - 1 with ( _ | _ | x ) <;> rcases y : q ^ b - 1 with ( _ | _ | y ) <;> simp_all +decide;
  grind

/-! ## The product formula for σ* -/

/-
σ*(n) = ∏_{p ∈ primeFactors n} (1 + p^{v_p(n)}).
-/
theorem unitarySigma_eq_prod_one_add_pow (n : ℕ) (hn : n ≥ 1) :
    unitarySigma n = ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  have h_eq : ∀ p ∈ n.primeFactors, unitarySigma (p ^ (Nat.factorization n p)) = 1 + p ^ (Nat.factorization n p) := by
    intro p hp; exact unitarySigma_prime_pow ( Nat.prime_of_mem_primeFactors hp ) ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) ;
  -- By induction on the number of prime (� factors� of $n$, we can show that the product of the unitary divisor sums of the � prime� power factors of $n$ equals the unitary divisor sum of $n$.
  have h_ind : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → (∏ p ∈ S, unitarySigma (p ^ (Nat.factorization n p))) = unitarySigma (∏ p ∈ S, p ^ (Nat.factorization n p)) := by
    intros S hS; induction S using Finset.induction <;> simp_all +decide ;
    rw [ unitarySigma_mul_coprime ];
    · exact Nat.one_le_pow _ _ hS.1.pos;
    · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( hS.2 p hp ) ) _;
    · exact Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.left.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.left ( hS.right p hp ) ; aesop;
  rw [ ← Finset.prod_congr rfl h_eq, h_ind fun p hp => Nat.prime_of_mem_primeFactors hp ];
  exact congr_arg _ ( Eq.symm <| Nat.factorization_prod_pow_eq_self <| by positivity )

/-! ## Main conjecture -/

/-- **Erdős Problem 1052** (Open Conjecture):
There are only finitely many unitary perfect numbers.

This is an open problem since the 1960s. The conjecture is widely believed to be true.
Only five unitary perfect numbers are known: 6, 60, 90, 87360, and
146361946186458562560000.

**Status**: This remains open. The `sorry` below reflects the fact that this
is an unsolved mathematical problem.
-/
theorem erdos_1052 :
    answer True ↔ {n | IsUnitaryPerfect n}.Finite := by
  simp only [answer]
  constructor
  · intro _
    -- This is the open conjecture: {n | IsUnitaryPerfect n} is finite.
    -- The proof would require deep results:
    -- 1. Bilu-Hanrot-Voutier primitive divisor theorem
    -- 2. Wall's 1972 theorem (finiteness for fixed number of prime factors)
    -- 3. A support-closure argument bounding the number of prime factors
    sorry
  · intro _; trivial

/-! ## Axiom checks for proved theorems -/
#print axioms IsUnitaryPerfect.even
#print axioms unitarySigma_prime_pow
#print axioms unitarySigma_mul_coprime
#print axioms unitarySigma_eq_prod_one_add_pow
#print axioms not_isUnitaryPerfect_prime_pow
#print axioms wall_k2