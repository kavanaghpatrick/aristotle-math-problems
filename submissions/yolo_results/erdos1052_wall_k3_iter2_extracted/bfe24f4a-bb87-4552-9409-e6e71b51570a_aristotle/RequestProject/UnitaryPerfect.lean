import Mathlib

set_option maxHeartbeats 1600000

open scoped BigOperators Pointwise

/-! # Unitary Perfect Numbers with Exactly 3 Prime Factors

We prove that the only unitary perfect numbers with exactly 3 prime factors are 60 and 90.
A unitary perfect number n satisfies σ*(n) = 2n where σ*(n) = ∑_{d|n, gcd(d, n/d) = 1} d.
-/

/-- The unitary sigma function: sum of unitary divisors of n. -/
def unitarySigma (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => Nat.Coprime d (n / d))).sum id

/-- A number n is unitary perfect if n ≥ 1 and σ*(n) = 2n. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  n ≥ 1 ∧ unitarySigma n = 2 * n

instance : DecidablePred IsUnitaryPerfect := fun _ => instDecidableAnd

/-! ## Product formula for unitarySigma -/

/-- σ* is multiplicative: σ*(ab) = σ*(a)σ*(b) when gcd(a,b) = 1. -/
lemma unitarySigma_mul_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    unitarySigma (a * b) = unitarySigma a * unitarySigma b := by
  unfold unitarySigma
  have h_divisors : (a * b).divisors.filter (fun d => Nat.Coprime d (a * b / d)) =
      Finset.image (fun (p : ℕ × ℕ) => p.1 * p.2)
        (Finset.filter (fun d => Nat.Coprime d (a / d)) a.divisors ×ˢ
         Finset.filter (fun d => Nat.Coprime d (b / d)) b.divisors) := by
    ext d
    constructor
    · intro hd
      obtain ⟨d1, d2, hd1, hd2, hd_eq⟩ : ∃ d1 d2, d1 ∣ a ∧ d2 ∣ b ∧ d = d1 * d2 := by
        simp +zetaDelta at *
        exact Exists.imp (by aesop) (Nat.dvd_mul.mp hd.1.1)
      simp_all +decide [Nat.mul_div_mul_comm]
      simp_all +decide [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
      grobner
    · simp +zetaDelta at *
      rintro x y hx ha hx' hy hb hy' rfl
      refine' ⟨⟨mul_dvd_mul hx hy, ha, hb⟩, _⟩
      simp_all +decide [Nat.mul_div_mul_comm, Nat.Coprime, Nat.gcd_mul_left, Nat.gcd_mul_right]
      apply_rules [Nat.Coprime.mul_left, Nat.Coprime.symm]
      · exact Nat.Coprime.coprime_dvd_left hx <|
          Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hy) h
      · refine' Nat.Coprime.mul_right _ _
        · exact Nat.Coprime.coprime_dvd_left hy <|
            Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hx) <| Nat.Coprime.symm h
        · assumption
  erw [h_divisors, Finset.sum_image, Finset.sum_product]
  · simp +decide [← Finset.mul_sum _ _ _, ← Finset.sum_mul]
  · intros x hx y hy
    simp_all +decide [Nat.divisors_mul]
    intro h_eq
    have hx1_eq_y1 : x.1 = y.1 := by
      exact Nat.dvd_antisymm
        (Nat.Coprime.dvd_of_dvd_mul_right
          (show Nat.Coprime (x.1) (y.2) from
            Nat.Coprime.coprime_dvd_left (by tauto) <|
              Nat.Coprime.coprime_dvd_right (by tauto) h) <|
          h_eq.symm ▸ dvd_mul_right _ _)
        (Nat.Coprime.dvd_of_dvd_mul_right
          (show Nat.Coprime (y.1) (x.2) from
            Nat.Coprime.coprime_dvd_left (by tauto) <|
              Nat.Coprime.coprime_dvd_right (by tauto) h) <|
          h_eq.symm ▸ dvd_mul_right _ _)
    aesop

/-- σ*(p^k) = 1 + p^k for prime p and k ≥ 1. -/
lemma unitarySigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≥ 1) :
    unitarySigma (p ^ k) = 1 + p ^ k := by
  convert Finset.sum_filter ?_ ?_ using 1
  rw [Finset.sum_eq_add (p ^ k) 1] <;> norm_num
  · rw [Nat.div_self (pow_pos hp.pos _), if_pos (by norm_num), add_comm]
  · aesop
  · intro c hc h₁ h₂ h h
    rw [Nat.dvd_prime_pow hp] at hc
    rcases hc with ⟨d, hd, rfl⟩
    simp_all +decide [Nat.coprime_pow_primes]
    exact absurd h (by
      rw [show p ^ k / p ^ d = p ^ (k - d) by
        rw [Nat.div_eq_of_eq_mul_left (pow_pos hp.pos _)]
        rw [← pow_add, Nat.sub_add_cancel hd]]
      exact fun h => absurd
        (h.gcd_eq_one ▸ Nat.dvd_gcd (dvd_pow_self _ (by aesop))
          (dvd_pow_self _ (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hd (by aesop)))))
        (by aesop))
  · aesop
  · aesop

/-! ## Coprimality of distinct prime powers -/

/-- Powers of distinct primes are coprime. -/
lemma coprime_prime_pow_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (a b : ℕ) : Nat.Coprime (p ^ a) (q ^ b) :=
  (hp.coprime_iff_not_dvd.mpr fun h =>
    hpq (hq.eq_one_or_self_of_dvd _ h |>.resolve_left hp.one_lt.ne')).pow _ _

/-! ## Decomposition of n with 3 prime factors -/

/-
If n has exactly 3 prime factors, then n = p^a * q^b * r^c for distinct primes p,q,r
    with exponents a,b,c ≥ 1.
-/
lemma three_primeFactors_decomp {n : ℕ} (hn : n ≠ 0) (hk : n.primeFactors.card = 3) :
    ∃ p q r : ℕ, ∃ a b c : ℕ,
      p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1 ∧
      n = p ^ a * (q ^ b * r ^ c) ∧
      n.primeFactors = {p, q, r} := by
        obtain ⟨ p, q, r, hp, hq, hr ⟩ := Finset.card_eq_three.mp hk;
        use p, q, r, n.factorization p, n.factorization q, n.factorization r; simp_all +decide [ Finsupp.prod ] ;
        exact ⟨ Nat.prime_of_mem_primeFactors ( hr.2.symm ▸ Finset.mem_insert_self _ _ ), Nat.prime_of_mem_primeFactors ( hr.2.symm ▸ Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ), Nat.prime_of_mem_primeFactors ( hr.2.symm ▸ Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ), Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self hn ] ; rw [ Finsupp.prod ] ; aesop ⟩

/-
Product formula for σ* of n with 3 prime factors.
-/
lemma unitarySigma_three_primes {n : ℕ} {p q r : ℕ} {a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1)
    (hn : n = p ^ a * (q ^ b * r ^ c)) :
    unitarySigma n = (1 + p ^ a) * ((1 + q ^ b) * (1 + r ^ c)) := by
      rw [hn];
      rw [ ← unitarySigma_prime_pow hp ha, ← unitarySigma_prime_pow hq hb, ← unitarySigma_prime_pow hr hc, ← unitarySigma_mul_coprime, ← unitarySigma_mul_coprime ];
      · apply_rules [ Nat.Coprime.mul_right, Nat.coprime_pow_primes ];
      · exact Nat.coprime_pow_primes _ _ hq hr hqr

/-! ## Diophantine bounds -/

/-- For x,y,z : ℕ with y ≥ 3, z ≥ 5, if (1+x)(1+y)(1+z) = 2xyz then x ≤ 4. -/
lemma dioph_bound_x {x y z : ℕ} (hy : y ≥ 3) (hz : z ≥ 5)
    (heq : (1 + x) * ((1 + y) * (1 + z)) = 2 * x * (y * z)) : x ≤ 4 := by
  have h1 : 3 * (1 + y) ≤ 4 * y := by omega
  have h2 : 5 * (1 + z) ≤ 6 * z := by omega
  have h3 : 15 * ((1 + y) * (1 + z)) ≤ 24 * (y * z) := by nlinarith
  have hyz : y * z > 0 := by positivity
  nlinarith

/-
For x,y,z : ℕ with x ≥ 2, z ≥ 5, if (1+x)(1+y)(1+z) = 2xyz then y ≤ 9.
-/
lemma dioph_bound_y {x y z : ℕ} (hx : x ≥ 2) (hz : z ≥ 5)
    (heq : (1 + x) * ((1 + y) * (1 + z)) = 2 * x * (y * z)) : y ≤ 9 := by
      nlinarith [ mul_le_mul_left' hx ( z + 1 ), mul_le_mul_left' hz ( x + 1 ) ]

/-
For x,y,z : ℕ with x ≥ 2, y ≥ 3, if (1+x)(1+y)(1+z) = 2xyz then z ≤ 29.
-/
lemma dioph_bound_z {x y z : ℕ} (hx : x ≥ 2) (hy : y ≥ 3)
    (heq : (1 + x) * ((1 + y) * (1 + z)) = 2 * x * (y * z)) : z ≤ 29 := by
      by_cases hz : z ≥ 30;
      · rcases y with ( _ | _ | _ | _ | y ) <;> rcases x with ( _ | _ | _ | _ | x ) <;> try norm_num at * <;> nlinarith;
        nlinarith only [ mul_pos ( Nat.succ_pos x ) ( Nat.succ_pos y ), heq, hz ];
      · linarith

/-! ## Evenness: 2 must be a prime factor -/

/-
If n has 3 prime factors all ≥ 3 (second ≥ 5, third ≥ 7), then σ*(n) < 2n.
    This is proved via the inequality 105·σ*(n) ≤ 192·n which contradicts σ*(n) = 2n.
-/
lemma odd_three_primes_not_unitary_perfect {n : ℕ} {p q r a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1)
    (hn : n = p ^ a * (q ^ b * r ^ c))
    (hp3 : p ≥ 3) (hq5 : q ≥ 5) (hr7 : r ≥ 7) :
    ¬IsUnitaryPerfect n := by
      -- By unitarySigma_three_primes, unitarySigma n = (1+p^a)*((1+q^b)*(1+r^c)).
      have h_unitarySigma : unitarySigma n = (1 + p ^ a) * ((1 + q ^ b) * (1 + r ^ c)) := by
        exact?;
      -- Now use the inequality: since p≥3, 3*(1+p^a) ≤ 4*p^a (i.e., 3 ≤ p^a, true since p≥3 and a≥1). Since q≥5, 5*(1+q^b) ≤ 6*q^b. Since r≥7, 7*(1+r^c) ≤ 8*r^c. Multiply all three: 105*(1+p^a)*((1+q^b)*(1+r^c)) ≤ 192*p^a*(q^b*r^c).
      have h_ineq : 105 * (1 + p ^ a) * ((1 + q ^ b) * (1 + r ^ c)) ≤ 192 * p ^ a * (q ^ b * r ^ c) := by
        -- Since $p \geq 3$, $q \geq 5$, and $r \geq 7$, we have $3 * (1 + p^a) \leq 4 * p^a$, $5 * (1 + q^b) \leq 6 * q^b$, and $7 * (1 + r^c) \leq 8 * r^c$.
        have h_ineq_parts : 3 * (1 + p ^ a) ≤ 4 * p ^ a ∧ 5 * (1 + q ^ b) ≤ 6 * q ^ b ∧ 7 * (1 + r ^ c) ≤ 8 * r ^ c := by
          exact ⟨ by linarith [ Nat.pow_le_pow_right hp.one_lt.le ha ], by linarith [ Nat.pow_le_pow_right hq.one_lt.le hb ], by linarith [ Nat.pow_le_pow_right hr.one_lt.le hc ] ⟩;
        convert Nat.mul_le_mul ( Nat.mul_le_mul h_ineq_parts.1 h_ineq_parts.2.1 ) h_ineq_parts.2.2 using 1 <;> ring;
      exact fun h => by linarith [ h.2, show p ^ a * ( q ^ b * r ^ c ) > 0 by positivity ] ;

/-! ## Main bound lemma -/

/-
Any unitary perfect n with exactly 3 prime factors satisfies n < 1100.
-/
lemma bound_unitary_perfect_three_primes {n : ℕ}
    (hn : IsUnitaryPerfect n) (hk : n.primeFactors.card = 3) : n < 1100 := by
      -- Since n has exactly 3 prime factors, we can write n as p^a * q^b * r^c where p, q, r are distinct primes and a, b, c are positive integers.
      obtain ⟨p, q, r, a, b, c, hp, hq, hr, hpa, hqbc, hrbc, hn_eq⟩ : ∃ p q r a b c : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1 ∧ n = p ^ a * (q ^ b * r ^ c) ∧ n.primeFactors = {p, q, r} ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r := by
        obtain ⟨ p, q, r, a, b, c, hp, hq, hr, hpq, hpr, hqr, ha, hb, hc, hn, h ⟩ := three_primeFactors_decomp ( show n ≠ 0 from by rintro rfl; exact absurd hn.1 ( by decide ) ) hk; exact ⟨ p, q, r, a, b, c, hp, hq, hr, ha, hb, hc, hn, h, hpq, hpr, hqr ⟩ ;
      -- Without loss of generality, assume $p = 2$.
      wlog hp2 : p = 2 generalizing p q r a b c;
      · by_cases hq2 : q = 2;
        · contrapose! this;
          grind;
        · by_cases hr2 : r = 2;
          · contrapose! this;
            grind +splitImp;
          · have h_odd_primes : p ≥ 3 ∧ q ≥ 5 ∧ r ≥ 7 ∨ p ≥ 3 ∧ r ≥ 5 ∧ q ≥ 7 ∨ q ≥ 3 ∧ p ≥ 5 ∧ r ≥ 7 ∨ q ≥ 3 ∧ r ≥ 5 ∧ p ≥ 7 ∨ r ≥ 3 ∧ p ≥ 5 ∧ q ≥ 7 ∨ r ≥ 3 ∧ q ≥ 5 ∧ p ≥ 7 := by
              cases lt_or_gt_of_ne hp2 <;> cases lt_or_gt_of_ne hq2 <;> cases lt_or_gt_of_ne hr2 <;> simp_all +decide only [Nat.Prime.two_le];
              any_goals linarith [ hp.two_le, hq.two_le, hr.two_le ];
              cases Nat.Prime.eq_two_or_odd hp <;> cases Nat.Prime.eq_two_or_odd hq <;> cases Nat.Prime.eq_two_or_odd hr <;> omega;
            contrapose! hn;
            rcases h_odd_primes with ( h | h | h | h | h | h );
            exact odd_three_primes_not_unitary_perfect hp hq hr ( by tauto ) ( by tauto ) ( by tauto ) hpa hqbc hrbc hn_eq.1 h.1 h.2.1 h.2.2;
            · convert odd_three_primes_not_unitary_perfect hp hr hq ( by tauto ) ( by tauto ) ( by tauto ) hpa hrbc hqbc ( by simpa only [ mul_comm, mul_left_comm, mul_assoc ] using hn_eq.1 ) h.1 h.2.1 h.2.2 using 1;
            · convert odd_three_primes_not_unitary_perfect hq hp hr ( by tauto ) ( by tauto ) ( by tauto ) hqbc hpa hrbc ( by simpa only [ mul_assoc, mul_comm, mul_left_comm ] using hn_eq.1 ) h.1 h.2.1 h.2.2 using 1;
            · convert odd_three_primes_not_unitary_perfect hq hr hp ( by tauto ) ( by tauto ) ( by tauto ) hqbc hrbc hpa ( by tauto ) h.1 h.2.1 h.2.2 using 1;
              grind +suggestions;
            · convert odd_three_primes_not_unitary_perfect hr hp hq ( by tauto ) ( by tauto ) ( by tauto ) hrbc hpa hqbc ( by simpa only [ mul_comm, mul_left_comm, mul_assoc ] using hn_eq.1 ) h.1 h.2.1 h.2.2 using 1;
            · convert odd_three_primes_not_unitary_perfect hr hq hp ( by tauto ) ( by tauto ) ( by tauto ) hrbc hqbc hpa ( by simpa only [ mul_assoc, mul_comm, mul_left_comm ] using hn_eq.1 ) h.1 h.2.1 h.2.2 using 1;
      · have hq_ge_3 : 3 ≤ q := by
          exact lt_of_le_of_ne hq.two_le ( Ne.symm <| by aesop_cat )
        have hr_ge_3 : 3 ≤ r := by
          contrapose! hn_eq; interval_cases r <;> simp_all +decide ;
        have hq_ne_r : q ≠ r := by
          tauto;
        -- Apply the bounds from dioph_bound_x, dioph_bound_y, and dioph_bound_z.
        have h_bounds : (1 + 2 ^ a) * ((1 + q ^ b) * (1 + r ^ c)) = 2 * (2 ^ a * (q ^ b * r ^ c)) := by
          have h_eq : unitarySigma n = (1 + 2 ^ a) * ((1 + q ^ b) * (1 + r ^ c)) := by
            rw [ hn_eq.1, unitarySigma_three_primes ] <;> aesop;
          have := hn.2; aesop;
        -- Without loss of generality, assume $q \leq r$.
        wlog hq_le_r : q ≤ r generalizing q r b c;
        · contrapose! this;
          grind +qlia;
        · -- Apply the bounds from dioph_bound_x, dioph_bound_y, and dioph_bound_z to get the inequalities.
          have h_bounds_x : 2 ^ a ≤ 4 := by
            -- Since $q \leq r$, we have $q^b \geq 3$ and $r^c \geq 5$.
            have hq_b_ge_3 : 3 ≤ q ^ b := by
              exact le_trans hq_ge_3 ( Nat.le_self_pow ( by linarith ) _ )
            have hr_c_ge_5 : 5 ≤ r ^ c := by
              by_cases hr_eq_3 : r = 3;
              · grobner;
              · exact le_trans ( by contrapose! hr_eq_3; interval_cases r <;> trivial ) ( Nat.le_self_pow ( by linarith ) _ );
            nlinarith only [ mul_pos ( pow_pos ( zero_lt_two' ℕ ) a ) ( pow_pos hq.pos b ), mul_pos ( pow_pos ( zero_lt_two' ℕ ) a ) ( pow_pos hr.pos c ), mul_pos ( pow_pos hq.pos b ) ( pow_pos hr.pos c ), h_bounds, hq_b_ge_3, hr_c_ge_5 ]
          have h_bounds_y : q ^ b ≤ 9 := by
            have h_bounds_y : q ^ b ≤ 9 := by
              have hq_ge_3 : 3 ≤ q ^ b := by
                exact le_trans hq_ge_3 ( Nat.le_self_pow ( by linarith ) _ )
              have hr_ge_5 : 5 ≤ r ^ c := by
                by_cases hr_eq_3 : r = 3;
                · grind;
                · exact le_trans ( show 5 ≤ r by exact le_of_not_gt fun h => by interval_cases r <;> trivial ) ( Nat.le_self_pow ( by linarith ) _ )
              interval_cases 2 ^ a <;> nlinarith only [ h_bounds, hq_ge_3, hr_ge_5, mul_pos ( pow_pos hq.pos b ) ( pow_pos hr.pos c ) ];
            exact h_bounds_y
          have h_bounds_z : r ^ c ≤ 29 := by
            apply dioph_bound_z;
            rotate_left;
            exact Nat.succ_le_of_lt ( show q ^ b > 2 from lt_of_lt_of_le ( by linarith ) ( Nat.le_self_pow ( by linarith ) _ ) );
            convert h_bounds using 1;
            · ring;
            · exact le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) hpa );
          simp_all +decide [ mul_assoc ];
          exact lt_of_le_of_lt ( Nat.mul_le_mul h_bounds_x ( Nat.mul_le_mul h_bounds_y h_bounds_z ) ) ( by decide )

/-! ## Finite check and main theorem -/

/-- Computational check: all unitary perfect numbers below 1100 with 3 prime factors are 60 or 90. -/
private theorem finite_check : ∀ n ∈ Finset.range 1100,
    IsUnitaryPerfect n → n.primeFactors.card = 3 → (n = 60 ∨ n = 90) := by native_decide

/-- The only unitary perfect numbers with exactly 3 prime factors are 60 and 90. -/
theorem erdos_1052_three_primes {n : ℕ} (hn : IsUnitaryPerfect n)
    (hk : n.primeFactors.card = 3) :
    n = 60 ∨ n = 90 := by
  have hbound := bound_unitary_perfect_three_primes hn hk
  exact finite_check n (Finset.mem_range.mpr hbound) hn hk