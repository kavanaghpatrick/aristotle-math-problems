import Mathlib

open scoped BigOperators
open Finset Finsupp

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- A natural number `n` is *powerful* iff for every prime `p` dividing `n`,
    `p ^ 2` also divides `n`. -/
def Nat.Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-! ## Reverse direction: a² · b³ with squarefree b is powerful -/

theorem powerful_of_sq_mul_cube {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hsq : Squarefree b) : Nat.Powerful (a ^ 2 * b ^ 3) := by
  intro p pp dp;
  rw [ Nat.Prime.dvd_mul pp ] at dp;
  rcases dp with ( dp | dp );
  · exact dvd_mul_of_dvd_left ( pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) 2 ) _;
  · exact dvd_mul_of_dvd_right ( dvd_trans ( pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) 2 ) ( pow_dvd_pow _ ( show 3 ≥ 2 by decide ) ) ) _

/-! ## Forward direction: powerful n ≥ 1 admits a decomposition -/

/-
Auxiliary arithmetic: for k ≥ 2, k = 2 * ((k - 3 * (k % 2)) / 2) + 3 * (k % 2).
-/
theorem aux_arith (k : ℕ) (hk : 2 ≤ k) :
    k = 2 * ((k - 3 * (k % 2)) / 2) + 3 * (k % 2) := by
  omega

theorem sq_mul_cube_of_powerful (n : ℕ) (hn : 1 ≤ n) (hp : Nat.Powerful n) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ Squarefree b ∧ n = a ^ 2 * b ^ 3 := by
  revert hp;
  -- Define $b$ as the product of primes $p$ dividing $n$ with odd exponents.
  intro hp
  let b := ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p % 2 = 1), p
  let a := ∏ p ∈ n.primeFactors, p ^ ((n.factorization p - 3 * (n.factorization p % 2)) / 2);
  -- We need to show that $n = a^2 � *� b^3$.
  have h_eq : n = a^2 * b^3 := by
    have h_factorization : ∀ p ∈ n.primeFactors, n.factorization p = 2 * ((n.factorization p - 3 * (n.factorization p % 2)) / 2) + 3 * (if n.factorization p % 2 = 1 then 1 else 0) := by
      intro p hp; split_ifs <;> simp_all +decide [ Nat.div_mul_cancel ] ;
      · have := ‹n.Powerful› p hp.1 hp.2.1; rcases k : n.factorization p with ( _ | _ | _ | k ) <;> simp_all +arith +decide [ Nat.pow_succ' ] ;
        · rw [ ← sq ] at this; rw [ ← Nat.factorization_le_iff_dvd ] at this <;> aesop;
        · omega;
      · grind;
    conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( by positivity : n ≠ 0 ) ];
    simp +zetaDelta at *;
    rw [ ← Finset.prod_pow, ← Finset.prod_pow ];
    rw [ Finset.prod_filter ];
    rw [ ← Finset.prod_mul_distrib ] ; refine' Finset.prod_congr rfl fun p hp => _ ; specialize h_factorization p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ( by positivity ) ; rw [ h_factorization ] ; ring;
    cases Nat.mod_two_eq_zero_or_one ( n.factorization p ) <;> simp +decide [ ‹_› ];
  refine' ⟨ a, b, _, _, _, h_eq ⟩;
  · exact Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_mem_primeFactors hp ) _;
  · exact Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors ( Finset.mem_filter.mp hp |>.1 );
  · refine' Nat.squarefree_iff_prime_squarefree.mpr _;
    intro p pp dp; simp +decide [ ← sq ] at dp;
    rw [ Nat.Prime.pow_dvd_iff_le_factorization ] at dp <;> norm_num at *;
    · rw [ Nat.factorization_prod ] at dp <;> norm_num at *;
      · rw [ Finset.sum_eq_single p ] at dp <;> norm_num at *;
        · norm_num [ pp.factorization ] at dp;
        · simp +contextual;
        · intro h; contrapose! dp; simp +decide [ pp.factorization ] at *;
          rw [ Finset.sum_eq_zero ] <;> norm_num;
          intro q hq hqn hn hq'; rw [ Nat.factorization_eq_zero_iff ] ;
          exact Or.inr <| Or.inl <| by rintro H; have := Nat.prime_dvd_prime_iff_eq pp hq; simp_all +singlePass ;
      · exact fun x hx _ _ _ => hx.ne_zero;
    · assumption;
    · exact Finset.prod_ne_zero_iff.mpr fun q hq => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors <| Finset.filter_subset _ _ hq

/-! ## Main theorem -/

theorem powerful_parametrization (n : ℕ) (hn : 1 ≤ n) :
    Nat.Powerful n ↔ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ Squarefree b ∧ n = a ^ 2 * b ^ 3 := by
  constructor
  · exact sq_mul_cube_of_powerful n hn
  · rintro ⟨a, b, ha, hb, hsq, rfl⟩
    exact powerful_of_sq_mul_cube ha hb hsq