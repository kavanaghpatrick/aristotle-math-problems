import Mathlib
import RequestProject.Powerful

open scoped BigOperators

set_option maxHeartbeats 8000000

/-! # Infinitely many powerful 3-APs with d = 2√N + 1

We construct an infinite family of three-term arithmetic progressions
(N, N+d, N+2d) of powerful natural numbers with d = 2·√N + 1, using
solutions to the Pell-like equation x² − 343y² = 2.

For each solution (x,y), the triple ((x−2)², (x−1)², x²−2) is a 3-AP
of powerful numbers with common difference d = 2x−3 = 2·√((x−2)²) + 1.
-/

/-! ## The Pell sequence -/

/-- The (x,y) pair for the k-th solution to x² − 343y² = 2. -/
def pellPair : ℕ → ℤ × ℤ
  | 0 => (11427, 617)
  | k + 1 =>
    let (x, y) := pellPair k
    (130576328 * x + 2418307437 * y, 7050459 * x + 130576328 * y)

def pellX (k : ℕ) : ℤ := (pellPair k).1
def pellY (k : ℕ) : ℤ := (pellPair k).2

@[simp] lemma pellX_zero : pellX 0 = 11427 := rfl
@[simp] lemma pellY_zero : pellY 0 = 617 := rfl
@[simp] lemma pellX_succ (k : ℕ) :
    pellX (k + 1) = 130576328 * pellX k + 2418307437 * pellY k := rfl
@[simp] lemma pellY_succ (k : ℕ) :
    pellY (k + 1) = 7050459 * pellX k + 130576328 * pellY k := rfl

/-! ## Pell equation invariant -/

lemma pell_invariant (k : ℕ) : pellX k ^ 2 - 343 * pellY k ^ 2 = 2 := by
  induction k <;> simp_all +decide [ pellX_succ, pellY_succ ] ; ring;
  linarith

/-! ## Positivity and bounds -/

lemma pellX_pos (k : ℕ) : 0 < pellX k := by
  -- By induction on $k$, we can show that both $pellX k$ and $pellY k$ are positive.
  have h_pos : ∀ k, 0 < pellX k ∧ 0 < pellY k := by
    intro k; induction k <;> [ exact ⟨ by decide, by decide ⟩ ; exact ⟨ by linarith! [ pellX_succ ‹_›, pellY_succ ‹_›, ‹0 < pellX _ ∧ 0 < pellY _› ], by linarith! [ pellX_succ ‹_›, pellY_succ ‹_›, ‹0 < pellX _ ∧ 0 < pellY _› ] ⟩ ] ;
  exact h_pos k |>.1

lemma pellY_pos (k : ℕ) : 0 < pellY k := by
  induction' k with k ih <;> norm_num [ pellX_succ, pellY_succ ];
  linarith [ pellX_pos k ]

lemma pellX_ge_three (k : ℕ) : 3 ≤ pellX k := by
  induction' k with k ih <;> norm_num [ pellX_zero, pellX_succ ];
  linarith [ pellY_pos k ]

/-! ## Strict monotonicity -/

lemma pellX_strictMono : StrictMono pellX := by
  refine' strictMono_nat_of_lt_succ _;
  intro n;
  exact by rw [ pellX_succ ] ; linarith [ pellX_pos n, pellY_pos n ] ;

/-! ## Arithmetic identities (in ℤ) -/

private lemma arith_mid (x : ℤ) : (x - 2) ^ 2 + (2 * x - 3) = (x - 1) ^ 2 := by ring

private lemma arith_last (x y : ℤ) (h : x ^ 2 - 343 * y ^ 2 = 2) :
    (x - 2) ^ 2 + 2 * (2 * x - 3) = 343 * y ^ 2 := by linarith

private lemma arith_diff (x : ℤ) : 2 * x - 3 = 2 * (x - 2) + 1 := by ring

/-! ## Conversion helpers -/

lemma pellX_sub2_nonneg (k : ℕ) : 0 ≤ pellX k - 2 := by
  linarith [pellX_ge_three k]

lemma two_pellX_sub3_nonneg (k : ℕ) : 0 ≤ 2 * pellX k - 3 := by
  linarith [pellX_ge_three k]

lemma pellX_sub1_nonneg (k : ℕ) : 0 ≤ pellX k - 1 := by
  linarith [pellX_ge_three k]

/-! ## The construction -/

/-- Map the k-th Pell solution to the pair (N, d). -/
noncomputable def mkPair (k : ℕ) : ℕ × ℕ :=
  ((pellX k - 2).toNat ^ 2, (2 * pellX k - 3).toNat)

/-! ## Membership in the target set -/

-- First term is powerful (it's a perfect square)
lemma first_powerful (k : ℕ) : Nat.Powerful (mkPair k).1 := by
  simp only [mkPair]
  exact sq_powerful _

/-
Second term (N + d) is powerful (it equals (x-1)²)
-/
lemma second_powerful (k : ℕ) :
    Nat.Powerful ((mkPair k).1 + (mkPair k).2) := by
      -- By definition of mkPair, we have that ((mkPair k).1 + (mkPair k).2) = ((pellX k - 1).toNat) ^ 2.
      have h_eq : ((mkPair k).1 + (mkPair k).2) = ((pellX k - 1).toNat) ^ 2 := by
        unfold mkPair;
        zify;
        grind +qlia
      exact h_eq.symm ▸ sq_powerful _

/-
Third term (N + 2d) is powerful (it equals 7³·y²)
-/
lemma third_powerful (k : ℕ) :
    Nat.Powerful ((mkPair k).1 + 2 * (mkPair k).2) := by
      -- By definition of $mkPair$, we know that $(mkPair k).1 + 2 * (mkPair k).2 = 7^3 * (pellY k).toNat^2$.
      have h_eq : (mkPair k).1 + 2 * (mkPair k).2 = 7^3 * (pellY k).toNat^2 := by
        unfold mkPair; norm_num;
        nlinarith only [ Int.toNat_of_nonneg ( pellX_sub2_nonneg k ), Int.toNat_of_nonneg ( two_pellX_sub3_nonneg k ), Int.toNat_of_nonneg ( pellY_pos k |> le_of_lt ), pell_invariant k ];
      -- Since $7^3 � *� (pellY k).toNat^2$ is powerful by the lemma powerful_7cube_mul_sq, we can conclude.
      rw [h_eq]
      apply powerful_7cube_mul_sq

/-
The common difference condition
-/
lemma diff_eq (k : ℕ) :
    (mkPair k).2 = 2 * Nat.sqrt (mkPair k).1 + 1 := by
      unfold mkPair; norm_num;
      zify [ pellX_pos ] ; ring;
      rw [ Int.toNat_of_nonneg, Int.toNat_of_nonneg ] <;> linarith [ pellX_ge_three k ]

/-! ## Injectivity -/

lemma mkPair_injective : Function.Injective mkPair := by
  intro a b hab;
  unfold mkPair at hab;
  norm_num +zetaDelta at *;
  exact StrictMono.injective pellX_strictMono ( by linarith [ Int.toNat_of_nonneg ( pellX_sub2_nonneg a ), Int.toNat_of_nonneg ( pellX_sub2_nonneg b ) ] )

/-! ## Main theorem -/

theorem powerful_3AP_d_eq_2sqrtN_plus_1 :
    {p : ℕ × ℕ | Nat.Powerful p.1 ∧ Nat.Powerful (p.1 + p.2) ∧
      Nat.Powerful (p.1 + 2 * p.2) ∧
      p.2 = 2 * Nat.sqrt p.1 + 1}.Infinite := by
  apply Set.infinite_of_injective_forall_mem mkPair_injective
  intro k
  exact ⟨first_powerful k, second_powerful k, third_powerful k, diff_eq k⟩