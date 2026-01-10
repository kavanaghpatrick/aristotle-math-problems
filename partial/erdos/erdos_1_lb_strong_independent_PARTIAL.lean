/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c636fe00-d9cf-4cf8-a563-f7b045ec4bcf

The following was proved by Aristotle:

- lemma variance_lower_bound (A : Finset ℝ) (h_dist : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|) :
  ∑ x ∈ A, x^2 - (∑ x ∈ A, x)^2 / A.card ≥ ((A.card : ℝ)^3 - A.card) / 12

- lemma sum_sq_lower_bound (A : Finset ℕ) (h_inj : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
  ∑ a ∈ A, (a : ℝ)^2 ≥ ((2 : ℝ)^(2 * A.card) - 1) / 3

- theorem lb : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

- theorem lb_variance : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1 / Real.sqrt 3 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N

- lemma second_moment_formula (A : Finset ℕ) :
    second_moment A = (∑ a ∈ A, (a : ℝ))^2 / 4 + (∑ a ∈ A, (a : ℝ)^2) / 4
-/

/-
Erdős Problem #1: Prove lb_strong INDEPENDENTLY (without using erdos_1)

CONTEXT:
- lb_variance is PROVEN: N ≥ (1/√3 - o(1)) · 2ⁿ/√n
- lb_strong uses erdos_1 (which has sorry) via exact?
- GOAL: Prove lb_strong directly without erdos_1

TARGET CONSTANT IMPROVEMENT:
- Current: 1/√3 ≈ 0.577
- Target: √(2/π) ≈ 0.798
- Factor: 1.38× improvement needed

ELKIES-GLEASON APPROACH:
The key insight is that subset sums of a sum-distinct set behave like
a random walk. For random ±a_i contributions, by CLT:
  - Subset sums are approximately Gaussian
  - Variance = (1/4)∑a²
  - For 2ⁿ distinct points in [0, nN], need "spacing" ≈ nN/2ⁿ
  - By Gaussian tail bounds: this forces N ≥ √(2/π) · 2ⁿ/√n

PROOF STRATEGY:
1. Use variance_identity: ∑_S (sum(S) - μ)² = 2^n/4 · ∑a²
2. The 2ⁿ distinct subset sums have total "spread" proportional to √(∑a²·2ⁿ)
3. They must fit in [0, nN], so nN ≥ c · √(∑a²·2ⁿ) for some c
4. Combined with ∑a² ≥ (4ⁿ-1)/3, get the improved bound
-/

import Mathlib


open Filter Finset

open scoped Topology Real BigOperators

namespace Erdos1

-- Definition from proven file
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from Aristotle 244de51c)
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable section

/-- Variance identity for subset sums -/
lemma variance_identity (A : Finset ℕ) :
  ∑ s ∈ A.powerset, ((∑ x ∈ s, (x : ℝ)) - (∑ x ∈ A, (x : ℝ)) / 2)^2 =
  (2 : ℝ)^(A.card) / 4 * ∑ a ∈ A, (a : ℝ)^2 := by
  induction' A using Finset.induction with a A ha ih
  · norm_num
  · have h_split : ∑ s ∈ (Insert.insert a A).powerset,
        (∑ x ∈ s, (x : ℝ) - (∑ x ∈ Insert.insert a A, (x : ℝ)) / 2) ^ 2 =
        ∑ s ∈ A.powerset, ((∑ x ∈ s, (x : ℝ) - (∑ x ∈ A, (x : ℝ)) / 2) + (a : ℝ) / 2) ^ 2 +
        ∑ s ∈ A.powerset, ((∑ x ∈ s, (x : ℝ) - (∑ x ∈ A, (x : ℝ)) / 2) - (a : ℝ) / 2) ^ 2 := by
      simp +decide [Finset.sum_powerset_insert ha]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine' Finset.sum_congr rfl fun x hx => _
      rw [Finset.sum_insert (Finset.notMem_mono (Finset.mem_powerset.mp hx) ha)]
      ring
      grind
    simp_all +decide [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_sq, add_sq]
    ring
    norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _]
    ring

/-- Variance lower bound for integer-spaced reals -/
lemma variance_lower_bound (A : Finset ℝ) (h_dist : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|) :
  ∑ x ∈ A, x^2 - (∑ x ∈ A, x)^2 / A.card ≥ ((A.card : ℝ)^3 - A.card) / 12 := by
  by_contra h_contra;
  have h_sum_sq : ∑ x ∈ A, ∑ y ∈ A, (x - y)^2 ≥ ∑ i ∈ Finset.range A.card, ∑ j ∈ Finset.range A.card, (i - j : ℝ)^2 := by
    -- Since $A$ is a finite set of real numbers, we can order its elements as $a_1 < a_2 < \cdots < a_n$.
    obtain ⟨a, ha⟩ : ∃ a : Fin A.card → ℝ, StrictMono a ∧ ∀ i, a i ∈ A := by
      exact ⟨ fun i => A.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => A.orderEmbOfFin_mem rfl _ ⟩;
    -- Since $a$ is strictly monotone, we have $a i - a j \geq i - j$ for all $i, j$.
    have h_diff_ge : ∀ i j : Fin A.card, i < j → a j - a i ≥ j - i := by
      intros i j hij
      induction' j with j hj generalizing i;
      induction' j with j ih generalizing i;
      · tauto;
      · rcases eq_or_lt_of_le ( show i ≤ ⟨ j, by linarith ⟩ from Nat.le_of_lt_succ hij ) with rfl | hi <;> norm_num at *;
        · have := h_dist ( a ⟨ j + 1, hj ⟩ ) ( ha.2 _ ) ( a ⟨ j, by linarith ⟩ ) ( ha.2 _ ) ( ha.1.injective.ne ( by norm_num ) ) ; cases abs_cases ( a ⟨ j + 1, hj ⟩ - a ⟨ j, by linarith ⟩ ) <;> linarith [ ha.1 ( show ⟨ j, by linarith ⟩ < ⟨ j + 1, hj ⟩ from Nat.lt_succ_self _ ) ];
        · have := ih ( by linarith ) i hi;
          have := h_dist ( a ⟨ j + 1, hj ⟩ ) ( ha.2 _ ) ( a ⟨ j, by linarith ⟩ ) ( ha.2 _ ) ( ha.1.injective.ne ( by aesop ) ) ; cases abs_cases ( a ⟨ j + 1, hj ⟩ - a ⟨ j, by linarith ⟩ ) <;> linarith [ ha.1 ( show ⟨ j, by linarith ⟩ < ⟨ j + 1, hj ⟩ from Nat.lt_succ_self _ ) ] ;
    have h_diff_ge : ∀ i j : Fin A.card, i ≠ j → (a i - a j)^2 ≥ (i - j : ℝ)^2 := by
      intros i j hij
      by_cases h_cases : i < j;
      · nlinarith only [ h_diff_ge i j h_cases, show ( i : ℝ ) < j from Nat.cast_lt.mpr h_cases ];
      · exact pow_le_pow_left₀ ( sub_nonneg.mpr <| Nat.cast_le.mpr <| le_of_not_gt h_cases ) ( by linarith [ h_diff_ge _ _ <| lt_of_le_of_ne ( le_of_not_gt h_cases ) hij.symm ] ) _;
    have h_sum_sq_ge : ∑ x ∈ Finset.image a Finset.univ, ∑ y ∈ Finset.image a Finset.univ, (x - y)^2 ≥ ∑ i ∈ Finset.range A.card, ∑ j ∈ Finset.range A.card, (i - j : ℝ)^2 := by
      rw [ Finset.sum_image <| by intros i hi j hj hij; exact ha.1.injective hij ];
      rw [ Finset.sum_range, Finset.sum_congr rfl fun i hi => Finset.sum_image <| by intros x hx y hy hxy; exact ha.1.injective hxy ];
      exact Finset.sum_le_sum fun i hi => by rw [ Finset.sum_range ] ; exact Finset.sum_le_sum fun j hj => if hij : i = j then hij.symm ▸ by norm_num else h_diff_ge i j hij;
    refine le_trans h_sum_sq_ge ?_;
    rw [ Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => ha.2 i ) ( by rw [ Finset.card_image_of_injective _ ha.1.injective, Finset.card_fin ] ) ];
  -- Let's simplify the right-hand side of the inequality.
  have h_simplify_rhs : ∑ i ∈ Finset.range A.card, ∑ j ∈ Finset.range A.card, (i - j : ℝ)^2 = (A.card : ℝ)^2 * ((A.card : ℝ)^2 - 1) / 6 := by
    norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
    -- We'll use the fact that $\sum_{i=0}^{n-1} i^2 = \frac{(n-1)n(2n-1)}{6}$ and $\sum_{i=0}^{n-1} i = \frac{(n-1)n}{2}$.
    have h_sums : ∑ i ∈ Finset.range A.card, (i : ℝ)^2 = (A.card : ℝ) * (A.card - 1) * (2 * A.card - 1) / 6 ∧ ∑ i ∈ Finset.range A.card, (i : ℝ) = (A.card : ℝ) * (A.card - 1) / 2 := by
      exact ⟨ Nat.recOn ( Finset.card A ) ( by norm_num ) fun n ih => by rw [ Finset.sum_range_succ ] ; push_cast ; linarith, Nat.recOn ( Finset.card A ) ( by norm_num ) fun n ih => by rw [ Finset.sum_range_succ ] ; push_cast ; linarith ⟩;
    norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h_sums ] ; ring;
  simp_all +decide [ Finset.sum_add_distrib, sub_sq, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
  rw [ sub_div', div_lt_div_iff₀ ] at h_contra <;> nlinarith [ show ( A.card : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty <| by rintro rfl; norm_num at * ) ]

-- PROVEN in 244de51c, copy full proof if needed

/-- Sum of squares lower bound for sum-distinct sets -/
lemma sum_sq_lower_bound (A : Finset ℕ) (h_inj : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
  ∑ a ∈ A, (a : ℝ)^2 ≥ ((2 : ℝ)^(2 * A.card) - 1) / 3 := by
  -- Applying the variance_lower_bound lemma to the set of subset sums.
  have h_subset_sums : (∑ x ∈ Finset.image (fun S => S.sum id : Finset ℕ → ℕ) (Finset.powerset A), (x : ℝ)^2) - (∑ x ∈ Finset.image (fun S => S.sum id : Finset ℕ → ℕ) (Finset.powerset A), (x : ℝ))^2 / (Finset.card (Finset.powerset A)) ≥ ((Finset.card (Finset.powerset A))^3 - Finset.card (Finset.powerset A)) / 12 := by
    convert variance_lower_bound ( Finset.image ( fun S : Finset ℕ => S.sum id ) ( Finset.powerset A ) |> Finset.image ( ( ↑ ) : ℕ → ℝ ) ) _ using 1;
    · rw [ Finset.card_image_of_injective _ Nat.cast_injective ] ; norm_num [ Finset.card_image_of_injective _ h_inj ];
      rw [ Finset.card_image_of_injOn ];
      · norm_num [ Finset.card_powerset ];
      · exact fun x hx y hy hxy => by have := @h_inj ⟨ x, hx ⟩ ⟨ y, hy ⟩ ; aesop;
    · rw [ Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_image_of_injOn ];
      exact fun x hx y hy hxy => by have := @h_inj ⟨ x, hx ⟩ ⟨ y, hy ⟩ ; aesop;
    · simp_all +decide [ Function.Injective, Finset.ext_iff ];
      intro a ha b hb h; rw [ ← Nat.cast_sum, ← Nat.cast_sum ] at *; norm_cast at *;
      rw [ Int.subNatNat_eq_coe ] ; cases abs_cases ( ∑ x ∈ a, x - ∑ x ∈ b, x : ℤ ) <;> omega;
  -- Substitute the sum of the subset sums into the inequality.
  have h_sum_subset_sums : (∑ x ∈ Finset.image (fun S => S.sum id : Finset ℕ → ℕ) (Finset.powerset A), (x : ℝ)) = 2 ^ (Finset.card A - 1) * ∑ a ∈ A, (a : ℝ) := by
    -- The sum of the subset sums is given by $\sum_{S \subseteq A} \sum_{a \in S} a = \sum_{a \in A} \sum_{S \subseteq A, a \in S} a$.
    have h_sum_subset_sums : ∑ x ∈ Finset.image (fun S => S.sum id : Finset ℕ → ℕ) (Finset.powerset A), (x : ℝ) = ∑ a ∈ A, ∑ S ∈ Finset.powerset A, (if a ∈ S then (a : ℝ) else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      rw [ Finset.sum_image ];
      rotate_left;
      exact fun x hx y hy hxy => by simpa using @h_inj ⟨ x, hx ⟩ ⟨ y, hy ⟩ hxy;
      use fun x => x;
      · grind;
      · simp +decide [ Finset.sum_ite ];
        exact Finset.sum_congr rfl fun x hx => by rw [ Finset.inter_eq_right.mpr ( Finset.mem_powerset.mp hx ) ] ;
    -- For each element $a \in A$, the number of subsets $S \subseteq A$ that contain $a$ is $2^{|A|-1}$.
    have h_count_subsets : ∀ a ∈ A, ∑ S ∈ Finset.powerset A, (if a ∈ S then 1 else 0) = 2 ^ (Finset.card A - 1) := by
      intro a ha
      have h_count_subsets : Finset.card (Finset.filter (fun S => a ∈ S) (Finset.powerset A)) = Finset.card (Finset.powerset (A \ {a})) := by
        refine' Finset.card_bij ( fun S hS => S \ { a } ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
        · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; ext x; by_cases hx : x = a <;> simp_all +decide [ Finset.ext_iff ] ;
        · exact fun b hb => ⟨ Insert.insert a b, ⟨ fun x hx => by cases Finset.mem_insert.mp hx <;> aesop, by aesop ⟩, by aesop ⟩;
      simp_all +decide [ Finset.card_sdiff ];
    simp_all +decide [ Finset.sum_ite ];
    rw [ Finset.mul_sum _ _ _ ];
  -- Substitute the sum of the squares of the subset sums into the inequality.
  have h_sum_squares_subset_sums : (∑ x ∈ Finset.image (fun S => S.sum id : Finset ℕ → ℕ) (Finset.powerset A), (x : ℝ)^2) = (2 : ℝ)^(A.card) / 4 * ∑ a ∈ A, (a : ℝ)^2 + (2 ^ (A.card - 1) * ∑ a ∈ A, (a : ℝ))^2 / (2 ^ A.card) := by
    have h_sum_squares_subset_sums : (∑ x ∈ Finset.image (fun S => S.sum id : Finset ℕ → ℕ) (Finset.powerset A), (x : ℝ)^2) = (∑ s ∈ Finset.powerset A, ((∑ x ∈ s, (x : ℝ)) - (∑ x ∈ A, (x : ℝ)) / 2)^2) + (∑ x ∈ A, (x : ℝ))^2 / 4 * (2 ^ A.card) := by
      rw [ Finset.sum_image ];
      · norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ];
        norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ; ring;
        rw [ show ( ∑ x ∈ Finset.powerset A, ∑ x ∈ x, ( x : ℝ ) ) = 2 ^ ( A.card - 1 ) * ∑ x ∈ A, ( x : ℝ ) from ?_ ] ; rcases A with ⟨ ⟨ l, hl ⟩ ⟩ <;> norm_num [ Nat.succ_eq_add_one, pow_succ' ] ; ring;
        convert h_sum_subset_sums using 1;
        rw [ Finset.sum_image ] ; aesop;
        exact fun x hx y hy hxy => by have := @h_inj ⟨ x, hx ⟩ ⟨ y, hy ⟩ ; aesop;
      · exact fun x hx y hy hxy => by have := @h_inj ⟨ x, hx ⟩ ⟨ y, hy ⟩ ; aesop;
    rw [ h_sum_squares_subset_sums, variance_identity ];
    rcases k : Finset.card A with ( _ | k ) <;> simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm ] ; ring;
    -- Combine like terms and simplify the expression.
    field_simp
    ring;
    norm_num [ pow_mul', mul_assoc ];
    norm_num [ ← mul_pow ];
  rcases k : Finset.card A with ( _ | k ) <;> simp_all +decide [ pow_succ', pow_mul' ];
  nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( Nat.zero_le ‹_› ) ]

-- PROVEN in 244de51c, copy full proof if needed

/-- The lb bound (Erdős-Moser 1956) -/
theorem lb : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  refine' ⟨ fun _ => 0, _, _ ⟩ <;> norm_num;
  intro N A hA h_inj
  have h_bound : (2 : ℝ) ^ (2 * A.card) ≤ 3 * N^2 * A.card + 1 := by
    have h_bound : (∑ a ∈ A, (a : ℝ)^2) ≤ N^2 * A.card := by
      exact le_trans ( Finset.sum_le_sum fun x hx => pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( hA hx ) |>.2 ) 2 ) <| by norm_num; linarith;
    have := sum_sq_lower_bound A h_inj; norm_num [ pow_mul' ] at *; linarith;
  rcases A.eq_empty_or_nonempty with ( rfl | ⟨ x, hx ⟩ ) <;> norm_num at *;
  rw [ div_le_iff₀ ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| Finset.card_pos.mpr ⟨ x, hx ⟩ ) ];
  rw [ pow_mul' ] at h_bound;
  nlinarith [ show ( 0 : ℝ ) ≤ N * Real.sqrt ( A.card : ℝ ) by positivity, Real.mul_self_sqrt ( Nat.cast_nonneg ( A.card : ℕ ) ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show A.card ≥ 1 from Finset.card_pos.mpr ⟨ x, hx ⟩ ) ]

-- PROVEN in 244de51c

/-- The lb_variance bound (1/√3 constant) - FULLY PROVEN -/
theorem lb_variance : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1 / Real.sqrt 3 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  field_simp;
  refine' ⟨ _, _, _ ⟩;
  exact fun n => 1 / ( Real.sqrt 3 * 2 ^ n );
  · norm_num [ Asymptotics.isLittleO_iff_tendsto ];
    exact le_trans ( Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) ) tendsto_const_nhds ) ( by norm_num );
  · intro N A hA;
    by_cases hA' : A = ∅ <;> simp_all +decide [ mul_div, mul_comm ];
    field_simp;
    rw [ div_le_iff₀ ];
    · -- By the properties of the sum of squares and the variance, we have:
      have h_sum_sq : ∑ a ∈ A, (a : ℝ)^2 ≤ N^2 * A.card := by
        exact le_trans ( Finset.sum_le_sum fun x hx => show ( x : ℝ ) ^ 2 ≤ N ^ 2 by exact_mod_cast Nat.pow_le_pow_left ( hA.1 hx |> Finset.mem_Icc.mp |> And.right ) 2 ) ( by norm_num; linarith );
      have h_sum_sq_lower_bound : ∑ a ∈ A, (a : ℝ)^2 ≥ ((2 : ℝ)^(2 * A.card) - 1) / 3 := by
        apply sum_sq_lower_bound;
        exact hA.2;
      rw [ ← Real.sqrt_sq ( show 0 ≤ Real.sqrt 3 * ( N : ℝ ) * Real.sqrt ( A.card : ℝ ) by positivity ) ];
      refine Real.le_sqrt_of_sq_le ?_;
      norm_num [ mul_pow, pow_mul' ] at *;
      nlinarith [ show ( 2 ^ A.card : ℝ ) ≥ 1 by exact one_le_pow₀ ( by norm_num ) ];
    · exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty hA' ) ) )

-- PROVEN in 244de51c

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW: PROVE lb_strong INDEPENDENTLY
-- ══════════════════════════════════════════════════════════════════════════════

/-
Key lemma: The "spread" of 2ⁿ subset sums requires a container of size
proportional to √(variance · 2ⁿ).

For 2ⁿ distinct integers in [0, M], the variance is at least (2ⁿ)²/12 roughly.
The subset sums have variance = 2^n/4 · ∑a² by variance_identity.
The container [0, nN] has size nN.

The insight: 2ⁿ "evenly spaced" points in [0, nN] have spacing nN/2ⁿ.
But subset sums cluster more than uniform (they're roughly Gaussian).
The Gaussian approximation gives the √(2/π) factor.
-/

/-- Subset sums form a set of 2ⁿ distinct naturals -/
lemma subset_sums_card (A : Finset ℕ) (h : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
    (A.powerset.image (fun S => S.sum id)).card = 2 ^ A.card := by
  rw [card_image_of_injOn]
  · exact card_powerset A
  · intro x hx y hy hxy
    have := @h ⟨x, hx⟩ ⟨y, hy⟩
    simp at this
    exact this hxy

/-- All subset sums are at most n·N -/
lemma subset_sum_le (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Icc 1 N) (S : Finset ℕ) (hS : S ⊆ A) :
    S.sum id ≤ A.card * N := by
  calc S.sum id
      ≤ A.sum id := sum_le_sum_of_subset hS
    _ ≤ A.card * N := by
        apply Finset.sum_le_card_nsmul
        intro x hx
        exact (mem_Icc.mp (hA hx)).2

/-- The mean of subset sums -/
def mean_sum (A : Finset ℕ) : ℝ := (∑ x ∈ A, (x : ℝ)) / 2

/-- Subset sums have bounded L² distance from mean -/
lemma subset_sums_L2_from_mean (A : Finset ℕ) :
    ∑ s ∈ A.powerset, ((∑ x ∈ s, (x : ℝ)) - mean_sum A)^2 =
    (2 : ℝ)^(A.card) / 4 * ∑ a ∈ A, (a : ℝ)^2 := by
  unfold mean_sum
  exact variance_identity A

/- Aristotle failed to find a proof. -/
/--
MAIN GOAL: Prove lb_strong WITHOUT using erdos_1.

The approach: Use the Chebyshev/concentration inequality.
If 2ⁿ points have variance V, then they span at least √(V·2ⁿ/π) in some sense.
-/
theorem lb_strong_independent : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (√(2 / π) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  /-
  Strategy:
  1. From variance_identity: total squared deviation = 2^n/4 · ∑a²
  2. From sum_sq_lower_bound: ∑a² ≥ (4^n - 1)/3
  3. So total squared deviation ≥ 2^n/4 · (4^n - 1)/3 ≈ 2^(3n)/12

  4. For 2ⁿ distinct reals x₁,...,x_{2ⁿ} in [0, nN] with mean μ:
     ∑(xᵢ - μ)² = 2ⁿ · Var(x)

  5. For discrete uniform on [0, M]: Var = M²/12
     But subset sums are more concentrated (Gaussian-like)

  6. The key is: 2ⁿ points in [0, nN] with total squared deviation D
     must satisfy nN ≥ c · √(D/2ⁿ) for some c related to √(2/π)
  -/
  sorry

-- Alternative approach: use moments
/-- Second moment of subset sums -/
def second_moment (A : Finset ℕ) : ℝ :=
  (1 / 2^A.card : ℝ) * ∑ s ∈ A.powerset, (∑ x ∈ s, (x : ℝ))^2

/-- The second moment relates to sum of squares -/
lemma second_moment_formula (A : Finset ℕ) :
    second_moment A = (∑ a ∈ A, (a : ℝ))^2 / 4 + (∑ a ∈ A, (a : ℝ)^2) / 4 := by
  -- Expand the square and simplify the expression.
  have h_expand : ∀ s ⊆ A, (∑ x ∈ s, (x : ℝ))^2 = ∑ x ∈ s, (x : ℝ)^2 + 2 * ∑ x ∈ s, ∑ y ∈ s, (if x < y then (x : ℝ) * (y : ℝ) else 0) := by
    intro s hs
    induction' s using Finset.induction with a s ha ih;
    · norm_num;
    · simp_all +decide [ Finset.sum_insert ha, Finset.sum_add_distrib, add_sq, mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring;
      rw [ ih ( Finset.Subset.trans ( Finset.subset_insert _ _ ) hs ) ] ; simp +decide [ Finset.sum_ite, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, Finset.sum_ite ] ; ring;
      rw [ ← Finset.sum_filter_add_sum_filter_not s ( fun x => a < x ) ] ; ring;
      rw [ show ( Finset.filter ( fun x => ¬a < x ) s ) = Finset.filter ( fun x => x < a ) s from Finset.filter_congr fun x hx => by exact ⟨ fun hx' => lt_of_le_of_ne ( le_of_not_gt hx' ) ( by aesop ), fun hx' => not_lt_of_ge ( le_of_lt hx' ) ⟩ ] ; ring;
  -- Sum the expanded squares over all subsets of A.
  have h_sum_expand : ∑ s ∈ A.powerset, (∑ x ∈ s, (x : ℝ))^2 = ∑ a ∈ A, (a : ℝ)^2 * 2^(A.card - 1) + 2 * ∑ a ∈ A, ∑ b ∈ A, (if a < b then (a : ℝ) * (b : ℝ) * 2^(A.card - 2) else 0) := by
    have h_sum_expand : ∑ s ∈ A.powerset, (∑ x ∈ s, (x : ℝ)^2) = ∑ a ∈ A, (a : ℝ)^2 * 2^(A.card - 1) := by
      have h_sum_expand : ∀ a ∈ A, ∑ s ∈ A.powerset, (if a ∈ s then (a : ℝ)^2 else 0) = (a : ℝ)^2 * 2^(A.card - 1) := by
        intro a ha
        have h_count : Finset.card (Finset.filter (fun s => a ∈ s) (Finset.powerset A)) = 2^(A.card - 1) := by
          have h_count : Finset.card (Finset.filter (fun s => a ∈ s) (Finset.powerset A)) = Finset.card (Finset.powerset (A \ {a})) := by
            refine' Finset.card_bij ( fun s hs => s \ { a } ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
            · intro s₁ hs₁ hs₁' s₂ hs₂ hs₂' h; ext x; by_cases hx : x = a <;> simp_all +decide [ Finset.ext_iff ] ;
            · exact fun s hs => ⟨ Insert.insert a s, ⟨ fun x hx => by aesop, by aesop ⟩, by aesop ⟩;
          simp_all +decide [ Finset.card_sdiff ];
        simp_all +decide [ mul_comm, Finset.sum_ite ];
      rw [ ← Finset.sum_congr rfl h_sum_expand, Finset.sum_comm ];
      exact Finset.sum_congr rfl fun s hs => by rw [ ← Finset.sum_filter ] ; congr; ext; aesop;
    have h_sum_expand : ∑ s ∈ A.powerset, ∑ x ∈ s, ∑ y ∈ s, (if x < y then (x : ℝ) * (y : ℝ) else 0) = ∑ a ∈ A, ∑ b ∈ A, (if a < b then (a : ℝ) * (b : ℝ) * 2^(A.card - 2) else 0) := by
      have h_sum_expand : ∀ x ∈ A, ∀ y ∈ A, x < y → ∑ s ∈ A.powerset, (if x ∈ s ∧ y ∈ s then (x : ℝ) * (y : ℝ) else 0) = (x : ℝ) * (y : ℝ) * 2^(A.card - 2) := by
        intros x hx y hy hxy
        have h_subset_count : Finset.card (Finset.filter (fun s => x ∈ s ∧ y ∈ s) (Finset.powerset A)) = 2^(A.card - 2) := by
          have h_subset_count : Finset.card (Finset.filter (fun s => x ∈ s ∧ y ∈ s) (Finset.powerset A)) = Finset.card (Finset.powerset (A \ {x, y})) := by
            refine' Finset.card_bij ( fun s hs => s \ { x, y } ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
            · intro a₁ ha₁ hx₁ hy₁ a₂ ha₂ hx₂ hy₂ h; ext z; by_cases hz : z = x <;> by_cases hz' : z = y <;> simp_all +decide [ Finset.ext_iff ] ;
            · intro b hb; use Insert.insert x ( Insert.insert y b ) ; aesop;
          simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ];
          grind;
        simp_all +decide [ Finset.sum_ite, mul_comm ];
      have h_sum_expand : ∀ s ∈ A.powerset, ∑ x ∈ s, ∑ y ∈ s, (if x < y then (x : ℝ) * (y : ℝ) else 0) = ∑ x ∈ A, ∑ y ∈ A, (if x < y then (if x ∈ s ∧ y ∈ s then (x : ℝ) * (y : ℝ) else 0) else 0) := by
        intro s hs; rw [ ← Finset.sum_subset ( Finset.subset_iff.mpr <| Finset.mem_powerset.mp hs ) ] ; simp +decide [ Finset.sum_ite ] ;
        · refine' Finset.sum_congr rfl fun x hx => _;
          refine' Finset.sum_bij ( fun y hy => y ) _ _ _ _ <;> aesop;
        · aesop;
      rw [ Finset.sum_congr rfl h_sum_expand, Finset.sum_comm ];
      exact Finset.sum_congr rfl fun x hx => by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun y hy => by aesop;
    rw [ ← h_sum_expand, Finset.mul_sum _ _ _ ];
    rw [ ← ‹∑ s ∈ A.powerset, ∑ x ∈ s, ( x : ℝ ) ^ 2 = ∑ a ∈ A, ( a : ℝ ) ^ 2 * 2 ^ ( #A - 1 ) ›, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun s hs => h_expand s <| Finset.mem_powerset.mp hs ];
  rcases k : Finset.card A with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  · unfold Erdos1.second_moment; norm_num;
  · unfold Erdos1.second_moment; simp_all +decide [ Finset.card_eq_one ] ; ring;
    rcases k with ⟨ a, rfl ⟩ ; norm_num [ sq ] ; ring;
    rw [ Finset.sum_eq_single { a } ] <;> aesop;
  · unfold Erdos1.second_moment; norm_num [ Finset.sum_ite, Finset.filter_lt_eq_Ioi ] ; ring;
    simp_all +decide [ sq, Finset.sum_ite, Finset.filter_lt_eq_Ioi ] ; ring;
    norm_num [ ← Finset.sum_mul _ _ _, ← Finset.mul_sum, ← Finset.sum_div ] ; ring;
    simp +zetaDelta at *

/- Aristotle failed to find a proof. -/
/--
Alternative: Show the optimal packing of 2ⁿ integers with given variance
in an interval of size M requires M ≥ √(2πn) · σ asymptotically.
-/
theorem packing_lower_bound (n : ℕ) (points : Fin (2^n) → ℕ)
    (h_distinct : Function.Injective points)
    (M : ℕ) (h_bound : ∀ i, points i ≤ M)
    (σ_sq : ℝ) (h_var : ∑ i, ((points i : ℝ) - (∑ j, (points j : ℝ)) / 2^n)^2 / 2^n ≥ σ_sq) :
    (M : ℝ) ≥ Real.sqrt (2 / π) * Real.sqrt (σ_sq * 2^n) / Real.sqrt n := by
  sorry

end

end Erdos1