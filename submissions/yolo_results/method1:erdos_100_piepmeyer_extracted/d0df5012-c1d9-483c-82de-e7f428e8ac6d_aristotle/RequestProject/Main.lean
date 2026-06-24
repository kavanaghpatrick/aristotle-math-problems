import RequestProject.Defs

set_option maxHeartbeats 4000000

noncomputable section

open Real Finset

/-! ## Basic properties of s2, s3, α -/

lemma s2_pos : 0 < s2 := sqrt_pos.mpr (by norm_num)
lemma s3_pos : 0 < s3 := sqrt_pos.mpr (by norm_num)
lemma s2_ne_zero : s2 ≠ 0 := ne_of_gt s2_pos
lemma s3_ne_zero : s3 ≠ 0 := ne_of_gt s3_pos

lemma s2_sq : s2 ^ 2 = 2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
lemma s3_sq : s3 ^ 2 = 3 := sq_sqrt (by norm_num : (0:ℝ) ≤ 3)

lemma two_sub_s3_pos : 0 < 2 - s3 := by
  nlinarith [s3_sq, sq_nonneg (s3 - 2)]

lemma α_pos : 0 < α := sqrt_pos.mpr two_sub_s3_pos
lemma α_ne_zero : α ≠ 0 := ne_of_gt α_pos
lemma α_sq : α ^ 2 = 2 - s3 := sq_sqrt (le_of_lt two_sub_s3_pos)

lemma t₀_pos : 0 < t₀ := by unfold t₀; exact mul_pos (by linarith [s2_pos]) α_pos
lemma r₀_pos : 0 < r₀ := by unfold r₀; exact div_pos t₀_pos s3_pos
lemma R₀_pos : 0 < R₀ := by unfold R₀; exact add_pos r₀_pos t₀_pos
lemma S₀_pos : 0 < S₀ := by unfold S₀; exact add_pos R₀_pos r₀_pos

-- D values are positive
lemma D₁_pos : 0 < D₁ := by
  unfold D₁; exact mul_pos (by linarith [s2_pos]) two_sub_s3_pos
lemma D₂_pos : 0 < D₂ := by unfold D₂; linarith [s2_pos]
lemma D₃_pos : 0 < D₃ := by unfold D₃; linarith [s2_pos]
lemma D₄_pos : 0 < D₄ := by
  unfold D₄; exact mul_pos (by linarith [s2_pos]) (by linarith [s3_pos])

-- Ordering: D₁ ≤ D₂ ≤ D₃ ≤ D₄
lemma s3_ge_one : s3 ≥ 1 := by
  rw [show (1:ℝ) = √1 from by simp]
  exact sqrt_le_sqrt (by norm_num)

lemma D₁_le_D₂ : D₁ ≤ D₂ := by
  unfold D₁ D₂
  have h : 2 - s3 ≤ 1 := by linarith [s3_ge_one]
  nlinarith [s2_pos]

lemma D₂_le_D₃ : D₂ ≤ D₃ := by unfold D₂ D₃; linarith [s2_pos]

lemma D₃_le_D₄ : D₃ ≤ D₄ := by
  unfold D₃ D₄; nlinarith [s3_pos, s2_pos, mul_pos s2_pos s3_pos]

/-! ## Squared distance classification -/

/-
Inner-inner: dist(P 0, P 1)² = D₁
-/
lemma dist_sq_01 : dist (P 0) (P 1) ^ 2 = D₁ := by
  unfold P D₁; ring;
  rw [ dist_sq_mkPt ] ; ring;
  unfold r₀ t₀ s2 s3 α; ring;
  rw [ Real.sq_sqrt ] <;> norm_num [ s3 ] ; ring;
  rw [ Real.sqrt_le_left ] <;> norm_num

/-
Inner-inner: dist(P 0, P 2)² = D₁
-/
lemma dist_sq_02 : dist (P 0) (P 2) ^ 2 = D₁ := by
  erw [ dist_sq_mkPt ] ; ring;
  unfold D₁; rw [ show r₀ = ( 1 + s2 ) * α / s3 by rfl ] ; ring_nf ; norm_num [ s2_sq, s3_sq, α_sq ] ; ring;

/-
Inner-inner: dist(P 1, P 2)² = D₁
-/
lemma dist_sq_12 : dist (P 1) (P 2) ^ 2 = D₁ := by
  -- Let's calculate the distance between P 1 and P 2.
  simp [P];
  rw [ dist_sq_mkPt, D₁ ] ; ring!; norm_num [ s2_sq, s3_sq, α_sq, s3_ne_zero ] ; ring!;
  unfold r₀ t₀; ring!; norm_num [ s2_sq, s3_sq, α_sq, s3_ne_zero ] ; ring!;

/-
Inner-outer matching: dist(P 0, P 3)² = D₁
-/
lemma dist_sq_03 : dist (P 0) (P 3) ^ 2 = D₁ := by
  convert dist_sq_mkPt 0 r₀ 0 ( r₀ + t₀ ) using 1 ; ring;
  unfold D₁ t₀; ring;
  rw [ α_sq ] ; rw [ s2_sq ] ; ring;

/-
Inner-outer matching: dist(P 1, P 4)² = D₁
-/
lemma dist_sq_14 : dist (P 1) (P 4) ^ 2 = D₁ := by
  convert dist_sq_mkPt _ _ _ _ using 1;
  unfold D₁ R₀ r₀; ring;
  unfold t₀; ring;
  rw [ α_sq, s2_sq, s3_sq ] ; ring

/-
Inner-outer matching: dist(P 2, P 5)² = D₁
-/
lemma dist_sq_25 : dist (P 2) (P 5) ^ 2 = D₁ := by
  convert dist_sq_14 using 1;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;

/-
Inner-outer non-matching: dist(P 0, P 4)² = D₂
-/
lemma dist_sq_04 : dist (P 0) (P 4) ^ 2 = D₂ := by
  unfold P;
  unfold r₀ R₀ D₂;
  unfold t₀ r₀; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  unfold t₀; norm_num [ s2, s3, α ] ; ring;
  rw [ Real.sq_sqrt, Real.sq_sqrt ] <;> try nlinarith [ Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
  · grind;
  · positivity

/-
Inner-outer non-matching: dist(P 0, P 5)² = D₂
-/
lemma dist_sq_05 : dist (P 0) (P 5) ^ 2 = D₂ := by
  -- By definition of $P$, we can see that the coordinates of $P 0$ and $P 5$ are symmetric with respect to the y-axis.
  have h_symm : P 0 = mkPt 0 r₀ ∧ P 5 = mkPt (R₀ * s3 / 2) (-(R₀ / 2)) := by
    exact ⟨ rfl, rfl ⟩;
  convert dist_sq_04 using 1 ; norm_num [ h_symm ] ; ring;
  rw [ show P 4 = mkPt ( - ( R₀ * s3 / 2 ) ) ( - ( R₀ / 2 ) ) from rfl ] ; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;

/-
Inner-outer non-matching: dist(P 1, P 3)² = D₂
-/
lemma dist_sq_13 : dist (P 1) (P 3) ^ 2 = D₂ := by
  unfold P;
  unfold R₀ r₀ t₀ s2 s3 α D₂; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  rw [ Real.sq_sqrt, Real.sq_sqrt ] <;> norm_num [ s2, s3 ];
  · grind;
  · rw [ Real.sqrt_le_left ] <;> norm_num;
  · positivity

/-
Inner-outer non-matching: dist(P 1, P 5)² = D₂
-/
lemma dist_sq_15 : dist (P 1) (P 5) ^ 2 = D₂ := by
  -- By definition of $P$, we know that
  have hP1 : P 1 = mkPt (-(r₀ * s3 / 2)) (-(r₀ / 2)) := by
    rfl
  have hP5 : P 5 = mkPt (R₀ * s3 / 2) (-(R₀ / 2)) := by
    rfl;
  rw [ hP1, hP5, dist_sq_mkPt ];
  unfold D₂; unfold R₀; unfold r₀; unfold t₀; unfold s2 s3 α; ring;
  rw [ Real.sq_sqrt ] <;> norm_num [ s3 ] ; ring;
  · grind;
  · rw [ Real.sqrt_le_left ] <;> norm_num

/-
Inner-outer non-matching: dist(P 2, P 3)² = D₂
-/
lemma dist_sq_23 : dist (P 2) (P 3) ^ 2 = D₂ := by
  convert dist_sq_13 using 1;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ;

/-
Inner-outer non-matching: dist(P 2, P 4)² = D₂
-/
lemma dist_sq_24 : dist (P 2) (P 4) ^ 2 = D₂ := by
  convert dist_sq_23 using 1 ; ring!;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  rw [ show s3 ^ 2 = 3 by rw [ show s3 = Real.sqrt 3 by rfl ] ; norm_num ] ; ring;

/-
Outer-outer: dist(P 3, P 4)² = D₃
-/
lemma dist_sq_34 : dist (P 3) (P 4) ^ 2 = D₃ := by
  unfold P;
  unfold D₃; rw [ dist_eq_norm, EuclideanSpace.norm_eq ] ; norm_num [ Fin.sum_univ_succ ] ; ring;
  rw [ Real.sq_sqrt ( by positivity ) ] ; rw [ show s3 ^ 2 = 3 by exact s3_sq ] ; ring;
  unfold R₀ r₀ t₀; ring; norm_num [ s2_sq, s3_sq, α_sq ] ; ring;
  unfold s2 s3; norm_num; ring;
  rw [ ← Real.sqrt_div_self ] ; ring

/-
Outer-outer: dist(P 3, P 5)² = D₃
-/
lemma dist_sq_35 : dist (P 3) (P 5) ^ 2 = D₃ := by
  convert dist_sq_34 using 1;
  unfold P;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ]

/-
Outer-outer: dist(P 4, P 5)² = D₃
-/
lemma dist_sq_45 : dist (P 4) (P 5) ^ 2 = D₃ := by
  -- By definition of $P$, we know that
  simp [P, D₃];
  convert dist_sq_35 using 1 ; ring!;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  rw [ show s3 ^ 2 = 3 by rw [ show s3 = Real.sqrt 3 by rfl, Real.sq_sqrt ] ; norm_num ] ; ring

/-
Inner-center matching: dist(P 0, P 6)² = D₃
-/
lemma dist_sq_06 : dist (P 0) (P 6) ^ 2 = D₃ := by
  unfold P;
  unfold D₃ r₀ R₀ S₀;
  unfold R₀ r₀ t₀ α s2 s3;
  rw [ dist_eq_norm, EuclideanSpace.norm_eq ] ; norm_num;
  rw [ Real.sq_sqrt ] <;> ring <;> norm_num;
  · rw [ Real.sq_sqrt ] <;> ring;
    · grind;
    · nlinarith [ Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
  · positivity

/-
Inner-center matching: dist(P 1, P 7)² = D₃
-/
lemma dist_sq_17 : dist (P 1) (P 7) ^ 2 = D₃ := by
  convert dist_sq_06 using 1;
  unfold P;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  unfold S₀; ring; norm_num [ s3_sq ] ; ring;

/-
Inner-center matching: dist(P 2, P 8)² = D₃
-/
lemma dist_sq_28 : dist (P 2) (P 8) ^ 2 = D₃ := by
  convert dist_sq_17 using 1;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;

/-
Inner-center non-matching: dist(P 0, P 7)² = D₂
-/
lemma dist_sq_07 : dist (P 0) (P 7) ^ 2 = D₂ := by
  convert dist_sq_mkPt _ _ _ _ using 1;
  unfold D₂ S₀ R₀ r₀ t₀ s2 s3 α; ring;
  unfold s3; norm_num [ ← Real.sqrt_eq_rpow ] ; ring;
  rw [ Real.sq_sqrt ] <;> norm_num;
  · grind;
  · rw [ Real.sqrt_le_left ] <;> norm_num

/-
Inner-center non-matching: dist(P 0, P 8)² = D₂
-/
lemma dist_sq_08 : dist (P 0) (P 8) ^ 2 = D₂ := by
  convert dist_sq_07 using 1;
  unfold P; norm_num [ EuclideanSpace.dist_eq ] ;

/-
Inner-center non-matching: dist(P 1, P 6)² = D₂
-/
lemma dist_sq_16 : dist (P 1) (P 6) ^ 2 = D₂ := by
  convert dist_sq_08 using 1;
  unfold P;
  rw [ dist_sq_mkPt, dist_sq_mkPt ] ; ring;
  rw [ show s3 ^ 2 = 3 by rw [ show s3 = Real.sqrt 3 by rfl, Real.sq_sqrt ] ; norm_num ] ; ring

/-
Inner-center non-matching: dist(P 1, P 8)² = D₂
-/
lemma dist_sq_18 : dist (P 1) (P 8) ^ 2 = D₂ := by
  convert dist_sq_08 using 1;
  unfold P ; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  rw [ show s3 ^ 2 = 3 by exact Real.sq_sqrt <| by norm_num ] ; ring

/-
Inner-center non-matching: dist(P 2, P 6)² = D₂
-/
lemma dist_sq_26 : dist (P 2) (P 6) ^ 2 = D₂ := by
  convert dist_sq_08 using 1 ; ring!;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  rw [ show s3 ^ 2 = 3 by rw [ show s3 = Real.sqrt 3 by rfl, Real.sq_sqrt ] ; norm_num ] ; ring;

/-
Inner-center non-matching: dist(P 2, P 7)² = D₂
-/
lemma dist_sq_27 : dist (P 2) (P 7) ^ 2 = D₂ := by
  unfold P D₂;
  unfold r₀ S₀ R₀ t₀;
  rw [ show r₀ = ( 1 + s2 ) * α / s3 by rfl ] ; ring;
  grind +suggestions

/-
Center-center: dist(P 6, P 7)² = D₄
-/
lemma dist_sq_67 : dist (P 6) (P 7) ^ 2 = D₄ := by
  unfold P;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  unfold S₀ R₀ r₀ t₀ s3 s2 α D₄; ring;
  rw [ Real.sq_sqrt ] <;> norm_num [ s3, s2 ] <;> ring;
  · rw [ Real.sq_sqrt ] <;> norm_num;
    · grind;
    · rw [ Real.sqrt_le_left ] <;> norm_num;
  · positivity

/-
Center-center: dist(P 6, P 8)² = D₄
-/
lemma dist_sq_68 : dist (P 6) (P 8) ^ 2 = D₄ := by
  convert dist_sq_67 using 1;
  unfold P;
  simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ]

/-
Center-center: dist(P 7, P 8)² = D₄
-/
lemma dist_sq_78 : dist (P 7) (P 8) ^ 2 = D₄ := by
  convert dist_sq_68 using 1;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  rw [ show s3 ^ 2 = 3 by rw [ show s3 = Real.sqrt 3 by rfl, Real.sq_sqrt ] ; norm_num ] ; ring

/-
Outer-center matching: dist(P 3, P 6)² = D₄
-/
lemma dist_sq_36 : dist (P 3) (P 6) ^ 2 = D₄ := by
  convert dist_sq_68 using 1 ; ring!;
  unfold P; norm_num [ EuclideanSpace.dist_eq ] ; ring!;
  norm_num [ dist_eq_norm, S₀, R₀, r₀, t₀, s3 ] ; ring!;
  rw [ ← Real.sqrt_sq_eq_abs ] ; ring!; norm_num; ring;

/-
Outer-center matching: dist(P 4, P 7)² = D₄
-/
lemma dist_sq_47 : dist (P 4) (P 7) ^ 2 = D₄ := by
  convert dist_sq_68 using 1;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  unfold R₀ S₀;
  unfold t₀; unfold r₀; unfold R₀; ring;
  unfold t₀; unfold r₀; unfold α; norm_num [ s2_sq, s3_sq ] ; ring;
  unfold t₀; ring;
  unfold α; norm_num [ s2_sq, s3_sq ] ; ring;

/-
Outer-center matching: dist(P 5, P 8)² = D₄
-/
lemma dist_sq_58 : dist (P 5) (P 8) ^ 2 = D₄ := by
  convert dist_sq_47 using 1;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;

/-
Outer-center non-matching: dist(P 3, P 7)² = D₂
-/
lemma dist_sq_37 : dist (P 3) (P 7) ^ 2 = D₂ := by
  unfold P;
  simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sq_sqrt ] <;> ring_nf;
  · unfold D₂ R₀ S₀; ring;
    unfold R₀ r₀ t₀ s3 s2; norm_num; ring;
    rw [ show α = Real.sqrt ( 2 - Real.sqrt 3 ) by rfl, Real.sq_sqrt ] <;> norm_num ; ring;
    · grind;
    · rw [ Real.sqrt_le_left ] <;> norm_num;
  · nlinarith [ sq_nonneg ( S₀ - 2 * R₀ ), show 0 ≤ s3 ^ 2 by positivity ]

/-
Outer-center non-matching: dist(P 3, P 8)² = D₂
-/
lemma dist_sq_38 : dist (P 3) (P 8) ^ 2 = D₂ := by
  convert dist_sq_37 using 1;
  unfold P;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ]

/-
Outer-center non-matching: dist(P 4, P 6)² = D₂
-/
lemma dist_sq_46 : dist (P 4) (P 6) ^ 2 = D₂ := by
  convert dist_sq_38 using 1;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  rw [ show s3 ^ 2 = 3 by exact s3_sq ] ; ring;

/-
Outer-center non-matching: dist(P 4, P 8)² = D₂
-/
lemma dist_sq_48 : dist (P 4) (P 8) ^ 2 = D₂ := by
  convert dist_sq_46 using 1;
  unfold P; norm_num [ EuclideanSpace.dist_eq ] ; ring;
  norm_num [ dist_eq_norm ] ; ring;
  rw [ show s3 ^ 2 = 3 by rw [ show s3 = Real.sqrt 3 by rfl ] ; norm_num ] ; ring;

/-
Outer-center non-matching: dist(P 5, P 6)² = D₂
-/
lemma dist_sq_56 : dist (P 5) (P 6) ^ 2 = D₂ := by
  convert dist_sq_46 using 1;
  unfold P;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ]

/-
Outer-center non-matching: dist(P 5, P 7)² = D₂
-/
lemma dist_sq_57 : dist (P 5) (P 7) ^ 2 = D₂ := by
  convert dist_sq_38 using 1;
  unfold P; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring;
  rw [ show s3 ^ 2 = 3 by rw [ show s3 = Real.sqrt 3 by rfl ] ; norm_num ] ; ring

/-! ## Injectivity of P (all 9 points are distinct) -/

lemma P_injective : Function.Injective P := by
  intro i j hij;
  fin_cases i <;> fin_cases j <;> simp +decide at hij ⊢;
  all_goals unfold P at hij; simp +decide [ mkPt ] at hij;
  any_goals nlinarith [ r₀_pos, R₀_pos, S₀_pos, s3_pos ];
  any_goals rcases hij with ( h | h ) <;> linarith [ r₀_pos, R₀_pos, S₀_pos, s3_pos ];
  all_goals unfold R₀ at hij; linarith [ t₀_pos ] ;

lemma A₀_card : A₀.card = 9 := by
  rw [A₀, card_image_of_injective _ P_injective]
  simp [Finset.card_univ, Fintype.card_fin]

/-! ## Gap conditions -/

lemma D₁_ge_one : D₁ ≥ 1 := by
  unfold D₁
  have h1 : (5+4*s2)^2 - 3*(3+2*s2)^2 = 6 + 4*s2 := by nlinarith [s2_sq]
  have h2 : (s3*(3+2*s2))^2 ≤ (5+4*s2)^2 := by nlinarith [s3_sq, s2_pos]
  have h3 : s3*(3+2*s2) ≤ 5+4*s2 := by
    nlinarith [sq_nonneg (5+4*s2 - s3*(3+2*s2)), s3_pos, s2_pos,
               mul_pos s3_pos (show (0:ℝ) < 3+2*s2 by linarith [s2_pos])]
  nlinarith

lemma D₁_le_two : D₁ ≤ 2 := by
  unfold D₁
  have h1 : 3*(3+2*s2)^2 - (4+4*s2)^2 = 3 + 4*s2 := by nlinarith [s2_sq]
  have h2 : (4+4*s2)^2 ≤ (s3*(3+2*s2))^2 := by nlinarith [s3_sq, s2_pos]
  have h3 : 4+4*s2 ≤ s3*(3+2*s2) := by
    nlinarith [sq_nonneg (s3*(3+2*s2) - (4+4*s2)), s3_pos, s2_pos,
               mul_pos s3_pos (show (0:ℝ) < 3+2*s2 by linarith [s2_pos])]
  nlinarith

lemma D₄_ge_sq : D₄ ≥ (3 + s2) ^ 2 := by
  unfold D₄
  have h1 : 3*(3+2*s2)^2 - (5+2*s2)^2 = 18 + 16*s2 := by nlinarith [s2_sq]
  have h2 : (5+2*s2)^2 ≤ (s3*(3+2*s2))^2 := by nlinarith [s3_sq, s2_pos]
  have h3 : 5+2*s2 ≤ s3*(3+2*s2) := by
    nlinarith [sq_nonneg (s3*(3+2*s2) - (5+2*s2)), s3_pos, s2_pos,
               mul_pos s3_pos (show (0:ℝ) < 3+2*s2 by linarith [s2_pos])]
  nlinarith [s2_sq]

lemma D₄_lt_25 : D₄ < 25 := by
  unfold D₄
  have hs2_lt : s2 < 3/2 := by nlinarith [s2_sq, sq_nonneg (s2 - 3/2)]
  have hs3_lt : s3 < 2 := by nlinarith [s3_sq, sq_nonneg (s3 - 2)]
  have h1 : 3 + 2*s2 < 6 := by linarith
  have h2 : 2 + s3 < 4 := by linarith
  calc (3+2*s2)*(2+s3) < 6*4 := mul_lt_mul h1 (le_of_lt h2) (by linarith [s3_pos]) (by norm_num)
    _ = 24 := by norm_num
    _ < 25 := by norm_num

/-! ## Full distance classification for all pairs -/

/-- Every pairwise squared distance is one of {0, D₁, D₂, D₃, D₄} -/
lemma dist_sq_mem (i j : Fin 9) :
    dist (P i) (P j) ^ 2 ∈ ({0, D₁, D₂, D₃, D₄} : Set ℝ) := by
  fin_cases i <;> fin_cases j <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  -- i=0
  · left; simp [dist_self]
  · right; left; exact dist_sq_01
  · right; left; exact dist_sq_02
  · right; left; exact dist_sq_03
  · right; right; left; exact dist_sq_04
  · right; right; left; exact dist_sq_05
  · right; right; right; left; exact dist_sq_06
  · right; right; left; exact dist_sq_07
  · right; right; left; exact dist_sq_08
  -- i=1
  · right; left; rw [dist_comm]; exact dist_sq_01
  · left; simp [dist_self]
  · right; left; exact dist_sq_12
  · right; right; left; exact dist_sq_13
  · right; left; exact dist_sq_14
  · right; right; left; exact dist_sq_15
  · right; right; left; exact dist_sq_16
  · right; right; right; left; exact dist_sq_17
  · right; right; left; exact dist_sq_18
  -- i=2
  · right; left; rw [dist_comm]; exact dist_sq_02
  · right; left; rw [dist_comm]; exact dist_sq_12
  · left; simp [dist_self]
  · right; right; left; exact dist_sq_23
  · right; right; left; exact dist_sq_24
  · right; left; exact dist_sq_25
  · right; right; left; exact dist_sq_26
  · right; right; left; exact dist_sq_27
  · right; right; right; left; exact dist_sq_28
  -- i=3
  · right; left; rw [dist_comm]; exact dist_sq_03
  · right; right; left; rw [dist_comm]; exact dist_sq_13
  · right; right; left; rw [dist_comm]; exact dist_sq_23
  · left; simp [dist_self]
  · right; right; right; left; exact dist_sq_34
  · right; right; right; left; exact dist_sq_35
  · right; right; right; right; exact dist_sq_36
  · right; right; left; exact dist_sq_37
  · right; right; left; exact dist_sq_38
  -- i=4
  · right; right; left; rw [dist_comm]; exact dist_sq_04
  · right; left; rw [dist_comm]; exact dist_sq_14
  · right; right; left; rw [dist_comm]; exact dist_sq_24
  · right; right; right; left; rw [dist_comm]; exact dist_sq_34
  · left; simp [dist_self]
  · right; right; right; left; exact dist_sq_45
  · right; right; left; exact dist_sq_46
  · right; right; right; right; exact dist_sq_47
  · right; right; left; exact dist_sq_48
  -- i=5
  · right; right; left; rw [dist_comm]; exact dist_sq_05
  · right; right; left; rw [dist_comm]; exact dist_sq_15
  · right; left; rw [dist_comm]; exact dist_sq_25
  · right; right; right; left; rw [dist_comm]; exact dist_sq_35
  · right; right; right; left; rw [dist_comm]; exact dist_sq_45
  · left; simp [dist_self]
  · right; right; left; exact dist_sq_56
  · right; right; left; exact dist_sq_57
  · right; right; right; right; exact dist_sq_58
  -- i=6
  · right; right; right; left; rw [dist_comm]; exact dist_sq_06
  · right; right; left; rw [dist_comm]; exact dist_sq_16
  · right; right; left; rw [dist_comm]; exact dist_sq_26
  · right; right; right; right; rw [dist_comm]; exact dist_sq_36
  · right; right; left; rw [dist_comm]; exact dist_sq_46
  · right; right; left; rw [dist_comm]; exact dist_sq_56
  · left; simp [dist_self]
  · right; right; right; right; exact dist_sq_67
  · right; right; right; right; exact dist_sq_68
  -- i=7
  · right; right; left; rw [dist_comm]; exact dist_sq_07
  · right; right; right; left; rw [dist_comm]; exact dist_sq_17
  · right; right; left; rw [dist_comm]; exact dist_sq_27
  · right; right; left; rw [dist_comm]; exact dist_sq_37
  · right; right; right; right; rw [dist_comm]; exact dist_sq_47
  · right; right; left; rw [dist_comm]; exact dist_sq_57
  · right; right; right; right; rw [dist_comm]; exact dist_sq_67
  · left; simp [dist_self]
  · right; right; right; right; exact dist_sq_78
  -- i=8
  · right; right; left; rw [dist_comm]; exact dist_sq_08
  · right; right; left; rw [dist_comm]; exact dist_sq_18
  · right; right; right; left; rw [dist_comm]; exact dist_sq_28
  · right; right; left; rw [dist_comm]; exact dist_sq_38
  · right; right; left; rw [dist_comm]; exact dist_sq_48
  · right; right; right; right; rw [dist_comm]; exact dist_sq_58
  · right; right; right; right; rw [dist_comm]; exact dist_sq_68
  · right; right; right; right; rw [dist_comm]; exact dist_sq_78
  · left; simp [dist_self]

/-- All pairwise distances are ≤ √D₄ -/
lemma dist_le_sqrt_D₄ (i j : Fin 9) : dist (P i) (P j) ≤ √D₄ := by
  have hmem := dist_sq_mem i j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hnn : 0 ≤ dist (P i) (P j) := dist_nonneg
  have hD₄_sq : √D₄ * √D₄ = D₄ := mul_self_sqrt (le_of_lt D₄_pos)
  suffices h : dist (P i) (P j) ^ 2 ≤ D₄ by
    nlinarith [sq_nonneg (√D₄ - dist (P i) (P j)), sqrt_nonneg D₄]
  rcases hmem with h | h | h | h | h
  all_goals (rw [h])
  · exact le_of_lt D₄_pos
  · exact le_trans D₁_le_D₂ (le_trans D₂_le_D₃ D₃_le_D₄)
  · exact le_trans D₂_le_D₃ D₃_le_D₄
  · exact D₃_le_D₄

/-! ## DistancesSeparated -/

lemma sqrt_D₂_eq : √D₂ = 1 + s2 := by
  rw [show D₂ = (1 + s2)^2 from by unfold D₂; nlinarith [s2_sq]]
  exact sqrt_sq (by linarith [s2_pos])

lemma sqrt_D₃_eq : √D₃ = 2 + s2 := by
  rw [show D₃ = (2 + s2)^2 from by unfold D₃; nlinarith [s2_sq]]
  exact sqrt_sq (by linarith [s2_pos])

/-- dist(P i, P j) is one of {0, √D₁, 1+s2, 2+s2, √D₄} -/
lemma dist_mem_values (i j : Fin 9) :
    dist (P i) (P j) ∈ ({0, √D₁, 1 + s2, 2 + s2, √D₄} : Set ℝ) := by
  have hmem := dist_sq_mem i j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
  have hnn := dist_nonneg (x := P i) (y := P j)
  rcases hmem with h | h | h | h | h
  · left; nlinarith [sq_nonneg (dist (P i) (P j))]
  · right; left
    have : (√D₁)^2 = D₁ := sq_sqrt (le_of_lt D₁_pos)
    nlinarith [sq_nonneg (dist (P i) (P j) - √D₁), sqrt_nonneg D₁]
  · right; right; left
    have : (1+s2)^2 = D₂ := by unfold D₂; nlinarith [s2_sq]
    nlinarith [sq_nonneg (dist (P i) (P j) - (1+s2)), s2_pos]
  · right; right; right; left
    have : (2+s2)^2 = D₃ := by unfold D₃; nlinarith [s2_sq]
    nlinarith [sq_nonneg (dist (P i) (P j) - (2+s2)), s2_pos]
  · right; right; right; right
    have : (√D₄)^2 = D₄ := sq_sqrt (le_of_lt D₄_pos)
    nlinarith [sq_nonneg (dist (P i) (P j) - √D₄), sqrt_nonneg D₄]

/-
Key lemma: the 5 distance values are pairwise separated by ≥ 1
-/
lemma values_separated : ∀ x ∈ ({0, √D₁, 1 + s2, 2 + s2, √D₄} : Set ℝ),
    ∀ y ∈ ({0, √D₁, 1 + s2, 2 + s2, √D₄} : Set ℝ),
    x ≠ y → |x - y| ≥ 1 := by
      -- We'll use that $D₁ \leq 2$ and $D \geq (3 + s2)^2$ to show the gaps.
      have h_gaps : Real.sqrt D₁ ≥ 1 ∧ Real.sqrt D₁ ≤ s2 ∧ Real.sqrt D₄ ≥ 3 + s2 := by
        refine' ⟨ Real.le_sqrt_of_sq_le _, Real.sqrt_le_iff.mpr _, Real.le_sqrt_of_sq_le _ ⟩ <;> norm_num [ D₁, D₄, s2, s3 ]; all_goals nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ];
      -- Let's consider the different cases for x and y.
      intros x hx y hy hxy
      by_cases hx0 : x = 0 ∨ x = Real.sqrt D₁ ∨ x = 1 + s2 ∨ x = 2 + s2 ∨ x = Real.sqrt D₄;
      · grind;
      · aesop

lemma A₀_separated : DistancesSeparated A₀ := by
  intro a ha b hb c hc d hd hne
  rw [A₀] at ha hb hc hd
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := mem_image.mp hb
  obtain ⟨k, _, rfl⟩ := mem_image.mp hc
  obtain ⟨l, _, rfl⟩ := mem_image.mp hd
  exact values_separated _ (dist_mem_values i j) _ (dist_mem_values k l) hne

lemma A₀_diam : Metric.diam (A₀ : Set E2) < 5 := by
  have hlt : √D₄ < 5 := by
    rw [show (5:ℝ) = √25 from by norm_num]
    exact sqrt_lt_sqrt (le_of_lt D₄_pos) D₄_lt_25
  calc Metric.diam (A₀ : Set E2)
      ≤ √D₄ := Metric.diam_le_of_forall_dist_le (sqrt_nonneg _) (fun x hx y hy => by
        rw [A₀] at hx hy
        obtain ⟨i, _, rfl⟩ := Finset.mem_coe.mp hx |> mem_image.mp
        obtain ⟨j, _, rfl⟩ := Finset.mem_coe.mp hy |> mem_image.mp
        exact dist_le_sqrt_D₄ i j)
    _ < 5 := hlt

/-! ## Main theorem -/

theorem erdos_100_piepmeyer :
    ∃ A : Finset E2, A.card = 9 ∧ DistancesSeparated A ∧ Metric.diam (A : Set E2) < 5 :=
  ⟨A₀, A₀_card, A₀_separated, A₀_diam⟩

end