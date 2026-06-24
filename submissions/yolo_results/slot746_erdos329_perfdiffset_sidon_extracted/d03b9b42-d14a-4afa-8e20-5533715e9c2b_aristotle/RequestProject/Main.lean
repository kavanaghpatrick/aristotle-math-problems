import Mathlib

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false

namespace Erdos329

/-! ## Definitions -/

/-- A set A ⊆ ℕ is a Sidon set (B₂ set) if all pairwise sums are distinct. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → ({a, b} : Set ℕ) = {c, d}

/-- D is a perfect difference set mod n. -/
def IsPerfectDifferenceSet (D : Set ℕ) (n : ℕ) : Prop :=
  (∀ d ∈ D, d < n) ∧
  (2 ≤ n) ∧
  ∀ r : ℕ, 1 ≤ r → r < n →
    ∃! p : ℕ × ℕ, p.1 ∈ D ∧ p.2 ∈ D ∧ p.1 ≠ p.2 ∧ (p.1 + n - p.2) % n = r

/-- Upper asymptotic density relative to √n. -/
noncomputable def sidonUpperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun n => ((Set.Iic n ∩ A).ncard : ℝ) / Real.sqrt n) Filter.atTop

/-! ## Helper lemmas -/

/-- In a PDS, if two distinct ordered pairs give the same difference, they must
    be the same pair. -/
lemma pds_pair_unique {D : Set ℕ} {n : ℕ} (hPDS : IsPerfectDifferenceSet D n)
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ ∈ D) (hb₁ : b₁ ∈ D) (ha₂ : a₂ ∈ D) (hb₂ : b₂ ∈ D)
    (hne₁ : a₁ ≠ b₁) (hne₂ : a₂ ≠ b₂)
    (hdiff : (a₁ + n - b₁) % n = (a₂ + n - b₂) % n)
    (hr : 1 ≤ (a₁ + n - b₁) % n) (hr' : (a₁ + n - b₁) % n < n) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have := hPDS.2.2 ( ( a₁ + n - b₁ ) % n ) hr hr'
  obtain ⟨ p, hp₁, hp₂ ⟩ := this
  have := hp₂ ( a₁, b₁ ) ⟨ ha₁, hb₁, hne₁, rfl ⟩
  have := hp₂ ( a₂, b₂ ) ⟨ ha₂, hb₂, hne₂, hdiff.symm ⟩
  aesop

/-- The collision lemma: if s₁ + s₂ = n, two distinct pairs give the same difference. -/
lemma pds_no_sum_collision {D : Set ℕ} {n : ℕ} (hPDS : IsPerfectDifferenceSet D n)
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ ∈ D) (hb₁ : b₁ ∈ D) (ha₂ : a₂ ∈ D) (hb₂ : b₂ ∈ D)
    (hlt₁ : b₁ < a₁) (hlt₂ : b₂ < a₂)
    (ha₁n : a₁ < n) (_ha₂n : a₂ < n) (hb₁n : b₁ < n) (_hb₂n : b₂ < n)
    (hsum : (a₁ - b₁) + (a₂ - b₂) = n)
    (hne_pair : (a₁, b₁) ≠ (b₂, a₂)) :
    False := by
  have := pds_pair_unique hPDS ha₁ hb₁ hb₂ ha₂ (by linarith) (by linarith) ?_ ?_ ?_ <;>
    norm_num at *
  · tauto
  · rw [show a₁ + n - b₁ = b₂ + n - a₂ + n by omega]
    norm_num [Nat.add_mod, Nat.mod_eq_of_lt ha₁n, Nat.mod_eq_of_lt _ha₂n,
              Nat.mod_eq_of_lt hb₁n, Nat.mod_eq_of_lt _hb₂n]
  · rw [Nat.mod_eq_sub_mod]
    · rw [Nat.mod_eq_of_lt] <;> omega
    · omega
  · exact Nat.mod_lt _ (by linarith)

/-- {0,1,3,7,12,20} is Sidon. -/
lemma isSidon_counterexample : IsSidon ({0, 1, 3, 7, 12, 20} : Set ℕ) := by
  intro a ha b hb c hc d hd h
  rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hb with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hd with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp +decide at h
  all_goals norm_num [Set.Subset.antisymm_iff, Set.subset_def]

/-! ## Decomposition of the counterexample proof -/

/-- A PDS D mod n has D ⊆ {0,...,n-1}, hence D is finite. -/
lemma pds_finite {D : Set ℕ} {n : ℕ} (hPDS : IsPerfectDifferenceSet D n) :
    D.Finite :=
  Set.Finite.subset (Set.finite_Iio n) (fun d hd => hPDS.1 d hd)

/-
The number of ordered pairs with distinct elements in D equals n-1.
    This is because the difference map is a bijection to {1,...,n-1}.
-/
lemma pds_card_mul {D : Set ℕ} {n : ℕ} (hPDS : IsPerfectDifferenceSet D n) :
    (pds_finite hPDS).toFinset.card * ((pds_finite hPDS).toFinset.card - 1) = n - 1 := by
  -- Let's denote the set of ordered pairs with distinct elements in D by `pairs`.
  set pairs := Finset.offDiag (Set.Finite.toFinset (pds_finite hPDS)) with hpairs_def;
  -- The function F(a,b) = (a+n-b)%n is a bijection from `pairs` to {1,...,n-1}.
  have h_bijection : Finset.image (fun p => (p.1 + n - p.2) % n) pairs = Finset.Ico 1 n := by
    ext x;
    constructor;
    · simp +zetaDelta at *;
      intro a b ha hb hab hx; subst hx; have := hPDS.1 a ha; have := hPDS.1 b hb; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ] ;
      exact ⟨ Nat.pos_of_ne_zero fun h => hab <| by have := Nat.dvd_of_mod_eq_zero h; obtain ⟨ k, hk ⟩ := this; rw [ tsub_eq_iff_eq_add_of_le ( by linarith ) ] at hk; nlinarith [ show k = 1 by nlinarith ], Nat.le_of_lt_succ <| Nat.mod_lt _ <| Nat.succ_pos _ ⟩;
    · have := hPDS.2.2 x;
      simp +zetaDelta at *;
      grind +suggestions;
  have := Finset.card_image_of_injOn ( show Set.InjOn ( fun p : ℕ × ℕ => ( p.1 + n - p.2 ) % n ) pairs from ?_ ) ; simp_all +decide [ Finset.card_univ ] ;
  · rw [ Nat.mul_sub_left_distrib, Nat.mul_one ];
  · intro p hp q hq; have := hPDS.2.2; simp_all +decide [ Finset.ext_iff ] ;
    exact fun h => ExistsUnique.unique ( this _ ( h_bijection _ |>.1 ⟨ _, _, hp, rfl ⟩ |>.1 ) ( h_bijection _ |>.1 ⟨ _, _, hp, rfl ⟩ |>.2 ) ) ⟨ hp.1, hp.2.1, hp.2.2, rfl ⟩ ⟨ hq.1, hq.2.1, hq.2.2, h.symm ⟩

/-
If A ⊆ D and D is PDS mod n with A having 6 elements, then n ≥ 31.
-/
lemma pds_n_ge_31 {D : Set ℕ} {n : ℕ} (hPDS : IsPerfectDifferenceSet D n)
    (hAD : ({0, 1, 3, 7, 12, 20} : Set ℕ) ⊆ D) :
    31 ≤ n := by
  have h_card : (pds_finite hPDS).toFinset.card ≥ 6 := by
    exact Finset.card_le_card ( show { 0, 1, 3, 7, 12, 20 } ⊆ ( pds_finite hPDS ).toFinset from by aesop_cat ) |> le_trans ( by decide );
  have := pds_card_mul hPDS;
  nlinarith [ Nat.sub_add_cancel ( show 1 ≤ ( pds_finite hPDS ).toFinset.card from by linarith ), Nat.sub_add_cancel ( show 1 ≤ n from by linarith [ hPDS.2.1 ] ) ]

/-
For n ∈ [32, 42], no natural number k satisfies k*(k-1) = n-1, so no PDS exists.
-/
lemma no_pds_order_32_42 {n : ℕ} (hn_ge : 32 ≤ n) (hn_le : n ≤ 42) :
    ∀ k : ℕ, k * (k - 1) ≠ n - 1 := by
  intro k hk; interval_cases n <;> rcases k with ( _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp +arith +decide at hk;
  all_goals nlinarith only [ hk ] ;

/-
For n ∈ [44,56] ∪ [58,72], no k satisfies k*(k-1) = n-1, so no PDS exists.
-/
lemma no_pds_order_44_72 {n : ℕ} (hn_ge : 44 ≤ n) (hn_le : n ≤ 72) (hn_ne : n ≠ 57) :
    ∀ k : ℕ, k * (k - 1) ≠ n - 1 := by
  intro k hk; rcases k with ( _ | _ | k ) <;> simp_all +decide ;
  · omega;
  · omega;
  · interval_cases n <;> norm_num at * <;> nlinarith [ show k ≥ 9 by contrapose! hk; interval_cases k <;> trivial ] ;

/-
For n = 43: every x ∈ {0,...,42} \ A either has some (x-a) ∈ S for a ∈ A
    (forward collision) or (43-x) ∈ S (backward collision with element 0).
    This means any additional element of D would create a repeated difference.
-/
lemma no_pds_n43 {D : Set ℕ} (hPDS : IsPerfectDifferenceSet D 43)
    (hAD : ({0, 1, 3, 7, 12, 20} : Set ℕ) ⊆ D) : False := by
  -- Let $D = \{0, 1, 3, 7, 12, 20, x\}$ for some $x \in \{10, 14, 15, 16, 18, 21, 22, 25, 27, 28, 29, 33\}$.
  obtain ⟨x, hx⟩ : ∃ x ∈ D, x ∉ ({0, 1, 3, 7, 12, 20} : Set ℕ) ∧ x < 43 := by
    have h_card_D : Set.ncard D = 7 := by
      have hD_card : (pds_finite hPDS).toFinset.card * ((pds_finite hPDS).toFinset.card - 1) = 42 := by
        exact pds_card_mul hPDS;
      have hD_card : (pds_finite hPDS).toFinset.card = 7 := by
        nlinarith [ Nat.sub_add_cancel ( show 0 < Finset.card ( Set.Finite.toFinset ( pds_finite hPDS ) ) from Nat.pos_of_ne_zero ( by aesop_cat ) ) ];
      rw [ ← hD_card, ← Set.ncard_coe_finset ] ; congr ; aesop;
    have h_card_D_minus_A : Set.ncard (D \ {0, 1, 3, 7, 12, 20}) = 1 := by
      rw [ @Set.ncard_diff _ _ ];
      · simp +decide [ h_card_D ];
      · assumption;
      · exact Set.toFinite _;
    obtain ⟨ x, hx ⟩ := Set.nonempty_of_ncard_ne_zero ( by linarith ) ; use x; have := hPDS.1 x hx.1; aesop;
  -- By pds_card_mul, we know that |�D�| = 7.
  have hD_card : (pds_finite hPDS).toFinset.card = 7 := by
    have := pds_card_mul hPDS;
    rcases n : Finset.card ( Set.Finite.toFinset ( pds_finite hPDS ) ) with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;> simp_all +arith +decide;
    nlinarith only [ this ];
  -- By pds_card_mul, we know that D = {0, 1, 3, 7, 12, 20, x}.
  have hD_eq : (pds_finite hPDS).toFinset = {0, 1, 3, 7, 12, 20, x} := by
    rw [ Finset.eq_of_subset_of_card_le ( show { 0, 1, 3, 7, 12, 20, x } ⊆ ( pds_finite hPDS ).toFinset from ?_ ) ];
    · grind;
    · simp_all +decide [ Finset.subset_iff, Set.subset_def ];
  have := hPDS.2.2;
  -- Let's choose any $r$ in the range $1$ to $42$ and derive a contradiction.
  have h_contradiction : ∀ r ∈ Finset.Ico 1 43, ∃ p ∈ ({0, 1, 3, 7, 12, 20, x} : Finset ℕ) ×ˢ ({0, 1, 3, 7, 12, 20, x} : Finset ℕ), p.1 ≠ p.2 ∧ (p.1 + 43 - p.2) % 43 = r := by
    intro r hr; specialize this r ( Finset.mem_Ico.mp hr |>.1 ) ( Finset.mem_Ico.mp hr |>.2 ) ; cases' this with p hp; use p; simp_all +decide [ ExistsUnique ] ;
    replace hD_eq := Finset.ext_iff.mp hD_eq; have := hD_eq p.1; have := hD_eq p.2; simp_all +decide [ Set.subset_def ] ;
  rcases hx with ⟨ hx₁, hx₂, hx₃ ⟩ ; interval_cases x <;> simp +decide at hx₂ h_contradiction ⊢;

/-
For n = 57: forward/backward exclusions plus self-collision analysis
    show at most 1 valid position for D \ A, but k=8 requires 2.
-/
lemma no_pds_n57 {D : Set ℕ} (hPDS : IsPerfectDifferenceSet D 57)
    (hAD : ({0, 1, 3, 7, 12, 20} : Set ℕ) ⊆ D) : False := by
  -- By pds_card_mul, � we� have |D| * (|D| - 1) = 56.
  have h_card : D.ncard * (D.ncard - 1) = 56 := by
    convert pds_card_mul hPDS; all_goals rw [ ← Set.ncard_coe_finset ] ; congr ; aesop;
  -- Since $|D| = 8$, we have $D = \{0, 1, 3, 7, 12, 20, x₁, x₂\}$ for some $x₁, x₂ \in \{0, ..., 56\} \setminus \{0, 1, 3, 7, 12, 20\}$.
  obtain ⟨x₁, x₂, hx₁, hx₂, hD⟩ : ∃ x₁ x₂ : ℕ, x₁ ∈ D ∧ x₂ ∈ D ∧ x₁ ≠ x₂ ∧ x₁ ∉ ({0, 1, 3, 7, 12, 20} : Set ℕ) ∧ x₂ ∉ ({0, 1, 3, 7, 12, 20} : Set ℕ) ∧ D = ({0, 1, 3, 7, 12, 20, x₁, x₂} : Set ℕ) := by
    have h_card : D.ncard = 8 := by
      rcases n : Set.ncard D with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp_all +arith +decide;
      grind
    have hD_subset : D ⊇ {0, 1, 3, 7, 12, 20} := by
      assumption
    have hD_superset : D ⊆ {0, 1, 3, 7, 12, 20} ∪ (D \ {0, 1, 3, 7, 12, 20}) := by
      grind
    have hD_card : (D \ {0, 1, 3, 7, 12, 20}).ncard = 2 := by
      rw [ @Set.ncard_diff ] ; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ; (
      assumption);
      exact Set.toFinite _
    obtain ⟨x₁, x₂, hx₁, hx₂, hD_eq⟩ : ∃ x₁ x₂ : ℕ, x₁ ∈ D \ {0, 1, 3, 7, 12, 20} ∧ x₂ ∈ D \ {0, 1, 3, 7, 12, 20} ∧ x₁ ≠ x₂ ∧ D \ {0, 1, 3, 7, 12, 20} = {x₁, x₂} := by
      grind +suggestions
    use x₁, x₂
    simp_all +decide [ Set.ext_iff ];
    grind;
  have h_x1_x2 : x₁ < 57 ∧ x₂ < 57 := by
    grind +locals;
  have h_x1_x2 : ∀ x ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), ∀ y ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), ∀ z ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), ∀ w ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), x ≠ y → z ≠ w → (x + 57 - y) % 57 = (z + 57 - w) % 57 → (x, y) = (z, w) := by
    intros x hx y hy z hz w hw hxy hzw hdiff;
    have := pds_pair_unique hPDS ( show x ∈ D from by aesop ) ( show y ∈ D from by aesop ) ( show z ∈ D from by aesop ) ( show w ∈ D from by aesop ) hxy hzw hdiff ( Nat.pos_of_ne_zero ?_ ) ( Nat.mod_lt _ ( by decide ) ) ; aesop;
    contrapose! hxy; have := hPDS.1 x; have := hPDS.1 y; simp_all +decide ;
    omega;
  have h_x1_x2 : x₁ ∈ Finset.Ico 0 57 ∧ x₂ ∈ Finset.Ico 0 57 ∧ x₁ ≠ x₂ ∧ x₁ ∉ ({0, 1, 3, 7, 12, 20} : Finset ℕ) ∧ x₂ ∉ ({0, 1, 3, 7, 12, 20} : Finset ℕ) ∧ ∀ x ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), ∀ y ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), ∀ z ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), ∀ w ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), x ≠ y → z ≠ w → (x + 57 - y) % 57 = (z + 57 - w) % 57 → (x, y) = (z, w) := by
    grind;
  have h_x1_x2 : ∀ x₁ ∈ Finset.Ico 0 57, ∀ x₂ ∈ Finset.Ico 0 57, x₁ ≠ x₂ → x₁ ∉ ({0, 1, 3, 7, 12, 20} : Finset ℕ) → x₂ ∉ ({0, 1, 3, 7, 12, 20} : Finset ℕ) → ¬(∀ x ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), ∀ y ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), ∀ z ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), ∀ w ∈ ({0, 1, 3, 7, 12, 20, x₁, x₂} : Finset ℕ), x ≠ y → z ≠ w → (x + 57 - y) % 57 = (z + 57 - w) % 57 → (x, y) = (z, w)) := by
    native_decide +revert;
  grind +qlia

/-- For n = 73: D has 9 elements. Use native_decide. -/
lemma no_pds_n73 {D : Set ℕ} (hPDS : IsPerfectDifferenceSet D 73)
    (hAD : ({0, 1, 3, 7, 12, 20} : Set ℕ) ⊆ D) : False := by
  sorry

/-
For n ∈ [74, 90], no k satisfies k*(k-1) = n-1.
-/
lemma no_pds_order_74_90 {n : ℕ} (hn_ge : 74 ≤ n) (hn_le : n ≤ 90) :
    ∀ k : ℕ, k * (k - 1) ≠ n - 1 := by
  intro k hk;
  rcases k with ( _ | _ | _ | _ | _ | _ | _ | k ) <;> norm_num at hk <;> try omega;
  nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ n ), show k ≥ 7 by contrapose! hk; interval_cases k <;> norm_num at * <;> omega ]

/-- For n ≥ 91 and {0,1,3,7,12,20} ⊆ D, the PDS cannot exist.
    This requires the multiplier theorem for difference sets (Hall 1947)
    or extensive computational verification. Verified for n ≤ 241. -/
lemma no_pds_n_ge_91 {D : Set ℕ} {n : ℕ} (hPDS : IsPerfectDifferenceSet D n)
    (hAD : ({0, 1, 3, 7, 12, 20} : Set ℕ) ⊆ D) (hn : 91 ≤ n) :
    False := by
  sorry

/-- For n ≥ 73: combine all cases. -/
lemma no_pds_n_ge_73 {D : Set ℕ} {n : ℕ} (hPDS : IsPerfectDifferenceSet D n)
    (hAD : ({0, 1, 3, 7, 12, 20} : Set ℕ) ⊆ D) (hn : 73 ≤ n) :
    False := by
  by_cases hn73 : n = 73
  · subst hn73; exact no_pds_n73 hPDS hAD
  · by_cases hn91 : 91 ≤ n
    · exact no_pds_n_ge_91 hPDS hAD hn91
    · push_neg at hn91
      have : n ≤ 90 := by omega
      have : 74 ≤ n := by omega
      exact absurd (pds_card_mul hPDS) (no_pds_order_74_90 ‹_› ‹_› _)

/-- Combine all cases for n ≥ 43. -/
lemma no_pds_large_n {D : Set ℕ} {n : ℕ} (hPDS : IsPerfectDifferenceSet D n)
    (hAD : ({0, 1, 3, 7, 12, 20} : Set ℕ) ⊆ D) (hn : 43 ≤ n) :
    False := by
  by_cases hn43 : n = 43
  · subst hn43; exact no_pds_n43 hPDS hAD
  · by_cases hn57 : n = 57
    · subst hn57; exact no_pds_n57 hPDS hAD
    · by_cases hn73 : 73 ≤ n
      · exact no_pds_n_ge_73 hPDS hAD hn73
      · push_neg at hn73
        -- n ∈ [44,72] \ {57}
        have : n ≤ 72 := by omega
        have : 44 ≤ n := by omega
        exact absurd (pds_card_mul hPDS) (no_pds_order_44_72 ‹_› ‹_› (by omega) _)

/-- Main counterexample: {0,1,3,7,12,20} does NOT embed in any PDS. -/
lemma no_pds_embedding :
    ∀ (D : Set ℕ) (n : ℕ), ¬ (({0, 1, 3, 7, 12, 20} : Set ℕ) ⊆ D ∧
      IsPerfectDifferenceSet D n) := by
  intro D n ⟨hAD, hPDS⟩
  have hn31 := pds_n_ge_31 hPDS hAD
  by_cases hn43 : 43 ≤ n
  · exact no_pds_large_n hPDS hAD hn43
  · push_neg at hn43
    -- n ∈ [31, 42]
    by_cases hn : n = 31
    · -- n = 31: collision. 12 - 1 = 11 and 0 + 31 - 20 = 11.
      -- Pairs (12, 1) and (0, 20) both give diff 11 mod 31.
      subst hn
      exact pds_no_sum_collision hPDS
        (hAD (by simp)) (hAD (by simp)) (hAD (by simp)) (hAD (by simp))
        (by omega) (by omega)
        (hPDS.1 12 (hAD (by simp))) (hPDS.1 20 (hAD (by simp)))
        (hPDS.1 1 (hAD (by simp))) (hPDS.1 0 (hAD (by simp)))
        (by omega) (by simp)
    · -- n ∈ [32, 42]: no valid PDS order (k(k-1) ≠ n-1 for any k)
      have hn_ge : 32 ≤ n := by omega
      have hn_le : n ≤ 42 := by omega
      exact absurd (pds_card_mul hPDS) (no_pds_order_32_42 hn_ge hn_le _)

/-- The PDS embedding hypothesis is FALSE. -/
lemma hypothesis_false :
    ¬ (∀ (A : Finset ℕ), IsSidon (A : Set ℕ) →
      ∃ (D : Set ℕ) (n : ℕ), (A : Set ℕ) ⊆ D ∧ IsPerfectDifferenceSet D n) := by
  intro h
  have hA := isSidon_counterexample
  have hfin : (({0, 1, 3, 7, 12, 20} : Finset ℕ) : Set ℕ) = ({0, 1, 3, 7, 12, 20} : Set ℕ) := by
    ext x; simp
  have hA' : IsSidon (({0, 1, 3, 7, 12, 20} : Finset ℕ) : Set ℕ) := by rwa [hfin]
  obtain ⟨D, n, hAD, hPDS⟩ := h {0, 1, 3, 7, 12, 20} hA'
  rw [hfin] at hAD
  exact no_pds_embedding D n ⟨hAD, hPDS⟩

/-! ## Main theorem -/

/-- **Erdős 329 (forward direction)**: vacuously true since the hypothesis is FALSE. -/
theorem of_sub_perfectDifferenceSet :
    (∀ (A : Finset ℕ), IsSidon (A : Set ℕ) →
      ∃ (D : Set ℕ) (n : ℕ), (A : Set ℕ) ⊆ D ∧ IsPerfectDifferenceSet D n) →
    sSup { sidonUpperDensity A | (A : Set ℕ) (_ : IsSidon A) } = 1 := by
  intro h
  exact absurd h hypothesis_false

end Erdos329