import Mathlib

set_option maxHeartbeats 800000

open Classical

namespace LeinsterGroup

/-- The sum of orders of all normal subgroups of a finite group. -/
noncomputable def normalSubgroupOrderSum (G : Type*) [Group G] [Fintype G] : ℕ :=
  ∑ H : {H : Subgroup G // H.Normal}, Fintype.card ↥H.val

/-- A Leinster group is a finite group where the sum of orders of its normal
subgroups equals twice its order. -/
def IsLeinster (G : Type*) [Group G] [Fintype G] : Prop :=
  normalSubgroupOrderSum G = 2 * Fintype.card G

end LeinsterGroup

/-! ### Coprime product decomposition of normal subgroups

The key theorem: for finite groups G, H with coprime orders,
every normal subgroup of G × H is a product N × M of normal subgroups.
-/

section CoprimeProd

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]

/-
If `K` is a normal subgroup of `G × H` and the orders are coprime,
and `(g, h) ∈ K`, then `(g, 1) ∈ K`. This uses the coprimality: since
`(g, h)^|H| = (g^|H|, 1) ∈ K` and `gcd(|H|, orderOf g) = 1` (as
`orderOf g ∣ |G|`), we get `g ∈ zpowers (g^|H|)`, hence `(g, 1) ∈ K`.
-/
lemma fst_one_mem_of_mem_coprime
    (K : Subgroup (G × H))
    (hcop : Nat.Coprime (Fintype.card G) (Fintype.card H))
    {g : G} {h : H} (hgh : (g, h) ∈ K) :
    (g, (1 : H)) ∈ K := by
  -- Since $g$ and $h$ have coprime orders, there exist integers $a$ and $b$ such that $a \cdot |H| + b \cdot \text{orderOf}(g) = 1$.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (Fintype.card H) + b * (orderOf g) = 1 := by
    have h_coprime : Nat.Coprime (Fintype.card H) (orderOf g) := by
      exact hcop.symm.coprime_dvd_right ( orderOf_dvd_card );
    exact Int.isCoprime_iff_gcd_eq_one.mpr ( mod_cast h_coprime );
  have h_g_pow : (g ^ (Fintype.card H), 1) ∈ K := by
    simpa [ pow_card_eq_one ] using K.pow_mem hgh ( Fintype.card H );
  convert K.zpow_mem h_g_pow a using 1 ; simp +decide [ ← zpow_natCast, ← zpow_mul, hab ];
  rw [ show ( Fintype.card H : ) * a = 1 - b * orderOf g by linarith, zpow_sub, zpow_mul ] ; simp +decide [ pow_orderOf_eq_one ]

/-
Symmetric version: if `(g, h) ∈ K` and orders are coprime, then `(1, h) ∈ K`.
-/
lemma one_snd_mem_of_mem_coprime
    (K : Subgroup (G × H))
    (hcop : Nat.Coprime (Fintype.card G) (Fintype.card H))
    {g : G} {h : H} (hgh : (g, h) ∈ K) :
    ((1 : G), h) ∈ K := by
  -- Since $(g, h) \in K$, we have $(g^{Fintype.card G}, h^{Fintype.card G}) \in K$.
  have hgh_pow : (g ^ Fintype.card G, h ^ Fintype.card G) ∈ K := by
    simpa using K.pow_mem hgh ( Fintype.card G );
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * Fintype.card G + b * Fintype.card H = 1 := by
    exact Int.isCoprime_iff_gcd_eq_one.symm.mp ( mod_cast hcop );
  convert K.zpow_mem hgh_pow a using 1;
  rw [ ← eq_sub_iff_add_eq' ] at hab ; replace hab := congr_arg ( fun x : ℤ => h ^ x ) hab ; simp_all +decide [ zpow_add, zpow_mul ];
  simp_all +decide [ zpow_sub, zpow_mul' ];
  simpa using eq_inv_of_mul_eq_one_left hab.symm

/-
For coprime finite groups, every normal subgroup of G × H is a product.
The proof: if (g, h) ∈ (K.map fst).prod (K.map snd), then g ∈ K.map fst
so ∃ h', (g, h') ∈ K, and h ∈ K.map snd so ∃ g', (g', h) ∈ K.
By coprimality, (g, 1) ∈ K and (1, h) ∈ K, so (g, h) ∈ K.
-/
theorem normal_subgroup_of_coprime_prod
    (hcop : Nat.Coprime (Fintype.card G) (Fintype.card H))
    (K : Subgroup (G × H)) :
    K = (K.map (MonoidHom.fst G H)).prod (K.map (MonoidHom.snd G H)) := by
  ext ⟨x, y⟩; simp [Subgroup.mem_prod];
  refine' ⟨ fun h => ⟨ ⟨ y, h ⟩, ⟨ x, h ⟩ ⟩, fun ⟨ ⟨ y', hy' ⟩, ⟨ x', hx' ⟩ ⟩ => _ ⟩;
  convert K.mul_mem ( fst_one_mem_of_mem_coprime K hcop hy' ) ( one_snd_mem_of_mem_coprime K hcop hx' ) using 1 ; simp +decide [ mul_assoc ]

end CoprimeProd

/-! ### Normal subgroups of DihedralGroup 3 -/

section DihedralNormal

/-
The rotation subgroup of DihedralGroup 3, consisting of {r 0, r 1, r 2}.
-/
def DihedralGroup.rotationSubgroup : Subgroup (DihedralGroup 3) where
  carrier := Set.range DihedralGroup.r
  mul_mem' := by
    simp +decide [ Set.mem_range ]
  one_mem' := by
    exists 0
  inv_mem' := by
    simp +decide

noncomputable instance : Fintype DihedralGroup.rotationSubgroup :=
  Fintype.ofFinite _

instance : DihedralGroup.rotationSubgroup.Normal where
  conj_mem := by
    simp +decide [ DihedralGroup.rotationSubgroup ]

/-
The rotation subgroup has order 3.
-/
lemma DihedralGroup.card_rotationSubgroup :
    Fintype.card DihedralGroup.rotationSubgroup = 3 := by
  simp +decide [ rotationSubgroup ]

/-
If a normal subgroup of D_3 contains any reflection sr i, it contains all
reflections and all rotations, hence equals ⊤.
-/
lemma DihedralGroup.normal_with_sr_eq_top
    (N : Subgroup (DihedralGroup 3)) (hN : N.Normal)
    (i : ZMod 3) (hi : DihedralGroup.sr i ∈ N) :
    N = ⊤ := by
  refine' eq_top_iff.mpr fun x hx => _;
  -- Since N is normal and contains a reflection, it must contain all reflections.
  have h_refl : ∀ j : ZMod 3, sr j ∈ N := by
    intro j;
    convert hN.conj_mem _ hi ( r ( j - i ) ) using 1;
    fin_cases i <;> fin_cases j <;> rfl;
  -- Since N is normal and contains all reflections, it must also contain all rotations.
  have h_rot : ∀ j : ZMod 3, r j ∈ N := by
    intro j; have := N.mul_mem ( h_refl j ) ( h_refl 0 ) ; simp_all +decide [ Subgroup.mul_mem_cancel_left, Subgroup.mul_mem_cancel_right ] ;
    convert N.inv_mem this using 1 ; fin_cases j <;> rfl;
  rcases x with ( _ | _ | _ | _ | _ | _ | x ) <;> tauto

/-
Every subgroup of rotationSubgroup is either ⊥ or rotationSubgroup itself
(since it has prime order 3).
-/
lemma DihedralGroup.le_rot_eq_bot_or_rot
    (N : Subgroup (DihedralGroup 3)) (hle : N ≤ DihedralGroup.rotationSubgroup) :
    N = ⊥ ∨ N = DihedralGroup.rotationSubgroup := by
  have h_prime : Nat.card N = 1 ∨ Nat.card N = 3 := by
    -- Since N is a subgroup of rotation �Sub�group, which has order 3, the possible orders of N are the divisors of 3.
    have h_div : Nat.card N ∣ 3 := by
      -- Since $N$ is a � subgroup� of the rotation subgroup, its order must divide the order of the rotation subgroup, which is 3.
      have h_div : Nat.card N ∣ Nat.card DihedralGroup.rotationSubgroup := by
        convert Subgroup.card_dvd_of_le hle;
      convert h_div using 1;
      convert DihedralGroup.card_rotationSubgroup.symm;
      convert Nat.card_eq_fintype_card;
    rwa [ Nat.dvd_prime Nat.prime_three ] at h_div;
  cases h_prime <;> simp_all +decide [ Nat.card_eq_fintype_card ];
  · rw [ Fintype.card_eq_one_iff ] at * ; aesop;
  · have h_eq : Fintype.card N = Fintype.card DihedralGroup.rotationSubgroup := by
      linarith [ DihedralGroup.card_rotationSubgroup ];
    rw [ Fintype.card_subtype, Fintype.card_subtype ] at h_eq;
    exact Or.inr <| by ext x; exact ⟨ fun hx => hle hx, fun hx => by_contra fun hx' => absurd h_eq <| ne_of_lt <| Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.mpr ⟨ fun y hy => by aesop, fun h => by have := Finset.mem_filter.mp ( h.symm ▸ Finset.mem_filter.mpr ⟨ Finset.mem_univ x, hx ⟩ ) ; aesop ⟩ ⟩ ;

/-
Every element of DihedralGroup 3 is either a rotation or a reflection.
-/
lemma DihedralGroup.mem_rot_or_sr
    (x : DihedralGroup 3) :
    x ∈ DihedralGroup.rotationSubgroup ∨ ∃ i : ZMod 3, x = DihedralGroup.sr i := by
  cases x <;> simp +decide [ rotationSubgroup ]

/-
Every normal subgroup of DihedralGroup 3 is one of ⊥, rotationSubgroup, or ⊤.
-/
lemma DihedralGroup.normal_eq_bot_or_rot_or_top
    (N : Subgroup (DihedralGroup 3)) (hN : N.Normal) :
    N = ⊥ ∨ N = DihedralGroup.rotationSubgroup ∨ N = ⊤ := by
  -- Since $N$ is normal, if it contains a reflection, it must be the whole group.
  by_cases h_refl : ∃ i : ZMod 3, DihedralGroup.sr i ∈ N;
  · exact Or.inr <| Or.inr <| DihedralGroup.normal_with_sr_eq_top N hN _ h_refl.choose_spec;
  · -- Since $N$ does not contain any reflections, every element of $N$ must be a rotation.
    have h_rot : ∀ x ∈ N, x ∈ DihedralGroup.rotationSubgroup := by
      intro x hx; have := DihedralGroup.mem_rot_or_sr x; aesop;
    exact Or.imp id ( Or.inl ) ( DihedralGroup.le_rot_eq_bot_or_rot N h_rot )

end DihedralNormal

/-! ### Normal subgroups of Multiplicative (ZMod 5) -/

section CyclicNormal

/-
A group of prime order p has exactly two subgroups: ⊥ and ⊤.
-/
lemma ZMod5.subgroup_eq_bot_or_top
    (M : Subgroup (Multiplicative (ZMod 5))) :
    M = ⊥ ∨ M = ⊤ := by
  rw [ Subgroup.eq_bot_iff_card, Subgroup.eq_top_iff' ];
  have := Subgroup.card_subgroup_dvd_card M; simp_all +decide [ Nat.dvd_prime ] ;
  exact this.imp id fun h => by have := Subgroup.card_mul_index M; simp_all +decide ;

end CyclicNormal

/-! ### Computing the normal subgroup order sum

We compute σ(G × H) = σ(G) · σ(H) for coprime G × H, then
σ(D₃) = 10 and σ(C₅) = 6. -/

section SigmaComputation

open LeinsterGroup

/-
The map from (N.prod M) back via fst gives N.
-/
lemma Subgroup.map_fst_prod {G H : Type*} [Group G] [Group H]
    (N : Subgroup G) (M : Subgroup H) :
    (N.prod M).map (MonoidHom.fst G H) = N := by
  ext x;
  exact ⟨ fun ⟨ y, hy, hxy ⟩ => hxy ▸ hy.1, fun hx => ⟨ ( x, 1 ), ⟨ hx, M.one_mem ⟩, rfl ⟩ ⟩

/-
The map from (N.prod M) back via snd gives M.
-/
lemma Subgroup.map_snd_prod {G H : Type*} [Group G] [Group H]
    (N : Subgroup G) (M : Subgroup H) :
    (N.prod M).map (MonoidHom.snd G H) = M := by
  ext x; simp +decide [ Subgroup.mem_map, Subgroup.mem_prod ] ; aesop;

/-
The map K ↦ (K.map fst, K.map snd) is injective for coprime groups.
-/
lemma normal_subgroup_coprime_prod_injective
    {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (hcop : Nat.Coprime (Fintype.card G) (Fintype.card H))
    (K₁ K₂ : Subgroup (G × H))
    (h1 : K₁.map (MonoidHom.fst G H) = K₂.map (MonoidHom.fst G H))
    (h2 : K₁.map (MonoidHom.snd G H) = K₂.map (MonoidHom.snd G H)) :
    K₁ = K₂ := by
  rw [ normal_subgroup_of_coprime_prod hcop K₁, normal_subgroup_of_coprime_prod hcop K₂, h1, h2 ]

/-
Subgroup.prod is injective (if the result is equal, the components must be equal).
-/
lemma Subgroup.prod_injective {G H : Type*} [Group G] [Group H]
    {N₁ N₂ : Subgroup G} {M₁ M₂ : Subgroup H}
    (h : N₁.prod M₁ = N₂.prod M₂) : N₁ = N₂ ∧ M₁ = M₂ := by
  constructor;
  · rw [ ← Subgroup.map_fst_prod N₁ M₁, ← Subgroup.map_fst_prod N₂ M₂, h ];
  · apply_fun ( fun x => x.map ( MonoidHom.snd G H ) ) at h; simp_all +decide [ Subgroup.map_fst_prod, Subgroup.map_snd_prod ] ;

/-
card (N.prod M) = card N * card M
-/
lemma Subgroup.card_prod {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (N : Subgroup G) (M : Subgroup H) :
    Fintype.card (N.prod M) = Fintype.card N * Fintype.card M := by
  rw [ Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype ];
  rw [ ← Finset.card_product ] ; congr ; ext ; aesop

/-
For coprime finite groups, σ(G × H) = σ(G) · σ(H).
This follows from the product decomposition of normal subgroups.
-/
lemma normalSubgroupOrderSum_prod_coprime
    {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (hcop : Nat.Coprime (Fintype.card G) (Fintype.card H)) :
    normalSubgroupOrderSum (G × H) =
      normalSubgroupOrderSum G * normalSubgroupOrderSum H := by
  -- We need:� K : {K : Subgroup (G×H) // K.Normal}, card K = (∑ N : {N : Subgroup G // N.Normal}, card N) * (∑ M : {M : Subgroup H // M.Normal}, card M).
  have h_sum : ∑ K : {K : Subgroup (G × H) // K.Normal}, Fintype.card K.val = ∑ N : {N : Subgroup G // N.Normal} × {M : Subgroup H // M.Normal}, Fintype.card (N.1.val.prod N.2.val) := by
    apply Finset.sum_bij (fun K _ => ((⟨K.val.map (MonoidHom.fst G H), by
      convert Subgroup.Normal.map K.2 ( MonoidHom.fst G H );
      simp +decide [ Function.Surjective ]⟩, ⟨K.val.map (MonoidHom.snd G H), by
      convert Subgroup.Normal.map K.2 ( MonoidHom.snd G H );
      simp +decide [ Function.Surjective ]⟩)));
    · aesop;
    · all_goals generalize_proofs at *;
      simp +zetaDelta at *;
      exact?;
    · simp +zetaDelta at *;
      intro N hN M hM; use N.prod M; simp +decide [ hN, hM, Subgroup.map_fst_prod, Subgroup.map_snd_prod ] ;
      infer_instance;
    · intro a ha; rw [ ← normal_subgroup_of_coprime_prod hcop a ] ;
  convert h_sum using 1
  generalize_proofs at *;
  erw [ Finset.sum_product ];
  simp +decide [ normalSubgroupOrderSum, Subgroup.card_prod ];
  simp +decide only [← Finset.mul_sum _ _ _, ← Finset.sum_mul]

/-
σ(DihedralGroup 3) = 10.
Normal subgroups: ⊥ (order 1), rotationSubgroup (order 3), ⊤ (order 6).
Sum = 1 + 3 + 6 = 10.
-/
lemma sigma_D3 : normalSubgroupOrderSum (DihedralGroup 3) = 10 := by
  -- Let's list out the normal subgroups of $D_3$.
  have h_normal_subgroups : ∀ H : Subgroup (DihedralGroup 3), H.Normal ↔ H = ⊥ ∨ H = DihedralGroup.rotationSubgroup ∨ H = ⊤ := by
    intro H; exact ⟨ fun h => DihedralGroup.normal_eq_bot_or_rot_or_top H h, fun h => by rcases h with ( rfl | rfl | rfl ) <;> infer_instance ⟩ ;
  unfold normalSubgroupOrderSum;
  rw [ show ( Finset.univ : Finset { H : Subgroup ( DihedralGroup 3 ) // H.Normal } ) = { ⟨ ⊥, by simp +decide [ h_normal_subgroups ] ⟩, ⟨ DihedralGroup.rotationSubgroup, by simp +decide [ h_normal_subgroups ] ⟩, ⟨ ⊤, by simp +decide [ h_normal_subgroups ] ⟩ } from ?_ ];
  · simp +decide [ DihedralGroup.rotationSubgroup ];
    rw [ Finset.sum_insert, Finset.sum_insert ] <;> simp +decide [ SetLike.ext_iff ];
  · grind

/-
σ(Multiplicative (ZMod 5)) = 6.
Normal subgroups: ⊥ (order 1), ⊤ (order 5).
Sum = 1 + 5 = 6.
-/
lemma sigma_C5 : normalSubgroupOrderSum (Multiplicative (ZMod 5)) = 6 := by
  -- Since this is a finite type, we can define the sum over the finite set of normal subgroups.
  have h_fintype : Fintype {H : Subgroup (Multiplicative (ZMod 5)) // H.Normal} := by
    exact Fintype.ofFinite _
  generalize_proofs at *;
  -- Since this is a finite type, we can define the sum over the finite set of normal subgroups and show it equals 6.
  have h_sum : ∑ H : {H : Subgroup (Multiplicative (ZMod 5)) // H.Normal}, Fintype.card ↥H.val = ∑ H ∈ ({⊥, ⊤} : Finset (Subgroup (Multiplicative (ZMod 5)))), Fintype.card ↥H := by
    refine' Finset.sum_bij ( fun H _ => H.val ) _ _ _ _ <;> simp +decide [ ZMod5.subgroup_eq_bot_or_top ];
    exact fun _ => inferInstance
  generalize_proofs at *; (
  convert h_sum using 1;
  · unfold normalSubgroupOrderSum;
    convert rfl;
  · simp +decide [ Subgroup.eq_top_iff' ])

end SigmaComputation

/-! ### The main theorem -/

section MainTheorem

open LeinsterGroup

/-- The product D₃ × C₅ is a Leinster group. -/
lemma isLeinster_D3_C5 :
    IsLeinster (DihedralGroup 3 × Multiplicative (ZMod 5)) := by
  unfold IsLeinster
  rw [normalSubgroupOrderSum_prod_coprime (by native_decide)]
  rw [sigma_D3, sigma_C5]
  simp [Fintype.card_prod, DihedralGroup.card, ZMod.card]

/-
The product D₃ × C₅ is nonabelian.
-/
lemma nonabelian_D3_C5 :
    ¬ ∀ (a b : DihedralGroup 3 × Multiplicative (ZMod 5)), a * b = b * a := by
  native_decide

/-- There exists a finite nonabelian Leinster group. -/
theorem exists_nonabelian_leinster_group_witness :
    ∃ G : Type, ∃ (_ : Group G) (_ : Fintype G),
      LeinsterGroup.IsLeinster G ∧ ¬ ∀ (a b : G), a * b = b * a :=
  ⟨_, _, _, isLeinster_D3_C5, nonabelian_D3_C5⟩

end MainTheorem