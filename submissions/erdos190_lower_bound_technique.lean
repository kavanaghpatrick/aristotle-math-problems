/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f175b608-a685-431c-8e21-c447540f9020
-/

/-
ITERATION 1 for Erdős #190 - Van der Waerden H(k) Lower Bound
Project ID: 8aeb661e-abf0-4e9c-99ad-e854f89eefcf

Previous iteration proved 8 helper lemmas but never stated/proved the main theorem.
This iteration adds the main theorem that connects them:

erdos_190_lower_bound: For k ≥ 2, if N² < (k-1)^(k-1), then N < H(k)

The proof chain uses the already-proven lemmas:
1. bad_card_bound with r = k-1: BadColorings < total colorings
2. not_validW_of_lt_bound: Therefore ¬ValidW (k-1) k N
3. contrapositive of validN_subset_validW: Therefore ¬ValidN k N
4. Definition of H as infimum: Therefore N < H k

CONSTRAINTS:
- All helper lemmas are ALREADY PROVEN (do not re-prove them)
- Only prove the main theorem at the end
- Use: exact, apply, rw, simp, nlinarith
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

def IsProperAP (l : List ℕ) : Prop :=
  ∃ a d, d > 0 ∧ l = List.ofFn (fun i : Fin l.length => a + (i : ℕ) * d)

def IsMono {α β : Type} (c : α → β) (l : List α) : Prop :=
  ∃ y, ∀ x ∈ l, c x = y

def IsRainbow {α β : Type} (c : α → β) (l : List α) : Prop :=
  (l.map c).Nodup

def ValidN (k N : ℕ) : Prop :=
  ∀ (c : Fin N → ℕ), ∃ (l : List (Fin N)),
    l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ (IsMono c l ∨ IsRainbow c l)

def ValidW (r k N : ℕ) : Prop :=
  ∀ (c : Fin N → Fin r), ∃ (l : List (Fin N)),
    l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ IsMono c l

noncomputable def H (k : ℕ) : ℕ := sInf {N | ValidN k N}

noncomputable def W (r k : ℕ) : ℕ := sInf {N | ValidW r k N}

def ValidPairs (k N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.product (Finset.range N) (Finset.range N)).filter (fun p => let (a, d) := p; d > 0 ∧ a + (k - 1) * d < N)

def BadColorings (r k N : ℕ) : Finset (Fin N → Fin r) :=
  Finset.univ.filter (fun c => ∃ l, l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ IsMono c l)

-- ALREADY PROVEN LEMMAS (from previous iteration)

lemma not_rainbow_of_range_subset {α : Type} (c : α → ℕ) (l : List α) (r : ℕ)
    (h_range : ∀ x ∈ l, c x < r) (h_len : l.length > r) : ¬ IsRainbow c l := by
      intro h_rainbow
      have h_card : (l.map c).toFinset.card = l.length := by
        rw [ List.toFinset_card_of_nodup ] <;> aesop;
      exact h_len.not_le ( h_card ▸ le_trans ( Finset.card_le_card ( show _ ⊆ Finset.range r from fun x hx => by aesop ) ) ( by simpa ) )

lemma mono_lift {α : Type} {r : ℕ} (hr : r > 0) (c : α → Fin r) (l : List α) :
    IsMono c l ↔ IsMono (fun x => (c x).val) l := by
      constructor <;> intro h <;> unfold IsMono at * <;> aesop;
      by_cases hl : l = [];
      · aesop;
        exact ⟨ ⟨ 0, hr ⟩ ⟩;
      · obtain ⟨ x, hx ⟩ := List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr hl ) ; use ⟨ w, h x hx ▸ Fin.is_lt _ ⟩ ; aesop;

lemma validN_subset_validW (k : ℕ) (hk : k ≥ 2) : {N | ValidN k N} ⊆ {N | ValidW (k - 1) k N} := by
  intro N hN c;
  rcases hN ( fun x => ( c x : ℕ ) ) with ⟨ l, hl₁, hl₂, hl₃ ⟩;
  cases hl₃;
  · exact ⟨ l, hl₁, hl₂, by rwa [ mono_lift ( Nat.sub_pos_of_lt hk ) ] ⟩;
  · have := not_rainbow_of_range_subset ( fun x => ( c x : ℕ ) ) l ( k - 1 ) ?_ ?_ <;> aesop;
    grind

theorem countAPs_le (k N : ℕ) : (ValidPairs k N).card ≤ N ^ 2 := by
  exact le_trans ( Finset.card_filter_le _ _ ) ( by norm_num [ sq ] )

theorem card_mono_on_indices {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (r : ℕ) :
  (Finset.univ.filter (fun c : α → Fin r => ∃ y, ∀ x ∈ s, c x = y)).card = r * r ^ (Fintype.card α - s.card) := by
    have h_monocromatic : ∀ y : Fin r, (Finset.filter (fun c : α → Fin r => ∀ x ∈ s, c x = y) (Finset.univ : Finset (α → Fin r))).card = r ^ (Fintype.card α - s.card) := by
      intro y
      have h_count : (Finset.filter (fun c : α → Fin r => ∀ x ∈ s, c x = y) (Finset.univ : Finset (α → Fin r))).card = (Finset.image (fun c : { x : α // x ∉ s } → Fin r => fun x => if hx : x ∈ s then y else c ⟨x, hx⟩) (Finset.univ : Finset ({ x : α // x ∉ s } → Fin r))).card := by
        congr with c ; aesop;
        exact ⟨ fun x => c x, funext fun x => by by_cases hx : x ∈ s <;> simp +decide [ * ] ⟩;
      rw [ h_count, Finset.card_image_of_injective ];
      · simp +decide [ Finset.card_univ ];
      · intro c₁ c₂ h; ext ⟨ x, hx ⟩ ; replace h := congr_fun h x; aesop;
    have h_monocromatic : Finset.filter (fun c : α → Fin r => ∃ y : Fin r, ∀ x ∈ s, c x = y) (Finset.univ : Finset (α → Fin r)) = Finset.biUnion Finset.univ (fun y => Finset.filter (fun c : α → Fin r => ∀ x ∈ s, c x = y) (Finset.univ : Finset (α → Fin r))) := by
      aesop;
    rw [ h_monocromatic, Finset.card_biUnion ];
    · aesop;
    · intro y hy z hz hyz; simp_all +decide [ Finset.disjoint_left ] ;
      exact fun _ _ => hs

theorem card_BadColorings_le (r k N : ℕ) (hk : k ≥ 2) :
  (BadColorings r k N).card ≤ (ValidPairs k N).card * (r * r ^ (N - k)) := by
    have h_card : ∀ (p : ℕ × ℕ), p ∈ ValidPairs k N → (Finset.univ.filter (fun (c : Fin N → Fin r) => ∃ l : List (Fin N), l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ IsMono c l ∧ l.map Fin.val = List.map (fun i : Fin k => p.1 + i.val * p.2) (List.finRange k))).card ≤ r * r ^ (N - k) := by
      intro p hp
      have h_s : ∃ s : Finset (Fin N), s.card = k ∧ ∀ l : List (Fin N), l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ l.map Fin.val = List.map (fun i : Fin k => p.1 + i.val * p.2) (List.finRange k) → l.toFinset = s := by
        use Finset.image (fun i : Fin k => ⟨p.1 + i.val * p.2, by
          unfold ValidPairs at hp; aesop;
          nlinarith [ Fin.is_lt i, Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ]⟩) Finset.univ;
        rw [ Finset.card_image_of_injective ] <;> aesop;
        · ext x; aesop;
          · replace a_2 := congr_arg List.toFinset a_2; rw [ Finset.ext_iff ] at a_2; specialize a_2 x; aesop;
            exact a_2.mp ⟨ x, a, rfl ⟩ |> fun ⟨ i, hi ⟩ => ⟨ i, Fin.ext hi ⟩;
          · replace a_2 := congr_arg List.toFinset a_2; rw [ Finset.ext_iff ] at a_2; specialize a_2 ( fst + w * snd ) ; aesop;
            contrapose! a_2;
            exact Or.inr ⟨ fun x hx => by intro H; exact a_2 <| by convert hx; aesop, w, Or.inl rfl ⟩;
        · intro i j; aesop;
          · exact Fin.ext h;
          · unfold ValidPairs at hp; aesop;
      obtain ⟨ s, hs ⟩ := h_s;
      have h_card_mono : (Finset.univ.filter (fun (c : Fin N → Fin r) => ∃ l : List (Fin N), l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ IsMono c l ∧ l.map Fin.val = List.map (fun i : Fin k => p.1 + i.val * p.2) (List.finRange k))).card ≤ (Finset.univ.filter (fun (c : Fin N → Fin r) => ∃ y : Fin r, ∀ x ∈ s, c x = y)).card := by
        refine Finset.card_le_card ?_;
        intro c hc;
        aesop;
        obtain ⟨ y, hy ⟩ := left_3;
        use y;
        intro x hx; specialize right w rfl left_2 right_1; replace right := Finset.ext_iff.mp right x; aesop;
      have := card_mono_on_indices s ( Finset.card_pos.mp ( by linarith ) ) r;
      aesop;
      grind;
    have h_union : (BadColorings r k N) ⊆ Finset.biUnion (ValidPairs k N) (fun p => Finset.univ.filter (fun (c : Fin N → Fin r) => ∃ l : List (Fin N), l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ IsMono c l ∧ l.map Fin.val = List.map (fun i : Fin k => p.1 + i.val * p.2) (List.finRange k))) := by
      intro c hc;
      obtain ⟨l, hl⟩ : ∃ l : List (Fin N), l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ IsMono c l := by
        unfold BadColorings at hc; aesop;
      obtain ⟨a, d, hd⟩ : ∃ a d : ℕ, d > 0 ∧ l.map Fin.val = List.map (fun i : Fin k => a + i.val * d) (List.finRange k) := by
        obtain ⟨ a, d, hd, hl ⟩ := hl.2.1;
        use a - 1, d;
        rw [ List.ext_get_iff ] at * ; aesop;
        linarith [ hl n h₁, Nat.sub_add_cancel ( show 1 ≤ a from by nlinarith [ hl 0 ( by linarith ) ] ) ];
      have h_valid_pair : a + (k - 1) * d < N := by
        replace hd := congr_arg List.toFinset hd.2; rw [ Finset.ext_iff ] at hd; specialize hd ( a + ( k - 1 ) * d ) ; aesop;
        exact hd.mpr ⟨ ⟨ l.length - 1, Nat.sub_lt ( by linarith ) zero_lt_one ⟩, Or.inl rfl ⟩ |> fun ⟨ x, hx₁, hx₂ ⟩ => hx₂.symm ▸ Fin.is_lt x;
      simp [ValidPairs];
      exact ⟨ a, d, ⟨ ⟨ by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ], by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ] ⟩, hd.1, h_valid_pair ⟩, l, hl.1, hl.2.1, hl.2.2, hd.2 ⟩;
    exact le_trans ( Finset.card_le_card h_union ) ( Finset.card_biUnion_le.trans ( Finset.sum_le_card_nsmul _ _ _ fun x hx => h_card x hx ) )

theorem bad_card_bound (r k N : ℕ) (hk : k ≥ 2) (hN : N ^ 2 < r ^ (k - 1)) :
  (BadColorings r k N).card < r ^ N := by
    by_cases hr : r > 0;
    · by_cases hNk : N < k;
      · have h_empty : BadColorings r k N = ∅ := by
          ext c
          simp [BadColorings, hNk];
          intro x hx hx'; obtain ⟨ a, d, hd, hx'' ⟩ := hx'; have := List.toFinset_card_of_nodup ( show List.Nodup x from ?_ ) ; aesop;
          · exact hNk.not_le ( by simpa using this ▸ le_trans ( Finset.card_le_univ _ ) ( by norm_num ) );
          · rw [ List.nodup_iff_injective_get ];
            intro i j hij; have := congr_arg ( fun z => z.get! i ) hx''; have := congr_arg ( fun z => z.get! j ) hx''; norm_num at * ; aesop;
        aesop;
      · have h_card : (BadColorings r k N).card ≤ (N ^ 2) * r * r ^ (N - k) := by
          refine le_trans ( card_BadColorings_le r k N hk ) ?_;
          simpa only [ mul_assoc ] using Nat.mul_le_mul_right _ ( countAPs_le k N );
        refine lt_of_le_of_lt h_card ?_;
        convert mul_lt_mul_of_pos_right hN ( pow_pos hr ( N - k + 1 ) ) using 1 ; ring;
        rw [ ← pow_add, show k - 1 + ( N - k + 1 ) = N by omega ];
    · rcases k with ( _ | _ | k ) <;> aesop

theorem not_validW_of_lt_bound (r k N : ℕ) (h : (BadColorings r k N).card < r ^ N) :
  ¬ ValidW r k N := by
    aesop;
    exact h.not_le ( le_trans ( by norm_num ) ( Finset.card_mono <| show Finset.univ.filter ( fun c : Fin N → Fin r => ∃ x : List ( Fin N ), List.length x = k ∧ IsProperAP ( x.map fun x : Fin N => x.val + 1 ) ∧ IsMono c x ) ≥ Finset.univ from Finset.subset_iff.mpr fun x _ => by simpa using a x |> fun ⟨ l, hl1, hl2, hl3 ⟩ => by aesop ) )

-- MAIN THEOREM: Connect the lemmas to prove the lower bound on H(k)

/-- Main result: For k ≥ 2, if N² < (k-1)^(k-1), then N is not valid for H(k), hence H(k) > N -/
theorem erdos_190_lower_bound (k : ℕ) (hk : k ≥ 2) (N : ℕ) (hN : N ^ 2 < (k - 1) ^ (k - 1)) :
    ¬ ValidN k N := by
  intro hValid
  -- Step 1: By validN_subset_validW, N is valid for ValidW (k-1) k
  have h1 : ValidW (k - 1) k N := validN_subset_validW k hk hValid
  -- Step 2: By bad_card_bound, BadColorings (k-1) k N < (k-1)^N
  have h2 : (BadColorings (k - 1) k N).card < (k - 1) ^ N := bad_card_bound (k - 1) k N hk hN
  -- Step 3: By not_validW_of_lt_bound, ¬ValidW (k-1) k N
  have h3 : ¬ ValidW (k - 1) k N := not_validW_of_lt_bound (k - 1) k N h2
  -- Contradiction
  exact h3 h1