/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 36804ee1-3d1f-4483-b0f2-adba81a38501

The following was proved by Aristotle:

- lemma universal_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) :
    (∀ T, isExternalOf G M X T → False) ∨  -- No externals
    (∃ v ∈ X, ∀ T, isExternalOf G M X T → v ∈ T) ∨  -- Apex in X
    (∃ t, t ∉ X ∧ ∀ T, isExternalOf G M X T → t ∈ T)  -- Apex outside X

- lemma cover_with_internal_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (hX_tri : X ∈ G.cliqueFinset 3)
    (v : V) (hv : v ∈ X) (h_apex : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (e₁ ∈ X.sym2 ∨ e₂ ∈ X.sym2) ∧  -- Covers X
    ∀ T, isExternalOf G M X T → (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)

- lemma cover_with_external_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (hX_tri : X ∈ G.cliqueFinset 3)
    (t : V) (ht : t ∉ X) (h_apex : ∀ T, isExternalOf G M X T → t ∈ T)
    (h_has_external : ∃ T, isExternalOf G M X T) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (e₁ ∈ X.sym2 ∨ e₂ ∈ X.sym2) ∧  -- Covers X
    ∀ T, isExternalOf G M X T → (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)

- lemma cover_no_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_card : X.card = 3) (hX_tri : X ∈ G.cliqueFinset 3) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (e₁ ∈ X.sym2 ∨ e₂ ∈ X.sym2)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
  slot324: τ ≤ 8 for ν = 4 - Case Split by Supported Edges

  STRATEGY (from Grok-4 analysis):
  Split by number of "supported edges" (edges of X with ≥1 external).

  Case 0: No externals → any 2 edges of X work
  Case 1: 1 supported edge → use that edge + another
  Case 2: 2 supported edges → use {s(shared_v, t), opposite edge}
  Case 3: 3 supported edges → use {s(a, t), s(b, c)} where t ∉ X

  KEY INSIGHT: Cases 0-2 have a common vertex IN X. Case 3 uses t ∉ X.
-/

import Mathlib


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC HELPERS (proven by Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

lemma edge_in_sym2_iff (T : Finset V) (u v : V) :
    s(u, v) ∈ T.sym2 ↔ u ∈ T ∧ v ∈ T := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h
    exact ⟨h u (Sym2.mem_iff.mpr (Or.inl rfl)), h v (Sym2.mem_iff.mpr (Or.inr rfl))⟩
  · intro ⟨hu, hv⟩ x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

lemma nonpacking_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm_in, hm_inter⟩ := hM.2 T hT_tri hT_notin
  exact ⟨m, hm_in, sharesEdgeWith_iff_card_inter_ge_two T m |>.mpr hm_inter⟩

lemma external_inter_card_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
  have hT_card : T.card = 3 := triangle_card_three G T hT.1
  have h_share : sharesEdgeWith T X := hT.2.2.1
  have h_inter_ge : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp h_share
  have h_inter_le : (T ∩ X).card ≤ 2 := by
    by_contra h_gt; push_neg at h_gt
    have h_sub : T ⊆ X := by
      have h_inter_sub : T ∩ X ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ X).card = T.card := by linarith [Finset.card_le_card h_inter_sub]
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact (Finset.mem_inter.mp hx).2
    have h_sub' : X ⊆ T := by
      have h_inter_sub : T ∩ X ⊆ X := Finset.inter_subset_right
      have h_card_eq : (T ∩ X).card = X.card := by linarith [Finset.card_le_card h_inter_sub]
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact (Finset.mem_inter.mp hx).1
    exact hT.2.1 (Finset.Subset.antisymm h_sub h_sub' ▸ hX_in_M)
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- TWO EXTERNALS SHARE EDGE (proven by Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  have hT₁_3 : T₁.card = 3 := triangle_card_three G T₁ hT₁.1
  have hT₂_3 : T₂.card = 3 := triangle_card_three G T₂ hT₂.1
  let M' := {T₁, T₂} ∪ M.erase X
  have hM'_card : M'.card = 5 := by
    have hT₁_not_M : T₁ ∉ M := hT₁.2.1
    have hT₂_not_M : T₂ ∉ M := hT₂.2.1
    have hM_minus_X_card : (M.erase X).card = 3 := by rw [Finset.card_erase_of_mem hX]; omega
    have hT₁_not_MX : T₁ ∉ M.erase X := fun h => hT₁_not_M (Finset.mem_erase.mp h).2
    have hT₂_not_MX : T₂ ∉ M.erase X := fun h => hT₂_not_M (Finset.mem_erase.mp h).2
    have h_pair_card : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem]; simp [h_ne]; simp [h_ne]
    have h_disj : Disjoint {T₁, T₂} (M.erase X) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact fun h => hT₁_not_MX (h ▸ hy);
                                    exact fun h => hT₂_not_MX (h ▸ hy)]
    rw [Finset.card_union_of_disjoint h_disj, h_pair_card, hM_minus_X_card]
  have hM'_packing : isTrianglePacking G M' := by
    constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with ht_pair | ht_MX
      · rcases Finset.mem_insert.mp ht_pair with rfl | ht_sing
        · exact hT₁.1
        · rw [Finset.mem_singleton] at ht_sing; rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MX).2
    · intro t₁ ht₁ t₂ ht₂ h_ne'
      have h_not_share : ∀ t m : Finset V, t.card = 3 → m.card = 3 → ¬sharesEdgeWith t m → (t ∩ m).card ≤ 1 := by
        intro t m ht hm h_ns
        by_contra h
        push_neg at h
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
        exact h_ns ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
                     (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩
      rcases Finset.mem_union.mp ht₁ with ht₁_pair | ht₁_MX <;>
      rcases Finset.mem_union.mp ht₂ with ht₂_pair | ht₂_MX
      · rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · exact absurd (heq₁.trans heq₂.symm) h_ne'
          · rw [Finset.mem_singleton] at ht₂_sing; rw [heq₁, ht₂_sing]
            exact h_not_share T₁ T₂ hT₁_3 hT₂_3 h_no_edge
        · rw [Finset.mem_singleton] at ht₁_sing
          rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · rw [ht₁_sing, heq₂, Finset.inter_comm]
            exact h_not_share T₁ T₂ hT₁_3 hT₂_3 h_no_edge
          · rw [Finset.mem_singleton] at ht₂_sing
            exact absurd (ht₁_sing.trans ht₂_sing.symm) h_ne'
      · have hY_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MX).2
        have hY_ne_X : t₂ ≠ X := (Finset.mem_erase.mp ht₂_MX).1
        have hY_3 : t₂.card = 3 := triangle_card_three G t₂ (hM.1.1 hY_M)
        rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rw [heq₁]
          have h_not_share' := hT₁.2.2.2 t₂ hY_M hY_ne_X
          exact h_not_share T₁ t₂ hT₁_3 hY_3 h_not_share'
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          have h_not_share' := hT₂.2.2.2 t₂ hY_M hY_ne_X
          exact h_not_share T₂ t₂ hT₂_3 hY_3 h_not_share'
      · have hY_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MX).2
        have hY_ne_X : t₁ ≠ X := (Finset.mem_erase.mp ht₁_MX).1
        have hY_3 : t₁.card = 3 := triangle_card_three G t₁ (hM.1.1 hY_M)
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂, Finset.inter_comm]
          have h_not_share' := hT₁.2.2.2 t₁ hY_M hY_ne_X
          exact h_not_share T₁ t₁ hT₁_3 hY_3 h_not_share'
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing, Finset.inter_comm]
          have h_not_share' := hT₂.2.2.2 t₁ hY_M hY_ne_X
          exact h_not_share T₂ t₁ hT₂_3 hY_3 h_not_share'
      · exact hM.1.2 (Finset.mem_erase.mp ht₁_MX).2 (Finset.mem_erase.mp ht₂_MX).2 h_ne'
  have h_bound := hν M' hM'_packing
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PAIRWISE EXTERNALS SHARE X-VERTEX (proven by Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
Two 2-subsets of a 3-set must intersect (pigeonhole).
T₁ ∩ X and T₂ ∩ X are 2-subsets of X (3-set), so they share ≥1 vertex.
-/
lemma pairwise_externals_share_X_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_card : X.card = 3) (hX_in : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂) :
    ∃ v ∈ X, v ∈ T₁ ∧ v ∈ T₂ := by
  have h1 : (T₁ ∩ X).card = 2 := external_inter_card_two G M X hX_in hX_card T₁ hT₁
  have h2 : (T₂ ∩ X).card = 2 := external_inter_card_two G M X hX_in hX_card T₂ hT₂
  have h_inter_nonempty : ((T₁ ∩ X) ∩ (T₂ ∩ X)).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have h_disj : Disjoint (T₁ ∩ X) (T₂ ∩ X) := Finset.disjoint_iff_inter_eq_empty.mpr h_empty
    have h_union_sub : (T₁ ∩ X) ∪ (T₂ ∩ X) ⊆ X := fun v hv =>
      match Finset.mem_union.mp hv with
      | Or.inl h => Finset.mem_of_mem_inter_right h
      | Or.inr h => Finset.mem_of_mem_inter_right h
    have h_union_card : ((T₁ ∩ X) ∪ (T₂ ∩ X)).card = 4 := by
      rw [Finset.card_union_of_disjoint h_disj]; omega
    have := Finset.card_le_card h_union_sub; omega
  obtain ⟨v, hv⟩ := h_inter_nonempty
  exact ⟨v, Finset.mem_of_mem_inter_right (Finset.mem_of_mem_inter_left hv),
         Finset.mem_of_mem_inter_left (Finset.mem_of_mem_inter_left hv),
         Finset.mem_of_mem_inter_left (Finset.mem_of_mem_inter_right hv)⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COMMON EXTERNAL VERTEX (proven by Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If T₁, T₂ are on DIFFERENT edges of X, their X-intersections share only 1 vertex.
But by two_externals_share_edge, T₁ ∩ T₂ ≥ 2.
So the extra intersection comes from outside X: t₁ = t₂ = t ∉ X.
-/
lemma common_external_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) (h_diff_edge : T₁ ∩ X ≠ T₂ ∩ X) :
    ∃ t, t ∉ X ∧ t ∈ T₁ ∧ t ∈ T₂ := by
  have h_share : sharesEdgeWith T₁ T₂ := two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ h_ne
  have h_inter_ge_2 : (T₁ ∩ T₂).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T₁ T₂ |>.mp h_share
  have hT₁X_card : (T₁ ∩ X).card = 2 := external_inter_card_two G M X hX hX_card T₁ hT₁
  have hT₂X_card : (T₂ ∩ X).card = 2 := external_inter_card_two G M X hX hX_card T₂ hT₂
  -- Two different 2-subsets of a 3-set intersect in exactly 1 element
  have h_X_inter_card : ((T₁ ∩ X) ∩ (T₂ ∩ X)).card = 1 := by
    have h_nonempty : ((T₁ ∩ X) ∩ (T₂ ∩ X)).Nonempty := by
      by_contra h_empty
      rw [Finset.not_nonempty_iff_eq_empty] at h_empty
      have h_disj : Disjoint (T₁ ∩ X) (T₂ ∩ X) := Finset.disjoint_iff_inter_eq_empty.mpr h_empty
      have h_union_sub : (T₁ ∩ X) ∪ (T₂ ∩ X) ⊆ X := fun v hv =>
        match Finset.mem_union.mp hv with
        | Or.inl h => Finset.mem_of_mem_inter_right h
        | Or.inr h => Finset.mem_of_mem_inter_right h
      have h_union_card : ((T₁ ∩ X) ∪ (T₂ ∩ X)).card = 4 := by
        rw [Finset.card_union_of_disjoint h_disj]; omega
      have := Finset.card_le_card h_union_sub; omega
    have h_card_ge_1 : 1 ≤ ((T₁ ∩ X) ∩ (T₂ ∩ X)).card := Finset.card_pos.mpr h_nonempty
    by_contra h_ne_1
    have h_card_ge_2 : 2 ≤ ((T₁ ∩ X) ∩ (T₂ ∩ X)).card := by omega
    have h_sub1 : (T₁ ∩ X) ∩ (T₂ ∩ X) ⊆ T₁ ∩ X := Finset.inter_subset_left
    have h_sub2 : (T₁ ∩ X) ∩ (T₂ ∩ X) ⊆ T₂ ∩ X := Finset.inter_subset_right
    have h_eq : T₁ ∩ X = T₂ ∩ X := by
      have h_eq1 : (T₁ ∩ X) ∩ (T₂ ∩ X) = T₁ ∩ X := by
        apply Finset.eq_of_subset_of_card_le h_sub1
        have := Finset.card_le_card h_sub1; omega
      have h_eq2 : (T₁ ∩ X) ∩ (T₂ ∩ X) = T₂ ∩ X := by
        apply Finset.eq_of_subset_of_card_le h_sub2
        have := Finset.card_le_card h_sub2; omega
      rw [← h_eq1, h_eq2]
    exact h_diff_edge h_eq
  -- T₁ \ X and T₂ \ X each have exactly 1 element
  have hT₁_card : T₁.card = 3 := triangle_card_three G T₁ hT₁.1
  have hT₂_card : T₂.card = 3 := triangle_card_three G T₂ hT₂.1
  have hT₁_ext_card : (T₁ \ X).card = 1 := by have h := Finset.card_sdiff_add_card_inter T₁ X; omega
  have hT₂_ext_card : (T₂ \ X).card = 1 := by have h := Finset.card_sdiff_add_card_inter T₂ X; omega
  obtain ⟨t₁, ht₁⟩ := Finset.card_eq_one.mp hT₁_ext_card
  obtain ⟨t₂, ht₂⟩ := Finset.card_eq_one.mp hT₂_ext_card
  have h_t1_in_T1 : t₁ ∈ T₁ := (Finset.mem_sdiff.mp (ht₁ ▸ Finset.mem_singleton_self t₁)).1
  have h_t2_in_T2 : t₂ ∈ T₂ := (Finset.mem_sdiff.mp (ht₂ ▸ Finset.mem_singleton_self t₂)).1
  have h_t1_notin_X : t₁ ∉ X := (Finset.mem_sdiff.mp (ht₁ ▸ Finset.mem_singleton_self t₁)).2
  have h_t2_notin_X : t₂ ∉ X := (Finset.mem_sdiff.mp (ht₂ ▸ Finset.mem_singleton_self t₂)).2
  -- t₁ = t₂ because T₁ ∩ T₂ must have 2 elements
  have h_t_eq : t₁ = t₂ := by
    by_contra h_ne_t
    have h_inter_sub_X : T₁ ∩ T₂ ⊆ X := by
      intro v hv
      have hv_T1 : v ∈ T₁ := Finset.mem_of_mem_inter_left hv
      have hv_T2 : v ∈ T₂ := Finset.mem_of_mem_inter_right hv
      by_contra hv_notin_X
      have hv_eq_t1 : v = t₁ := Finset.mem_singleton.mp (ht₁ ▸ Finset.mem_sdiff.mpr ⟨hv_T1, hv_notin_X⟩)
      have hv_eq_t2 : v = t₂ := Finset.mem_singleton.mp (ht₂ ▸ Finset.mem_sdiff.mpr ⟨hv_T2, hv_notin_X⟩)
      exact h_ne_t (hv_eq_t1.symm.trans hv_eq_t2)
    have h_sub : T₁ ∩ T₂ ⊆ (T₁ ∩ X) ∩ (T₂ ∩ X) := fun v hv =>
      Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨Finset.mem_of_mem_inter_left hv, h_inter_sub_X hv⟩,
                             Finset.mem_inter.mpr ⟨Finset.mem_of_mem_inter_right hv, h_inter_sub_X hv⟩⟩
    have := Finset.card_le_card h_sub; omega
  use t₁
  exact ⟨h_t1_notin_X, h_t1_in_T1, h_t_eq ▸ h_t2_in_T2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY STRUCTURAL LEMMA: Universal Apex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for universal_apex:

For X = {a, b, c}, externals have T ∩ X ∈ {{a,b}, {a,c}, {b,c}}.

Case: All externals use same edge (say {a,b})
  → Both a and b are in all externals. Pick apex = a (or b).

Case: Externals use 2 different edges (say {a,b} and {a,c})
  → They share vertex a. By pairwise lemma, any pair shares an X-vertex.
  → Since {a,b} ∩ {a,c} = {a}, apex = a works.

Case: Externals use all 3 edges
  → No X-vertex is in all ({a,b} ∩ {a,c} ∩ {b,c} = ∅)
  → By common_external_vertex, any two on different edges share t ∉ X
  → All three share the SAME t (apply pairwise and use uniqueness)
  → apex = t ∉ X
-/
lemma universal_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) :
    (∀ T, isExternalOf G M X T → False) ∨  -- No externals
    (∃ v ∈ X, ∀ T, isExternalOf G M X T → v ∈ T) ∨  -- Apex in X
    (∃ t, t ∉ X ∧ ∀ T, isExternalOf G M X T → t ∈ T)  -- Apex outside X
    := by
  by_cases h : ∃ T, isExternalOf G M X T;
  · by_cases h₂ : ∃ T₁ T₂ : Finset V, isExternalOf G M X T₁ ∧ isExternalOf G M X T₂ ∧ T₁ ∩ X ≠ T₂ ∩ X;
    · obtain ⟨ T₁, T₂, hT₁, hT₂, hne ⟩ := h₂
      obtain ⟨ t, ht₁, ht₂ ⟩ := common_external_vertex G M hM hM_card hν X hX hX_card T₁ T₂ hT₁ hT₂ (by
      grind) hne;
      refine' Or.inr ( Or.inr ⟨ t, ht₁, fun T hT => _ ⟩ );
      by_cases hT₁T : T ∩ X = T₁ ∩ X;
      · -- Since T and T₂ are on different edges of X, by `common_external_vertex`, they share a vertex t' ∉ X.
        obtain ⟨ t', ht'₁, ht'₂ ⟩ : ∃ t', t' ∉ X ∧ t' ∈ T ∧ t' ∈ T₂ := by
          apply common_external_vertex G M hM hM_card hν X hX hX_card T T₂ hT hT₂;
          · grind;
          · grind;
        have hT₂_card : T₂.card = 3 := by
          exact triangle_card_three G T₂ hT₂.1;
        have hT₂_inter_card : (T₂ ∩ X).card = 2 := by
          exact external_inter_card_two G M X hX hX_card T₂ hT₂;
        have hT₂_unique : ∀ t'' ∈ T₂, t'' ∉ X → t'' = t := by
          intro t'' ht'' ht''_not_in_X
          have hT₂_unique : T₂ = (T₂ ∩ X) ∪ {t} := by
            rw [ Finset.eq_of_subset_of_card_le ( show T₂ ∩ X ∪ { t } ⊆ T₂ from Finset.union_subset ( Finset.inter_subset_left ) ( Finset.singleton_subset_iff.mpr ht₂.2 ) ) ] ; aesop;
          rw [ hT₂_unique ] at ht''; simp +decide [ ht''_not_in_X ] at ht'';
          exact ht'';
        grind;
      · -- By `common_external_vertex`, T and T₁ share a vertex t' ∉ X.
        obtain ⟨ t', ht'₁, ht'₂ ⟩ : ∃ t', t' ∉ X ∧ t' ∈ T ∧ t' ∈ T₁ := by
          apply common_external_vertex G M hM hM_card hν X hX hX_card T T₁ hT hT₁ (by
          aesop) (by
          exact hT₁T);
        have h_unique : (T₁ \ X).card = 1 := by
          have h_unique : (T₁ ∩ X).card = 2 := by
            exact?;
          have h_unique : (T₁).card = 3 := by
            exact triangle_card_three G T₁ hT₁.1;
          grind;
        rw [ Finset.card_eq_one ] at h_unique;
        obtain ⟨ a, ha ⟩ := h_unique; rw [ Finset.eq_singleton_iff_unique_mem ] at ha; aesop;
    · -- If all externals share the same edge of X, then any vertex of that edge is in all externals.
      obtain ⟨E, hE⟩ : ∃ E : Finset V, ∀ T : Finset V, isExternalOf G M X T → T ∩ X = E := by
        exact ⟨ _, fun T hT => Classical.not_not.1 fun hT' => h₂ ⟨ T, h.choose, hT, h.choose_spec, hT' ⟩ ⟩;
      -- Since E is a subset of X and X has 3 elements, E must have 2 elements.
      have hE_card : E.card = 2 := by
        obtain ⟨ T, hT ⟩ := h;
        rw [ ← hE T hT, external_inter_card_two G M X hX hX_card T hT ];
      obtain ⟨ v, hv ⟩ := Finset.card_pos.mp ( by linarith );
      exact Or.inr <| Or.inl ⟨ v, Finset.mem_of_mem_inter_right ( hE _ h.choose_spec ▸ hv ), fun T hT => Finset.mem_of_mem_inter_left ( hE _ hT ▸ hv ) ⟩;
  · aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERING LEMMA: Apex in X
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If apex v ∈ X and X = {v, u, w}, then:
- Cover = {s(v, u), s(v, w)}
- X contains both edges (v, u, w ∈ X)
- Any X-external T contains v, and T ∩ X = {v, x} for x ∈ {u, w}
- So s(v, x) ∈ Cover covers T
-/
lemma cover_with_internal_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (hX_tri : X ∈ G.cliqueFinset 3)
    (v : V) (hv : v ∈ X) (h_apex : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (e₁ ∈ X.sym2 ∨ e₂ ∈ X.sym2) ∧  -- Covers X
    ∀ T, isExternalOf G M X T → (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  obtain ⟨ u, hu, w, hw, h ⟩ : ∃ u w, u ∈ X ∧ w ∈ X ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w := by
    have := Finset.card_eq_three.mp hX_card;
    obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := this; use if v = x then y else if v = y then z else x, if v = x then z else if v = y then x else y; aesop;
  refine' ⟨ Sym2.mk ( v, u ), Sym2.mk ( v, hu ), _, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.cliqueFinset ];
  · exact hX_tri.1 ( by aesop ) ( by aesop ) ( by aesop );
  · have := hX_tri.1; aesop;
  · intro T hT
    have hT_inter : (T ∩ X).card = 2 := by
      exact?;
    have := Finset.card_eq_two.mp hT_inter;
    rcases this with ⟨ x, y, hxy, h ⟩ ; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
    have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ w, Finset.insert_subset_iff.mpr ⟨ hw, Finset.singleton_subset_iff.mpr hv ⟩ ⟩ ) ; aesop;

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERING LEMMA: Apex outside X
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If apex t ∉ X and X = {a, b, c}, then:
- All externals contain t and share an edge with X
- Externals: {a,b,t}, {a,c,t}, {b,c,t} (at most one per edge)
- Cover = {s(a, t), s(b, c)}
- X contains s(b, c)
- External on {a,b}: {a,b,t} contains s(a,t)
- External on {a,c}: {a,c,t} contains s(a,t)
- External on {b,c}: {b,c,t} contains s(b,c)
-/
lemma cover_with_external_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (hX_tri : X ∈ G.cliqueFinset 3)
    (t : V) (ht : t ∉ X) (h_apex : ∀ T, isExternalOf G M X T → t ∈ T)
    (h_has_external : ∃ T, isExternalOf G M X T) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (e₁ ∈ X.sym2 ∨ e₂ ∈ X.sym2) ∧  -- Covers X
    ∀ T, isExternalOf G M X T → (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  obtain ⟨ u, v, w, huvw ⟩ := Finset.card_eq_three.mp hX_card;
  -- Since $t \notin X$, we have $G.Adj t u \lor G.Adj t v \lor G.Adj t w$.
  have h_adj : G.Adj t u ∨ G.Adj t v ∨ G.Adj t w := by
    obtain ⟨ T, hT ⟩ := h_has_external;
    have := hT.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    have := this.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    have := hT.2.2; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
    rcases this.1 with ⟨ x, y, hxy, hx, hy, hx', hy' ⟩ ; aesop;
  rcases h_adj with ( h | h | h ) <;> simp_all +decide [ SimpleGraph.cliqueFinset ];
  · refine' ⟨ Sym2.mk ( t, u ), _, Sym2.mk ( v, w ), _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.IsNClique ];
    · exact hX_tri.1 ( by aesop ) ( by aesop ) ( by aesop );
    · intro T hT; specialize h_apex T hT; simp_all +decide [ isExternalOf ] ;
      rcases hT.2.2.1 with ⟨ x, y, hxy, hx, hy, hx', hy' ⟩ ; aesop;
  · use Sym2.mk (t, v), by
      exact?, Sym2.mk (u, w), by
      have := hX_tri.1; aesop;
    generalize_proofs at *;
    simp_all +decide [ Sym2.forall, isExternalOf ];
    intro T hT hT_notin hT_shares hT_no_other; specialize h_apex T hT hT_notin hT_shares hT_no_other; simp_all +decide [ sharesEdgeWith ] ;
    grind +ring;
  · refine' ⟨ Sym2.mk ( t, w ), _, Sym2.mk ( u, v ), _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
    intro T hT; specialize h_apex T hT; simp_all +decide [ isExternalOf ] ;
    rcases hT.2.2.1 with ⟨ u', v', huv', hu', hv', hu'', hv'' ⟩ ; aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERING LEMMA: No externals
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
Just pick any 2 edges of X. They cover X, and there are no externals.
-/
lemma cover_no_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX_card : X.card = 3) (hX_tri : X ∈ G.cliqueFinset 3) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (e₁ ∈ X.sym2 ∨ e₂ ∈ X.sym2) := by
  simp_all +decide [ Finset.card_eq_three ];
  rcases hX_card with ⟨ x, y, hxy, z, hxz, hyz, rfl ⟩ ; have := hX_tri.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  exact ⟨ s(x, y), by aesop, s(x, z), by aesop, Or.inl <| by aesop ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE LEMMA (from slot319)
-- ══════════════════════════════════════════════════════════════════════════════

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

lemma bridge_covered_by_some_m_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V) (hT : isBridgeTriangle G M T) :
    ∃ X ∈ M, ∃ u v : V, u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ s(u, v) ∈ T.sym2 := by
  obtain ⟨_, _, X, _, hX_in, _, _, hX_share, _⟩ := hT
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := hX_share
  exact ⟨X, hX_in, u, v, huv, hu_X, hv_X, edge_in_sym2_iff T u v |>.mpr ⟨hu_T, hv_T⟩⟩

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

For each X ∈ M, use universal_apex_exists to get 2 edges covering X and its externals.
- Case "no externals": cover_no_externals gives 2 edges
- Case "apex in X": cover_with_internal_apex gives 2 edges
- Case "apex outside X": cover_with_external_apex gives 2 edges

Total: 4 × 2 = 8 edges.

Bridges are covered by bridge_covered_by_some_m_edge (they share an edge with some X).
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end