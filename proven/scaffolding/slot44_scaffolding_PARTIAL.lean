/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6d1c9101-3d94-47b3-ae11-037960e944a4

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Tuza ν=4 Strategy - Slot 44: Adjacent Pair Bound (Fully Scaffolded)

TARGET: τ(T_e ∪ T_f) ≤ 4 for any two vertex-sharing packing elements

STRATEGIC VALUE (from Gemini consultation 2024-12-24):
This is THE key lemma for completing ν=4. If we prove this, then:
- Split M = {e₁,e₂} ∪ {e₃,e₄} into adjacent pairs
- τ(T_{e₁} ∪ T_{e₂}) ≤ 4
- τ(T_{e₃} ∪ T_{e₄}) ≤ 4
- All triangles are in T_L ∪ T_R (no loose triangles)
- Total: τ(G) ≤ 8 ✓

SCAFFOLDING INCLUDED (full proofs from slots 28, 32):
- tau_union_le_sum with helper infrastructure
- tau_S_le_2 with full proof chain
- tau_X_le_2 with full proof
- bridges_contain_v
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

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: tau_union_le_sum (FULL PROOF from slot28)
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangleCover (G : SimpleGraph V) (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

lemma isTriangleCover_union (G : SimpleGraph V) (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  exact ⟨ Finset.union_subset hA.1 hB.1, fun t ht => by cases' Finset.mem_union.mp ht with ht ht <;> [ exact hA.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_left _ he₁, he₂ ⟩ ; exact hB.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_right _ he₁, he₂ ⟩ ] ⟩

lemma triangleCoveringNumberOn_le_of_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (E' : Finset (Sym2 V)) (h : isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  have h_min : triangleCoveringNumberOn G triangles ≤ Finset.min (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card) := by
    unfold triangleCoveringNumberOn;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 ) G.edgeFinset.powerset ) ) <;> aesop;
  contrapose! h_min;
  refine' lt_of_le_of_lt _ ( WithTop.coe_lt_coe.mpr h_min );
  simp +decide [ Finset.min ];
  exact ⟨ E', ⟨ fun e he => by have := h.1 he; aesop, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := h.2 t ht; aesop ⟩, le_rfl ⟩

lemma exists_min_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ∃ E', isTriangleCover G triangles E') :
    ∃ E', isTriangleCover G triangles E' ∧ E'.card = triangleCoveringNumberOn G triangles := by
  obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G triangles E' ∧ ∀ E'' : Finset (Sym2 V), isTriangleCover G triangles E'' → E'.card ≤ E''.card := by
    apply_rules [ Set.exists_min_image ];
    exact Set.finite_iff_bddAbove.mpr ⟨ _, fun a ha => ha.1 ⟩;
  use E';
  unfold triangleCoveringNumberOn;
  rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 } ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from ?_ ];
  · rw [ show Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from rfl, Finset.min_eq_inf_withTop ];
    rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) ).inf WithTop.some = WithTop.some E'.card from ?_ ] ; aesop;
    refine' le_antisymm _ _ <;> simp_all +decide [ Finset.inf_le ];
    exact ⟨ E', ⟨ fun e he => by have := hE'.1.1 he; aesop, hE'.1 ⟩, le_rfl ⟩;
  · ext; simp [isTriangleCover]

lemma triangleCoveringNumberOn_eq_zero_of_not_coverable (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ¬ ∃ E', isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles = 0 := by
  unfold triangleCoveringNumberOn;
  simp_all +decide [ Finset.min ];
  rw [ Finset.inf_eq_iInf ];
  rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
  case b => exact ⊤;
  · rfl;
  · simp_all +decide [ isTriangleCover ];
  · aesop

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E', isTriangleCover G A E';
  · by_cases hB : ∃ E', isTriangleCover G B E';
    · obtain ⟨E_A, hE_A⟩ := exists_min_isTriangleCover G A hA
      obtain ⟨E_B, hE_B⟩ := exists_min_isTriangleCover G B hB;
      have h_union : isTriangleCover G (A ∪ B) (E_A ∪ E_B) := by
        exact isTriangleCover_union G A B E_A E_B hE_A.1 hE_B.1;
      exact le_trans ( triangleCoveringNumberOn_le_of_isTriangleCover _ _ _ h_union ) ( by rw [ ← hE_A.2, ← hE_B.2 ] ; exact Finset.card_union_le _ _ );
    · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
      · exact Nat.zero_le _;
      · exact fun ⟨ E', hE' ⟩ => hB ⟨ E', by exact ⟨ Finset.Subset.trans hE'.1 ( Finset.Subset.refl _ ), fun t ht => hE'.2 t ( Finset.mem_union_right _ ht ) ⟩ ⟩;
  · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
    · exact Nat.zero_le _;
    · exact fun ⟨ E', hE' ⟩ => hA ⟨ E', ⟨ hE'.1, fun t ht => hE'.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: tau_X_le_2 (FULL PROOF from slot28)
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  simp_all +decide [ Finset.ext_iff, X_ef ];
  by_contra hv_not_in_t
  have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
    exact Finset.disjoint_left.mpr fun x hx hx' => hv_not_in_t <| by have := hv x; aesop;
  have h_card : (t ∩ e) ∪ (t ∩ f) ⊆ t := by
    aesop_cat;
  have := Finset.card_le_card h_card; simp_all +decide [ Finset.card_union_add_card_inter ] ;
  linarith [ ht.1.card_eq ]

lemma X_ef_covering_number_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v}) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  simp_all +decide [ SimpleGraph.cliqueFinset ];
  set E' : Finset (Sym2 V) := Finset.image (fun u => Sym2.mk (v, u)) (e \ {v}) with hE';
  have h_cover : ∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2 := by
    intro t ht
    have h_triangle : v ∈ t := by
      unfold X_ef at ht;
      simp_all +decide [ Finset.ext_iff ];
      contrapose! ht;
      intro ht ht';
      have h_card : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        rw [ show t ∩ e ∪ t ∩ f = t ∩ ( e ∪ f ) by ext; aesop, show t ∩ e ∩ ( t ∩ f ) = ∅ by ext; aesop ] ; simp +decide;
      have h_card : (t ∩ (e ∪ f)).card ≤ t.card := by
        exact Finset.card_le_card fun x hx => by aesop;
      linarith [ ht.2 ];
    obtain ⟨u, hu⟩ : ∃ u ∈ e \ {v}, u ∈ t := by
      have h_card : (t ∩ e).card ≥ 2 := by
        unfold X_ef at ht; aesop;
      contrapose! h_card;
      rw [ show t ∩ e = { v } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_inter.mpr ⟨ h_triangle, by replace hv := Finset.ext_iff.mp hv v; aesop ⟩, fun x hx => by_contradiction fun hx' => h_card x ( by aesop ) ( Finset.mem_inter.mp hx |>.1 ) ⟩ ] ; simp +decide;
    aesop;
  have h_covering : E' ⊆ G.edgeFinset ∧ (∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2) := by
    simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
    rintro _ u hu huv rfl; have := he.1 ( show v ∈ e from by rw [ Finset.eq_singleton_iff_unique_mem ] at hv; aesop ) ( show u ∈ e from hu ) ; aesop;
  have h_card_E' : E'.card ≤ 2 := by
    have := he.card_eq;
    grind;
  refine' le_trans ( _ : triangleCoveringNumberOn G ( X_ef G e f ) ≤ E'.card ) h_card_E';
  have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
    intros S hS; exact (by
    have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Option.getD (Finset.min S) 0 ≤ E'.card := by
      intro S hS; exact (by
      have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Finset.min S ≤ E'.card := by
        exact fun { S } hS => Finset.min_le hS;
      specialize h_min_le_card hS; cases h : Finset.min S <;> aesop;);
    exact h_min_le_card ( Finset.mem_image_of_mem _ hS ));
  exact h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_covering.1, h_covering.2 ⟩ )

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  apply X_ef_covering_number_le_2 G e f v hv;
  exact hM.1.1 he

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: tau_S_le_2 (FULL PROOF from slot32)
-- ══════════════════════════════════════════════════════════════════════════════

lemma pairwise_intersecting_Se_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    Set.Pairwise ((S_e G M e).filter (· ≠ e) : Set (Finset V)) (fun t1 t2 => 2 ≤ (t1 ∩ t2).card) := by
  by_contra h_contra
  obtain ⟨t1, t2, ht1, ht2, h_disjoint⟩ : ∃ t1 t2 : Finset V, t1 ≠ t2 ∧ t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ (t1 ∩ t2).card ≤ 1 := by
    rw [ Set.Pairwise ] at h_contra;
    grind;
  have h_disjoint_M : ∀ f ∈ M \ {e}, (t1 ∩ f).card ≤ 1 ∧ (t2 ∩ f).card ≤ 1 := by
    unfold S_e at *; aesop;
  have h_packing : isTrianglePacking G ((M \ {e}) ∪ {t1, t2}) := by
    constructor;
    · intro x hx;
      simp +zetaDelta at *;
      rcases hx with ( rfl | rfl | ⟨ hx, hx' ⟩ ) <;> simp_all +decide [ S_e ];
      · unfold trianglesSharingEdge at ht2; aesop;
      · unfold trianglesSharingEdge at h_disjoint; aesop;
      · have := hM.1.1 hx; aesop;
    · simp_all +decide [ Set.Pairwise ];
      refine' ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint.2.2.2, fun a ha ha' => ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.1, fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.2, fun b hb hb' hab => _ ⟩ ⟩;
      have := hM.1;
      have := this.2 ha hb hab; aesop;
  have h_card : ((M \ {e}) ∪ {t1, t2}).card > M.card := by
    have h_card : ((M \ {e}) ∪ {t1, t2}).card = (M \ {e}).card + 2 := by
      have h_card : Disjoint (M \ {e}) {t1, t2} := by
        simp_all +decide [ Finset.disjoint_left ];
        intro f hf hfe; have := h_packing.1; simp_all +decide [ Finset.subset_iff ] ;
        constructor <;> intro h <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
        · grind;
        · have := h_disjoint_M t2 hf; simp_all +decide ;
      rw [ Finset.card_union_of_disjoint h_card, Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop;
    simp_all +decide [ Finset.card_sdiff ];
    omega;
  have h_contradiction : ((M \ {e}) ∪ {t1, t2}).card ≤ trianglePackingNumber G := by
    have h_contradiction : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro S hS;
      have h_contradiction : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by exact fun x hx => by have := hS.1 hx; aesop ), hS ⟩, rfl ⟩;
      have := Finset.le_max h_contradiction;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_contradiction _ h_packing;
  exact h_card.not_le ( h_contradiction.trans ( hM.2.ge ) )

lemma common_ext_vertex_of_diff_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V)
    (ht1 : t1 ∈ (S_e G M e).filter (· ≠ e))
    (ht2 : t2 ∈ (S_e G M e).filter (· ≠ e))
    (h_diff : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} ∧ t2 = (t2 ∩ e) ∪ {x} := by
  have h_inter : 2 ≤ (t1 ∩ t2).card := by
    have := pairwise_intersecting_Se_aux G M hM e he;
    exact this ht1 ht2 ( by aesop );
  have ht1_card : t1.card = 3 := by
    simp +zetaDelta at *;
    simp_all +decide [ S_e ];
    simp_all +decide [ trianglesSharingEdge ];
    exact ht1.1.1.1.2
  have ht2_card : t2.card = 3 := by
    simp_all +decide [ S_e ];
    simp_all +decide [ trianglesSharingEdge ];
    exact ht2.1.1.1.2;
  have ht1_inter_e_card : (t1 ∩ e).card = 2 := by
    have ht1_inter_e_card_ge2 : 2 ≤ (t1 ∩ e).card := by
      simp +zetaDelta at *;
      exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht1.1 |>.1 ) |>.2;
    have ht1_inter_e_card_le3 : (t1 ∩ e).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht1_card.le;
    interval_cases _ : Finset.card ( t1 ∩ e ) <;> simp_all +decide;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ⊆ t1 ) ; simp_all +decide ;
    have := Finset.eq_of_subset_of_card_le this; simp_all +decide ;
    have := hM.1; simp_all +decide [ Finset.subset_iff ] ;
    have := this.1; simp_all +decide [ Finset.subset_iff ] ;
    have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  have ht2_inter_e_card : (t2 ∩ e).card = 2 := by
    have ht2_inter_e_card : 2 ≤ (t2 ∩ e).card := by
      unfold S_e at ht2;
      unfold trianglesSharingEdge at ht2; aesop;
    have ht2_inter_e_card : (t2 ∩ e).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht2_card.le;
    interval_cases _ : Finset.card ( t2 ∩ e ) <;> simp_all +decide;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t2 ∩ e ⊆ t2 ) ; simp_all +decide ;
    have := Finset.eq_of_subset_of_card_le this ; simp_all +decide ;
    have := hM.1.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  obtain ⟨x, hx⟩ : ∃ x, x ∈ t1 ∧ x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} := by
    have := Finset.card_sdiff_add_card_inter t1 e; simp_all +decide ;
    obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp this; use x; simp_all +decide [ Finset.ext_iff ] ;
    exact ⟨ by specialize hx x; tauto, by specialize hx x; tauto, fun a => ⟨ fun ha => by specialize hx a; tauto, fun ha => by specialize hx a; tauto ⟩ ⟩
  obtain ⟨y, hy⟩ : ∃ y, y ∈ t2 ∧ y ∉ e ∧ t2 = (t2 ∩ e) ∪ {y} := by
    have h_diff_t2 : (t2 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t2 e; simp +decide [ ht2_card, ht2_inter_e_card ] at this ⊢; linarith;
    obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_diff_t2;
    exact ⟨ y, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.left, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.right, by ext z; by_cases hz : z ∈ e <;> simp +decide [ hz, hy.symm ] ⟩;
  have hxy : x = y := by
    contrapose! h_inter;
    have h_inter_eq : t1 ∩ t2 = (t1 ∩ e) ∩ (t2 ∩ e) := by
      grind;
    rw [ h_inter_eq ];
    refine' lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ht1_inter_e_card.le ) _;
    intro H;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t1 ∩ e ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t2 ∩ e ) ; simp +decide [ H, ht1_inter_e_card, ht2_inter_e_card ] at *;
    grind +ring;
  grind

lemma Se_structure_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ uv, uv ⊆ e ∧ uv.card = 2 ∧ ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) ∨
    (∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) := by
  by_cases h : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ t1 ∩ e ≠ t2 ∩ e;
  · obtain ⟨ t1, t2, ht1, ht2, h1, h2, h3 ⟩ := h;
    obtain ⟨ x, hx ⟩ := common_ext_vertex_of_diff_edges G M hM e he t1 t2 ( by aesop ) ( by aesop ) h3;
    refine' Or.inr ⟨ x, hx.1, fun t ht ht' => _ ⟩;
    by_cases h4 : t ∩ e = t1 ∩ e;
    · have := common_ext_vertex_of_diff_edges G M hM e he t t2 ( by
        exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
        exact Finset.mem_filter.mpr ⟨ ht2, h2 ⟩ ) ( by
        exact h4.symm ▸ h3 );
      grind;
    · have := common_ext_vertex_of_diff_edges G M hM e he t t1 ( by
        exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
        exact Finset.mem_filter.mpr ⟨ ht1, h1 ⟩ ) h4;
      grind;
  · by_cases h_empty : S_e G M e \ {e} = ∅;
    · simp_all +decide [ Finset.ext_iff ];
      contrapose! h_empty;
      have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      have := this.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      exact False.elim ( h_empty.1 ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.left ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.right ) );
    · obtain ⟨t, ht⟩ : ∃ t ∈ S_e G M e \ {e}, ∀ t' ∈ S_e G M e \ {e}, t ∩ e = t' ∩ e := by
        exact Exists.elim ( Finset.nonempty_of_ne_empty h_empty ) fun t ht => ⟨ t, ht, fun t' ht' => Classical.not_not.1 fun h' => h ⟨ t, t', by aesop ⟩ ⟩;
      have := Finset.mem_filter.mp ( Finset.mem_sdiff.mp ht.1 |>.1 );
      have := Finset.mem_filter.mp this.1;
      obtain ⟨uv, huv⟩ : ∃ uv ⊆ t ∩ e, uv.card = 2 := by
        exact Finset.exists_subset_card_eq this.2;
      grind

lemma tau_S_le_2_case1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (uv : Finset V) (huv : uv ⊆ e) (huv_card : uv.card = 2)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  unfold triangleCoveringNumberOn;
  obtain ⟨u, v, hu, hv, huv_eq⟩ : ∃ u v, uv = {u, v} ∧ u ≠ v ∧ u ∈ e ∧ v ∈ e := by
    rw [ Finset.card_eq_two ] at huv_card; obtain ⟨ u, v, huv ⟩ := huv_card; use u, v; aesop;
  have huv_edge : Sym2.mk (u, v) ∈ G.edgeFinset := by
    have := hM.1.1 he; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
    exact this.1 ( by aesop ) ( by aesop ) hv;
  have h_triangle_covering : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2)), E'.card ≤ 2 := by
    refine' ⟨ { Sym2.mk ( u, v ) }, _, _ ⟩ <;> simp_all +decide;
    intro t ht; specialize h_struct t ht; by_cases h : t = e <;> simp_all +decide [ Finset.subset_iff ] ;
  obtain ⟨ E', hE₁, hE₂ ⟩ := h_triangle_covering;
  have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', by aesop ⟩ );
  exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop ) hE₂

lemma tau_S_le_2_case2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (x : V) (hx : x ∉ e)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ G.Adj u v := by
    have := hM.1;
    have := this.1 he; simp +decide [ isTrianglePacking ] at this;
    rcases Finset.card_eq_three.mp this.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v ; simp_all +decide [ SimpleGraph.isNClique_iff ];
  obtain ⟨w, hw⟩ : ∃ w : V, w ∈ e ∧ w ≠ u ∧ w ≠ v := by
    have h_card : e.card = 3 := by
      have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      exact this.card_eq;
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase e u ) from by rw [ Finset.card_erase_of_mem huv.1, h_card ] ; decide ) v );
  by_cases huv_cover : ∀ t ∈ S_e G M e, t ≠ e → (u ∈ t ∧ v ∈ t) ∨ (w ∈ t ∧ x ∈ t);
  · set E' : Finset (Sym2 V) := {Sym2.mk (u, v), Sym2.mk (w, x)};
    have hE'_cover : ∀ t ∈ S_e G M e, t ≠ e → ∃ e' ∈ E', e' ∈ t.sym2 := by
      intro t ht ht'; specialize huv_cover t ht ht'; rcases huv_cover with ( ⟨ hu, hv ⟩ | ⟨ hw, hx ⟩ ) <;> [ exact ⟨ _, Finset.mem_insert_self _ _, by simp +decide [ hu, hv ] ⟩ ; exact ⟨ _, Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ), by simp +decide [ hw, hx ] ⟩ ] ;
    have h_triangleCoveringNumberOn_le_2 : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2 := by
      refine' ⟨ E' ∩ G.edgeFinset, _, _, _ ⟩;
      · exact Finset.inter_subset_right;
      · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( Finset.card_insert_le _ _ );
      · intro t ht;
        by_cases h : t = e <;> simp +decide [ h ] at hE'_cover ⊢;
        · exact ⟨ Sym2.mk ( u, v ), ⟨ Finset.mem_insert_self _ _, by simpa using huv.2.2.2 ⟩, by simp +decide [ huv.1, huv.2.1 ] ⟩;
        · obtain ⟨ e', he', he'' ⟩ := hE'_cover t ht h;
          simp +zetaDelta at *;
          rcases he' with ( rfl | rfl ) <;> [ exact ⟨ _, ⟨ Or.inl rfl, by simpa using huv.2.2.2 ⟩, he'' ⟩ ; exact ⟨ _, ⟨ Or.inr rfl, by
            have := Finset.mem_filter.mp ht |>.1; simp +decide [ SimpleGraph.mem_edgeSet ] at this ⊢;
            unfold trianglesSharingEdge at this; simp +decide [ SimpleGraph.mem_edgeSet ] at this;
            have := this.1.1; simp +decide [ SimpleGraph.isNClique_iff ] at this;
            exact this ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inl rfl ) ) ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inr rfl ) ) ( by rintro rfl; simp +decide [ hx ] at * ) ⟩, he'' ⟩ ];
    obtain ⟨ E', hE'_sub, hE'_card, hE'_cover ⟩ := h_triangleCoveringNumberOn_le_2;
    have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
      intro S hS; have := Finset.min_le ( Finset.mem_image_of_mem Finset.card hS ) ; simp +decide at this ⊢;
      cases h : Finset.min ( Finset.image Finset.card S ) <;> simp +decide [ h ] at this ⊢ ; exact this;
    exact le_trans ( h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'_sub, hE'_cover ⟩ ) ) hE'_card;
  · contrapose! huv_cover;
    intro t ht hte
    have ht_edges : t ∩ e = {u, v} ∨ t ∩ e = {v, w} ∨ t ∩ e = {u, w} := by
      have ht_edges : (t ∩ e).card = 2 := by
        have := h_struct t ht hte;
        have ht_card : t.card = 3 := by
          unfold S_e at ht; norm_num at ht;
          unfold trianglesSharingEdge at ht; norm_num at ht;
          exact ht.1.1.card_eq;
        rw [ this, Finset.card_union ] at ht_card ; simp +decide [ hx ] at ht_card ⊢ ; linarith;
      have ht_edges_subset : t ∩ e ⊆ {u, v, w} := by
        have := hM.1;
        have := this.1 he; simp +decide [ SimpleGraph.cliqueFinset ] at this;
        have := this.2; simp +decide [ Finset.card_eq_three ] at this;
        grind;
      have := Finset.card_eq_two.mp ht_edges;
      rcases this with ⟨ x, y, hxy, h ⟩ ; simp +decide [ h, Finset.Subset.antisymm_iff, Finset.subset_iff ] at ht_edges_subset ⊢;
      grind;
    rcases ht_edges with ( h | h | h ) <;> specialize h_struct t ht hte <;> simp +decide [ h ] at h_struct ⊢;
    · simp +decide [ h_struct ];
    · simp +decide [ h_struct ];
    · simp +decide [ h_struct ]

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain h | h := Se_structure_lemma G M hM e he
  all_goals generalize_proofs at *;
  · exact tau_S_le_2_case1 G M hM e he _ h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2;
  · apply tau_S_le_2_case2 G M hM e he h.choose h.choose_spec.left h.choose_spec.right

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Adjacent Pair Bound
-- ══════════════════════════════════════════════════════════════════════════════

/--
KEY LEMMA: τ(T_e ∪ T_f) ≤ 4 for any adjacent pair

T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f) ∪ (external bridges)

The insight is that the naive bound τ(S_e) + τ(S_f) + τ(X) = 2 + 2 + 2 = 6
can be improved to 4 because the covers OVERLAP:
- Edges through v cover both X(e,f) and parts of S_e/S_f
- The star/K4 structure of S_e forces shared coverage
-/
theorem tau_adjacent_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry

end