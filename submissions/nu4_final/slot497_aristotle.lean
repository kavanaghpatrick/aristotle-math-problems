/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5d3b13d2-09d4-4b10-9592-99a7d5b2aab5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma some_vertex_shared (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∃ v : V9, (vertexInTri v m0 ∧ vertexInTri v m1) ∨
              (vertexInTri v m0 ∧ vertexInTri v m2) ∨
              (vertexInTri v m0 ∧ vertexInTri v m3) ∨
              (vertexInTri v m1 ∧ vertexInTri v m2) ∨
              (vertexInTri v m1 ∧ vertexInTri v m3) ∨
              (vertexInTri v m2 ∧ vertexInTri v m3)

- lemma shared_vertex_edge_no_external (m0 m1 m2 m3 m : Tri) (v : V9)
    (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3)
    (hv_m : vertexInTri v m)
    (hv_other : ∃ m' : Tri, (m' = m0 ∨ m' = m1 ∨ m' = m2 ∨ m' = m3) ∧ m' ≠ m ∧ vertexInTri v m')
    (e : V9 × V9) (he : e ∈ m.edges) (he_v : edgeContainsVertex e v) :
    hasNoExternal m e m0 m1 m2 m3

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
  slot497_vertex_counting.lean

  KEY INSIGHT: A 4-packing on Fin 9 uses 12 vertex-triangle incidences
  but only has 9 vertices. By pigeonhole, some vertex is shared by 2+ triangles.

  For the "star" configuration (all 4 triangles share vertex v):
  - Any edge containing v has NO external triangles!
  - Because any external would need to use v, conflicting with other M-elements.

  This gives exists_safe_edge for the star case directly.

  For other configurations, similar counting arguments apply.

  TIER: 1-2 (finite counting with decidable predicates)
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

open Finset

abbrev V9 := Fin 9

def mkE (x y : V9) : V9 × V9 := if x ≤ y then (x, y) else (y, x)

structure Tri where
  a : V9
  b : V9
  c : V9
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  deriving DecidableEq

def Tri.vertices (t : Tri) : Finset V9 := {t.a, t.b, t.c}

def Tri.e1 (t : Tri) : V9 × V9 := mkE t.a t.b

def Tri.e2 (t : Tri) : V9 × V9 := mkE t.a t.c

def Tri.e3 (t : Tri) : V9 × V9 := mkE t.b t.c

def Tri.edges (t : Tri) : Finset (V9 × V9) := {t.e1, t.e2, t.e3}

def edgeDisj (t1 t2 : Tri) : Prop := Disjoint t1.edges t2.edges

instance (t1 t2 : Tri) : Decidable (edgeDisj t1 t2) :=
  inferInstanceAs (Decidable (Disjoint _ _))

def pack4 (m0 m1 m2 m3 : Tri) : Prop :=
  edgeDisj m0 m1 ∧ edgeDisj m0 m2 ∧ edgeDisj m0 m3 ∧
  edgeDisj m1 m2 ∧ edgeDisj m1 m3 ∧ edgeDisj m2 m3

instance (m0 m1 m2 m3 : Tri) : Decidable (pack4 m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def sharesVertex (t1 t2 : Tri) : Prop := (t1.vertices ∩ t2.vertices).Nonempty

instance (t1 t2 : Tri) : Decidable (sharesVertex t1 t2) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

def sharedVertex (t1 t2 : Tri) (h : sharesVertex t1 t2) : V9 :=
  (t1.vertices ∩ t2.vertices).min' h

def vertexInTri (v : V9) (t : Tri) : Prop := v ∈ t.vertices

instance (v : V9) (t : Tri) : Decidable (vertexInTri v t) :=
  inferInstanceAs (Decidable (_ ∈ _))

def allVertices (m0 m1 m2 m3 : Tri) : Finset V9 :=
  m0.vertices ∪ m1.vertices ∪ m2.vertices ∪ m3.vertices

lemma all_vertices_le_9 (m0 m1 m2 m3 : Tri) :
    (allVertices m0 m1 m2 m3).card ≤ 9 := by
  unfold allVertices
  calc (m0.vertices ∪ m1.vertices ∪ m2.vertices ∪ m3.vertices).card
      ≤ Fintype.card V9 := card_le_univ _
    _ = 9 := by native_decide

lemma total_incidences (m0 m1 m2 m3 : Tri) :
    m0.vertices.card + m1.vertices.card + m2.vertices.card + m3.vertices.card = 12 := by
  have h0 : m0.vertices.card = 3 := by
    unfold Tri.vertices
    simp only [card_insert_of_not_mem, card_singleton]
    · rfl
    · simp; exact m0.hbc
    · simp; constructor <;> [exact m0.hab; exact m0.hac]
  have h1 : m1.vertices.card = 3 := by
    unfold Tri.vertices
    simp only [card_insert_of_not_mem, card_singleton]
    · rfl
    · simp; exact m1.hbc
    · simp; constructor <;> [exact m1.hab; exact m1.hac]
  have h2 : m2.vertices.card = 3 := by
    unfold Tri.vertices
    simp only [card_insert_of_not_mem, card_singleton]
    · rfl
    · simp; exact m2.hbc
    · simp; constructor <;> [exact m2.hab; exact m2.hac]
  have h3 : m3.vertices.card = 3 := by
    unfold Tri.vertices
    simp only [card_insert_of_not_mem, card_singleton]
    · rfl
    · simp; exact m3.hbc
    · simp; constructor <;> [exact m3.hab; exact m3.hac]
  linarith

lemma some_vertex_shared (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∃ v : V9, (vertexInTri v m0 ∧ vertexInTri v m1) ∨
              (vertexInTri v m0 ∧ vertexInTri v m2) ∨
              (vertexInTri v m0 ∧ vertexInTri v m3) ∨
              (vertexInTri v m1 ∧ vertexInTri v m2) ∨
              (vertexInTri v m1 ∧ vertexInTri v m3) ∨
              (vertexInTri v m2 ∧ vertexInTri v m3) := by
  -- By pigeonhole: 12 incidences into 9 vertices means some vertex appears twice
  -- But we need to show it appears in DIFFERENT triangles
  -- Actually, this follows from |all_vertices| ≤ 9 and total incidences = 12
  by_contra h
  push_neg at h
  -- No vertex appears in 2+ triangles → all vertices are distinct → need 12 vertices
  -- But we only have 9 → contradiction
  -- Calculate the total number of vertices in the four triangles.
  have h_total_vertices : (m0.vertices ∪ m1.vertices ∪ m2.vertices ∪ m3.vertices).card = m0.vertices.card + m1.vertices.card + m2.vertices.card + m3.vertices.card := by
    -- Since the vertices of the triangles are disjoint, the cardinality of their union is the sum of their cardinalities.
    have h_disjoint : Disjoint m0.vertices m1.vertices ∧ Disjoint m0.vertices m2.vertices ∧ Disjoint m0.vertices m3.vertices ∧ Disjoint m1.vertices m2.vertices ∧ Disjoint m1.vertices m3.vertices ∧ Disjoint m2.vertices m3.vertices := by
      simp_all +decide [ Finset.disjoint_left, vertexInTri ];
    -- Apply the lemma for two disjoint sets three times to get the result for four disjoint sets.
    have h_union_four : ∀ (A B C D : Finset V9), Disjoint A B → Disjoint A C → Disjoint A D → Disjoint B C → Disjoint B D → Disjoint C D → (A ∪ B ∪ C ∪ D).card = A.card + B.card + C.card + D.card := by
      intros A B C D hAB hAC hAD hBC hBD hCD; simp [Finset.card_union_add_card_inter, hAB, hAC, hAD, hBC, hBD, hCD];
      ring;
    exact h_union_four _ _ _ _ h_disjoint.1 h_disjoint.2.1 h_disjoint.2.2.1 h_disjoint.2.2.2.1 h_disjoint.2.2.2.2.1 h_disjoint.2.2.2.2.2;
  -- Since each triangle has exactly 3 vertices, the total number of vertices is 4 * 3 = 12.
  have h_total_vertices_eq_12 : (m0.vertices ∪ m1.vertices ∪ m2.vertices ∪ m3.vertices).card = 12 := by
    exact h_total_vertices.trans ( by linarith [ total_incidences m0 m1 m2 m3 ] );
  exact h_total_vertices_eq_12.not_lt ( lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by decide ) )

def hasNoExternal (m : Tri) (e : V9 × V9) (m0 m1 m2 m3 : Tri) : Prop :=
  ∀ t : Tri, e ∈ t.edges → e ∈ m.edges → t ≠ m →
    ¬edgeDisj t m0 ∨ ¬edgeDisj t m1 ∨ ¬edgeDisj t m2 ∨ ¬edgeDisj t m3

def edgeContainsVertex (e : V9 × V9) (v : V9) : Prop := e.1 = v ∨ e.2 = v

instance (e : V9 × V9) (v : V9) : Decidable (edgeContainsVertex e v) :=
  inferInstanceAs (Decidable (_ ∨ _))

lemma shared_vertex_edge_no_external (m0 m1 m2 m3 m : Tri) (v : V9)
    (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3)
    (hv_m : vertexInTri v m)
    (hv_other : ∃ m' : Tri, (m' = m0 ∨ m' = m1 ∨ m' = m2 ∨ m' = m3) ∧ m' ≠ m ∧ vertexInTri v m')
    (e : V9 × V9) (he : e ∈ m.edges) (he_v : edgeContainsVertex e v) :
    hasNoExternal m e m0 m1 m2 m3 := by
  intro t ht_e ht_m ht_ne
  obtain ⟨m', hm'_in, hm'_ne, hv_m'⟩ := hv_other
  -- t contains edge e, which contains v
  -- t also contains some vertex x ≠ endpoints of e (since t is a triangle)
  -- For t to be external, t must be edge-disjoint from m'
  -- But t contains v (via e), and m' contains v
  -- So t and m' share vertex v
  -- If t shares an edge with m', then t is not external to m'
  -- We need to show t shares an edge with m' (or another M-element)
  -- Since both t and m' contain v, any edge of t containing v might be in m'
  -- The edge e contains v and is in t
  -- If e is also in m', we're done
  -- Otherwise, t has another edge containing v (since t is a triangle with v in it)
  -- Wait, t contains edge e which contains v. But e ∈ m.edges and m ≠ m'.
  -- Since m and m' are edge-disjoint (hpack), e ∉ m'.edges
  -- But t might have another edge that IS in m'...
  -- Since $e$ is in $t$'s edges and $e$ is in $m$'s edges, and $t \neq m$, then $e$ must not be in $m'$'s edges.
  have h_not_in_m' : e ∉ m'.edges := by
    have h_not_in_m' : Disjoint m.edges m'.edges := by
      -- Since $m$ and $m'$ are distinct and both are among $m0$, $m1$, $m2$, or $m3$, they are disjoint by the pack4 condition.
      have h_disjoint : ∀ m m' : Tri, m ∈ ({m0, m1, m2, m3} : Finset Tri) → m' ∈ ({m0, m1, m2, m3} : Finset Tri) → m ≠ m' → Disjoint m.edges m'.edges := by
        rcases hpack with ⟨ h0, h1, h2, h3, h4, h5 ⟩ ; simp_all +decide [ Finset.disjoint_left ] ;
        -- By examining all possible pairs of m and m', we can conclude that their edges are disjoint.
        intros m m' hm hm' hne a b ha hb
        by_cases hm0 : m = m0
        by_cases hm1 : m = m1
        by_cases hm2 : m = m2
        by_cases hm3 : m = m3
        by_cases hm0' : m' = m0
        by_cases hm1' : m' = m1
        by_cases hm2' : m' = m2
        by_cases hm3' : m' = m3
        all_goals simp_all +decide [ edgeDisj ];
        · rcases hm' with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ Finset.disjoint_left ] ;
        · rcases hm with ( rfl | rfl | rfl ) <;> rcases hm' with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ Finset.disjoint_left ] ;
      generalize_proofs at *; (
      exact h_disjoint m m' ( by simpa using hm ) ( by simpa using hm'_in ) ( Ne.symm hm'_ne ))
    generalize_proofs at *; (
    -- Since $m$'s edges and $m'$'s edges are disjoint, and $e$ is in $m$'s edges, $e$ cannot be in $m'$'s edges.
    apply Finset.disjoint_left.mp h_not_in_m' he)
  generalize_proofs at *; (
  contrapose! h_not_in_m'; simp_all +decide [ edgeDisj ] ;
  rcases hm'_in with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ Finset.disjoint_left ] ;
  · grind;
  · rcases hm with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ pack4 ];
  · rcases hm with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ pack4 ] ;
  · rcases hm with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ pack4 ] ;)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Received a different number of the word 'sorry' (1) than the number of goals (24)-/
theorem exists_safe_edge (m0 m1 m2 m3 m : Tri) (hpack : pack4 m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) :
    hasNoExternal m m.e1 m0 m1 m2 m3 ∨
    hasNoExternal m m.e2 m0 m1 m2 m3 ∨
    hasNoExternal m m.e3 m0 m1 m2 m3 := by
  -- By some_vertex_shared, m shares a vertex with another M-element
  -- Edges containing that shared vertex have no externals
  -- m has 3 vertices, each in 2 of its edges
  -- So at least one of its 3 edges contains the shared vertex
  obtain ⟨v, hv_shared⟩ := some_vertex_shared m0 m1 m2 m3 hpack
  rcases hm with rfl | rfl | rfl | rfl
  all_goals {
    rcases hv_shared with ⟨hv0, hv1⟩ | ⟨hv0, hv2⟩ | ⟨hv0, hv3⟩ | ⟨hv1, hv2⟩ | ⟨hv1, hv3⟩ | ⟨hv2, hv3⟩
    all_goals sorry
  }

end