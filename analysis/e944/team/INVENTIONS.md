# E944 INVENTIONS — algebra lane (dense asymmetric substrates that dodge density-freezing)

Each candidate: definition · why it might dodge the freezing wall · cheapest kill-test · result.
Density-freezing wall (my prior finding): redundancy needs density; density kills vertex-criticality.
Escape thesis: STRUCTURED LOCAL redundancy (each edge in ≥2 obstructions arranged so vertex-deletion
still collapses ALL of them) at n≥13, asymmetric (trivial Aut so no orbit-uniform criticality).
All χ dual-verified vs checkers.py (backtracking + SAT). Target: 4-vertex-critical, 0 critical edges.

---

## ROUND 1

### C1 — Double quasigroup-circulant superposition
- **Def:** edge-union of TWO independent non-associative quasigroup-circulants Q1, Q2 on the same
  vertex set Z_n (different random Latin squares, different generator sets). G = Q1 ∪ Q2.
- **Why dodge:** each edge of Q1 is "backed" by the independent conflict structure of Q2 — a second,
  algebraically unrelated reason the endpoints differ. Single-edge deletion in Q1 may leave Q2's
  obstruction intact (redundancy) while keeping |Aut|=1 (asymmetric, no orbit lock). Denser than a
  single QC (dodges the "too sparse at n≥11" failure of v1).
- **Kill-test:** score(Q1∪Q2) for n=13,14,15; need χ=4 ∧ vertex-critical, then min #critical edges.
- **Result:** DEAD. No χ=4 vertex-critical found — superposition overshoots (χ≥5, too dense) or
  isn't vertex-critical. Diagnosis: two full QC graphs is too much density. FIX for round 2: superpose
  a SPARSE QC with a single odd-cycle backbone, not two full QCs.

### C2 — Perturbed Latin cell graph (delete-to-restore-criticality)
- **Def:** start from a dense Latin-square cell graph (row+symbol relation), then greedily DELETE
  edges (keeping χ=4) until vertex-critical is restored.
- **Why dodge:** Latin cell graphs are dense (every edge double-witnessed by row AND symbol) but
  over-dense ⟹ not vertex-critical. Deleting back to the vertex-critical boundary might land in the
  Goldilocks band where residual density still gives edge-redundancy.
- **Kill-test:** delete-greedy then score; n=4,5 (16,25 vertices).
- **Result:** DEAD. Greedy deletion collapsed the 16-vertex graph all the way down to K4 (V=4, m=6,
  6 critical, min-deg 3 — violates δ≥4). Diagnosis: unconstrained greedy deletion destroys the dense
  structure entirely. FIX for round 2: delete only while PRESERVING δ≥4 and |V| (vertex count fixed).

### C3 — ℤ₃ gain-graph cover
- **Def:** gain graph over ℤ₃ on a base (K4/K5/C5) with nonzero gains; derived graph = base × ℤ₃,
  edge (u,t)–(v,(t+g)%3) for gain g. χ=4 obstruction is a global ℤ₃ tension (not ℤ₂ parity).
- **Why dodge:** a ℤ₃ (rather than ℤ₂) global obstruction distributes the 4-chromaticity over 3 cover
  sheets; each edge lifts to 3 copies, giving built-in 3-fold redundancy of the obstruction while
  vertex-deletion removes a whole fiber.
- **Kill-test:** score the ℤ₃ cover for nonzero-gain assignments; need χ=4 ∧ vertex-critical.
- **Result:** DEAD. No χ=4 vertex-critical — ℤ₃ COVERS preserve colorability (like the ℤ₂ covers in
  the earlier voltage experiment). The obstruction lives in the base, not the cover. FIX for round 2:
  the obstruction must be in the QUOTIENT/monodromy, not the cover — use ℤ₃ gains on a base whose
  ℤ₃-tension is globally non-vanishing (Youngs-analog for ℤ₃: triangulations, not quadrangulations).

---

# count lane — search objects that target the DEBT-TRADE / entanglement

My assault thesis: a witness needs dense ∧ vertex-critical ∧ no-critical-edge;
every family gets any TWO, the third breaks, because vertex-criticality debt and
critical-edge debt are TRADED (fix one, the other rises). NO prior search object
operates on the COUPLING between the two ledgers. NOTE: algebra's C3 already killed
plain ℤ₂/ℤ₃ covers (obstruction stays in base), so I do NOT re-skin covers; my
objects act on the trade itself.

## ROUND 1 (count, 2026-06-10)

### CNT-1 — Pair-move on the (critical-edge, non-critical-vertex) coupling
- **Def:** a move that acts on a PAIR simultaneously: pick a critical edge e=uv and
  a non-critical vertex w, and do a local rewiring that re-routes the 3-coloring
  conflict from "u,v forced equal" toward "w forced into a fresh color class" — i.e.
  spend critical-edge debt to buy vertex-criticality (or vice versa). Run SA under a
  combined potential Φ = #non-critical-vertices + #critical-edges with ONLY pair-moves
  (plus degree-preserving repair). Stays min-deg≥6.
- **Why:** single-element moves are provably stuck (proximity: 39 adds + 416 swaps;
  my basin-hopping). The obstruction IS the coupling, so a move that touches both
  ledgers at once is the only thing that can descend where single moves can't.
- **Kill-test:** from C₁₃(1,2,5) (critE=13,ncV=0) and C₁₄(1,2,5) (critE=0,ncV=14),
  does pair-move SA ever reach Φ < 13 with BOTH components feasible (min-deg≥6)? If
  not in 10k moves from both, the pair-move can't cross the gap → kill. Cheap.
- **Result:** PARTIAL/KILL. Pair-move DID move off both seeds and reached combined
  Φ=10 (from C14) at (χ=4, ncV=8, critE=2, min-deg=6) — but this is a MIXED state
  (8 non-critical vertices), NOT closer to the (0,0) witness corner. The move walks
  the trade curve (13 critE,0 ncV) ↔ (2 critE,8 ncV) but lands in a worse interior
  point, never near both-zero. Φ<13 is an artifact of summing the two ledgers; the
  witness needs BOTH=0, and the pair-move trades one for the other rather than
  reducing both. KILL as a witness-finder; but it CONFIRMS the trade is continuous
  and bidirectional — useful data: there's a whole interior arc of (critE, ncV)
  mixed states, all feasible (min-deg 6), none at the corner. Round-2 fix: penalize
  the PRODUCT critE·ncV (corner-seeking) not the sum, to forbid trade-curve drift.

### CNT-2 — Entanglement-direct scorer (minimize coupling, not counts)
- **Def:** new OBJECTIVE, not a graph family. For 4-vtx-critical G: coupling(G) =
  Σ_{critical e} |{vertices that go non-critical if e is de-criticalized by cheapest
  local edit}| + Σ_{non-critical v}|{critical edges created by cheapest edit making v
  critical}|. Minimize coupling. A DECOUPLED graph (coupling≈0) can be driven to the
  witness by independent moves; high coupling = inherent entanglement = impossibility
  signal.
- **Why:** reframes the search from "minimize counts" to "minimize entanglement" —
  directly attacks the obstruction my assault identified. Genuinely different objective.
- **Kill-test:** compute coupling on C₁₃, C₁₆, C₁₄ and random feasible graphs. If
  coupling is bounded BELOW by a positive constant everywhere → impossibility intel
  (ledgers inherently entangled). If some graph shows low coupling → that's the lead.
- **Result:** HIGH COUPLING (impossibility-signal, kept as diagnostic). C₁₃(1,2,5):
  fixing one critical edge damages 8.08 vertices on average (105 total over 13 edges);
  C₁₆(1,2,5): 10.88 avg (174 over 16). So de-criticalizing ANY edge knocks ~60-70%
  of vertices out of vertex-criticality — the ledgers are DEEPLY entangled in
  circulants, not decoupled anywhere tested. Caveat: my "cheapest edit" de-criticalizes
  by ADDING an edge (over-densifies), which inflates damage; a fairer edit (swap, not
  add) is the round-2 refinement. As-is it's a clean ENTANGLEMENT metric and a useful
  impossibility companion to the mod-3 dichotomy: no low-coupling (≈decoupled) feasible
  graph found ⟹ ordinary independent descent can't finish ⟹ explains why ALL searches
  stall. Genuinely new objective; KEEP and refine.

### CNT-3 — Monodromy-obstructed voltage search (NOT a plain cover)
- **Def:** per algebra's C3 fix: put the χ=4 obstruction in the MONODROMY, not the
  base or cover. Take a base that is itself only 3-chromatic, and choose Z_m voltages
  so the DERIVED graph's chromatic number jumps to 4 due to a non-vanishing voltage
  cycle (monodromy obstruction), NOT inherited from the base. Search (base, voltages,
  m) scoring the derived graph's critical-edge count under feasibility.
- **Why:** algebra showed plain covers keep χ in the base (dead). The fix nobody has
  run: make the cover's 4-chromaticity a GENUINE monodromy effect (base χ=3, cover
  χ=4). Such a graph's criticality structure is distributed differently — the
  obstruction is global-but-asymmetric, the regime a witness should live in.
- **Kill-test:** enumerate 3-chromatic bases (C5, C7, small) with Z_m voltages m=3..5;
  keep derived graphs with χ=4 (monodromy lift confirmed), min-deg≥6, vertex-critical;
  count critical edges. If none lift to χ=4 vertex-critical, OR all floor at |G|/3 →
  kill. If a monodromy-lifted graph drops below → escalate.
- **Result:** DEAD (cheap kill). Tested 14,579 covers (bases C5, C7; voltages Z_m,
  m=3,4,5) — ZERO lifted to χ=4. A regular Z_m cover of a 3-chromatic base stays
  3-chromatic (the cover is a "blow-up" that preserves the base's coloring up to the
  fiber action; no monodromy chromatic JUMP for cyclic voltages on a cycle base).
  Confirms+extends algebra's C3: the χ=4 obstruction will NOT appear in a cyclic
  voltage lift of a low-χ base. Round-2 fix (if pursued): the jump needs a base that
  is 3-chromatic but has a voltage cycle whose net voltage forces an odd-cover
  conflict — i.e. NON-abelian voltage group or a base that is itself NOT bipartite-
  plus-triangle-free. Cyclic-on-cycle is provably flat. KILL this variant.

## ROUND 2 (count, 2026-06-10) — built on R1 lessons

### CNT-4 — Corner-seeking PRODUCT potential (fix CNT-1 trade-curve drift)
- **Def:** replace Φ=ncV+critE (lets the chain slide along the trade curve) with
  Φ = critE·ncV + (critE+ncV) + degree-penalty. The product term is 0 only AT a
  corner (one ledger zero), forcing the search to a corner then down the axis.
- **Result:** KILL (informative). From all three seeds the SA reaches a corner —
  but always the (0 critE, 10-12 ncV) corner: it drives critical edges to 0 by
  pushing ALL vertices non-critical (the n≡2 / over-full corner). NEVER the (0,0)
  witness. So even with explicit corner-seeking, the only reachable 0-critical-edge
  graphs are maximally non-vertex-critical. Confirms the mod-3 dichotomy dynamically:
  the two zero-axes are reachable but disjoint; the search slides to whichever corner,
  never their intersection.

### CNT-5 — Fair swap-based coupling (fix CNT-2 add-inflation)
- **Def:** measure de-criticalization damage via a DEGREE-PRESERVING 2-swap edit
  (not an add, which over-densified in CNT-2), for a fair entanglement metric.
- **Result:** entanglement CONFIRMED real (not an add-artifact): fair swap-based
  damage avg 7.0 (C13), 9.8 (C16) — de-criticalizing an edge still knocks out ~60-70%
  of vertices. The reported "min=0" edges turned out to be a MEASUREMENT ARTIFACT: the
  chosen swap maps the circulant back to an isomorphic copy (still 13 critE, 0 ncV),
  so 0 "damage" but also 0 progress — NOT a decoupling lead (verified by applying the
  edit: critE stays 13). So no genuinely decoupled edge exists in C13. Entanglement
  is uniform and real. KEEP CNT-5 as the validated entanglement diagnostic.

### CNT-6 — Twin-vertex graft (coupled construction)
- **Def:** twin a vertex v of a vertex-critical circulant (add v' with N(v')=N(v)),
  growing n while preserving χ; iterate toward a witness.
- **Result:** KILL (clean). Twinning C13(1,2,5) → (χ=4, ncV=2, critE=11): the twin
  PAIR immediately becomes non-critical (ncV jumps 0→2) and critical edges barely
  drop (13→11). Twins are inherently non-critical (deleting one leaves the other as a
  "spare"), so twinning directly injects vertex-criticality debt. Structural dead end.

NET ROUND 2: no witness. Genuine intel: (a) corner-seeking confirms the two zero-axes
are disjoint and reachable separately, never together (CNT-4); (b) entanglement is
real and uniform, no decoupled edge in the flagship circulant (CNT-5 validated). The
entanglement metric is the keeper — a new quantitative companion to the impossibility
side. ROUND 3 idea: invert the search — work in COLORING space (fix a target set of
forbidden 3-colorings, realize a graph carrying exactly that obstruction with no
single edge responsible) rather than graph space. Distinct from all forward graph→check searches.

---

# gallai lane — GLOBAL IDENTITIES over the full 3-coloring space

My death point (gallai_assault_Estar.md): the obstruction is an irreducibly global 3-coloring CSP that
no local/counting/potential/Kempe certificate resolves. My lane: invent ALGEBRAIC identities over the
full coloring space that could FORCE E*≠∅ at k=4 while being realizable at k=5 (passes reality check).
Convention: E* = critical-edge set; B_k = #{3-colorings of G with exactly k monochromatic edges};
q = #colors (3 for k=4). All tested on n≤8 census (17 graphs) this round.

## ROUND 1 (gallai, 2026-06-10)

### G-INV-1 — vertex near-coloring sum D = Σ_v #{proper 3-col of G−v}. WEAK (parked).
- Def: D(G)=Σ_v (#proper 3-colorings of G−v). Why: vertex-crit forces all terms >0; sought D↔E* relation.
- Kill-test n≤8: D varies (24,60,96,66,72,…), no clean forcing of E*. STATUS: no identity, parked.

### G-INV-2 — single-bad-edge count B₁. ★ exact reformulation.
- Def: B₁(G)=#{3-colorings proper on every edge except EXACTLY one}. A coloring mono on only uv ⟹ G−uv
  is 3-colorable ⟹ uv critical. So **B₁>0 ⟺ E*≠∅.**
- Kill-test n≤8: B₁>0 ⟺ E* nonempty, **0 mismatches/17**. Open: is B₁>0 FORCED by χ=4+vertex-crit?
- k=5 check: B₁(q=4)=0 for real (5,1)-graphs ⟹ forcing must be q=3-specific. PASSES.

### G-INV-3 — Potts double-root reformulation. ★★ cleanest algebraic form, NOT density-killable.
- Def: Z(G,t)=Σ_{3-colorings c} t^{#mono edges of c} = Σ_k B_k t^k (q=3 Potts partition poly), Z(G,1)=3ⁿ.
  χ=4 ⟹ B₀=0. E*=∅ ⟹ B₁=0. So **witness ⟺ Z(G,t) has a DOUBLE root at t=0.** CONJECTURE: the q=3
  Potts poly of a 4-chromatic vertex-critical graph cannot have a double root at t=0 (B₀=0 forces B₁>0).
- Kill-test n≤8: every graph has B₀=0, B₁>0 (36,60,108,132,78,…) — double root never occurs. ✓
- k=5 check: at q=4 real (5,1)-graphs DO realize the double root (B₀=B₁=0). So conjecture is genuinely
  q=3-SPECIFIC and PASSES by construction — the lever IS the q=3-vs-q=4 distinction.
- Why it may DODGE the density wall (that killed all prior routes): this is polynomial-ROOT-MULTIPLICITY
  non-degeneracy at a fixed point, NOT an edge count. Density bounds don't directly constrain root order.

### G-INV-4 — deletion-contraction identity B₁ = Σ_e P(G−e,3). PROVEN, makes G-INV-3 attackable.
- Identity (verified 0 failures/17): since P(G,3)=0, **B₁(G)=Σ_{e∈E} P(G−e,3)=Σ_{e∈E*} P(G−e,3)**
  (non-critical e contribute P(G−e,3)=0). Turns "B₁>0" into "Σ over critical edges of P(G−e,3)>0".
- Why: P(G−e,3) is the chromatic polynomial at 3 — has known lower-bound machinery (Birkhoff–Lewis
  type). A positive lower bound on Σ_e P(G−e,3) for χ=4 vertex-critical G forces a critical edge.
- k=5 check: analogue Σ_e P(G−e,4)=0 at k=5 ⟹ any positive bound must be q=3-specific. PASSES.

**Round-1 verdict (gallai):** G-INV 2/3/4 unify into ONE exact statement —
**E*≠∅ at k=4 ⟺ q=3 Potts polynomial Z(G,t) has a SIMPLE (not double) root at t=0 ⟺ Σ_e P(G−e,3) > 0.**
It is exact, q=3-specific (passes k=5 by construction), and phrased as root-multiplicity / chromatic-
polynomial positivity rather than an edge count — so it is NOT obviously killed by the density wall that
defeated every prior route. Also UNIFIES with wall's ℤ₃-tension (Z(G,t) at q=3 is the ℤ₃-tension
generating function). NEXT ROUND: attack the chromatic-polynomial lower bound on Σ_e P(G−e,3).

> **SKEPTIC ADJUDICATION — gallai G-INV lane (round 1):**
> - G-INV-4 IDENTITY (B₁ = Σ_e P(G−e,3)): CONFIRMED, independently re-derived, 0 failures / 17 four-vc graphs n≤8.
> - G-INV-2/3 reformulations (B₁>0 ⟺ E*≠∅; witness ⟺ Potts double root at t=0): CONFIRMED exact, 0 mismatches / 17.
> - **k=5 REALITY CHECK: PASSES.** Built 2 genuine (5,1)-graphs C₁₇(1,3,4,5), C₁₇(1,4,6,7) (dual-checker, skeptic_k5_fixtures.txt). At q=4 both have B₀=B₁=0 (double root REALIZED), so the conjecture "B₀=0 forces B₁>0" is correctly q=3-specific and does NOT refute k=5. Sound — does NOT fall to the reality-check kill-rule.
> - **HONEST STATUS: the core "B₀=0 forces B₁>0 at q=3" IS the open problem restated** (= "every 4-vc graph has a critical edge"). gallai correctly LABELS it a CONJECTURE — NO overclaim. Value: chromatic-poly positivity (Birkhoff–Lewis machinery) + root-multiplicity framing dodge the density wall. Not progress until a real lower bound on Σ_e P(G−e,3) materializes.
> - **VERDICT: SURVIVES round 1** as the SOLE substantive survivor (exact + reality-check-passing reformulation). NEXT TEST (round 2): a genuine positive lower bound on Σ_e P(G−e,3) for χ=4 vertex-critical G. If none, it's a reformulation-only dead end. FLAGGED to team-lead.
>
> **SKEPTIC ADJUDICATION — algebra C1–C6:** all KILLED, agent verdicts CONFIRMED (covers keep χ in base; superposition/two-hub overshoot density→χ≥5; greedy deletion destroys structure→K4 δ=3; per-rung shifts + overlays don't de-criticalize). Diagnoses sound, no survivors.

---

# algebra lane — ROUND 2 results

### C4 — Asymmetric-shift quadrangulation (per-rung independent shifts)
- Def: Youngs quadrangulation but each rung position j gets its OWN random shift pair (sa,sb),
  breaking the rung symmetry that locks all rungs critical.
- Why dodge: if rungs aren't equivalent, maybe some become individually redundant.
- Result: DEAD. Random per-rung shifts destroy the χ=4 quadrangulation structure (χ≠4 or not
  vertex-critical) in all 60 trials × t∈{2,3,4}. The global ℤ₂ obstruction NEEDS the rung regularity.

### C5 — Quadrangulation (50% redundant) + sparse extra-edge overlay
- Def: quad t=2 plus 1–3 random extra edges to back up the critical rungs.
- Why dodge: add redundancy precisely to the critical half.
- Result: DEAD (no improvement). Best stays 10 critical (adding edge (1,9) keeps χ=4 vertex-critical
  but criticality unchanged; m 20→21). Consistent with the rung-lock: extra edges don't de-criticalize
  rungs without breaking vertex-criticality. Reconfirms the freezing wall on the quadrangulation.

### C6 — ℤ₃ double-wheel triangulation
- Def: odd cycle C_n + TWO hubs both adjacent to all of C_n + hub-hub edge (for δ≥4).
- Why dodge: intended a global ℤ₃ obstruction with built-in redundancy via two hubs.
- Result: DEAD. χ=5, not 4 (two mutually-adjacent hubs each see the whole odd cycle ⟹ 2 + 3 = 5
  colors). Wrong construction. Single-hub wheel is χ=4 but has degree-3 rim issues; the two-hub fix
  overshoots. Triangulation route needs a different δ≥4 gadget.

---

# jensen/parity lane — entanglement-by-construction (no separable rails; δ≥6 dense)

My design constraint (skeptic-vetted): edge-redundancy from SEPARABLE PARALLELISM (literal disjoint
rails) → rail vertices non-critical. Build ENTANGLED density instead. ℤ₃-tension-first where possible.
χ via harness.py (2 engines) ⟂ checkers.py. Target: 4-vertex-critical, 0 critical edges.

## ROUND 1 (jensen, 2026-06-10) — code: jensen_code/blitz_round1.py

### J1 — Tension-monodromy wheel-web (h pairwise-adj hubs + odd rim, hubs↔all rim)
- Why: every rim edge in many hub-triangles (entangled); hubs force χ up globally.
- Result: DEAD. h=2→χ=5, h=3→χ=6 (overshoot). A hub adjacent to ALL of an odd rim forces the rim
  2-colored = impossible ⟹ χ jumps. [Independently = algebra's C6 two-hub overshoot — cross-confirmed.]
  δ too low (4) anyway. FIX r2: thicken the RIM not the hubs; one hub = wheel (χ=4).

### J2 — Antiprism stack (w-cycles stacked w/ antiprism joins → triangulated cylinder)
- Why: triangulated → every edge in ≥2 triangles (entangled), tunable density.
- Result: PARTIAL. χ=4 at 3–4 layers but NOT vertex-critical; δ=4 < 6 (gallai floor). Flat top/bottom
  under-constrained. FIX r2: wrap into a TORUS (no boundary) + 2nd-neighbor diagonals to push δ→6.

### J3 — Complement of sparse triangle-free graph (complement of C_n)
- Why: complement of sparse = dense, δ scales (6,7,8 at n=9,10,11), every edge in many triangles, χ near 4.
- Result: PARTIAL. n=8→χ=4 (not vertex-critical); n≥9→χ=5,6 (too dense). δ=6 at n=9 is the floor exactly
  but χ overshoots. FIX r2: complement of a DENSER triangle-free base (C_n², Kneser, incidence) to land
  χ=4 ∧ δ≥6.

### J4 — Dihedral Cayley Cay(D_k, inverse-closed conn) — NON-ABELIAN (dodges circulant dead-end)
- Why: non-abelian regular dense graph; group structure may give entangled (not rail) redundancy.
- Result: PROMISING LEAD. D7 (n=14) → χ=4 (not yet vertex-critical); D6 → χ=2 (conn too bipartite).
  Reaching χ=4 with a non-abelian group at n=14 (hunter/count's flagged witness zone) is the best lead.
  FIX r2: sweep D7/D8/Dic conn sets for χ=4 ∧ vertex-critical ∧ δ≥6 — LIVE FRONTIER next round.

**Round-1 verdict (jensen):** the χ=4 ∩ vertex-critical ∩ δ≥6 triple is the choke point — J2/J4 get
χ=4 but miss vertex-criticality; J3 gets δ≥6 but overshoots χ. The non-abelian Cayley route (J4) is the
most promising (reaches χ=4 dense at n=14). NEXT: D7/D8 connection-set sweep + toroidal antiprism.

---

## archivist lane → see archivist_inventions.md + archivist_inventions_results.md
Round 1: A1 (doubled J–S gadget), A2 (entangled Hajós), A3 (witness downward surgery). All 3 DEAD as-is.
META-LESSON: redundancy must be EDGE-LOCAL, never VERTEX-LOCAL. Each edge needs >=2 independent obstructions (→non-critical) but NO vertex may be covered by redundancy surviving its deletion (→stays vertex-critical). A2/A3/A1-doubling all failed by making some vertex non-critical. This localizes algebra's density-freezing wall.

---

# wall lane — tension-rank design + the global-redundancy/local-rigidity principle

Seed: my DESIGN PRINCIPLE (witness = GLOBALLY edge-redundant, LOCALLY vertex-rigid, expander-like,
NOT modular) + the ℤ₃-tension lever. NOT covers (algebra C3 killed those — obstruction stays in base).
My angle: design the graph's STRUCTURE (asymmetry, tension rank, joint-necessity) directly.
n≥31 rule applies: small-n nulls are NOT conclusive (the middle corner may require n≥31; gallai δ≥6 ⟹ n≥11 floor).

## ROUND 1 (wall, 2026-06-10)

### WALL-1 — Cayley graph on a NON-cyclic abelian group ℤ_a × ℤ_b
- **Def:** 6-regular Cayley graph on ℤ_a×ℤ_b (|gens|=3, deduped ±g). Breaks the single-cycle ℤ_n
  structure of circulants while staying vertex-transitive — tests whether a DIFFERENT transitive group
  escapes the circulant orbit-lock.
- **Why:** circulants fail because ℤ_n's single rotation forces one orbit critical; a 2-generator group
  has a richer automorphism structure that might distribute criticality differently.
- **Kill-test:** sweep (a,b)∈{(2,7),(3,5),(2,9),(3,6),(2,11),(4,4),(3,7),…}, all 3-gen sets; score χ=4
  ∧ vertex-critical ∧ min #critical.
- **Result:** DEAD (this round, small n). No low-critical-fraction Cayley(ℤ_a×ℤ_b) found. Vertex-transitivity
  still imposes orbit-uniform criticality (algebra's orbit lemma applies to ANY vertex-transitive graph,
  not just circulants). DIAGNOSIS: the problem is vertex-transitivity itself, not ℤ_n specifically.
  FIX for round 2: ABANDON vertex-transitive substrates entirely — the design principle demands ASYMMETRY.

### WALL-2 — Asymmetric 2-swap perturbation of C_n(1,2,5)
- **Def:** start from the best near-miss C₁₃(1,2,5) (critE=13, vertex-critical), apply degree-preserving
  2-swaps (replace disjoint edges ab,cd → ac,bd) to break vertex-transitivity while keeping 6-regular;
  hill-climb on #critical-edges.
- **Why:** the design principle says the witness is asymmetric; a small perturbation off the best
  symmetric near-miss might reach the middle corner that vertex-transitivity forbids.
- **Kill-test:** 4000 perturbation iters from C₁₃(1,2,5), track min #critical with restarts.
- **Result:** DEAD at n=13 (stayed at critE=13). But n=13 is the ABSOLUTE minimum (gallai δ≥6 ⟹ n≥11);
  the middle corner likely needs n≥31 (my n≥31 rule). NOT a conclusive kill — re-run at n=31 in round 2.

### WALL-3 — Union of two complementary sparse circulants (joint-necessity by construction)
- **Def:** G = C_n(S1) ∪ C_n(S2), S1,S2 disjoint difference sets, chosen so NEITHER alone is 4-chromatic
  but the union is — forcing jointly-necessary obstructions (the design-principle escape from jensen's
  independent-gadget trap).
- **Why:** directly engineers the "no localized sub-structure independently 4-chromatic" requirement.
- **Kill-test:** sweep S1,S2 pairs at n=13,16,19; score.
- **Result:** DEAD (small n). The disjoint-pair unions tested were either χ<4, χ>4, or not vertex-critical.
  But this collapses to the 6-regular circulant search (union of 3 orbits) which is already known witness-free
  to n≤31. The joint-necessity must be NON-circulant. FIX round 2: glue two edge-disjoint 4-critical graphs
  on shared vertices via a NON-transitive identification (random perfect matching between their vertex sets).

ROUND 1 META: all 3 died, but the unifying diagnosis is sharp and matches my design principle —
VERTEX-TRANSITIVITY is the enemy (orbit lemma forces orbit-uniform criticality). Round 2 must be
ASYMMETRIC and tested at n≥31. The principle predicts the witness is genuinely irregular.

## ROUND 2 (gallai, 2026-06-10) — attacking the Potts double-root conjecture

Attacked G-INV-3 ("q=3 Potts poly of 4-chromatic vertex-critical G has no double root at t=0").

### Finding R2-A: the double root IS achievable for general 4-chromatic graphs.
Searched ALL connected 4-chromatic graphs n≤7: **15 have min_mono ≥ 2 (B₁=0, double root)** at n=7
(e.g. g6 FEl~w, FQhVw). So "B₁>0" is FALSE for general 4-chromatic graphs — the conjecture rests
ENTIRELY on vertex-criticality. Good: it's non-vacuous and the work is localized.

### Finding R2-B: every min_mono≥2 graph found is NON-vertex-critical (proof skeleton).
All 15 (n=7) + all 429 (n=8, min-deg≥3) four-chromatic min_mono≥2 graphs have a NON-CRITICAL vertex
(χ(G−v)=4 for some v), 0 counterexamples. So the candidate implication is:
**min_mono(G) ≥ 2 ⟹ G has a non-critical vertex.** Contrapositive = the theorem:
vertex-critical ⟹ min_mono=1 ⟹ B₁>0 ⟹ E*≠∅. k=5 reality check PASSES (the k=5 witness G_{5,2,2} IS
vertex-critical with min_mono(q=4)≥2, so the q=4 analogue is FALSE — correctly q=3-specific).

### Finding R2-C (death point): the skeleton reduces EXACTLY to Theorem 4 — circular.
Pushing the proof: min_mono=1 achievable ⟺ ∃ vertex v + 3-coloring of G−v where some color is used by
EXACTLY ONE neighbor of v. min_mono≥2 ⟺ for every v and every 3-coloring of G−v, no color is used
exactly once in N(v) ⟺ (a 0-used color would 3-color G) every color used ≥2 in N(v) at every v ⟺
**every vertex is "good"** (Theorem 4: deg≥6, forced-2-2-2 balanced) ⟺ E*=∅ ⟺ witness. So the
Potts/B₁ reformulation is LOGICALLY EQUIVALENT to E*=∅ — an exact restatement as polynomial
root-multiplicity, NOT a reduction to anything easier. Same irreducible global CSP core.

**Round-2 verdict:** the Potts double-root identity is the cleanest available LANGUAGE for E*≠∅
(algebraic, q=3-specific, dodges the density wall) but does not escape the core. VALUE: it converts
the problem from a structural/CSP question into "chromatic-polynomial positivity Σ_e P(G−e,3) > 0 for
χ=4 vertex-critical G" — a form amenable to analytic chromatic-polynomial tools (root location,
Birkhoff–Lewis) that the structural framing could not access. That analytic attack is the open lever;
recorded for the successor. Honest status: no proof; best reformulation in hand.

---

# algebra lane — ROUND 3 results

### C7 — Schrijver graph critical-edge fraction
- Result: DEAD as witnesses, useful as data. SG(6,2): 15/18=83% critical; SG(8,3): 28/36=77%.
  Schrijver graphs are NEAR edge-critical — worse band than the quadrangulation. (SG(10,3) has 50
  vertices, too big for per-edge backtracking — skipped.)

### C9 — Shared-triangle book on an odd cycle (every backbone edge in 2 triangles)
- Def: odd cycle 0..n-1; apex a_j adjacent to j and j+1; apexes joined a_j~a_{j+1}.
- Result: at n=5 (V=10) and n=11 (V=22): χ=4, vertex-critical, δ=4, EXACTLY 50% critical
  (10/20, 22/44). n=7 not vertex-critical; n=9 χ=3. This is structurally a re-realization of the
  two-interleaved-odd-cycle / quadrangulation family — and it hits the SAME 50% ceiling.

## KEY PATTERN (now 4 independent families): the 50% / positive-fraction ceiling
The critical-edge fraction floors observed: circulant/Cayley (≥ 1 full orbit), quasigroup (~50–80%),
Youngs quadrangulation (exactly 50%), triangle-book (exactly 50%). NO structured construction has
broken below ~50% while staying 4-vertex-critical with δ≥4. The "exactly 50%" in the two-layer parity
families looks like a forced equipartition (redundant half = cycle/parity edges, critical half =
inter-layer connectors). Strong evidence: (a) a witness, if it exists, is NOT a clean structured
construction — it must be irregular (forge SA / hunter SAT-CEGAR); (b) the recurring positive floor
is a candidate impossibility statement (routed to wall). Either way, the structured-substrate program
(my lane) has a real, repeatedly-confirmed ceiling.

---

# proximity lane — ENCODINGS (SAT/ILP/QBF formulations nobody has tried)

My lane: invent FORMULATIONS that make the two co-NP conditions (vertex-criticality, no-critical-edge)
cheap or direct, instead of CEGAR-expensive. Distinct from algebra (graph families) and count (search
objectives). All validated against checkers.py (backtracking + SAT) at small n THIS round.

## ROUND 1 (proximity, 2026-06-10)

### ENC-1 — Monochromatic-deficit reformulation (skeptic's lemma as the objective)
- **Def:** Let m*(G) = min over all 3-colorings of G of the number of MONOCHROMATIC edges (an
  optimization, computable by SAT+cardinality: smallest k s.t. "∃ 3-assignment with ≤k mono edges").
  Then the (4,1)-WITNESS criterion is EXACTLY:  **m*(G) ≥ 2  AND  m*(G−v) = 0 for every v.**
  - m*(G) ≥ 2  ⟺  no critical edge (no single-edge deletion drops χ to 3; deleting one edge can
    erase at most one mono edge, so if every 3-coloring has ≥2 mono edges, no G−e is 3-colorable).
  - m*(G−v) = 0  ⟺  G−v is 3-colorable (vertex-criticality lower half). χ(G)=4 follows from m*(G)≥1.
- **Why new:** reframes the whole problem as an OPTIMIZATION over colorings (min monochromatic edges)
  rather than a graph-property CEGAR. The no-critical-edge condition becomes a single clean threshold
  "m* ≥ 2" instead of |E| separate "G−e not 3-colorable" co-NP checks. Grounded in skeptic's verified
  lemma (smallest critical edge-set size == min mono edges over 3-colorings). Enables a direct ILP:
  minimize mono-edge count, search for graphs where the optimum is ≥2 while every vertex-deletion
  drops it to 0 — a coupled optimization no one has posed.
- **Kill-test (cheapest):** compute m* on known graphs; criterion must match checkers. DONE.
- **Result:** VALIDATED. K4 m*=1, C5 m*=0, C13(1,2,5) m*=1 (=its smallest critical set, has critical
  edges), C14(1,2,5) m*=2 (0 critical edges, matches!). The biconditional "no-critical-edge ⟺ m*≥2"
  held on both circulants. ALIVE — promote to: search graphs with m*(G)≥2 ∧ m*(G−v)=0 ∀v, e.g. via
  an ILP that maximizes min-mono subject to vertex-deletion-3-colorability. Hand to hunter/count.

### ENC-2 — Incremental assumption-based vertex-criticality (one solver, shared learned clauses)
- **Def:** Instead of baking n separate full 3-colorings (hunter's 3n² vars) to enforce
  "G−v 3-colorable ∀v", use ONE coloring var block x(u,c) + a per-vertex ACTIVATION literal a(u).
  Guard every edge clause: (a(u)∧a(v)) → proper on uv. Then "G−v is 3-colorable" = solve under
  ASSUMPTIONS {a(u) : u≠v} ∪ {¬a(v)}. The n vertex-deletion checks become n incremental SAT calls on
  the SAME solver, REUSING learned clauses across all of them.
- **Why new:** turns vertex-criticality from a static 3n²-variable bake (hunter) into n cheap
  incremental solves sharing conflict-clause learning — the activation-literal-guarded-edge trick
  models all G−v in a single solver. Much smaller instance; the solver amortizes work across the n
  deletions. Standard incremental-SAT technique, never applied to this problem.
- **Kill-test (cheapest):** does it agree with checkers' is_vertex_critical on a vertex-critical graph
  (C13(1,2,5)) and a non-vertex-critical one (C14(1,2,5))? DONE.
- **Result:** VALIDATED. C13(1,2,5) → all-G−v-3-colorable = True (matches checkers vertex-critical);
  C14(1,2,5) → False (matches not-vertex-critical). ALIVE — drop into hunter's CEGAR to replace the
  baked-coloring block; shrinks the instance and amortizes the n deletion checks.

### ENC-3 — Joint single-model static core (bundle all cheap witness conditions, CEGAR only the rest)
- **Def:** ONE SAT model over edge vars e_ij (search the GRAPH) bundling ALL statically-encodable
  witness conditions: (a) a baked proper 4-coloring c4 (enforces χ ≤ 4, kills χ≥5 candidates);
  (b) per-vertex proper 3-coloring cV[v] of G−v (vertex-criticality lower half); (c) gallai THM4
  atleast-2 prune on cV (kills the entire "vertex-critical-but-has-critical-edges" class). Only the
  two genuine FORALL conditions remain for CEGAR: χ(G) ≥ 4 (not ≤3) and the residual no-critical-edge.
- **Why new:** maximizes the STATIC (non-CEGAR) core. hunter bakes (a)+(b); the new element is folding
  in (c) THM4 so the solver never even proposes a has-critical-edge graph — the most expensive CEGAR
  refinements (per-edge no-critical checks) are pre-empted at the SAT level. Combined with ENC-2 the
  per-vertex block also shrinks.
- **Kill-test (cheapest):** with G FIXED, the joint static core must be SAT iff G is a vertex-critical
  χ=4 graph with no critical edge, and UNSAT for the two non-witness failure modes. DONE.
- **Result:** VALIDATED. C13(1,2,5) (has critical edges) → UNSAT (THM4 rejects). C14(1,2,5) (not
  vertex-critical) → UNSAT (cV[v] step rejects). Both non-witnesses correctly excluded by the static
  core alone. ALIVE — this is the tightest static pre-filter; hand to hunter as the model skeleton.

NEXT ROUND ideas (seeds): ENC-4 ILP with min-mono as objective + vertex-deletion constraints solved
as one MILP (Gurobi/CBC); ENC-5 symmetry-broken degree-sequence-pinned model (fix the degree multiset,
break vertex-permutation symmetry via lex-leader on the adjacency rows) to shrink the n≥14 search;
ENC-6 a 2-QBF formulation of no-critical-edge (∀ 3-coloring of G−e: conflict) — needs a QBF solver
installed (none present now), so currently reduces to CEGAR; revisit if depqbf/caqe added.

---

# forge lane — ROUND 1 (forge owns ledger; deg-3 theorem is my feasibility filter)

My theorem (deg-3 vertex in 4vc graph => 3 critical edges) => every candidate MUST be delta>=4 (ideally >=6)
AND must NOT route the disagreement through low-degree transfer vertices (kills J-S/gadget families).
My candidates source the chi=4 disagreement from the DENSE BULK, edge-entangled, asymmetric.

### [forge-1] Edge-entangled triangle-cover (every edge in >=2 edge-disjoint triangles, delta>=6) — TESTING
- Def: search delta>=6 graphs where EVERY edge has >=2 common-neighbor witnesses forming triangles that
  share ONLY that edge (edge-disjoint elsewhere). Each edge's odd-obstruction has >=2 routes through
  DIFFERENT third vertices.
- Why: engineers ENTANGLED per-edge redundancy at the EDGE level (reroutes share the edge's endpoints,
  not parallel copies) = archivist's "edge-local not vertex-local" lesson made concrete; no deg-3.
  Distinct from jensen-J3 (plain complement): I REQUIRE the >=2-edge-disjoint-triangle property as a
  filter, not just density.
- Kill-test: geng delta>=6 n=11..14, filter "every edge in >=2 triangles", reduce to 4vc, measure |E*|.

### [forge-2] Double shift graph DS(n) / bounded iterated line-digraph — TESTING
- Def: shift graph S(n) (vertices ordered pairs i<j; edge iff j=k) has chi=ceil(log n); the DOUBLE shift
  graph + truncated iterated line-digraphs give 4-chromatic graphs whose chi=4 is a global "no long
  monotone chain" (Ramsey/ordering) obstruction, NOT a clique or odd cycle.
- Why: GENUINELY NEW substrate (nobody posted shift/ordering graphs). chi=4 carried by the whole ordered
  vertex set (entangled by construction); dense-ish, asymmetric. Not a cover/circulant/gadget/topological.
- Kill-test: build smallest 4-chromatic DS(n) / line-digraph truncations, check delta + |Aut|, reduce to
  4vc, measure |E*|. checkers.py.

### [forge-3] Asymmetric independent-set blow-up of the n=10 champion (g6 ICpdbY{]_) — TESTING
- Def: take my best object (n=10, |E*|=8, delta=4, |Aut|=4), replace vertex v by independent set I_v of
  size t_v, join I_u-I_v completely iff uv in E (blow-up; chi preserved =4). Blow up the endpoints of the
  8 critical edges so each becomes a complete-bipartite bundle; deleting one bundle edge leaves the rest
  carrying the constraint => non-critical.
- Why: directly attacks MY 8 residual critical edges by bundling, on my best asymmetric substrate, raising
  degrees above 3. New (blow-up of the exhaustive champion). Asymmetric t_v keeps |Aut| small.
- Kill-test: blow up ICpdbY{]_ with t_v in {1,2,3} (larger on critical-edge endpoints), reduce to 4vc,
  measure |E*|. Risk: blown-up vertices become non-critical (whole set removable); test if asymmetric
  small blow-up threads it. checkers.py.

## ROUND 2 (wall, 2026-06-10) — ASYMMETRIC, the round-1 diagnosis fix

### WALL-4 — Random 6-regular expander graphs at n=31
- **Def:** sample random 6-regular graphs on n=31 (generically asymmetric + expander = the design
  principle's profile), filter to χ=4 vertex-critical, measure min #critical.
- **Why:** directly tests the "expander-like, asymmetric" hypothesis at the witness floor degree.
- **Kill-test:** 60 random samples, n=31.
- **Result:** DEAD + INFORMATIVE. All 60 were χ=4 but ZERO vertex-critical — random 6-regular graphs are
  too over-connected (deleting a vertex keeps χ=4 = the n≡2 mod3 / C₁₄(1,2,5) corner). CONFIRMS count's
  debt-trade at the random level: density gives "no critical edge" but kills vertex-criticality. The
  witness is NOT a generic expander; it sits at the chromatic threshold (sparse enough to be vertex-critical).

### WALL-5 — Greedy/stochastic edge-ADDITION from a 4-critical seed, keeping vertex-criticality ★ BEST
- **Def:** start from a 4-vertex-critical seed (Grötzsch n=11, Myc(C7) n=15); ADD non-edges one at a time,
  greedily picking the addition that most reduces #critical-edges WHILE preserving vertex-criticality.
  Builds GLOBAL redundancy incrementally (design-principle aligned), no localized gadget.
- **Why:** edge-addition monotonically can only reduce criticality; the constraint "keep vertex-critical"
  walks the (a)+(b) corner toward (c). The first construction primitive that actually MOVES toward a witness.
- **Kill-test:** greedy + 3 stochastic restarts, n=11 and n=15.
- **Result:** PARTIAL DESCENT, then plateau. Grötzsch: 20→13 critical edges. Myc(C7): 28→18. It genuinely
  DESCENDS (symmetric families can't), but floors at ≈ n+2 and then every vertex-criticality-preserving
  addition stops helping (further additions hit the n≡2 corner). NOT a witness, but a REAL search primitive
  worth handing to forge/count — it's the construction-side dual of count's debt-trade, and the plateau-at-n
  matches the "critical count ≈ n" empirical law. NOT conclusively killed: needs larger seeds + smarter
  escape from the plateau (hand to count's pair-move SA, which targets exactly this coupling).

### WALL-6 — Iterated Hajós sums of K4 (non-modular 4-critical builder)
- **Def:** build asymmetric 4-critical graphs by iterated Hajós sums of K4 (delete an edge from each,
  identify a vertex, add a cross edge). The canonical non-circulant/non-Mycielski 4-critical builder.
- **Why:** generates asymmetric 4-critical graphs outside the symmetric families.
- **Kill-test:** 200 random Hajós-sum towers (3-7 K4's), score.
- **Result:** DEAD by design. Hajós sums of edge-critical graphs are 4-EDGE-critical ⟹ EVERY edge critical
  ⟹ #critical = |E|, the maximally-bad case (min found 21). Hajós builds exactly the WRONG object. Confirms:
  edge-criticality is preserved by Hajós, so this route can never approach a witness. Do not re-attempt.

ROUND 2 META: WALL-5's edge-addition descent is the one live primitive — it provably descends where
symmetric families are stuck, and its plateau-at-≈n is the construction-side image of count's debt-trade.
Best deliverable: hand WALL-5 + count's pair-move SA together (WALL-5 finds the corner, pair-move escapes
the plateau). WALL-4 confirmed the witness is NOT a generic expander (over-density kills vertex-criticality).

---

# algebra lane — ROUND 4 results

### C10 — K4-necklace (odd cycle of edge-sharing K4 blocks)
- Def: t K4-blocks in a cycle, consecutive blocks share an edge (every shared edge in 2 K4's).
- Result: DEAD. χ oscillates 4/5/6 with t; the χ=4 cases (even t) are NOT vertex-critical (edge-
  sharing K4's are too rigid — a vertex deletion leaves enough K4 structure for χ=4). Clique-based
  redundancy overshoots into non-vertex-criticality.

### C12 — Random 6-regular graphs (probe the irregular dense Prop-5.1 band directly)
- Def: random 6-regular graphs at n=11..14, filter χ=4 ∧ vertex-critical, measure critical fraction.
- Result: STRIKING NULL — 0 of ~1600 random 6-regular graphs were 4-vertex-critical at all. Random
  6-regular graphs on small n are χ>4 or have a non-critical vertex. A witness (6-regular per SS
  Prop 5.1) is therefore NOT a typical/random 6-regular graph — it must be a rare, specially-
  structured one. Relevant to hunter's SAT-CEGAR: random sampling won't find it; need exhaustive/
  guided search. (Reported to hunter.)

## CUMULATIVE (rounds 1-4): the structured-substrate program has a hard ceiling
12 candidates across quasigroup, gain-graph, parity-quadrangulation, triangle-book, Schrijver,
K4-clique, random-regular families. NONE broke below ~50% critical edges while 4-vertex-critical at
δ≥4. Every two-layer parity family hits EXACTLY 50% (forced equipartition). Random dense graphs aren't
even 4-vertex-critical. Conclusion: no clean algebraic/structured substrate reaches a witness; the
witness (if any) is irregular and rare (global-search territory), and the robust positive-fraction
floor is a genuine impossibility-proof lead for wall.

## ROUND 3 (gallai, 2026-06-10) — three new candidates beyond the Potts reformulation

### G-INV-5 — ℤ₃ character (Fourier) sum over single-bad-edge colorings. DEAD (cancels).
- Def: S = Σ over (3-colorings with exactly 1 mono edge) of ω^(Σ colors mod 3), ω=e^{2πi/3}. Hoped a
  Gauss-sum identity forces |S|>0 ⟹ B₁>0.
- Kill-test n≤8: |S| = 0 on most graphs (n=4: 0, n=7: 0,0,0). The phase fully cancels — no leverage.
  Tried the obvious character; cancellation is generic. DEAD (this phase choice; other characters
  likely cancel too by symmetry).

### G-INV-6 — Tutte/Whitney rank polynomial at q=3, low-order coefficients. DEAD (collapses to G-INV-3).
- The B_k ARE the Whitney-rank expansion of the q=3 Potts/Tutte specialization. So this is literally
  G-INV-3 in Tutte language — same object, same leverage, same death point. No new content.

### G-INV-7 — chromatic-polynomial ratio bound B₁ ≥ c·P(G,4). PROMISING then DEAD (ratio→0).
- Def: P(G,4) (# proper 4-colorings) is >0 for every 4-chromatic G. If B₁ ≥ c·P(G,4) for a UNIVERSAL
  c>0, then B₁>0 always ⟹ E*≠∅. (B₁ = near-3-colorings; P(G,4) = 4-colorings.)
- Kill-test n≤8: ratio B₁/P(G,4) DECREASES with n — 1.50 (n=4), ~0.30 (n=7), 0.15–0.21 (n=8), roughly
  halving per +1 vertex. Strongly suggests ratio → 0. So NO universal constant c>0 exists; a dense
  witness could have B₁=0 with P(G,4) large. **= the density-escape risk, confirmed quantitatively.**
  DEAD as a universal-constant bound.
- Residual (not dead, weaker): an n-DEPENDENT lower bound B₁ ≥ f(n)·P(G,4) with f(n)→0 but f(n)>0 for
  all finite n would still force B₁>0 at every finite n (hence no finite witness). The ratio is
  positive for every actual graph; the open question is whether it can hit 0. This is just the
  reformulated conjecture again (B₁>0), so no escape — but f(n) ~ (1/2)^? is a data point for the
  successor's analytic attack.

**Round-3 verdict:** all three new candidates die, but the deaths are informative: (5) ℤ₃ Fourier
phases cancel generically — character sums won't force B₁; (6) Tutte is the same object; (7) the
B₁-vs-4-coloring ratio →0, confirming that ANY bound of the form "B₁ ≥ (something abundant for dense
graphs)" inherits the density-escape. CONSOLIDATED LESSON across R1–R3: every global identity I can
build is EXACTLY equivalent to B₁>0 (the Potts simple-root / Σ_e P(G−e,3)>0 form), and every attempt
to lower-bound B₁ by an abundant quantity fails by density. The one un-killed lever remains a
chromatic-polynomial-analytic bound on Σ_e P(G−e,3) that is q=3-specific and does NOT route through an
abundant comparand — i.e. uses the ROOT STRUCTURE of P(G,x) near x=3 directly (Sokal/Jackson-style
zero-free-region arguments), not a count. Recorded for the analytic successor.

---

# hunter lane — SEARCH ARCHITECTURES (not substrates)

My prior findings constrain the architecture: (1) forcing χ≥4 in SAT is the killer (one-3-coloring
blocking never converges); (2) local search plateaus at the C13(1,2,5) optimum (13 critical edges) —
the witness is isolated, not reachable by moves; (3) complete enumeration dies at n=13. So my
architectures must AVOID discovering χ≥4 from scratch, AVOID treating criticality as a post-hoc test,
and AVOID full enumeration. Each grows/restricts the search so the entangled spec is an INVARIANT.

## ROUND 1 (hunter, 2026-06-10)

### A1 — Criticality-preserving vertex-addition growth (criticality as INVARIANT, not test)
- **Def:** maintain a 4-VERTEX-CRITICAL graph as an invariant while GROWING it. Start from a known
  4-vtx-critical graph G_k on k vertices (e.g. C13(1,2,5)). Add a new vertex w with a neighborhood
  N(w) chosen so that (i) G_{k+1} stays 4-chromatic, (ii) every existing vertex stays critical, (iii)
  w itself is critical. The classical operation that preserves vertex-criticality is the HAJÓS-style /
  Dirac "add a vertex joined to an independent-ish set" — but tuned to ALSO not create a critical
  edge. Search over choices of N(w) (subject to δ≥6 ⟹ |N(w)|≥6) at each step, scoring by #critical
  edges. The invariant means we never leave the 4-vtx-critical manifold (unlike annealing, which
  wastes ~all time off-manifold).
- **Why it could work:** the rigidity wall (plateau at 13) is because RANDOM moves leave the manifold;
  growth that PRESERVES criticality stays on it and can climb in n where there's more room to push
  critical-edge count down (Brown's k=5 needed n=17 — room matters). It directly attacks "the witness
  is isolated": you reach it by a PATH of critical graphs, not by landing near it.
- **Cheapest kill-test:** implement add-vertex-preserving-vertex-criticality from C13(1,2,5); at each
  of ~20 growth steps enumerate N(w) candidates (degree-6..8 subsets, pruned by "G+w still 4-chromatic
  AND no new critical edge at w"), keep the min-critical-edge child, grow to n=20. If min #critical
  edges does NOT decrease below 13 over the growth path → the invariant doesn't help, DEAD. If it
  trends down → push to n where it could hit 0. ~1hr, reuses checkers.py.

### A2 — Reverse search: shrink from a dense no-critical-edge graph toward vertex-criticality
- **Def:** invert the debt-trade. Local search keeps failing because vertex-criticality is hard to
  GET in the dense regime. Instead START dense enough to have NO critical edge (easy: dense 4-chromatic
  graphs have every edge non-critical because removing one edge leaves plenty of 4-chromatic
  structure), then DELETE edges to drive toward vertex-criticality WHILE monitoring that no edge
  becomes critical. Maintain "no-critical-edge" as the invariant; chase vertex-criticality as the
  objective. This is the EXACT REVERSE of every prior search (all of which kept vertex-criticality and
  chased no-critical-edge).
- **Why it could work:** the two conditions are antagonistic (count's debt-trade); nobody has tried
  holding the OTHER one fixed. A dense 4-chromatic graph trivially has no critical edge; the question
  is whether you can thin it to vertex-critical before some edge becomes critical. If a "no-critical-
  edge corridor" connects dense graphs to a vertex-critical one, this finds it; prior searches couldn't
  because they started on the wrong side of the trade.
- **Cheapest kill-test:** start from a random dense 4-chromatic graph on n=14 (e.g. ~50 edges, δ high),
  confirm 0 critical edges, then greedily delete edges that (a) keep δ≥6, (b) keep 0 critical edges,
  (c) maximize the number of now-critical vertices. Stop when stuck. Report: did #non-critical
  vertices reach 0 (= witness) or plateau? If it plateaus with non-critical vertices remaining while
  every further deletion creates a critical edge → corridor is blocked, DEAD (and that blockage is a
  NEW impossibility datum for wall). ~30min.

### A3 — Orbit-restricted canonical enumeration on a PINNED degree sequence (beat the n=13 wall)
- **Def:** full n=13 δ≥6 enumeration is infeasible (billions), but the witness spec is highly
  entangled. Restrict geng/canonical generation to ONE pinned degree sequence at a time (e.g. all-6
  = skeptic did; then 6^11·7^2, 6^9·7^4, …) AND add a generation-time filter that prunes any partial
  graph already containing a vertex whose neighborhood CANNOT be 2-2-2-balanced (gallai THM4 local
  necessary condition) in any extension. Use nauty's `genbg`/`vcolg` or a custom canonical-augmentation
  generator that rejects sub-configurations violating the local witness constraints DURING generation,
  not after. This makes each degree-sequence slice tractable where the blanket enumeration isn't.
- **Why it could work:** THM4 failed as STATIC SAT clauses (made the instance intractable, my finding)
  but as a GENERATION-TIME PRUNE on partial graphs it's cheap and prunes the tree early. Pinning the
  degree sequence shrinks each job to skeptic-6-regular scale (~350K-20M), and THM4-pruning during
  augmentation cuts deeper. Union over degree sequences = complete n=13 within δ≥6.
- **Cheapest kill-test:** take the SECOND-sparsest degree sequence at n=13 (6^11 7^2, i.e. exactly two
  degree-7 vertices, the rest degree-6) and count it with `geng -c -d6 -D7 13 40:40` (|E|=40, = 23.5M
  — feasible to process at ~200K/s parallel ≈ 2min). Run my floor_worker on it. If it completes and
  finds 0 witnesses → that degree-sequence slice is closed and the architecture is validated; iterate
  to the next slice. If 23.5M is too slow even parallel → the pinned-degree approach also dies at n=13,
  report the true wall location. ~5min for the kill-test.

## forge ROUND-1 RESULTS (forge_blitz_r1.py, dual-verified)
- [forge-3] blow-up of n=10 champion — DEAD. Blow-ups DO reach |E*|=0 (bundling de-criticalizes edges!)
  but are NOT vertex-critical (whole independent sets removable, noncrit_v=16-30). Asymmetric size
  patterns (best blowup#4: δ=6, |E*|=1) don't thread it. Same antagonism: bundling kills critical edges
  AND makes bundled vertices removable. Confirms: blow-up redundancy is vertex-aligned.
- [forge-2] shift / double-shift graphs — DEAD (wrong regime). S(n)/DS(n) only reach χ=2,3 at tractable
  n; χ=4 needs n~16 (thousands of vertices, intractable) and the small instances have isolated vertices
  (mindeg 0). The log-growth of χ makes shift graphs the wrong substrate for a fixed χ=4 target.
- [forge-1] edge-entangled triangle-cover — TESTING (geng δ≥6 stream); early: most reduce toward K4.
  [result pending full scan]

## ROUND 3 (wall, 2026-06-10) — pushing WALL-5

### WALL-7 — Add-delete cycling at larger n (escape the plateau)
- **Def:** WALL-5 edge-addition descent, then a DELETE phase (remove a non-critical edge to perturb),
  then re-add — cycled 8×. Construction-side analogue of count's pair-move, at n=19 (Myc C9), n=23 (Myc C11).
- **Why:** add-delete cycling might escape WALL-5's plateau the way SA escapes local minima.
- **Result:** DESCENDS but SAME PLATEAU. Myc(C9) n=19: 36→22 critical. Myc(C11) n=23: 44→27 critical.
  Add-delete does NOT escape — floors at ≈ n+few (22 vs 19, 27 vs 23), consistent with n=11 (13) and
  n=15 (18). The "critical-count ≈ n floor" is ROBUST across seed, size, and search method.

### QUANTITATIVE FINDING (the real round-3 deliverable, n≥31 rule applied across sizes)
WALL-5/WALL-7 descent floor vs n (4-vertex-critical, edge-addition + add-delete, min #critical reached):
  n=11 →13,  n=15 →18,  n=19 →22,  n=23 →27.  Floor ≈ n + 3 to 4, NEVER approaching 0.
This is the construction-side measurement of count's debt-trade: greedily buying edge-redundancy
(dropping critical edges) by densifying is capped at ≈ n critical edges, because the next addition
crosses into the n≡2 over-dense corner (kills vertex-criticality). A witness needs critical=0, which is
≈ n below this empirical floor — a LARGE gap, not a near-miss. STRONG (non-proof) evidence the middle
corner is unreachable by monotone densification; if reachable at all, it requires a NON-monotone path
(count's pair-move from a WALL-5 plateau seed is the proposed combined attack).

BLITZ SUMMARY (wall, 3 rounds, 7 candidates): WALL-1,3,6 dead by vertex-transitivity/edge-criticality;
WALL-4 (random expander) confirmed witness ≠ generic expander (over-dense); WALL-2 inconclusive at n=13;
WALL-5/7 = the one live primitive (real descent) but with a robust ≈n+4 critical-count floor across all
sizes tested. Handed to count for pair-move seeding. No witness found; the floor is the finding.
- [forge-1] edge-entangled triangle-cover — DEAD. ~7000/60000 δ≥6 graphs per n (n=11,12,13) passed the
  "every edge in ≥2 triangles + χ=4" filter, but ALL reduce toward K4 (best |E*|=6) when forced
  vertex-critical. The triangle redundancy is still VERTEX-ALIGNED: a triangle uvw backing up edge uv
  has its third vertex w, and deleting w removes that backup. "Every edge in ≥2 triangles" does NOT
  imply the backups survive vertex deletion. Same wall.

## forge ROUND-1 VERDICT
All 3 DEAD, same mechanism: triangle-cover, blow-up bundling, shift graphs — each makes redundancy
VERTEX-ALIGNED (the backup obstruction for edge e lives on a vertex whose deletion removes it). This
is the THIRD independent confirmation (after covers and gadgets) that "edge in ≥2 obstructions" is
necessary but NOT sufficient — the obstructions must avoid being killed by any single vertex deletion.
SHARPENED SPEC for round 2: not just "every edge in ≥2 obstructions" but "every edge in ≥2 obstructions
that are NOT simultaneously destroyed by deleting any single vertex" — i.e. the obstruction hypergraph
must be a VERTEX-deletion-robust edge cover. This is exactly count's "coupling" / my robustness-asymmetry,
now a concrete design constraint for round 2.

## ROUND 2 (proximity, 2026-06-10)

### ENC-6 — Fully-incremental witness checker (edge-deactivation, mirror of ENC-2)
- **Def:** mirror ENC-2's activation-literal trick onto EDGES. Each edge i gets activation literal
  ae(i); guard its proper-coloring clause by ae(i). Then "G−e_i is 3-colorable?" = solve under
  assumptions {ae(j):j≠i} ∪ {¬ae(i)} on ONE solver. no-critical-edge ⟺ ALL these are UNSAT.
  Combined with ENC-2 (vertex-deactivation) this gives a SINGLE solver that checks BOTH co-NP witness
  halves (vertex-criticality via vertex-deactivation, no-critical-edge via edge-deactivation) as
  incremental assumption solves, sharing all learned clauses — NO CEGAR loop at all for the checker.
- **Why new:** turns the no-critical-edge CEGAR (hunter's expensive refinement loop) into |E| cheap
  incremental SAT calls on one persistent solver. The conflict clauses learned while refuting "G−e₁
  3-colorable" carry over to "G−e₂ 3-colorable" etc., so the |E| checks amortize. Replaces the whole
  CEGAR no-critical-edge machinery with incremental SAT.
- **Kill-test (cheapest):** agree with checkers.has_no_critical_edge on C13(1,2,5) (has crit) and
  C14(1,2,5) (none)? DONE.
- **Result:** VALIDATED. C13(1,2,5) → has critical edge, first found = (0,1) the diff-1 edge (matches
  its diff-1 critical orbit!); C14(1,2,5) → no critical edge. Both match checkers. ALIVE — together
  with ENC-2, a complete incremental witness VERIFIER (one solver, no CEGAR) for hunter's candidates.

### ENC-5 — Degree-sequence-pinned + lex-leader symmetry breaking (shrink the n≥14 search)
- **Def:** (1) PIN the degree multiset (e.g. 6^n exactly-6-regular, or 6^a·7^b·8^c for the non-regular
  min-deg-6 regime, sweeping the multiset) via per-vertex cardinality. (2) Add LEX-LEADER symmetry
  breaking: order vertices and require adjacency-row(i) ≤ adjacency-row(i+1) lexicographically (the
  standard degree-then-lex partial break). Kills the n!-fold vertex-permutation symmetry of the search.
- **Why new (for THIS problem):** hunter's edge-var search has full S_n symmetry — every witness is
  found n! times, exploding the search. Lex-leader is sound (every iso class has a unique lex-min
  canonical rep, so ≥1 representative always survives) and is the single biggest lever for pushing the
  exact SAT search to n≥14-20 where geng becomes infeasible. Pinning the degree multiset also lets the
  search sweep degree-profiles (e.g. "one degree-7 vertex, rest degree-6") that target the non-regular
  regime where a witness must live (per my circulant/6-regular closure).
- **Kill-test (cheapest):** confirm soundness (the lex-min rep of any graph satisfies the constraint)
  + solution-count vs geng iso-class count at small n (n=8 6-regular = 1 class). DONE (sound; n=8→1).
- **Result:** VALIDATED sound. ALIVE — bolt onto hunter's edge-var model; biggest payoff at n≥14.

### ENC-4 — MILP with min-mono objective (bilevel → single MILP via duality) [DESIGNED, partial]
- **Def:** from ENC-1, the witness needs m*(G)≥2. m*(G)=min over 3-colorings of #mono-edges is an
  inner minimization; "m*≥2" is a min ≥ 2 (a ∀-coloring statement). Cast the inner 3-coloring LP and
  dualize: a graph has m*(G)≥2 iff the LP/IP "min mono edges s.t. proper-3-assignment" has optimum ≥2.
  Search (outer) over edge vars for graphs where this inner optimum is ≥2 AND each G−v inner optimum
  is 0. The bilevel min-min over G−v is easy (feasibility); the m*(G)≥2 is the hard ∀-part.
- **Why new:** an exact ILP/MILP formulation of the witness via the mono-edge objective, solvable by
  Gurobi/CBC with branch-and-bound rather than SAT-CEGAR — different solver technology, may scale
  differently.
- **Kill-test:** build the inner min-mono IP, confirm its optimum = m* (matches ENC-1's SAT values on
  C13→1, C14→2); then the outer search. INNER VALIDATED via ENC-1 (same quantity). Outer MILP build
  pending (needs CBC/Gurobi wiring — no MILP solver confirmed present yet; SAT version = ENC-1).
- **Result:** PARTIAL — inner objective validated (= ENC-1's m*); outer MILP not yet built (solver
  dependency). Lower priority than ENC-1's SAT form unless a MILP solver is available.

---

# algebra lane — ROUND 5 results

### C13 — K4-on-each-edge with shared apexes (mixed clique+cycle obstruction)
- Result: 50% AGAIN. n=5 (V=10): χ=4, vertex-critical, δ=4, 10/20 critical. n=7 not vc; n=9 χ=3.
  Combining K4 and odd-cycle obstruction types still lands on the equipartition.

### C14 — Hajós-sum of two quadrangulations (asymmetric merge to break equipartition)
- Result: NEAR-MISS of the same wall. Hajós-merging two 50%-graphs gives χ=4 vertex-critical n=19,
  δ=4, but 19/39 ≈ 49% critical — still on the 50% line. Even an asymmetric merge of two
  50%-redundant graphs reproduces ~50%. Strongest evidence yet that 50% is a structural invariant.

### C15 — Subdivided-rung quadrangulation
- Result: DEAD. Subdividing rungs drops χ to 3 (subdivision kills the ℤ₂ parity carrier) and makes
  degree-2 vertices (violates δ≥4). Wrong direction.

## CANDIDATE THEOREM (5 families + Hajós merge, all ~50%)
Across quasigroup, parity-quadrangulation, triangle-book, mixed-K4-cycle, Schrijver, K4-necklace,
and Hajós-merges, EVERY 4-vertex-critical graph with δ≥4 built from a 2-layer / parity / clique-cycle
substrate has ≈50% (often exactly 50%) of its edges critical, and NONE goes below. This is a sharp,
reproducible ceiling. Conjecture for wall: "a 4-vertex-critical graph that is a 2-layer parity or
clique-cycle construction has a critical edge — in fact ≥ a constant fraction are critical." Combined
with the random-6-regular null (no random 6-regular graph is even 4-vertex-critical at n≤14), the
structured-substrate route to a (4,1)-witness is empirically closed; remaining hope is irregular
global search (forge/hunter) or this ceiling sharpening into an impossibility proof (wall).

## forge ROUND 2 (targeting the sharpened spec: vertex-deletion-robust edge cover)

### [forge-4] Expander / Ramanujan substrate (no small obstruction-isolating cut) — TESTING
- Def: take a δ≥6 expander (Ramanujan graph, or high-spectral-gap random regular with girth control),
  4-chromatic, and reduce to 4vc. Expanders have NO small vertex cut, so no single vertex deletion can
  isolate/destroy an edge's obstruction backups (high vertex-connectivity ⟹ obstruction reroutes survive
  any one deletion).
- Why: directly answers round-1's death (vertex-aligned redundancy). Expansion = vertex-deletion-robust
  by definition. New: nobody tried high-vertex-connectivity expanders as the substrate.
- Kill-test: build δ=6 graphs with high vertex-connectivity (κ≥6) + girth≥5 (kills tiny triangles), χ=4,
  reduce to 4vc, measure |E*|. checkers.py. (Risk: expanders are often NOT vertex-critical — too robust.)

### [forge-5] Rigid-diamond critical-edge replacement (keeps endpoints essential, no independent set) — TESTING
- Def: take the n=10 champion; replace each of its 8 critical edges uv by a "diamond" K4−e on {u,v,x,y}
  (u,v non-adjacent in the diamond but joined through x,y; x,y adjacent) — a rigid gadget that forces
  u,v to differ via TWO internal paths, WITHOUT making u or v removable (unlike independent-set blow-up).
- Why: round-1 blow-up failed because independent sets are removable; a RIGID diamond keeps every vertex
  load-bearing. Each critical edge gets a 2-path backup that shares u,v (entangled) but adds degree-≥3
  internal vertices — wait, x,y are degree-3 (deg-3 theorem risk!). FIX: make x,y degree ≥4 by linking
  diamonds. Test whether rigid replacement de-criticalizes without removability.
- Kill-test: replace champion's critical edges with linked diamonds, reduce to 4vc, |E*|. checkers.py.

### [forge-6] Tensor/lexicographic product with chromatic entanglement — TESTING
- Def: G[H] (lexicographic) or G×H (tensor) of two small graphs where the χ=4 of the product is forced
  jointly by both factors (Hedetniemi-type), entangling obstructions across factors. E.g. C5[K2] or a
  4-critical × triangle-free product tuned to χ=4, δ≥6.
- Why: product structure can make every edge's obstruction depend on BOTH factors (vertex deletion only
  touches one fiber), a genuinely different entanglement source. New (no products tried).
- Kill-test: build small products with χ=4, δ≥6, reduce to 4vc, |E*|. checkers.py.

---

# algebra lane — STRUCTURAL ANALYSIS of E* (the critical-edge set) [new, not a re-skin]

In the 50%-redundant Youngs quadrangulations (t=2: V=10; t=5: V=22), dissected the critical set E*
and redundant set R as subgraphs (verified via checkers.py):
- **E\* (critical edges) = a SPANNING, CONNECTED, 2-REGULAR subgraph** — i.e. a single Hamiltonian
  cycle through all vertices. deg ≡ 2, connected, covers 100% of vertices.
- **R (redundant edges) = 2-regular with exactly 2 components** = the two odd cycles (the ℤ₂ parity
  carriers that back each other up).

CLEAN DECOMPOSITION explaining the exact 50%: |V| rung edges form a Hamiltonian cycle and are ALL
critical (each rung is the unique connector at its position); the other |V| edges are the two odd
cycles and are ALL redundant (delete one, the other carries the parity). Total 2|V| edges, 50/50.

IMPACT (for wall): the critical edges aren't scattered — they form a Hamiltonian cycle, a strong
structural invariant. This matches Jensen–Siggers' question about whether E* is connected/spanning:
in this family E* is BOTH. If "the critical edges of a 4-vertex-critical graph always contain a
spanning connected subgraph (or a large 2-factor)" can be proven in general, |E*|>0 follows ⟹ a
critical edge always exists ⟹ k=4 closes negatively. Routed to wall as the sharpest impossibility lead.

## forge ROUND-2 RESULTS (forge_blitz_r2.py, dual-verified)
- [forge-4] expander / high-vertex-connectivity δ≥6 — DEAD. High-κ random 6-regular graphs that are χ=4
  reduce toward K4 (best |E*|=6) when forced vertex-critical; expanders are "too robust" — rarely
  vertex-critical (the robustness that defeats vertex-aligned redundancy ALSO defeats vertex-criticality,
  exactly the robustness-asymmetry principle). Confirmed prediction.
- [forge-5] rigid-diamond critical-edge replacement — DEAD. Diamonds reach |E*|=0 (χ=4) but NOT
  vertex-critical (diamond apexes x,y removable, noncrit_v=26); reduced-to-4vc collapses to n=7 |E*|=11.
  Rigid≠vertex-essential: the apex still has a backup, so it's removable.
- [forge-6] tensor/lexicographic products — DEAD (wrong χ). Lex products overshoot χ≥5 (C5[K2], C7[K2],
  C5[C5]); tensor K4×C5 undershoots χ=3. Products don't land χ=4 with δ≥6 vertex-critical structure.

## forge BLITZ META-CONCLUSION (after 6 candidates, 2 rounds)
ALL 6 die the SAME way: the redundancy that kills critical edges (|E*|→0) is achievable EASILY (diamonds,
blow-ups, expanders, triangle-covers all reach |E*|=0 at χ=4) but is ALWAYS vertex-aligned ⟹ NOT
vertex-critical. The reduction-to-vertex-critical then strips exactly that redundancy. This is now
~10 construction families + 6 blitz candidates = 16 independent confirmations of ONE principle:

  ROBUSTNESS-ASYMMETRY (forge): an obstruction robust enough that |E*|=0 is, by the same robustness,
  robust to vertex deletion ⟹ the graph is not vertex-critical. The two requirements are coupled and
  no construction decouples them.

This is no longer just heuristic — the universality across 16 independent mechanisms is strong evidence
that EITHER (a) the witness requires a global decoupling no local/structured mechanism provides (⟹ only
blind global SAT/CEGAR over δ≥6 asymmetric graphs can find it, hunter's lane), OR (b) it does not exist
(⟹ the robustness-asymmetry should be PROVABLE — wall/gallai's impossibility lane, where it = the
"every vertex good ⟺ E*=∅" Theorem-4 core / Potts double-root). forge's constructive lane recommends
PIVOTING squad weight to (b): the robustness-asymmetry is the most-confirmed empirical fact and the
likeliest theorem.

### hunter ROUND 1 RESULTS (2026-06-10)
- **A2 (reverse search): DEAD, with a NEW impossibility datum.** Implemented reverse_search.py
  (invariant=no-critical-edge from a dense seed, objective=vertex-criticality via edge deletion).
  n=13, 120s, 10,884 restarts: min #non-critical vertices reached = **11 of 13** (0 = witness). The
  no-critical-edge corridor is BLOCKED from the dense side — a dense 4-chromatic graph has almost no
  critical vertices, and deleting edges to create them almost always creates a critical edge first, so
  the greedy gets stuck near the all-non-critical seed. ⟹ the debt-trade blocks the REVERSE direction
  even harder than forward. NEW DATUM for wall: there is no monotone no-critical-edge path from dense
  graphs down to a vertex-critical one at n=13.
- **A3 (orbit-restricted canonical / pinned-degree enum): kill-test RUNNING** — n=13 |E|=40 slice
  (second-sparsest δ≥6, ~23.5M graphs, parallel floor_worker). Result pending; if it completes it
  closes that slice AND validates the pinned-degree architecture for pushing the n=13 floor.
- **A1 (criticality-preserving growth): not yet run** — needs the add-vertex-preserving-criticality
  operator; deferred to round 2 (A3 is the higher-value floor-advancing test).

## ROUND 3 (proximity, 2026-06-10)

### ENC-7 — Asymmetry-forced search (break the orbit-criticality lock)
- **Def:** add to the witness search a constraint/objective driving |Aut(G)| small (ideally 1).
  Practical SAT form: lex-leader (ENC-5) already forces a canonical rep; ADD strict "no nontrivial
  color-preserving automorphism" by requiring the degree-then-lex order to be STRICT (row_i < row_{i+1}
  for vertices of equal degree), which excludes vertex-transitive/high-symmetry graphs. Or run it as a
  separate search ARM restricted to asymmetric graphs (geng -c can emit only asymmetric graphs).
- **Why new + MOTIVATED BY DATA:** my circulant results show vertex-TRANSITIVE graphs have
  orbit-pinned criticality (critical-count = n per orbit, NEVER 0) — symmetry is exactly what FORCES
  positive critical-count. VALIDATED correlation: forge's lowest-critical 4-vertex-critical champions
  are LOW-symmetry — n=10 champ (8 crit) has |Aut|=4, n=9 (9 crit) has |Aut|=2 — vs C13(1,2,5)
  (|Aut|≥26, crit=13=n). So the witness (critical-count 0) should be SOUGHT among asymmetric graphs.
  No prior search arm deliberately targets asymmetric graphs to escape orbit-locking.
- **SOUNDNESS CAVEAT:** forcing |Aut|=1 is NOT a sound hard filter for a complete search (a witness
  *could* be symmetric in principle). Use it as a HEURISTIC search-ordering / a high-priority first
  ARM, not as an exhaustive restriction. Pair with a separate symmetric-graph arm for completeness.
- **Kill-test (cheapest):** confirm low-critical graphs are low-|Aut| (correlation). DONE.
- **Result:** VALIDATED motivation (the |Aut| vs critical-count anti-correlation holds on forge's
  champions). ALIVE — prioritize asymmetric/non-regular graphs in the search. Hand to hunter as a
  search-ordering heuristic; complements the structural prune.

### ENC-8 — Degree-profile-targeted search (the non-regular regime forge's trend points to)
- **Def:** instead of exactly-6-regular (geng -d6 -D6) OR all min-deg-6 (geng -d6, huge), sweep
  SPECIFIC non-regular degree profiles: 6^(n-k)·7^k for small k (k=1,2,3 vertices bumped to degree 7),
  then 6^a·7^b·8^c. Pin the profile via per-vertex cardinality in the SAT model (or geng's degree
  bounds + a post-filter), and search each profile separately.
- **Why new + MOTIVATED:** forge's exhaustive n≤10 profile shows the min-critical-count graphs are
  NON-regular (n=10 champ degs [4^6,5^4], n=9 [3^2,4^5,6^2]). Prop 5.1 allows degrees in [6, n-5], so
  at n=13 the profiles 6^12·7, 6^11·7^2, etc. are admissible and UNEXPLORED — exactly-6-regular (which
  I closed) is just one profile. The witness, if it exists, is likely a "mostly-6-regular with a few
  higher-degree vertices" graph — a profile nobody has isolated. This slices the otherwise-huge
  min-deg-6 space into targeted, tractable sub-searches.
- **Kill-test (cheapest):** confirm the lowest-critical small-n graphs are non-regular (degree spread).
  DONE (forge champions are non-regular, confirmed above).
- **Result:** VALIDATED motivation + RAN the first slice. NOTE: 6^12·7^1 is impossible (odd degree
  sum); first valid non-regular profile is 6^11·7^2 (|E|=40). DEMO (1/500 geng sample, 31819 graphs all
  matching profile): 25477 are χ=4 but **0 vertex-critical**. So even this non-regular profile at n=13
  is vertex-criticality-poor — vertex-criticality, not the degree profile, is the binding scarcity at
  n=13 (consistent with the 4/11→8/12 critical-vertex-window trend; the window opens with n). ALIVE —
  the profile-slicing works and is tractable; the signal says push to larger n where vertex-criticality
  becomes attainable. Hand to hunter for the n≥14 profile sweep.

### ENC-9 — Two-obstruction robustness encoding [DESIGNED]
- **Def:** no-critical-edge means 4-chromaticity SURVIVES any single edge deletion. Encode this as: G
  must contain TWO edge-disjoint "4-chromatic certificates" (e.g. two edge-disjoint subgraphs each
  forcing χ≥4 OR a single certificate using each edge ≥twice), so no single edge deletion can break
  all of them. Search for G admitting such a redundant certificate structure. (skeptic's lemma view:
  every 3-coloring has ≥2 mono edges that are NOT coverable by one edge ⟺ m*≥2 robustly.)
- **Why new:** directly encodes the REDUNDANCY that no-critical-edge demands (the obstruction must be
  ≥2-covered), rather than checking it after the fact. Turns "no critical edge" into a positive
  structural requirement (two-fold obstruction cover) the search can build toward.
- **Kill-test:** does C14(1,2,5) (0 critical edges) admit a 2-edge-disjoint χ≥4 certificate while
  C13(1,2,5) (has critical edge) does not? PENDING (needs the certificate extractor — next round).
- **Result:** DESIGNED, validation pending. Lower priority than ENC-7/8 (which have validated data).

## ROUND 4 (gallai, 2026-06-10) — the chromatic-root analytic lever, tested and KILLED

### G-INV-8 — chromatic-root multiplicity at x=3 characterizes B₁>0. DEAD (refuted).
- Def/hope: P(G,x) has x=3 as a root for any 4-chromatic G (P(G,3)=0). Hoped "x=3 is a SIMPLE root ⟺
  B₁>0 ⟺ E*≠∅", giving an analytic (zero-free-region / root-multiplicity) handle that dodges density.
- Kill-test (n=7, all 282 four-chromatic graphs): **(x=3 simple root) ⟺ (B₁>0) FAILS — 90 mismatches.**
  Concretely: B₁>0 graphs occur with root multiplicities 1, 2, AND 3 (e.g. F?rNw: mult 2, B₁=72>0);
  and a B₁=0 graph (FEl~w) has multiplicity 4. So the chromatic-root multiplicity at x=3 is a DIFFERENT,
  coarser invariant than B₁ — it does NOT track the single-bad-edge structure. REFUTED.
- Lesson: P(G,x)'s VALUE at 3 detects χ≥4, but its root MULTIPLICITY at 3 does not see B₁. The
  hoped-for "analytic lever via root structure near x=3" does not connect to E* through multiplicity.
  A genuine chromatic-polynomial-analytic attack on Σ_e P(G−e,3) would need a different invariant than
  root multiplicity (e.g. a zero-free disc in the complex plane around a non-integer point) — still
  open, but multiplicity at the integer x=3 is ruled out.

**Round-4 verdict + LANE ASSESSMENT (gallai global-identity lane, R1–R4):** The global-identity space
is now mapped. Every clean reformulation of "E*≠∅ at k=4" I could construct is EXACTLY equivalent to
B₁>0 (Potts simple-root / Σ_e P(G−e,3)>0), and:
- counting/edge-density lower bounds on B₁ → vacuous (density escape, quantified in G-INV-7);
- ℤ₃ character/Fourier sums → cancel (G-INV-5);
- Tutte/Whitney → same object (G-INV-6);
- chromatic-root multiplicity → doesn't track B₁ (G-INV-8).
The reformulations are valuable LANGUAGE (the Potts/B₁ form is exact, q=3-specific, density-dodging)
but none ESCAPES the irreducible global CSP. The single direction not ruled out: a complex-analytic
zero-free-region bound on P(G,x) near (not at) x=3 that lower-bounds Σ_e P(G−e,3) — requires
statistical-mechanics machinery beyond this lane. RECOMMENDATION: the global-identity lane is
saturated; further rounds here will keep rediscovering B₁>0. Best handoff = the Potts/B₁ reformulation
(G-INV-2/3/4) as the canonical exact statement + the open zero-free-region target for an analytic successor.

---
## count ROUND 3 pointer (appended atomically to avoid edit race)
Coloring-space INVERSE objects — full detail in count_inventions_round3.md:
- CNT-7 BLAME DISTRIBUTION (strong new): edge e critical ⟺ blame(e)=#{3-colorings whose ONLY
  monochromatic edge is e}>0. Witness ⟺ min-conflict≥2 (no 1-conflict 3-coloring). Full enum of
  531441 colorings of C13(1,2,5): ALL 13 critical edges blame EXACTLY 2 (uniform 26=13×2), min-conflict=1.
  Rigidity = perfectly-uniform blame (kill-one-revive-another at coloring-incidence level). New crisp
  coloring-space target: 4-chromatic vertex-critical with min-conflict≥2. Search running (cnt7_search.log).
- CNT-8 Hajós-join walk DEFERRED r4; CNT-9 blame-bipartite PARKED (blame uniform, no sparse cover).

### hunter ROUND 1 RESULTS (cont., 2026-06-10)
- **A3 (pinned-degree-slice enumeration): VALIDATED + advances the floor.** n=13 |E|=40 slice
  (degrees ≤7) = 20,899,992 graphs, parallel floor_worker: 0 four-vtx-critical, 0 witnesses. The
  architecture WORKS — slicing the infeasible n=13 enumeration by edge count makes each slice
  tractable. Combined with skeptic's 6-regular (|E|=39), n=13 with ≤40 edges is now WITNESS-FREE.
  Continuing to |E|=41,42,... to fully close n=13 within δ≥6. THIS IS THE LIVE FLOOR-ADVANCING LANE.
- **A1 (criticality-preserving growth via vertex-split M1): DEAD.** From C13(1,2,5), NO vertex-split
  child is 4-vertex-critical (path never left n=13; every split breaks criticality). You cannot take
  even ONE criticality-preserving growth step from the extremal by vertex-splitting — corroborates the
  rigidity (the manifold is not connected by simple local growth moves). M2 (Hajós sum) / M3 (Gallai
  subdivision) untried but the M1 failure suggests the manifold is genuinely isolated. Pivoting effort
  to A3 (the lane that works).

## ROUND 4 (proximity, 2026-06-10)

### ENC-10 — Hajós-closure vertex-criticality-preserving generator — DEAD (wrong target)
- **Def:** generate candidates by Hajós joins of 4-critical seeds (K4, odd wheels) so every candidate
  is criticality-preserved, avoiding the n=13 vertex-criticality SCARCITY (most random graphs aren't
  vertex-critical).
- **Why it seemed good:** Hajós join preserves 4-criticality; a generator that stays critical wastes
  no search on non-critical graphs.
- **Kill-test:** Hajós(K4,K4), then iterate; check vertex-criticality + critical-edge count. DONE.
- **Result:** DEAD. Hajós(K4,K4) is 7-vertex 4-vertex-critical but with ALL 11 edges critical (it's
  EDGE-critical) — the EXACT OPPOSITE of our target (we want ZERO critical edges). Worse, iterating
  (Hajós(Hajós(K4,K4),K4), n=10) BROKE vertex-criticality entirely (vc=False). DIAGNOSIS: Hajós-closure
  generates EDGE-critical graphs (every edge critical), and the target is precisely vertex-critical-
  NOT-edge-critical. So criticality-preserving operations from the classical toolkit pull toward
  all-edges-critical — the wrong corner. CONFIRMS gallai's vocab trap from the generator side: the
  classical "critical graph" constructions build the wrong object. A witness generator must bias AWAY
  from edge-criticality, not preserve it.

### ENC-11 — Anti-edge-critical seeded growth (the corrected ENC-10) [LIVE]
- **Def:** seed from graphs that ALREADY have non-critical edges (vertex-critical but not edge-critical
  — these exist, e.g. forge's n=9/10 champions with redundant fraction 53%/64%), and grow with moves
  that ADD non-critical edges (each new edge double-witnessed so it's redundant) while preserving
  vertex-criticality. Goal: drive the critical fraction from 64% toward 0, the opposite direction from
  Hajós. Use ENC-2's incremental verifier to keep every grown graph vertex-critical cheaply.
- **Why new:** explicitly grows toward the LOW-edge-criticality corner (forge's decreasing-fraction
  trend), using the redundant-edge champions as seeds — the inverse of the Hajós (edge-critical) closure
  that ENC-10 showed is the wrong direction. Each move's effect on critical-count is checked by the
  incremental verifier (cheap).
- **Kill-test:** from forge's n=10 champion (8 critical edges, redundant 64%), do redundant-edge-adding
  moves reduce critical-count below 8 while keeping vertex-criticality + Prop 5.1? (next round)
- **Result:** RAN kill-test. From forge'"'"'s n=10 champion (8 critical edges), only 1 single-edge-addition
  keeps vertex-criticality, and it STAYS at 8 — no reduction. PLATEAU-TRAPPED, same rigidity as the
  circulant seeds (my 39-add/416-swap result + count'"'"'s basin-hopping). CONVERGENT FINDING across ALL
  seeds tried (circulant + forge champion): single/local moves are pinned at the seed'"'"'s critical-count.
  ENC-11 needs MULTI-edge coordinated moves (add k redundant edges at once) or a non-local jump to have
  any chance — single moves are dead. Marked PARTIAL: the redundant-edge-growth direction is right, but
  the move set must be multi-edge. Hand the multi-edge version to count (basin-hopping infra exists).

### ENC-12 — Minimal-4-chromatic direct encoding (vertex-criticality as the PRIMARY constraint) [LIVE]
- **Def:** encode vertex-criticality CONSTRUCTIVELY as "G is 4-chromatic AND every proper induced
  subgraph G[V∖{v}] is 3-colorable" using the incremental activation-literal model (ENC-2), and make
  this the PRIMARY search constraint (the scarce one per ENC-8's finding) — i.e. search the space of
  minimal-4-chromatic graphs directly, then impose no-critical-edge on top. Since vertex-criticality is
  the binding scarcity at n=13 (ENC-8: 0 vertex-critical even among non-regular profiles), making it
  the first-class generation target (not a post-filter) is the efficiency lever.
- **Why new:** flips the search order — generate minimal-4-chromatic (vertex-critical) graphs FIRST
  (the rare property), filter for no-critical-edge SECOND, instead of hunter's order (structural graph
  first, criticality checks later). ENC-8 proved vertex-criticality is the bottleneck, so front-loading
  it is the right architecture.
- **Kill-test:** confirm the incremental vertex-criticality model (ENC-2) can be run as a GENERATOR
  (enumerate its SAT solutions) and that they're all vertex-critical. ENC-2 already validated as a
  CHECKER; generator mode = enumerate-with-blocking. (next round: measure solution density vs random)
- **Result:** DESIGNED on validated ENC-2 substrate. The architectural insight (front-load the scarce
  property) is the contribution; implementation is ENC-2 in enumeration mode.

---

# algebra lane — EXHAUSTIVE 6-regular floor (joint f-invariant target with wall+gallai)

Wall's cocycle invariant f(G)=min over ℤ₃-colorings of #mono edges unifies everything:
χ=4 ⟺ f≥1; critical edge ⟺ ∃ℤ₃-coloring with mono-set ={e}; (4,1)-witness ⟺ f≥2 ∧ vertex-critical.
My "50% ceiling" = "f=1". CONFIRMED (my f-impl vs checkers): f(quad_t2)=1, f(quad_t5,n=22)=1.

EXHAUSTIVE RESULT (geng, ALL connected 6-regular graphs):
- n=8: 1 graph — 0 are χ=4 vertex-critical
- n=10: 21 graphs — 0 are χ=4 vertex-critical
- n=11: 266 graphs — 0 are χ=4 vertex-critical
- n=12: 7849 graphs — 0 are χ=4 vertex-critical
- TOTAL n≤12: 8137 6-regular graphs, ZERO 4-vertex-critical ⟹ no 6-regular (4,1)-witness on ≤12 vertices (PROVEN by exhaustion).
- n=13: 326587 graphs — [scan running]

This is a HARD floor for the sparsest-witness regime (SS Prop 5.1: sparsest (4,1)-graph is 6-regular).
The 6-regular vertex-critical χ=4 class is EMPTY up to n=12 — so f≤1 holds vacuously there. The joint
f≤1 target's content is at the n where this class first becomes nonempty. Feeds wall's impossibility
proof: if 6-regular ⟹ never 4-vertex-critical (or always f=1), the sparsest witness is excluded.

## ROUND 5 (gallai + wall, 2026-06-10) — the f(G) cocycle invariant, joint dig

wall's invariant: f(G) = min over ℤ₃-colorings of #monochromatic edges (= my Round-2 min_mono).
Identity (wall, validated n≤7): **witness ⟺ f(G) ≥ 2 AND vertex-critical.** Joint target: prove
vertex-criticality at k=4 FORCES f(G) ≤ 1 (⟹ E*≠∅).

### Mechanism worked out (the "absorber" reformulation). VERIFIED + reality-checked.
Define g(v) = min over 3-colorings of #{mono edges NOT incident to v}. Then **v is critical ⟺ g(v)=0**
(a 3-coloring with all mono edges at v restricts to a proper 3-coloring of G−v). So:
**vertex-critical ⟺ max_v g(v) = 0 ⟺ every vertex is an "ABSORBER"** (∃ a 3-coloring with all
monochromatic edges incident to it). A WITNESS ⟺ f(G)≥2 AND every vertex is an absorber.

- Empirical (n=7): every f=2 graph has max_v g(v)=1 (some non-absorber vertex) ⟹ not vertex-critical.
  So "f≥2 ⟹ a non-absorber vertex exists" holds n≤7. At n=8: every vertex-critical 4-chromatic graph
  has f=1 (max f among the 8 vertex-critical graphs = 1); non-vertex-critical reach f=4.
- **k=5 reality check PASSES:** the k=5 witness G_{5,2,2} has f_4≥2 AND every vertex an absorber (it's
  vertex-critical) — so "f≥2 ⟹ non-absorber" is FALSE at q=4. Correctly q=3-specific.

### What we RULED OUT this round (honest):
- "f≥2 forces the ≥2 conflicts vertex-DISJOINT (uncolocatable)": REFUTED. All 15 f=2 graphs (n=7) have
  SOME min-coloring where the two conflicts SHARE a vertex (e.g. FEl~w: conflicts {(0,6),(5,6)} share
  vertex 6, and vertex 6 IS critical). So conflicts ARE co-locatable — at SOME vertices.
- The real obstruction is sharper and global: a witness needs every vertex to be an absorber
  SIMULTANEOUSLY. For FEl~w only 1 of 7 vertices absorbs; the other 6 cannot. The q=3-specific
  difficulty: with 3 colors, the set of "absorber" vertices is too small to be all of V while keeping
  f≥2. With 4 colors (k=5) the absorber set CAN be all of V (witnesses exist).

### The sharp joint-dig target (for wall + gallai, recorded for successor):
Prove: in a 4-chromatic graph with f(G)≥2, the set of absorber vertices (g(v)=0) is a PROPER subset
of V — equivalently, some vertex v has g(v)≥1. This is q=3-specific (fails at q=4). The triangle
rigidity should bound the absorber set: an absorber v must, in its all-conflicts-at-v coloring,
3-color G−v; the ℤ₃ triangle constraints on G−v limit which v can do this. NOT YET PROVEN — but this
is the cleanest statement of the obstruction, and it does not reduce to a vacuous count (it's about
the SIZE of the absorber set, a structural/coloring property). Best lever from the f-cocycle pairing.

## forge CEGAR-CONSTRAINT CONTRIBUTION (2026-06-10, for hunter's search)
forge_cegar_constraints.py: ForgeCegarSearch subclasses hunter's CegarSearch, adds 3 SOUND barrier
constraints (validated: n=7 correctly UNSAT in 1 iter; wall_balance verified DISCRIMINATING not vacuous):
- min_deg=6 (forge deg-3 thm ⟹ δ≥4 free; SkSt ⟹ δ≥6) — massive prune.
- entangle: every edge in ≥2 triangles (≥2 common neighbors), reified — necessary for non-vertex-aligned
  reroutes (sound, weaker than SkSt edge-conn≥6).
- wall_balance: the SHARPEST — directly encodes "no critical edge" = wall's criterion (baked G−v coloring
  has every color ≥2× in N(v)). Front-loads the witness predicate as static clauses ⟹ SAT solver proves
  no-witness WITHOUT CEGAR loop (n=7: 1 iter). SOUND: a true witness admits a balanced baked coloring at
  every v. Discriminating: C7(2,3)-type (all vertices have a critical edge) correctly UNSAT.
Handed to hunter for the n=14-20 witness band (drop-in replace CegarSearch). Caveat unchanged:
UNSAT-under-clauses ≠ completeness proof (symmetry not certified) — geng floor remains the rigorous LB.

# algebra lane — f=1 CONJECTURE base case (ALL 4-vertex-critical graphs, exhaustive)

Tested wall's full conjecture "vertex-critical χ=4 ⟹ f=1" over ALL 4-vertex-critical graphs (any
degree, geng -c -d3 exhaustive). EVERY ONE has f=1; ZERO have f≥2:
- n=6: 1 4-vc graph, f-dist {1:1}
- n=7: 7 4-vc graphs, f-dist {1:7}
- n=8: 8 4-vc graphs, f-dist {1:8}
- n=9: 124 4-vc graphs, f-dist {1:124}
- TOTAL n≤9: 140 4-vertex-critical graphs, ALL f=1 ⟹ ALL have a critical edge ⟹ NO (4,1)-witness
  on ≤9 vertices, PROVEN by exhaustion over all degrees.

This is the clean base case for the joint impossibility target with wall+gallai: "vertex-critical
χ=4 ⟹ f=1" holds with ZERO exceptions through n=9 (all degrees) and the 6-regular subclass is
empty through n=12. The f-invariant is exactly right; the proof task is to show f can never reach 2
under vertex-criticality (k=4-specific: at k=5 Brown's witness has f₅≥2).

### hunter ROUND 1 — A3 CORRECTNESS FIX (2026-06-10)
CAUGHT a completeness gap in my own A3 |E|=40 run: I used -D7 (degrees ≤7), but at |E|=40 (degree
sum 80, n=13) a graph CAN have a degree-8 vertex (one deg-8 + twelve deg-6 = 80). -D7 EXCLUDED those
~2.59M graphs (full -D8 count = 23,489,426 vs my -D7 = 20,899,992). So the |E|=40 closure was
INCOMPLETE. Re-running the COMPLETE |E|=40 slice with -D8 (23.5M graphs) now. Lesson for the slicing
architecture: each |E| slice must use the FULL Δ≤n−5 cap, not a tighter one — the degree cap and edge
count interact. (The 6-regular |E|=39 slice is fine: 39 = 6·13/2 forces exactly 6-regular.)

# algebra lane — UNIQUE n=13 6-regular 4-vc graph + E*-Hamiltonian invariant CONFIRMED twice

EXHAUSTIVE (geng, ALL 367860 connected 6-regular graphs on n=13): EXACTLY ONE is 4-vertex-critical.
g6 = L?bFFbw~B{FwFw. It has:
- f(G) = 1 (confirms wall's conjecture; has critical edges; NOT a (4,1)-witness).
- |E*| = 13 critical edges (of 39), and E* is EXACTLY A HAMILTONIAN CYCLE (spanning, connected,
  2-regular).

So the 6-regular 4-vertex-critical class: EMPTY for n≤12, FIRST nonempty at n=13 with a single graph,
which has f=1. The sparsest-witness regime produces its first member only at n=13 and it is not a witness.

E*-HAMILTONIAN INVARIANT now confirmed on TWO structurally-unrelated families:
- Youngs ℤ₂ quadrangulations (t=2 n=10, t=5 n=22): E* = Hamiltonian cycle.
- The unique exhaustive n=13 6-regular 4-vc graph: E* = Hamiltonian cycle.
Conjecture (strong, for wall): in EVERY 4-vertex-critical graph, the critical-edge set E* contains
(or equals) a spanning structure — at minimum is nonempty (f=1). If E*⊇spanning-connected provable,
|E*|≥n−1>0 ⟹ critical edge always exists ⟹ Dirac k=4 FALSE (no witness). This is the impossibility
spine, with two independent confirmations.

## forge ROUND 3 (keeping quota; sharper after CEGAR insight)

### [forge-7] Closure-entangled triangle cover (apex backs up MULTIPLE edges) — TESTING
- Def: build δ≥6 graph where every edge e is in ≥2 triangles AND each triangle apex w is itself an
  endpoint/apex for ≥2 OTHER edges' triangles — a "closure" so no single vertex deletion frees any edge
  (deleting w breaks e's backup but w is load-bearing for others, so w isn't removable). Search graphs
  closed under "every vertex is a critical-backup for ≥2 edges."
- Why: round-1 forge-1 died because triangle apexes were removable; this REQUIRES apexes to be
  non-removable by making them multiply-load-bearing — directly the "vertex-deletion-robust edge cover."
- Kill-test: geng δ≥6 n=11..14 filtered to the closure property, reduce to 4vc, |E*|. checkers.py.

### [forge-8] Non-abelian Cayley at the witness band (A4, S4, SL(2,3), beyond dihedral) — TESTING
- Def: extend jensen's J4 lead (dihedral reached χ=4) to other non-abelian groups: Cayley(A4),
  Cayley(S4), Cayley(SL(2,3)) with inverse-closed 6-element connection sets; seek χ=4 ∧ vertex-critical
  ∧ δ≥6. Non-abelian ⟹ entangled monodromy (count/algebra: abelian dead, non-abelian open).
- Why: the ONLY vertex-transitive door count/algebra left open is non-abelian; J4 shows it reaches χ=4.
  Distinct from J4 (different groups, witness-band sizes).
- Kill-test: sweep connection sets of A4(n=12)/S4(n=24)/SL(2,3)(n=24); χ=4 ∧ vertex-critical ∧ |E*|.

### [forge-9] SAT-seed + vertex-criticality repair (reverse of trimming) — TESTING
- Def: use ForgeCegarSearch WITHOUT the vertex-criticality bake (just χ=4 + wall_balance + entangle +
  δ≥6) to get a graph with 0 critical edges that may NOT be vertex-critical; then ADD edges/vertices to
  make removable vertices critical WITHOUT creating critical edges (reverse of the trim that always failed).
- Why: every method APPROACHED from "make vertex-critical, then kill critical edges" (trimming, which
  collapses). This goes the OTHER way: start at 0-critical-edge, REPAIR vertex-criticality. Untried
  direction. The SAT seed guarantees the 0-critical-edge starting point at δ≥6.
- Kill-test: SAT-seed a 0-critical-edge δ≥6 graph; greedily add minimal structure to criticalize
  removable vertices; check if |E*| stays 0. checkers.py.

---
## count×wall JOINT (blitz) → count_wall5_joint.md
WALL-5 edge-addition descent (wall) + count pair-move cross: from Mycielski-derived WALL-5 plateaus
(Grötzsch n=11 critE=13; Myc(C7) n=15 critE=20 — asymmetric basin, NOT circulant), the pair-move CANNOT
cross to a witness — it slides to (0 critical edges, ~all vertices non-critical) = the over-full corner.
THREE independent basins (circulant, Mycielski, random-6-reg) now show the IDENTICAL wall: every route to
0 critical edges loses vertex-criticality. Basin-independent impossibility intel (heuristic, not proof).

## ROUND 4 ADDENDUM — empirical reality check on the SAT-SEARCH encodings (proximity + hunter, 2026-06-10)

hunter wired thm4_apply into the variable-edge SEARCH and stress-tested. HARD FINDING:
- STATIC THM4 in the SEARCH (edge vars variable) makes the SAT instance INTRACTABLE: first solve does
  NOT return in 90s (vs 0.00s without). Root cause: THM4 is conditioned on edge vars, so it layers a
  huge tightly-coupled cardinality network (thm4y aux vars + atleast-2 seqcounter, per vertex×color)
  on the n baked colorings. My earlier validation FIXED the graph (edge vars constant) so THM4 was a
  trivial check — it does NOT transfer to the search where edges are variable. Lesson: validate
  constraints in the SEARCH setting, not just on fixed graphs.
- LAZY THM4 (hunter's fix, I implemented + validated): base instance WITHOUT static THM4 solves in
  0.01s at n=13 |E|=40; check THM4 on each proposed graph's actual (constant) neighborhoods cheaply
  (~0.5ms via incremental verifier), block violators. Keeps the base solvable.
- BUT even lazy/fast base solve does NOT make the SEARCH scale: generate-and-test blocks ONE graph per
  iteration ⟹ ~16M iterations to cover n=13 |E|=40. Monolithic witness-SAT is DEAD for SEARCH at n≥13
  by either failure mode (hunter's coloring-blocking non-convergence OR my graph-blocking count).

REVISED STATUS of the SAT-search encodings:
- ENC-3 (joint static core): DEMOTED — intractable in search with static THM4; the static-core idea
  only works as a SMALL targeted instance (one degree profile), not bulk. The VALIDATED-on-fixed-graph
  result stands but does NOT imply search usefulness.
- ENC-1 (m* reformulation), ENC-2 (incremental vertex-crit), ENC-6 (incremental no-crit-edge): these
  are VERIFICATION primitives and SURVIVE — they're the fast per-candidate CHECK, blowup-free. The
  proximity_incremental_verifier.py (ENC-2+ENC-6) is the keeper.
- WORKING STACK (honest): geng/annealer GENERATE + incremental-verifier CHECK + lazy-THM4 fast skip.
  NOT a monolithic SAT search. The live witness hope is EXPLICIT constructions (forge/archivist) +
  count's multi-edge annealer, NOT SAT search.

DISCIPLINE NOTE: this addendum exists because the invention "validated" tag (on fixed graphs) over-
promised search utility for ENC-3. Future encoding candidates get a SEARCH-setting kill-test, not just
a fixed-graph check.

# algebra lane — n=13 unique graph is LOCALLY FROZEN at f=1
Tested all single-edit moves (add/delete one edge, preserving 4-vertex-criticality) on the unique
n=13 6-regular 4-vc graph: ZERO reach f≥2. Even the sole graph in the sparsest-witness regime cannot
be perturbed toward a witness by a local move — it sits in an f=1 basin. Consistent with every other
family: the f=1 ceiling is locally rigid under vertex-criticality.

## CONSOLIDATED EVIDENCE for "vertex-critical χ=4 ⟹ f=1" (Dirac k=4 FALSE direction)
1. All 140 4-vc graphs on n≤9 (all degrees, exhaustive): f=1, no exceptions.
2. 6-regular 4-vc class: empty n≤12 (8137 graphs); n=13 exactly 1 graph, f=1, E*=Hamiltonian cycle.
3. e critical ⟺ achievable as unique mono edge of an f=1 coloring (n=7, exact match).
4. E* = Hamiltonian cycle in 2 unrelated families (quadrangulations + unique 6-reg n=13).
5. quad_t2 (n=10) and quad_t5 (n=22): f=1.
6. Local rigidity: no single 4-vc-preserving edit of the n=13 graph reaches f≥2.
ZERO counterexamples found anywhere. The conjecture is the full content of Dirac k=4; the f-invariant
+ E*-Hamiltonian structure are the proof handles (joint target with wall + gallai).

### Round 5 closure (gallai) — absorber-degree threshold IS Theorem 4 (circular again, but informative).
Measured the absorber-set size + degree across all f≥2 4-chromatic graphs n=7,8:
- Absorber-set fraction |A|/n ≤ 0.375 (far below 1) for all 429 f≥2 graphs at n=8 — so f≥2 ⟹ |A|<n
  empirically, consistent with "no witness."
- **Absorbers have degree ≥ 6 (distribution {6,7}); non-absorbers have degree 3..6.** So the absorber
  threshold is δ≥6 — which is EXACTLY my Theorem 4's "good vertex" condition (deg≥6 + 2-2-2 balance).
  An absorber = a good vertex. "Every vertex an absorber" = "every vertex good" = Theorem 4 = E*=∅.

**Honest verdict (f-cocycle dig, R5):** the absorber/cocycle reformulation is the cleanest LANGUAGE
for the witness condition, and it correctly localizes the obstruction (absorbers need deg≥6, a witness
needs all-absorbers), but the absorber-degree threshold IS Theorem 4 — so "f≥2 ⟹ non-absorber exists"
reduces to "not every vertex is good," i.e. it is logically equivalent to E*≠∅, NOT a reduction to
something provable. Same irreducible core as all R1–R4 routes. The f-invariant gives the BEST
language (single-integer cocycle invariant, q=3-specific, density-dodging) but no escape. CONSISTENT
across the ENTIRE blitz: every reformulation = "every vertex is good" (Theorem 4) = the global CSP.
The ONLY non-circular handle would bound the absorber-set size by something INDEPENDENT of the
good-vertex condition (e.g. a global cocycle-rank argument on the ℤ₃ cut space) — open, needs wall's
cohomology side. Best joint artifact: the f≥2 ∧ all-absorber characterization + the deg-6 threshold.

## forge ROUND-3 RESULTS (partial)
- [forge-9] reverse-repair (0-critical-edge seed → repair vertex-criticality) — DEAD on K(6,2).
  Direct test: from K(6,2) (|E*|=0, all 15 removable), NO edge addition reduces removable count without
  creating a critical edge. STUCK round 0, all restarts. This is the robustness-asymmetry confirmed by
  DIRECT ATTEMPT — edge-robustness and vertex-criticality are locally INSEPARABLE around K(6,2).
  (forge-7 closure-triangle, forge-8 non-abelian Cayley: testing/queued.)

### hunter A3 — |E|=40 COMPLETE result (2026-06-10)
n=13, |E|=40, degrees in [6,8] (full δ≥6 regime at this edge count): **23,489,426 graphs, 0
four-vertex-critical, 0 witnesses** (10-shard parallel, sum verified vs geng count). So n=13 with
|E| ≤ 40 is rigorously WITNESS-FREE (skeptic |E|=39 6-regular + this |E|=40). A3 architecture
delivers: slicing by edge count makes the otherwise-infeasible n=13 enumeration tractable for the
sparse edge bands. |E|=41+ slices grow past feasibility (|E|=41 already times out to count), so the
realistic A3 reach at n=13 is |E| ≤ 40.

## SOUNDNESS LEDGER — entanglement clauses tested (proximity, 2026-06-10)

Coordinating with forge on hunter's CEGAR entanglement clauses. SOUNDNESS results (dual-checked):

- ❌ UNSOUND: "every edge has ≥2 common neighbors" (forge's first version). Counterexamples: forge's
  own n=10 champion has non-critical edges with 1 common neighbor; C14(1,2,5) (6-regular, 0 critical
  edges) has 28 non-critical edges with <2 common neighbors (two with ZERO). Non-criticality is a
  GLOBAL coloring obstruction, not local triangles — a witness can have non-critical edges with no
  common neighbors. Imposing this as a hard clause would EXCLUDE witnesses. DO NOT USE.
- ❌ UNSOUND (strictly worse): "≥2 edge-disjoint triangles per edge", "color-balanced common
  neighborhoods" — both STRONGER than ≥2-common-neighbors, so also exclude witnesses.
- ✅ SOUND (partial): "every 2-vertex-subset boundary ≥ 6" as edge-connectivity proxy. Necessary
  (λ≥6 ⟹ every cut ≥6; |V|≥11 ⟹ 2-set always small side). Validated on C14(1,2,5) (λ=6, min
  2-set boundary 10). PARTIAL: covers only 1/2-vertex-side cuts; verify full λ≥6 post-hoc.
- ✅ SOUND but must be LAZY: gallai THM4 (2-2-2 neighborhoods). Static form intractable in search
  (hunter); apply lazily on each proposed graph.

LESSON: local-structure entanglement clauses are almost all UNSOUND because non-criticality is global.
The only sound static pieces are degree/connectivity bounds (min-deg≥6, 2-set-boundary≥6). The witness
must be checked GLOBALLY (incremental verifier) — there is no cheap local certificate for "no critical
edge". This is itself a structural finding: the (4,1) property resists local encoding.

# algebra lane — CORRECTION (wall's census discipline): E*-Hamiltonian is FAMILY-SPECIFIC, NOT general

Wall flagged + I independently VERIFIED on the full n=7 4-vc census (geng, 7 graphs):
- E* = Hamiltonian cycle: only 1/7 (the 2-regular one IS my quadrangulation type). The other 6 have
  E* degree sequences like [3,3,3,3,4,4,4], [2,2,2,3,3,3,3] — NOT 2-regular, NOT Hamiltonian.
- E* 2-regular: 1/7. So "E* = Hamiltonian cycle" is FALSE in general — a quadrangulation-family artifact.
- E* connected: 7/7 at n=7 BUT wall/skeptic found it FAILS at n=10 (disconnected E*). NOT general.
- E* SPANNING (every vertex incident to ≥1 critical edge = "no good vertex"): 7/7 — THIS is the general
  property (= gallai's framing).

RETRACTION: my earlier "E* contains a spanning CONNECTED subgraph / Hamiltonian cycle" proof target is
WRONG-as-stated (connectivity fails at n=10; 2-regularity fails at n=7). I fell into the family-specific
trap (same one as proximity's one-orbit, wall's uniqueness lemma). The quadrangulation E*-Hamiltonian
fact remains valid only as a CONCRETE MODEL, not a lemma.

CORRECTED general target (wall+gallai): "E* SPANNING" = "no good vertex" = f(G)=1 restated. This is the
honest survivor — but it's equivalent-difficulty to Dirac k=4 itself. The f-invariant / ℤ₃-cut-space
framing is where any leverage must come from; structural E* shape gives none beyond "spanning."
DISCIPLINE NOTE: verify every E* claim across the n≤7 census AND to n≥31 before generalizing.

## ROUND 2 (hunter, 2026-06-10) — learning from round 1 (enum works; witness rare/irregular/isolated)

### A4 — Edge-count-sliced enumeration pushed with gallai THM2 GENERATION-TIME prune (extend the floor past |E|=40)
- **Def:** continue A3's edge-slicing to |E|=41,42,... at n=13, but the raw counts explode. Add a
  cheap NECESSARY-condition prune applied to each enumerated graph BEFORE the expensive full predicate:
  gallai THM2 says edge uv is non-critical ONLY IF N(u)∖{v} is rainbow (all 3 colors) in every
  3-coloring of G−u. A witness needs EVERY edge non-critical. So a SUPER-cheap pre-filter: pick ONE
  3-coloring of G (it's 4-chromatic so this needs G−v first... ) — practically: for the candidate G,
  compute a single proper 3-coloring of G−v for one low-degree vertex v; if N(v) is NOT rainbow in it,
  v has a critical edge ⟹ reject immediately without the full O(m) critical-edge scan. Most graphs die
  on the first vertex. Makes the per-graph cost ~O(1) instead of O(m·3-coloring), so |E|=41,42 become
  feasible at the same throughput.
- **Why:** the full predicate test (critical-edge scan over all m edges) is the per-graph bottleneck in
  A3. THM2 gives an early-out that kills non-witnesses on the first vertex check. Could 5-10x the
  enumeration throughput → push n=13 floor to |E|=42 or 43.
- **Kill-test:** implement the THM2 early-out in floor_worker, re-run |E|=40 (must give identical 0
  witnesses, validating the prune is sound), measure throughput gain. If >3x, run |E|=41. ~20min.

### A5 — Degree-sequence-targeted SAT (not graph-search): fix the EXACT degree sequence, SAT only the wiring
- **Def:** the SAT-CEGAR failure was searching over ALL edge sets (degrees free). Instead FIX a specific
  degree sequence d (e.g. n=14, eleven 6s + three 8s — irregular, the regime round 1 says the witness
  lives in) and SAT only "which wiring realizes d AND is a witness". Fixing degrees collapses the
  cardinality blowup (no atleast/atmost network — degrees are pinned by construction constraints) and
  the symmetry (vertices of equal degree are the only swappable ones — small symmetry group, tractable
  to break soundly). Still CEGAR the chi>=4 + no-critical-edge, but on a vastly smaller, degree-pinned
  space.
- **Why:** round-1 SAT died on (a) cardinality blowup from free degrees and (b) unsound full symmetry
  break. Pinning the degree sequence removes BOTH — degrees are hard-wired (no cardinality), and the
  residual symmetry is just permutations within equal-degree classes (small, soundly breakable by
  ordering within classes). The chi>=4 CEGAR blowup may remain, but on a 100x smaller space it might
  converge. Targets exactly the irregular witness.
- **Kill-test:** pick n=13 degree-seq = eleven 6s + two 8s (|E|=41, the slice my enumeration can't
  reach), encode wiring-SAT + CEGAR, 10-min budget. If it returns UNSAT → that degree-seq slice closed
  by SAT where enumeration failed (= the breakthrough). If it stalls in chi3-refine like before →
  degree-pinning didn't fix the core blowup, A5 dead but we KNOW the blowup is intrinsic to chi>=4.

### A6 — "Critical-skeleton + redundancy-shell" two-layer construction search
- **Def:** structural, learning from archivist's Jensen-Siggers near-miss (critical edges confined to a
  gadget; a rigid CORE has 0 critical edges). Search for a witness as CORE ∪ SHELL: a small rigid
  4-chromatic core B (whose internal edges are all non-critical because B is over-determined) plus a
  shell that makes EVERY core-vertex critical (so vertex-criticality holds) WITHOUT introducing a
  critical edge. Parameterize by (|core|, core-graph, shell-attachment pattern); enumerate small cores
  (the n<=10 4-vtx-critical census IS the core candidate list) × shell patterns; test full predicate.
- **Why:** every prior search treated the graph monolithically and hit the debt-trade. The two-layer
  decomposition separates the two debts: the core pays the no-critical-edge debt (rigid/over-determined
  ⟹ edges redundant), the shell pays the vertex-criticality debt. archivist's H(m=3) near-miss IS this
  structure at k=4 but with critical edges leaking into the gadget — A6 searches shell patterns that
  DON'T leak. Directly targets the only known near-miss family.
- **Kill-test:** take the n=10 δ=5 4-vtx-critical graph (densest core from my census) as core B; enumerate
  shell attachments adding 3-5 vertices each joined to >=6 core/shell vertices keeping δ>=6; test. If any
  is a witness → done (route through adjudicator). If all leak a critical edge into the core→shell
  boundary → the leak is the obstruction, characterize WHERE it leaks (datum for wall). ~30min.

---
## count×proximity JOINT (ENC-11, multi-edge granularity)
proximity: single-edge moves UNIVERSALLY trapped (circulant C13 + forge n=10 champ both pinned).
Untested lever = MULTI-edge coordinated moves. count ran batch add/del (k=1-4) SA from forge's n=10
champion (g6 ICpdbY{]_, 8 critE, min-deg 4): best stayed (χ=4, 0 ncV, 8 critE, min-deg 4) — multi-edge
coordination did NOT cross. Could not even lift min-deg 4→6 while keeping vertex-criticality + reducing
critE (the degree-lift adds always raised the score). So the wall holds under multi-edge granularity too,
not just single moves. Granularity-independent, adding to the basin-independent (WALL-5) result.

### hunter ROUND 2 RESULT — A4 (THM2 early-out prune): WEAK, does NOT extend the floor
Implemented the gallai-THM2 early-out screen (reject if some vertex u has a 3-coloring of G-u where
N(u) misses a color ⟹ a critical edge at u). Tested on |E|=40 (n=13): screen rejects only ~7% of
graphs — too weak to give the 5-10x throughput needed for |E|=41. Root cause: the per-graph cost is
dominated by the VERTEX-CRITICALITY test (3-colorability of every G-v), which THM2 doesn't touch; and
a single-3-coloring screen catches few non-witnesses (most have a critical edge only under SOME
coloring, not the one sampled). A4 DEAD as a throughput lever. ⟹ n=13 floor realistically stops at
|E| ≤ 40 (|E|=41+ has too many graphs regardless of per-graph speed). A5 (degree-pinned wiring-SAT)
and A6 (core+shell construction) remain as round-2 candidates.

## ROUND 3 ADDENDUM (wall) — random-regular is the WRONG distribution

WALL-4 follow-up (sharper, n≥31 rule): tested ~30 uniform random 6-regular graphs at EACH n∈{11,12,13,14,16,20,25,31}. At EVERY n: ~all 4-chromatic, ZERO vertex-critical (0/30 across the board).
⟹ Uniform random 6-regular graphs are NEVER vertex-critical in this range — uniformly over-robust
(χ(G−v)=4 for all v, the n≡2-corner failure). So random-regular / Ramanujan-style sampling is the WRONG
distribution for the existence search: it samples comfortably-above-threshold graphs, never the
threshold-tight ones a witness requires.

DESIGN PRINCIPLE REFINED: "expander-like" alone is too loose. Witness = expander-like REDUNDANCY
(global/distributed) AND threshold-tight CHROMATIC structure (barely 4-chromatic, every vertex
essential). Random regular graphs have the first, never the second. The ONLY way onto the threshold
manifold is criticality-preserving densification from a vertex-critical seed (WALL-5), NOT sampling.
This is why every search that samples dense graphs (random regular, jensen J7 probe) fails at the
vertex-criticality test. Handed to jensen/forge/count: search must STAY on the vertex-critical manifold.

### hunter ROUND 2 RESULT — A5 (degree-pinned wiring SAT): decisive DIAGNOSTIC, SAT path confirmed dead
n=13, degseq = two 8s + eleven 6s (|E|=41, the slice enumeration can't reach): degree-pinned SAT+CEGAR
ran 44,012 iterations in 150s (~300 iter/s — degree-pinning DID speed each solve ~7x vs the unpinned
~40/s, confirming the cardinality blowup is relieved) but DID NOT converge (TIMEOUT, all churning in
chi3-refine). DECISIVE: pinning degrees fixes the cardinality cost but the chi>=4 CEGAR refinement
STILL can't converge — so the chi>=4 blowup is INTRINSIC to the problem, NOT an artifact of free
degrees or symmetry. 44K one-3-coloring blocks cannot exhaust the 3-colorable graphs even on ONE
degree sequence. ⟹ the SAT path is DEFINITIVELY dead, and the bottleneck is now PRECISELY located:
forcing 4-chromaticity (a co-NP condition) via lazy 3-coloring-blocking. No encoding trick (cardinality
relief, degree-pinning, THM4 static, symmetry) addresses it. Only complete enumeration (A3) or explicit
construction (forge/A6) can produce a result.

## ROUND-2 SCORECARD (hunter)
- A4 (THM2 early-out): DEAD — only 7% prune, doesn't extend the floor.
- A5 (degree-pinned SAT): DEAD as a search, but DECISIVE diagnostic — chi>=4 blowup is intrinsic.
- A6 (core+shell construction): handed to forge (construction lane); directly targets archivist's
  Jensen-Siggers near-miss structure. Not run by hunter (avoid duplicating forge).

## forge PROOF-TEAM contributions (post-pivot, 2026-06-10)
Pivoted to impossibility per team-lead. Three pieces toward "χ=4 vertex-critical ⟹ B₁>0":
1. B₁ LOCALIZATION (forge_B1_localization.md): B₁ = ½Σ_v cnt(v), cnt(v)=#{3-col of G−v with exactly
   one singleton color in N(v) + other 2 present}. VERIFIED ratio 2.000. Converts global B₁>0 to
   "∃v: cnt(v)>0" = per-vertex. deg-3 case DONE (cnt(v)≥1). Open core: δ≥6.
2. COCKTAIL CRUX (forge_cocktail_crux.md): smallest |E*|=0 χ=4 graph = K_{2,2,2,2} (cocktail party);
   |E*|=0 AND non-vertex-critical from the SAME partition-robustness. The canonical almost-witness any
   proof must explain.
3. EXHAUSTIVE |E*|=0 ⟹ non-vertex-critical: n=8 (130 graphs), n=9 (5681 graphs) — ALL |E*|=0 χ=4
   graphs are non-vertex-critical (0 witnesses), and they're DIVERSE (mostly non-multipartite), so the
   obstruction is general robustness-asymmetry, not a multipartite artifact. STRONG impossibility base.
REFINED IMPOSSIBILITY CONJECTURE: every χ=4 |E*|=0 graph has a removable vertex (⟹ Dirac k=4 = NO).
q=3 lever (skeptic): G_{5,2,2} escapes at k=5 because the extra color breaks the 3-color balance
rigidity that |E*|=0 forces at k=4. Hand to gallai (Potts) + wall (ℤ₃-tension) for the zero-free-region.


## ENC-11 CLOSURE + ROBUST PLATEAU FINDING (proximity + count, 2026-06-10)
ENC-11 (redundant-edge growth toward critE=0) is exhausted across move granularities and seeds:
- count ran MULTI-EDGE coordinated batch moves (k=1-4) from forge n=10 champion: does NOT cross the
  wall. Could not even LIFT min-deg 4 -> 6 while keeping vertex-criticality + reducing critE.
- proximity tested the principled DOUBLE-WITNESS construction (edge-union of C13(1,2,5) diff-1 +
  C13(1,3,5) diff-5, each edge backed by the other orbit): OVER-DENSIFIES to 8-regular chi=7. The
  over-full trap, at the construction level.
ROBUST JOINT FINDING — the plateau is:
  * granularity-INDEPENDENT (single-edge: proximity 39 adds/416 swaps; multi-edge: count k=1-4 batches)
  * basin-INDEPENDENT (circulant, Mycielski/WALL-5, random-6reg, forge-champion, union-construction)
  * blocked at TWO levels: the critical-count floor AND the degree-lift step.
NO local-or-coordinated move from ANY tested seed, and no naive double-witness construction, reaches a
(4,1)-witness. Empirical backbone for wall's impossibility lemma (heuristic, not proof). Deep reason:
non-criticality is GLOBAL; vertex-criticality ⊥ no-critical-edge tension resists local repair.
ONLY UNTESTED ROUTE LEFT: a GLOBAL TOPOLOGICAL obstruction (ℤ₃-tension on a triangulation where chi=4
is topologically forced + edges intrinsically redundant) — gallai/algebra Youngs-analog territory, NOT
reachable by any local/SA/construction-glue move. If built, proximity verifier + skeptic adjudicate ready.
# algebra lane — PER-VERTEX LEMMA (wall's v-localized formulation, exhaustively measured)

Following wall's redirect (f≤1 is NOT local/averaging — it's a vertex-criticality collapse; use the
n vertex-deletion colorings directly). For each vertex v: a proper 3-coloring of G−v extends to a
ℤ₃-coloring of G whose mono edges are ⊆ v's incident edges; minimizing over v's color, #mono =
min over the 3 colors of |neighbors of that color| = the minority-class size of v's neighbor coloring.

EXHAUSTIVE MEASUREMENT (all 4-vc graphs, geng): the best v-localized #mono is EXACTLY 1 for EVERY
vertex of EVERY 4-vc graph:
- n=7: all 7 graphs, all vertices → per-vertex localized-mono = 1 (49/49)
- n=8: all 8 graphs → {1: 64}, ALL exactly 1
- n=9: all 124 graphs → {1: 1116}, ALL exactly 1
Total: 1229 (graph,vertex) pairs, ALL exactly 1. Zero are 0 (that'd be a good vertex = not vc) and
zero are ≥2.

PER-VERTEX LEMMA (conjectured; exhaustively verified n≤9): In a 4-vertex-critical graph, for EVERY
vertex v, there is a proper 3-coloring of G−v under which v's neighbors realize some color exactly
once (minority class = 1) — i.e. the best v-localized ℤ₃-coloring of G has exactly one mono edge.

CONSEQUENCES:
- ⟹ f(G)≤1 immediately (pick any vertex). This is STRONGER than f≤1 (it's per-vertex, uniform).
- The "never 0" half = vertex-criticality (no good vertex). The "never ≥2" half is the content:
  vertex-criticality forces v's neighbor-coloring to admit a minority-1 split in SOME G−v coloring.
- This is wall's "can all n v-localized colorings have ≥2 mono?" answered NO, exhaustively, n≤9 — and
  in fact each SINGLE one already achieves exactly 1.
- It is NOT a local averaging bound (generic 6-reg has f~n); it's driven by the existence of the G−v
  proper 3-coloring (vertex-criticality) + a minority-split argument on N(v). This is the cut-space
  statement with teeth. NEXT: prove "in any proper 3-coloring landscape of G−v for a 4-vc G, some
  coloring gives N(v) a minority class of size 1" — likely via gallai's triangle rigidity on N(v).
DISCIPLINE: verified n≤9 exhaustively; MUST check the unique n=13 6-reg graph + n≥31 before claiming general.

# algebra lane — PER-VERTEX LEMMA: degree threshold + n=13 6-reg confirmation

PASSED the discipline check (not family-specific): per-vertex min-minority = 1 for ALL 13 vertices of
the unique n=13 6-REGULAR 4-vc graph too (structurally unrelated to the n≤9 census). Lemma robust.

DEGREE-THRESHOLD INSIGHT (sharpens the proof target): min-minority(v) = min over proper G−v
3-colorings of the smallest color-class size on N(v). To have min-minority ≥ 2, EVERY one of the 3
color classes on N(v) must have ≥2 vertices ⟹ deg(v) ≥ 6. So:
- deg(v) ≤ 5 ⟹ min-minority(v) = 1 AUTOMATICALLY (can't fit (≥2,≥2,≥2)); vertex-criticality gives ≥1,
  pigeonhole gives ≤1. Verified: n=7 census, EVERY proper G−v coloring has minority EXACTLY 1
  (distribution concentrated at {1}, deg 3-4).
- deg(v) ≥ 6 is the ONLY regime where min-minority ≥ 2 is even combinatorially possible. This is why
  wall flagged 6-regular: it's the first/only place the lemma has content.

So the WHOLE proof reduces to: "for a degree-≥6 vertex v in a 4-vc graph, some proper 3-coloring of
G−v gives N(v) a color class of size 1." Equivalently: the (2,2,2)-and-up splits are NEVER forced —
there's always a proper G−v coloring avoiding the all-classes-≥2 condition on N(v). On the n=13
6-regular graph (deg exactly 6, so the tight case), this holds for all 13 vertices.

PROOF ROUTE (for wall+gallai): at a degree-6 v with neighbors in a (2,2,2) split, find a Kempe chain
(2-colored component) recoloring that moves one neighbor to make a class size 1, without making
another class empty (which would free v = contradiction with criticality). gallai's triangle rigidity
on N(v) constrains the adjacencies among the 6 neighbors that block/enable such Kempe swaps. This is
the concrete, degree-6-localized, vertex-criticality-driven statement — verified, not yet proven.

# algebra lane — PROOF MECHANISM probe: is (2,2,2) split EXCLUDED, or escapable?

For the per-vertex lemma (deg-6 v ⟹ some proper G−v coloring gives N(v) a size-1 color class), there
are two possible mechanisms; I'm distinguishing them empirically:
- (a) "(2,2,2) EXCLUDED": the balanced split never occurs in any proper G−v coloring of a 4-vc graph
  ⟹ lemma is automatic (every split has a 1). Cleaner.
- (b) "Kempe-escapable": (2,2,2) can occur but some OTHER proper coloring reaches minority 1.

DATA: n=13 6-regular graph, EVERY vertex's N(v) split over ALL proper G−v colorings is (1,1,4) —
the (2,2,2) split NEVER occurs. So for this graph, mechanism (a): vertex-criticality + global coloring
rigidity forces a HIGHLY UNEVEN (1,1,4) neighbor split, automatically minority 1. [Testing whether
(2,2,2) is excluded in ALL 4-vc graphs with deg-6 vertices at n=10,11 — result pending.]

If (2,2,2) is universally excluded in 4-vc graphs, the lemma proof is: "a proper 3-coloring of G−v
cannot split N(v) as (2,2,2)" — a local-coloring-rigidity statement, candidate for gallai's
triangle-rigidity machinery. This would be the clean route to f≤1 for all n.

# algebra lane — (2,2,2) mechanism: feasibility note + single clean datapoint

ATTEMPTED to census whether (2,2,2) split is universally excluded vs escapable across 4-vc graphs with
deg-6 vertices (n=10,11). BLOCKED by feasibility: deg-6 vertices in 4-vc graphs are RARE below n=13
(min-deg-6 4-vc class empty at n≤12, confirmed: 0 such graphs at n=10), and mixed-degree 4-vc graphs
with a deg-6 vertex are buried in a huge geng -d3 stream whose per-graph χ+vc+coloring-enumeration
times out. So no exhaustive (2,2,2) census at small n.

CLEAN DATAPOINT (the one deg-6-rich object that exists small): n=13 6-regular 4-vc graph — every
vertex's N(v) split is (1,1,4) over ALL proper G−v colorings; (2,2,2) NEVER occurs. Mechanism (a)
"(2,2,2) excluded" holds here. But n=1 graph — NOT generalized (discipline: do not over-claim, per
the E*-Hamiltonian lesson).

HONEST STATE of the per-vertex lemma:
- VERIFIED (exhaustive): min-minority = 1 for all 1229 (graph,vertex) pairs over 4-vc graphs n≤9, AND
  all 13 vertices of the n=13 6-reg graph.
- REDUCED: lemma is automatic for deg≤5 (pigeonhole); content is ONLY at deg≥6.
- MECHANISM (open): for the one deg-6-rich graph, (2,2,2) is excluded → (1,1,4). Whether this is general
  (clean route) or whether (2,2,2) occurs-but-escapable elsewhere is UNTESTED at scale (feasibility).
- This is wall+gallai's proof architecture to drive; my role is verified base cases + the deg-6
  reduction + the (1,1,4) observation. Awaiting wall's call on direction (theory vs n=14 f-values).

# algebra lane — (2,2,2)-exclusion DUAL-VERIFIED on n=13 6-reg graph (SAT + brute)

Built a SAT formulation (Cadical + cardinality "exactly 2 neighbors per color") to test (2,2,2)
existence fast (sidesteps brute 3^(n-1) enumeration). On the n=13 6-regular 4-vc graph: NO vertex
admits a proper G−v coloring with N(v) in a (2,2,2) split (all 13 False) — INDEPENDENTLY confirming
the brute-force (1,1,4)-only result via a different code path.

Tried to find more deg-6 4-vc graphs to test: min-deg-6 4-vc class is EMPTY at n=11 (0 of 868311
min-deg-6 graphs are 4-vc) — confirms again these graphs barely exist below n=13. So at scale the
(2,2,2)-exclusion question has exactly ONE clean small datapoint (n=13, excluded, dual-verified);
generalizing it is wall+gallai's theoretical job, not a census I can run.

FINAL HANDOFF STATE (algebra → wall+gallai impossibility proof):
- f≤1 ⟺ Dirac k=4 false; verified all 4-vc n≤9 (f=1) + n=13 6-reg (f=1).
- f≤1 reduces to per-vertex lemma; lemma reduces to deg-6 "(2,2,2) never forced".
- On the one deg-6-rich small graph, (2,2,2) is fully EXCLUDED (dual-verified) → (1,1,4) → minority 1.
- PROOF CRUX (for wall+gallai): prove "a proper 3-coloring of G−v cannot put N(v) in (2,2,2) for a
  deg-6 vertex v of a 4-vc graph" — a local coloring-rigidity statement matching gallai's triangle
  machinery. If true in general, f≤1 follows for all n, closing Dirac k=4 negatively.
- SAT (2,2,2)-checker is built + fast — ready to run on any deg-6 4-vc graph forge/hunter/skeptic find.

# algebra lane — f-optimal dissection: DEAD END confirmed (one focused pass, per wall's cap)

Wall pre-checked the local route: greedy single-vertex recoloring does NOT uniformly reach ≤1 mono
(stuck at ≥2 from some starts: F{cZG 90/2187, FJe~O 354/2187). So f=1 needs GLOBAL rearrangement —
no local/greedy descent rule exists (wall verified). I spent the one allotted pass looking for a
GLOBAL invariant across wall's 6 n=7 non-Hamiltonian-E* 4-vc graphs beyond "mono edge = critical edge":
- mono-achievable edges == critical edges: TRUE for all 6 (the trivial restatement, e crit ⟺ achievable
  as unique mono edge). No new content.
- mono edges all lie in a triangle: MIXED (True for 2/6, False for 4/6) — no structural position invariant.
- No ℤ₃-affine / cut-space-distinguished commonality beyond the critical-edge identity.

VERDICT: dead end, as wall predicted. Every lever in the f/cocycle framework collapses to E*≠∅ =
Dirac k=4 (the nowhere-zero ℤ₃-tension condition hides 3-colorability = NP-hard global content). There
is no local recoloring rule and no extra global invariant of f-optimal colorings. The f≤1 fact is
genuinely equivalent-difficulty to the problem; the only handle is gallai+wall's absorber
anti-correlation ("f≥2 ⟹ #absorbers < n") in the dense regime, NOT anything from the coloring structure.

CLOSED on my side: f-optimal-coloring dissection exhausted. My standing-useful assets remain: the
exhaustive f=1 base cases (n≤9 all, n=13 6-reg), the deg-6 reduction, the dual-verified SAT (2,2,2)-
checker + f-computer ready for any deg-6 4-vc graph the team produces.

# algebra lane — E* SPANNING extends to ASYMMETRIC/non-circulant regime (forge's test)

Forge's discriminating test for the impossibility base: does any 4-vc graph have a "good vertex" =
a vertex incident to NO critical edge (= E* NOT vertex-spanning)? A good vertex is the only thing
that moves toward a witness. Forge's exhaustive sweep: 0 good vertices over all 2453 4-vc graphs at
n=10 (circulant/general). My contribution: extend this into the ASYMMETRIC/non-circulant regime no one
else covers — my quasigroup-circulants (trivial Aut, non-vertex-transitive).

RESULT: across 65 asymmetric quasigroup-circulant 4-vc graphs spanning n=8–14 (16/20 in the first
batch had trivial automorphism group = genuinely asymmetric): E* VERTEX-SPANNING in 65/65. ZERO good
vertices anywhere. So "no good vertex" / E* spanning holds robustly in the asymmetric, trivial-Aut,
non-circulant regime too — not just the symmetric families everyone else tested.

This extends the impossibility base (E* spanning = no good vertex) into the one regime that was
uncovered, using my quasigroup substrate. Consistent with forge's robustness-asymmetry crux: vertex-
criticality forces tight/load-bearing edges (E* touches every vertex) regardless of symmetry. A good
vertex anywhere would be an impossibility-base CRACK / witness-direction lead — none found.

# algebra lane — DEG-6 KEMPE ROUTE CLOSED by wall: (2,2,2) IS forceable; obstruction is GLOBAL

Wall checked the crux before I enumerated Kempe-reducibility and steered me away (correctly):

THE (2,2,2) SPLIT IS FORCEABLE AT DEGREE 6. Wall enumerated all 6-vertex graphs H: 2860 FORCE every
proper 3-coloring to be 2-2-2 balanced (the uniquely-balanced-3-colorable ones). If N(v)'s INTERNAL
structure is such a "forcing-H", then v is a GOOD vertex regardless of the rest of the graph — adding
edges elsewhere only REMOVES colorings (all survivors stay 2-2-2), never adds a 1-minority one. Wall
built a concrete gadget (forcing-H + apex, χ=4, v good). So a SINGLE good vertex is trivially
constructible, and "(2,2,2) never forced at deg-6 v" is FALSE LOCALLY.

RECONCILES with my data: I found (2,2,2) EXCLUDED on C13(1,2,5) — that's because no vertex of C13 has
a forcing-H neighborhood, NOT because (2,2,2) is impossible in general. My "(2,2,2) excluded" was a
PROPERTY OF C13, not a general fact. (Avoided over-claiming it as general — good, consistent with the
discipline; wall's enumeration shows it would have been wrong as a general lemma.)

CONSEQUENCE: the local Kempe enumeration CANNOT close the lemma — the 2860 forcing-H are exactly the
Kempe-RIGID configs (no swap breaks them). The witness obstruction is IRREDUCIBLY GLOBAL: making ALL
n vertices good SIMULTANEOUSLY (consistent colorings + vertex-criticality + χ=4). Single good vertex =
easy; all-good = the wall. Same conclusion as wall+gallai's cocycle-rank lever.

CLEAN "WHY" STATEMENT (the loop closes): deg-6 reduction correctly isolates WHERE the content is →
good-vertex gadgets (forcing-H + apex) exist LOCALLY → they are jensen's spare/modular gadgets that
free vertices → can't tile into a witness (jensen's modular-gluing failures + wall's spanning lemma).
The deg-6 good-vertex gadget IS the provably-untileable modular piece. This is the correct framing of
WHY k=4 is hard, but it is NOT a proof of impossibility — it's the same global wall restated.

ACTION: per wall, deg-6 reduction logged as a CORRECT FRAMING result; local Kempe enumeration NOT run
(would confirm 2-2-2 forceable and stall). My computationally-tractable contribution to the
impossibility side is COMPLETE.

# algebra lane — n≥15 6-regular frontier: INFEASIBLE for me + duplicates marathon sampler (final)

Wall's identity resolves n=14: skeptic's min-crit≥1 check IS the f-verification (critical-edge ⟺
f=1, validated). n=14 fully covered, skip.

n=15,16 frontier: measured ~937 6-reg graphs/s through chi+vc filter (the bottleneck; wall's
early-exit witness-gate only helps AFTER vc, and 0 of 8000 processed at n=15 were even 4-vc).
n=15 6-reg population ~1e8+ ⟹ exhaustive = weeks; time-boxed sample completes negligible fraction.
ALSO task #29 ("overnight n≥14 marathon existence sampler") already covers this in the witness lane
at higher throughput. So I do NOT compete with it — the n≥14 sampling frontier is the marathon
sampler's job. Datum obtained: n=15, 0/8000 processed 6-reg graphs 4-vertex-critical (rarity continues).

FINAL ALGEBRA CONTRIBUTION SUMMARY (E944, complete + honestly bounded):
CONSTRUCTION SIDE (no witness): orbit-uniformity kills symmetric substrates; quasigroup breaks
symmetry (trivial Aut) but hits density-freezing; 15+ families all ~50% critical floor.
IMPOSSIBILITY SIDE (verified): f=1 exhaustive base (all 4-vc n≤9 + n=13 6-reg); per-vertex lemma
reduced to deg-6 (correct framing; Kempe route closed by wall — (2,2,2) IS forceable, obstruction is
global); E*-spanning extended to asymmetric/trivial-Aut regime (65/65). Tools: f-computer, SAT
(2,2,2)-checker, good-vertex checker, witness-gate — all built, fast, ready on demand.
RETRACTED under census discipline: E*-Hamiltonian (family-specific), (2,2,2)-excluded-in-general
(was a C13 property). Both caught before propagating.
REMAINING: wall+gallai's global absorber-anticorrelation theory (theirs); hunter/skeptic's marathon
sampler (n≥14). My lane is complete.

# algebra lane — RUNG-DOUBLING closes E*=0 but breaks vertex-criticality (forge's test, I verified)

Forge tested rung-doubling on my quadrangulation (closing my own earlier open "double the rungs" lead).
I INDEPENDENTLY reproduced (dual-verified vs checkers.py, with removable-vertex count):
- baseline quad t=2: χ=4, vertex-critical, |E*|=10, removable vertices=0.
- 3-LAYER t=2 (o+m+i cycles, rungs o-m and m-i): n=15, χ=4, |E*|=0 (ALL edges redundant!), but NOT
  vertex-critical — 10 removable vertices.
- 3-layer t=3: n=21, χ=4, |E*|=0, but 21 removable (EVERY vertex removable).

So parity-doubling ACHIEVES the edge-redundancy goal (|E*|=0) but at the EXACT cost of vertex-
criticality — the doubled rung's twin carries the ℤ₂ parity obstruction when its partner's vertex is
deleted, so vertices become removable. This is the ROBUSTNESS-ASYMMETRY WALL confirmed from the
parity/topological (ℤ₂) angle — a FOURTH independent confirmation alongside Kneser, covers, gadgets
(forge) and quasigroup-density (me). Edge-redundancy and vertex-criticality are dynamically locked:
fix one, the other breaks, at q=3. No quadrangulation-family escape.

This is the clean "parity-mechanism instance" of the wall for the impossibility writeup. Closes my
"rung-doubling" lead definitively: it works for edge-redundancy, fails vertex-criticality — same wall.

# algebra lane — vc-first witness search: throughput confirmed, but lane is OWNED (task #29 GPU marathon)

Wall's vc-first early-reject insight CONFIRMED: reject on the first vertex v with chi(G-v)=4 (not
vertex-critical) — cheap because ~all 6-reg graphs fail on an early vertex. Measured n=15 6-reg:
~1435 graphs/s (up from ~937 full-check), 0 of 15000 survived vc-check (none 4-vertex-critical).
BUT n=15 6-reg population ~1e8+ ⟹ full exhaustive still ~weeks; it's a witness DETECTOR not a floor.

COORDINATION: task #29 = "BHK GPU marathon" (gpu-smith builds 2^n inclusion-exclusion engine, hands
to hunter for n=14-18 primary band witness search). The CPU marathon sampler was KILLED PER USER
ORDER. So the n=15 witness-search lane is OWNED (GPU, being rebuilt) and the user explicitly killed
CPU sampling. A CPU vc-first n=15 scan from me would DUPLICATE the GPU band AND contradict the user's
kill order. Correct call: do NOT launch it.

INSTEAD: my vc-first reject + witness-gate is exactly the "exact CPU gate" task #29 calls for. Offered
to hunter/gpu-smith as the CPU verification gate for any GPU-marathon hit. My checkers (f, (2,2,2),
good-vertex, removable-vertex, witness-gate, vc-first-reject) all built + fast, ready for the marathon's
exact-gate step. My standalone compute contribution is complete; I'm a verification resource now.

# algebra lane — CORRECTION (forge): the floor is |E*|≥⌈n/2⌉ (absolute count), NOT my 50% fraction

Forge sharpened my reading-(b) and corrected a framing error of mine — accepted, verified:
1. DROP "structured": vertex-spanning (every vertex incident to a critical edge) holds for ALL 4-vc
   graphs (forge exhaustive n≤10). My 3 families were instances, not the general class.
2. FRACTION → ABSOLUTE COUNT: vertex-spanning ⟹ E* is an EDGE COVER of V ⟹ |E*| ≥ ⌈n/2⌉.
   Verified: n=13 6-reg |E*|=13≥7; min|E*| at n=7,8,9 all ≥⌈n/2⌉.
3. MY "50% CEILING" IS FAMILY-SPECIFIC, not the general floor. VERIFIED: the n=13 6-reg graph has
   fraction |E*|/m = 0.33 (=13/39), NOT 0.50 — my quadrangulations are 4-regular (m=2n ⟹ exactly
   0.5); at δ=6 (m=3n) the fraction drops to ~0.33, and as m grows the FRACTION can →0. So the
   fraction is the wrong invariant; the absolute COUNT floor ⌈n/2⌉ is the real impossibility bound.

RETRACTION #4 (under census discipline): the "~50% critical-edge ceiling" I reported as a general
pattern across families is a STRUCTURED SHADOW of the general vertex-spanning theorem, not itself
general. The general statement is |E*|≥⌈n/2⌉ (forge's, from vertex-spanning). A witness needs |E*|=0,
contradicting ⌈n/2⌉≥1. Whole impossibility reduces to: prove vertex-spanning for ALL n (= B₁>0
localized = gallai's Potts lever / q=3 zero-free region).

(Good catch by forge — this is the 4th of my framings corrected by a teammate's check; the
fraction-vs-count distinction matters because the fraction misleads at high δ where a witness lives.)

# algebra lane — BRIDGE: per-vertex ℤ₃ lemma ⟺ forge's vertex-spanning ⟺ |E*|≥⌈n/2⌉

Established the equivalence connecting my algebraic angle to forge's theorem (verified 113/113 vertices,
n=7,8): the mono edge of each vertex v's best v-localized ℤ₃-coloring is INCIDENT TO v AND CRITICAL.
So the chain is:
  per-vertex lemma (min-minority(v)=1 for all v)
    ⟹ each v has a v-localized ℤ₃-coloring with exactly 1 mono edge, incident to v
    ⟹ (wall's identity: 1-mono-edge coloring ⟹ that edge critical) each v incident to a critical edge
    ⟹ vertex-spanning (forge) ⟹ E* is an edge cover ⟹ |E*| ≥ ⌈n/2⌉ (forge's floor).

So my per-vertex ℤ₃ lemma IS the algebraic/coloring form of forge's vertex-spanning theorem — same
statement, two languages. The ℤ₃ form makes the q=3 specificity explicit: min-minority(v)≥2 needs N(v)
to admit a (2,2,2)-or-balanced split in EVERY proper G−v coloring = a forcing-H neighborhood = a good
vertex. Wall: forcing-H is locally constructible but (conjecturally) globally excluded.

HONEST: this is an EQUIVALENCE/bridge, not a proof — per-vertex lemma ⟺ vertex-spanning ⟺ no good
vertex ⟺ |E*|≥⌈n/2⌉, all reduce to the same hard global content (exclude forcing-H neighborhoods in a
global 4-vc graph = gallai's q=3 zero-free region). Value: it shows my ℤ₃-cut-space framework and
forge's edge-cover framework are the SAME lever, so effort isn't split — and the q=3 form ("3 color
classes can't all stay ≥2 on N(v) globally") is the crispest statement of WHERE the q=3-specificity
lives, which is the lever gallai/wall need. Handed to forge+wall+gallai.

# algebra lane — (2,2,2) CORRECT FORM (wall's counterexample): "never FORCED" not "excluded"

RETRACTION #5 (wall's counterexample, I verified): my "(2,2,2) excluded" idea was graph-specific to
C13. Wall found g6=HCQbfrm (n=9, m=18, χ=4, VERTEX-CRITICAL — verified) whose deg-6 vertex v=8 has
N(v) split-types {(1,2,3), (2,2,2)} — so (2,2,2) DOES occur at a deg-6 vertex in a genuine 4-vc graph.
The C13 "(2,2,2) never appears / all (1,1,4)" was a property of C13, NOT general.

CORRECT LEMMA FORM (wall): NOT "(2,2,2) excluded" but "(2,2,2) is never FORCED — there is always SOME
proper G−v coloring with a 1-minority." HCQbfrm's v=8 has min-minority=1 because alongside its (2,2,2)
coloring it ALSO has a (1,2,3) coloring. So:
- good/witness vertex = 2-2-2 FORCED (every proper G−v coloring balanced) = forcing-H neighborhood.
- wall: forcing-H apex gadget is χ=4 but NOT vertex-critical (all 6 nbrs non-critical) — so good
  vertices exist locally but only non-vertex-critically.
- 4-vc graph CAN have a vertex with a (2,2,2) coloring, but always ALSO a 1-minority one ⟹ min-minority=1.
The lemma "vc χ=4 ⟹ every deg-6 vertex has a 1-minority coloring" is the global all-good-CSP-infeasible
statement = equivalent to Dirac k=4. gallai's triangle-rigidity will NOT close it (since (2,2,2) isn't
excluded, only always-accompanied-by-1-minority, which is global). f≤1 thread is COMPLETE at this
checkpoint (per wall): deg-6 reduction is correct framing; the barrier is the irreducible global wall.

# algebra lane — EXACT CPU GATE delivered for the BHK GPU marathon (task #29)

Built algebra_exact_gate.py — the exact-gate step in hunter's marathon v2 pipeline. Public API:
- vc_first_reject(edges, n, k=4): True iff k-vertex-critical (early-exit on first non-critical vertex).
- witness_gate(edges, n, k=4): True iff NO single critical edge (early-exit on first critical edge).
- f_value(edges, n): exact f for n≤13, upper bound above.
- exact_gate(g6_or_edges, n=None): full dual-verified (4,1)-witness verdict dict. WITNESS iff
  chi=4 (backtrack+SAT cross-checked, raises on disagreement) AND vertex-critical AND no critical edge
  AND f≥2. Accepts a graph6 string OR (edges,n).
Self-test passes: C13(1,2,5) and HCQbfrm both correctly return is_witness=False (chi=4, vc=True, has
critical edge, f=1). Handed to hunter as instrument-1 of the 6-instrument verification chain.
