# wall — HANDOFF (impossibility direction, E944 k=4 r=1) — FINAL, post-assault

## What I proved (rigorous, durable) — cite these
1. **Spanning-{H_e} decomposition** (wall_impossibility.md §1): for a witness G and every edge e, G−e
   contains a SPANNING 4-EDGE-critical subgraph H_e with e∉H_e (spanning via vertex-criticality). The
   critical-edge set E*(G) = ⋂ over spanning 4-chromatic subgraphs of their edge sets (count verified
   set-equality n≤7). Feeds gallai's E* attempt.
2. **Sharp local witness criterion** (VALIDATED, 0 mismatches n≤7): G is a (4,1)-witness ⟺ for every
   vertex v and every 3-coloring of G−v, each of the 3 colors appears ≥2 times in N(v). Cheap per-vertex
   search prune; handed to forge/hunter. (= gallai Thm 4 local form.)
3. **Lemma A** (rigorous, n-uniform): if (after a multiplier) {1,2}⊆S, then C_n(S)−0 is uniquely
   3-colorable (consecutive-triple triangles force a 3-periodic coloring). Covers 68/112 four-vc
   circulants n≤27. A true theorem fragment.
4. **k=5 reality-check principle**: any proof of "E*≠∅ for all 4-vc G" (= Dirac k=4 false) MUST break at
   k=5, since k=5 witnesses exist (Brown 1992). ⟹ NO k-independent route (density/KY/Gallai) can work.
   The squad's filter for impossibility arguments.

## What DIED (honest death points — do NOT reattempt these ways)
- **Global Kostochka–Yancey / density squeeze**: only a LOWER bound |E(G)|≥(5n+1)/3 (≤ gallai's 3n);
  vertex-critical graphs densify freely, no upper bound. Overlap-counting + Gallai-forest count have
  slack. count confirmed empirically. NO counting obstruction exists.
- **The UNIQUENESS LEMMA is FALSE** (★): C₃₁(1,4,6), C₃₁(5,6,7) are 4-vc triangle-free 6-reg circulants
  with 9 (not 6) colorings of G−0. Uniqueness was an n≤27 artifact. So the whole "uniqueness ⟹ one
  critical orbit ⟹ no circulant witness" program is dead, and the affine-closed-form + coprime-color-shift
  observations are FALSE at n≥31. The "exactly one critical orbit / n critical edges" pattern also dies
  (C₃₁(1,4,6) has 62 critical = 2 orbits). Lemma A survives only for its 68/112 {1,2}-reducible cases.
- **The all-good 2-2-2 CSP**: not forceable into a contradiction; locally feasible (B-core K_{2m,2m,2m},
  but χ=3). The ℤ_3-tension/flow lever is under-constrained for triangle-free graphs (cycle-space rank
  ~27-39); could not make it bite.

## Empirical state of the conclusion (survives even though proofs died)
- NO circulant witness at any n≤31 (n=31: 120 four-vc circulants, all have ≥1 critical edge). count:
  min-critical-edges > 0 to n≈40. proximity: no non-circulant 6-reg vertex-critical graph at n=11,12.
- Every 4-vc 6-regular circulant has n≡1 mod 3 (verified n≤27).

## Next steps for a successor
1. **Do NOT pursue impossibility via density, uniqueness, or any k-independent argument** — all dead.
2. If pursuing impossibility, the ONLY viable lever is a k=4-specific global invariant (candidate: a
   ℤ_3-flow/tension obstruction; must pass the k=5 reality check). Low EV — it's Dirac k=4 restated.
3. **Highest-EV move: EXISTENCE search** (forge/hunter) using criterion #2 above — 6-regular,
   NON-vertex-transitive, color-balanced 4-vc graphs (each color ≥2 in every neighborhood across every
   3-coloring of G−v). This is Skottová–Steiner's open Problem 5.2. No counting obstruction + circulant
   route blocked only empirically ⟹ honest prior leans YES (witness exists).

## Traps (heed)
- VOCAB (gallai): IsCritical = VERTEX-critical; KY/Gallai/Ore are EDGE-critical theorems — apply only to
  extracted edge-critical H_e, never to G.
- Finiteness (skeptic): justify via Mathlib Set.ncard(infinite)=0, NOT de Bruijn–Erdős.
- Circulant regularity: antipodal s=n/2 contributes +1 to degree; only |S|=3 (no antipodal) is 6-regular.
- **SMALL-n ARTIFACTS ARE REAL (the big lesson):** uniqueness, "one critical orbit", affine coloring ALL
  held to n≤27 then broke at n=31. Verify any structural circulant claim to n≥31 before believing it.

## Files
wall_impossibility.md (main), wall_uniqueness_lemma.md (the failed proof + falsification record),
wall_Estar_nonempty.md (E* contribution + reality-check principle), wall_circulant_theorem.md (earlier,
superseded re: the death point).
