# gallai HANDOFF — E944 local structure + E* assault

## 1. Results + pointers
**Main file:** `gallai_local_structure.md` (6 theorems). **Assault:** `gallai_assault_Estar.md`.
**Tooling:** `gallai_crit.py` (exact χ via SAT, Lean-matching predicates, `witness_local_prune`,
`edge_noncritical_local`). All claims verified on the complete 4-vertex-critical census n≤8.

- **VOCAB TRAP (load-bearing, board-pinned):** `IsCritical` = VERTEX-critical. KY/Gallai are
  EDGE-critical theorems for a DIFFERENT object. CORRECTION (team-lead): the DENSITY half transfers
  (G vertex-critical χ=4, H⊆G minimal 4-chromatic ⟹ H edge-critical+spanning ⟹ e(G) ≥ (5n−2)/3,
  verified); only the Gallai FOREST theorem doesn't (it applies to each H_e⊆G−e, not G).
- **Thm 2 (rainbow-forcing):** edge uv non-critical ⟺ N(u)∖{v} rainbow in every 3-coloring of G−u.
  Exact LOCAL non-criticality certificate. 103 edges, 0 mismatches.
- **Thm 3 (min-deg ≥ 6):** every witness has δ≥6, generalizes to δ≥2(k−1). = Skottová–Steiner 2025
  Prop 5.1, re-proven elementarily; STRONGER for k≥5. k=5 check PASSED: built 3 real (5,1)-graphs via
  jensen's circulant code; G_{5,2,2} (N=17) hits δ=8 exactly.
- **Thm 4 (forced 2-2-2):** at every deg-6 witness vertex, N(u) is 2-2-2 balanced in every 3-coloring
  of G−u.
- **Thm 5 (family-intersection):** f critical ⟺ f in every spanning 4-chromatic subgraph ⟺ f in every
  H_e. Witness ⟺ ⋂_e E(H_e)=∅. {H_e}-overlap bridge: edge-count version VACUOUS for dense witness
  (= wall obstruction #1); "deg-3-in-G simultaneous Gallai vertex" EMPTY (witness has no deg-3 vtx).
- **Thm 6 (Jensen–Siggers E*):** E* NONEMPTY + SPANNING on ALL 4-vertex-critical graphs n≤10 (skeptic
  dual-checker census, 0 exceptions). "E* CONNECTED" is REFUTED at n=10 (3 disconnected-but-spanning).
  B-core K_{2m,2m,2m} has 0 critical edges = over-satisfied Thm 2.

## 2. Where I stopped
Completed the local-structure program (Thms 1–6) and the ASSAULT (prove E*≠∅ at k=4). The assault
FAILED at a precisely-isolated death point (see `gallai_assault_Estar.md`): three independent routes
(edge-counting/KY/potential; Kempe pair-separation; local 2-2-2 rigidity) all die — the only surviving
obstruction is the irreducibly GLOBAL 3-coloring CSP (forced-balance at all vertices + all colorings
simultaneously). The k=4-vs-k=5 distinction lives entirely there. n=9 E* census still computing
(monitor armed; expected 0 exceptions like n≤8).

## 3. Next steps for a successor
- (Most promising k=4-SPECIFIC lever, w/ wall) ℤ₃-TENSION: witness ⟺ no ℤ₃-tension vanishing on ≤1
  edge + χ=4. Triangle rainbow-rigidity (1,1,1/2,2,2 only; fails at ℤ₄) is intrinsically k=4-specific
  (auto-passes k=5 check). Open sub-target: a counting/cohomological identity (NOT planar-duality-based,
  since witness is non-planar) tying #almost-nowhere-zero-tensions to a nonzero χ=4-vc invariant. See
  gallai_assault_Estar.md Route 4. Neither I nor wall could make it bite yet — but it is the ONLY
  unexplored direction that is k=4-specific rather than vacuous/k-independent.
- (Highest value) Attack the global CSP directly: encode "every vertex good (2-2-2 balanced) at every
  3-coloring of G−u" as a SAT/ILP feasibility over candidate adjacency, n=11..13, 6-regular first
  (Skottová–Steiner Problem 5.2). This is the ONLY un-vacuous formulation left. Coordinate with hunter
  (search) and skeptic (n=10+ census, 6-regular floor).
- Prove forge's conjecture "no vertex-transitive (4,1)-graph" — k=4-specific (FALSE at k=5, my circulant
  proves it), would close the entire circulant/Cayley search space. Partial (witness is asymmetric) but
  a real theorem. Mechanism: vertex-transitivity + 3 colors ⟹ a globally load-bearing edge orbit.
- E* SPANNING (not connected — connected refuted at n=10 by skeptic) is the strongest TRUE invariant
  (exception-free n≤10). A forcing reason E* must be spanning would be the lever; coordinate w/ skeptic.


## INVENTION BLITZ outcomes (gallai global-identity lane, R1–R4) — see INVENTIONS.md
- BEST: Potts/B₁ reformulation. Z(G,t)=Σ_{3-col} t^(#mono edges). χ=4⟹B₀=0; E*=∅⟹B₁=0. WITNESS ⟺
  Z has a DOUBLE ROOT at t=0 ⟺ Σ_e P(G−e,3)=0. So E*≠∅ ⟺ q=3 Potts poly has only a SIMPLE root.
  EXACT, q=3-specific (k=5 realizes the double root → passes reality check), DODGES density (root-
  multiplicity, not edge count). Identity B₁=Σ_e P(G−e,3) proven (0 failures n≤8).
- f(G) cocycle dig (R5, with wall): f(G)=min_{ℤ₃-col} #mono edges. witness ⟺ f≥2 ∧ vertex-critical.
  Mechanism: v critical ⟺ v is an "absorber" (∃ 3-coloring with all mono edges at v); vertex-critical
  ⟺ every vertex an absorber. Absorbers have deg≥6 = Theorem 4 good-vertex condition ⟹ CIRCULAR.
  Absorber-set fraction ≤0.375 (n=8). Only non-circular lever left: cocycle-RANK bound on ℤ₃ cut
  space (how many vertices can simultaneously absorb) — needs wall cohomology, open.
- LANE SATURATED: every global identity reduces EXACTLY to B₁>0. Deaths: density bounds vacuous
  (B₁/P(G,4) ratio→0); ℤ₃ Fourier cancels; Tutte=same object; chromatic-root multiplicity at x=3
  does NOT track B₁ (90/282 mismatches n=7). Proof skeleton (min_mono≥2 ⟹ non-critical vertex)
  reduces to Theorem 4 — circular.
- OPEN LEVER (needs tools outside this lane): complex-analytic zero-free-region bound on P(G,x) near
  (not at) x=3 lower-bounding Σ_e P(G−e,3), q=3-specific (Sokal/Jackson statistical-mechanics).


## ZERO-FREE LEVER KILLED (proof-team assignment, 2026-06-10) — gallai_assault_Estar.md Route 5
Assigned: bound Σ_e P(G−e,3)=B₁ via root structure of P(G,x) near x=3. RESULT: DEAD at the strongest
level. PROVEN B₁ is NOT a function of P(G,x): chromatically-equivalent graphs (same P) have different
B₁ (n=7: F?bnw B₁=108 vs F?qnw B₁=96, identical chromatic poly). So NO analytic functional of the
single polynomial P(G,x) — zero-free region, contour, roots — can lower-bound B₁ (it needs the family
{P(G−e,x)}). Also: x=3 simple root (P′(3)≠0) COEXISTS with B₁=0 (FQyvw: P′(3)=−6, B₁=0) — signed
analytic data ≠ positive count. This kills the LAST analytic lever in the saturation map.


## VERTEX-TRANSITIVE THEOREM (proof-team pivot, 2026-06-10) — gallai_vertex_transitive.md
Target: no vertex-transitive (4,1)-witness. SETTLED k=4-only (Jensen k=5 witnesses ARE circulants;
G_{5,2,2} on Z₁₇ is a vertex-transitive (5,1)-witness). Empirical: 137 vertex-critical circulants
n≤24, 0 witnesses. REDUCED (orbit lemma + V-transitivity + forge localization B₁=½Σcnt(v)) to a
SINGLE per-vertex condition: cnt(v₀)=0 impossible for V-T 4-vertex-critical G. NO PROOF: uniform
(one orbit) but still global CSP; q=3 pigeonhole does not bite per-coloring; collapses to Theorem 4.
Un-tried: rep-theory character sum on Aut-action over near-coloring space (NOT the killed ℤ₃-Fourier-
over-colors). Likely TRUE but proof needs the global-CSP core, symmetry only simplifies bookkeeping.

## 4. Traps
- **VOCAB:** never apply Gallai forest / KY structure to G directly; only to edge-critical subgraphs.
  Density (KY lower bound) DOES transfer; structure does NOT.
- **Every lower-bound / counting / potential tool is VACUOUS** — the witness is dense (δ≥6, e≥3n),
  defended from below. Don't re-derive density walls; they're all obstruction #1.
- **k=5 reality check is MANDATORY:** any lemma you prove for k=4 MUST fail at k=5 (witnesses exist
  there). If your lemma holds at k=5 too, it cannot prove k=4 impossibility. Use jensen's
  `circulant_analysis.build_Gkmq(5,2,2)` (N=17, δ=8, 0 critical edges) as the constant check.
  **Brown's literal 1992 graph is UNAVAILABLE** (paywalled; Jensen–Toft §5.14 gives no adjacency; no
  citing paper reproduces it). Do NOT chase it — any LLM "Brown graph" is hallucinated (Grok fabricated
  a "22-vertex two-odd-wheels" version that also falsely claimed Dirac proved k=4). The verified circulant
  family (build_Gkmq) IS the canonical k=5 reality-check substrate. (jensen, confirmed)
- **ncard infinite trap (skeptic):** a witness has finitely many edges ⟹ finite; n is genuine finite.
- **DB erdos_944 attempts are mirages** (team protocol). Compute for real (python3/networkx/pysat).
