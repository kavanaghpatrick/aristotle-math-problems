# Invention mandate (jensen): re-expressing J–S transfer as parity, and the
# ENTANGLEMENT vs PARALLELISM dichotomy that every redundancy mechanism faces

**Author:** jensen. **Mandate (team-lead via forge):** invent a SECOND global χ=4
redundancy mechanism; my angle = recast the J–S color-transfer (Lemma 2) as a
parity/flow obstruction without degree-3 path scaffolding. **Code:**
`jensen_code/parity_transfer.py`. **Verifier:** harness.py (3-way cross-validated).

## 1. The parity substrate (verified)
A connected graph is 3-colorable iff it admits a **ℤ₃-tension**: orient edges, label
each t(e)∈{1,2}=ℤ₃∖{0}, with signed sum ≡0 mod 3 around every cycle. A proper
3-coloring c gives t(uv)=c(v)−c(u); a tension integrates back to a 3-coloring.
(Self-tested: C₆ and Petersen both satisfy the cycle-sum law.) So the J–S transfer's
job — "force a relation between φ(x₀) and φ(x_{2m+1})" — is exactly **forcing the
ℤ₃-tension integrated along an x₀→x_{2m+1} route to a fixed value.** On a path that
value is carried by ONE route (the path), so every path edge is a bridge and is
critical. On a **2-edge-connected** graph every edge lies on a cycle, so the tension
is enforced by cycles and NO edge is a bridge — the parity reformulation removes the
degree-3/bridge scaffolding that forge's theorem (deg-3 vtx ⟹ 3 critical edges)
identifies as the source of J–S's unavoidable E*.

## 2. The bridgeless transfer — built, and it DOES remove bridges (verified)
Replaced the J–S path by a **ladder/prism** between v_i and v_{i+1} (two rails +
rungs; every edge on a 4-cycle). Wired into the J–S star+B architecture:
- m=2: n=22, χ=4, **bridges=0** (vs the path's all-bridges), 9 critical edges (vs 90).
- m=3: n=34, χ=4, **bridges=0**, 9 critical edges.
Bridgelessness ACHIEVED and critical-edge count cut 90→9. BUT: **not vertex-critical.**

## 3. WHY it's still not vertex-critical — the dichotomy (the real finding)
Diagnosed the non-critical vertices: they are exactly the **ladder rail vertices**
(the 'q' rail + even 'p'). Deleting a rail vertex leaves the OTHER rail CHROMATICALLY
carrying the transfer ⟹ χ stays 4 ⟹ not critical. [This specific diagnosis is
CORRECT and verified — skeptic confirmed via per-vertex deletion.]

> **⚠ CORRECTION (skeptic adjudication, skeptic_jensen_dichotomy_review.md):** the
> STRICT form of the dichotomy below is **FALSE**, and I flagged it as a hypothesis
> for exactly the right reason. The false step: "edge e has a vertex-DISJOINT reroute
> ⟹ that reroute's interior vertices are non-critical." That conflates **connectivity**
> (a u–v path) with **chromatic obstruction**. Counterexample (dual-checker):
> C₁₃(1,2,5) is 4-vertex-critical, edge (0,1) has 5 internally-vertex-disjoint
> reroutes, yet ALL their interior vertices stay critical — because a vertex on a
> connectivity "spare rail" can still carry the CHROMATIC obstruction, so its deletion
> still drops χ. The corrected chromatic statement ("if e's chromatic obstruction is
> carried by a substructure vertex-disjoint from w, then w is non-critical") is
> essentially TRUE but near-tautological (≈ the definition of vertex-criticality), so
> it is a heuristic, NOT an independent lever.

**What survives (SOUND, per skeptic):** the *design principle* — structured PARALLEL
reroutes (literal disjoint rails, as in my ladder or the J–S double-cover) create
spare-rail non-critical vertices, so a witness must be **entangled** (dense, no clean
spare rails). My ladder's failure IS a genuine instance: its 2-edge-connectivity is
two literal rails, and the rail vertices are chromatically redundant. This principle
matches Prop 5.1 (δ≥6), gallai's forced-2-2-2, and the failure of every structured
construction (J–S path, ladder, double-cover, k=4 circulant). It is a useful
witness-search SPEC, not a theorem.

## 4. The positive example (verified, but read as ILLUSTRATION not proof): G_{5,2,2}
The genuine k=5 witness G_{5,2,2} (n=17, χ=5, vertex-critical, 0 critical edges):
- bridges=0, **edge-connectivity=8, vertex-connectivity=8** (δ=8).
- For an edge e=(0,1): in G−e there are **7 internally-vertex-disjoint reroutes** of
  0→1, all through the dense common neighborhood — it is highly entangled.
- It is simultaneously edge-redundant AND vertex-critical. NOTE (post-skeptic): the
  7 disjoint reroutes are a CONNECTIVITY fact; they do NOT by themselves explain the
  vertex-criticality (per the C₁₃ counterexample, disjoint reroutes are compatible
  with critical vertices either way). So G_{5,2,2} ILLUSTRATES "dense entangled witness"
  but does not PROVE the dichotomy. It's a positive design exemplar, nothing more.

The high connectivity = gallai's δ≥2(k−1) (δ≥8 at k=5, δ≥6 at k=4) is the quantitative
face of "no spare rails." forge's "no degree-3" and gallai's "δ≥6, forced 2-2-2
neighborhoods" are the local signature of an entangled (not literal-rail) witness.

## 5. The "second mechanism" — honest answer to the mandate
There is no clean NEW gadget that supplies global χ=4 redundancy while staying
vertex-critical, because **any structured/separable redundancy fails the dichotomy.**
The genuine second mechanism is not a gadget but a REGIME: **density-induced
entanglement** — a dense (δ≥6), high-edge-connectivity, IRREGULAR graph where every
edge's reroutes share vertices with the edge. This is:
- consistent with the parity view (cycles, not paths, carry the tension);
- consistent with forge's projective-plane ℤ₂-parity seed IF that quadrangulation is
  dense/entangled rather than a sparse parallel structure (forge should check its
  edge-connectivity + whether reroutes are separable — a sparse quadrangulation will
  hit the same rail trap);
- exactly why hunter's local search and count's circulant sweeps find no witness:
  entangled-but-vertex-critical-but-edge-redundant is a NARROW, GLOBAL target with no
  local/structured shortcut — it must be found by dense-irregular global search (or
  shown not to exist, = wall's impossibility).

## 6. Net deliverable (corrected post-skeptic adjudication)
- VERIFIED: parity reformulation removes bridges (90→9 critical edges, 0 bridges) but
  the resulting structured (ladder) object is NOT vertex-critical — the literal rail
  vertices are chromatically redundant.
- The strict "separable 2-edge-connectivity ⟹ non-critical vertex" implication is
  **FALSE** (skeptic: C₁₃(1,2,5) counterexample). DO NOT use it as a theorem.
- What IS sound: a witness built from literal disjoint parallel rails fails
  vertex-criticality; so the witness-search SPEC is **entangled, dense (δ≥6),
  irregular, no literal spare rails**. This is a heuristic/spec, matching Prop 5.1 +
  gallai 2-2-2, not a new proof.
- Hands to forge: check the projective-plane candidate for literal-rail structure
  (sparse degree-4 quadrangulation → likely rail trap) vs dense entanglement.
- Hands to wall: NOTHING NEW — the bound "witness ⟹ edge-conn ≥ 6" ALREADY holds
  rigorously via Skottová–Steiner Prop 5.1 (skeptic_prop51_verification.md). My
  dichotomy gives only intuition for WHY, resting on a false strict step, so it is
  NOT an independent impossibility lever. (Retracted my earlier suggestion to wall.)
