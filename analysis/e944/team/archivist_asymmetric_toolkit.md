# E944 — Asymmetric vertex-critical construction toolkit (for jensen/forge/algebra)

Goal: build a 4-vertex-critical graph with NO critical edge. Symmetric circulants provably fail at k=4 (W2). This file surveys ASYMMETRIC / ad-hoc construction techniques. VERIFIED builders on disk (import checkers.py): archivist_k5_witness.py (a real (5,1)-witness), archivist_jensen_siggers_build.py (the k=4 near-miss).

## ★ THE CENTRAL WARNING (read first)
The classical critical-graph operations — **Hajós join, Dirac join, Toft, Gallai, Mycielski** — all produce **EDGE-critical** graphs (every edge IS critical). That is the EXACT OPPOSITE of what we need. We want vertex-critical with NO critical edge. So these operations are the wrong primitive for the SEED; they are only useful as the "frame" H in a gluing (where you WANT a rigid k-critical scaffold), never as the witness itself. The vocab trap (gallai) bites here: don't reach for Hajós/Gallai expecting a witness.

The ONLY known mechanism that yields vertex-critical-WITHOUT-critical-edges is **REDUNDANCY**: a rigid high-multiplicity core whose coloring survives any single edge deletion, glued to a small "disagreement" gadget that forces χ up. Two concrete realizations exist (both built + verified by archivist):
- Jensen–Siggers tripartite-core mechanism (archivist_jensen_siggers_build.py).
- Jensen circulant high-distance mechanism (archivist_k5_witness.py).

## Operation-by-operation

### 1. Hajós join (the workhorse k-critical builder)
Take k-critical G1 (edge u1v1), G2 (edge u2v2). Delete u1v1, u2v2; identify u1=u2; add edge v1v2. Result is k-critical (BOTH vertex- AND edge-critical). PRESERVES edge-criticality ⟹ result HAS critical edges. USE: only as the rigid frame H in Skottová–Steiner gluing Lemma 2.1, OR to generate sparse k-critical graphs of any order (their Lemma 2.2). NOT a witness source.

### 2. Dirac join / Hajós–Ore (Toft's "operation B")
Recursive vertex/edge identification after edge deletions from two critical graphs. Preserves k-criticality; outputs edge-critical. Same role as Hajós. [Toft, Discrete Math 1989]

### 3. Toft's constructions (dense 4-critical graphs, many edges)
Toft built dense 4-critical / many-edge critical graphs and studied criticality-preserving operations. ALL edge-critical. Toft is NOT credited with any vertex-critical-without-critical-edge construction. His dense-4-critical machinery is useful intel for the IMPOSSIBILITY direction (what dense 4-critical graphs look like), not for a witness. [renyi.hu/~miki/SimColourCrit.pdf]

### 4. Schäuble's construction
1960s-70s critical-graph gluings (alongside Dirac/Gallai/Hajós). Criticality-preserving, edge-critical outputs. Low modern prominence; not a witness route.

### 5. Gallai's constructions (1963)
Sparse k-critical families (e.g. 4-critical 4-regular non-planar on the Klein bottle; low-edge-count critical graphs). Structural theorem: the low-vertex subgraph of a k-edge-critical graph is a Gallai tree (blocks = cliques or odd cycles). EDGE-critical. The Gallai-tree theorem is an EDGE-critical structural result (vocab trap) — does NOT bound our vertex-critical target directly, but DOES apply to each spanning H_e ⊆ G−e (per gallai/wall KY-bridge). Use for impossibility, not construction. [Gallai 1963; Springer BF01215921]

### 6. Mycielski / Grötzsch
M(G) has χ = χ(G)+1, preserves triangle-freeness. Grötzsch = M(C5), 4-chromatic triangle-free. Mycielskians are typically k-critical = EDGE-critical. Raises χ but does NOT create the no-critical-edge property. Tangential note: a triangle-free 4-vertex-critical witness would be interesting (Grötzsch graph is 4-vertex-critical AND edge-critical — has critical edges, so not a witness), but Mycielski doesn't remove edge-criticality.

### 7. THE redundancy principle (the ONLY thing that works)
To get vertex-critical-but-NOT-edge-critical: build in REDUNDANCY so that
  (a) every vertex deletion still drops χ (vertex-critical preserved), but
  (b) every single edge has an "alternative" — deleting it leaves enough structure that χ stays k (no critical edge).
Two realized mechanisms:
  - **Rigid multipartite core (Jensen–Siggers):** K_{2m,2m,2m} has a UNIQUE 3-coloring (up to perm) that SURVIVES any single edge deletion (Lemma 1) ⟹ its 12m² edges are ALL non-critical. Glue a small gadget that forces a 4th color via color-disagreement. archivist VERIFIED: at m=3, all 108 core edges non-critical, 90 critical edges confined to the gadget. To win at k=4: kill the gadget's residual criticality.
  - **High-distance circulant (Jensen):** overlapping long distances give each color class enough redundancy that single-edge deletion doesn't free up a recoloring. WORKS at k=5 (archivist's G_{5,2,4} on Z₃₃, ZERO critical edges, verified). FAILS at k=4 by distance-set degeneracy (W2).

## ASYMMETRIC LEVERS for k=4 (synthesis for forge/jensen)
- Brown's k=5 (17 vtx, asymmetric, unrecoverable) PROVES asymmetric witnesses exist — symmetry is not required. A k=4 witness need not be a circulant.
- The redundancy principle is mechanism-agnostic: ANY rigid-core + disagreement-gadget that lands at χ=4 with edge-redundancy would work. The Jensen–Siggers tripartite core is the most promising asymmetric scaffold because it's a 3-coloring-rigid object (exactly the k=4 regime). The open problem is engineering the disagreement gadget to have NO critical edges of its own.
- Hajós/Gallai/Mycielski are the WRONG primitive (they make edges critical). Use them only for the scaffold H in gluing, never the witness.

## VERIFIED ARTIFACTS ON DISK
- **CANONICAL k=5 witness: G_{5,2,2} on Z₁₇** (jensen's, archivist-cross-verified). Build via archivist_k5_witness.py `jensen_circulant_k5(2,2)`. n=17 (= Brown's vertex count!), 8-regular, D={1,3,4,5,13}, χ=5, vertex-critical, 0 critical edges. BOTH χ paths agree. USE THIS as the "what a k=5 witness looks like" reference — smaller/cleaner than the N=33 below.
- archivist_k5_witness.py + archivist_k5_witness_N33.{g6,json} — also a real (5,1)-witness, Jensen circulant G_{5,2,4}/Z₃₃, D={1,3,4,5,12,13,21}. (Larger; N=17 above is preferred.)
- archivist_jensen_siggers_build.py — k=4 near-miss H(m), the rigid-core+gadget surgery target. m=3: n=67, χ=4, 90 critical edges all in gadget, core B fully non-critical.

## ⚠️ BROWN LITERAL GRAPH — DO NOT CHASE (jensen exhausted this, archivist concurs)
The Brown 1992 LITERAL 17-vtx graph is UNAVAILABLE in open literature: DM 102:99-101 paywalled; Jensen–Toft §5.14 references but gives no adjacency/vertex count; NO citing paper/thesis/survey reproduces it; and **LLMs HALLUCINATE it** (Grok fabricated a "22-vertex two-odd-wheels" version + falsely claimed Dirac k=4 settled — the abstracts-vs-proofs trap). The verified G_{5,2,2}/Z₁₇ above is the canonical k=5 reference instead — SAME vertex count as Brown, genuinely verified (not retrieved).
