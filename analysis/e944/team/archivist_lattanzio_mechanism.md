# E944 — Lattanzio's mechanism: what k−1 composite buys, why k−1=3 prime denies it

Co-owned with algebra (algebra owns "exact requirement R + replacement substrates at level 3"; archivist owns literature-grounding + cite-chain). Per jensen's hallucination warning: every claim below is tagged [CONFIRMED] (from a verifiable theorem statement / multiple independent citations) or [INFERRED] (structural reconstruction — the Lattanzio PDF is paywalled and gives no open construction text). NO fabricated adjacency.

## [CONFIRMED] The theorem statement (conflict RESOLVED)
**Lattanzio 2002 (Discrete Math 258:323-330) proves Dirac's conjecture for all k≥4 with k−1 COMPOSITE (not prime).**
- Source: consistent across Martinsson–Steiner 2025 (arXiv:2310.12891) AND Skottová–Steiner 2025 (arXiv:2508.08703) AND the formal-conjectures repo Lean statement (`k_sub_one_not_prime`).
- The Jensen–Siggers 2012 phrasing "odd values of k≥5" is an IMPRECISE paraphrase. Odd k≥5 ⟺ k−1 even ⟺ k−1 composite (for k≥5) — a PROPER SUBSET of "k−1 composite." Lattanzio is NOT restricted to odd k; it includes even k with composite k−1 (e.g. k=10, k−1=9=3·3). TRUST "k−1 composite" (the repo's `k_sub_one_not_prime`), not "odd k."
- Consequence for k=4: k−1 = 3 is PRIME ⟹ NOT covered by Lattanzio. (Jensen 2002 separately covers all k≥5 by a different method, so k=4 is the sole gap.)

## [CONFIRMED] What is NOT recoverable
The exact construction (which graphs, what product, how k−1=a·b enters, the precise prime-failure step) is ONLY in the paywalled paper. No open abstract, arXiv version, ResearchGate-extractable text, or MathSciNet/zbMATH detail gives the mechanics. Anything below about the mechanism is INFERENCE.

## [INFERRED] The likely mechanism (structural reconstruction — flag as unconfirmed)
The "k−1 composite" boundary is the fingerprint of a PRODUCT / FACTORIZATION construction. The standard reading (consistent with Brown's k=5 being the a=b=2 base case, k−1=4=2·2):
- Write k−1 = a·b with a,b ≥ 2. Build a graph whose proper (k−1)-colorings correspond to assignments into an a×b color grid (≅ Z_a × Z_b color set), via a graph product of two factor-structures sized by a and b (categorical/tensor or lexicographic product of cycles/cliques — UNCONFIRMED which).
- The NO-CRITICAL-EDGE property comes from 2-DIMENSIONAL redundancy: after deleting any single edge, a proper (k−1)-coloring can be "repaired" by shifting along EITHER the a-factor OR the b-factor independently, so χ does not drop. Vertex-criticality is preserved because deleting a whole vertex removes a grid coordinate that no shift can compensate.
- **Why k−1=3 prime FAILS [INFERRED]:** Z_3 has no nontrivial product decomposition (3 = 3·1 only), so there is only a 1-DIMENSIONAL (single cyclic) shift axis. One axis is not enough redundancy to repair every single-edge deletion → some edge becomes critical. The factorization that powers the repair simply does not exist when k−1 is prime.

## [CONFIRMED, cross-check] This is consistent with the OTHER constructions' k=4 walls
- The "needs a factorization / 2D redundancy" reading matches WHY the redundancy principle (archivist_asymmetric_toolkit.md §7) is the only route to no-critical-edge: you need MULTIPLE independent ways to recolor after an edge deletion. Lattanzio gets that from k−1=a·b; Jensen gets it from overlapping long circulant distances (k≥5); Jensen–Siggers gets it from the rigid tripartite core. ALL three need "enough room"/structure that k=4 (=smallest nontrivial, k−1=3 prime) denies.
- This does NOT prove k=4 impossible — it explains why the THREE KNOWN templates miss it. A genuinely new redundancy mechanism not based on factoring 3 could still exist.

## OPEN handoff to algebra
The precise "requirement R" and whether a level-3 substrate (quasigroup/Latin-square/STS/PG(2,3)/GF(9)/Cayley) can supply 2D-redundancy WITHOUT factoring k−1=3 is exactly algebra's question. If a non-product algebraic structure on 3 colors can provide the missing repair-redundancy, that would be the k=4 construction lever. My [INFERRED] mechanism above is the spec; algebra verifies/refutes realizability at level 3.

## Provenance summary
- [CONFIRMED]: theorem = "k−1 composite"; J–S paraphrase imprecise; construction text unavailable. (MS 2025, SkSt 2025, formal-conjectures repo, multiple citations.)
- [INFERRED, then REFINED by algebra — see VERDICT below]: I inferred a "product/factorization → 2D-redundancy, Z_3-prime failure" mechanism. algebra's computational verdict CORRECTS the root cause: the Z_3 wall is ASSOCIATIVITY-INDUCED SYMMETRY (escapable at level 3 via non-associative quasigroups, |Aut|=1), NOT the arithmetic non-factorability of 3. And the requirement splits: R1 (symmetry — solvable at level 3) + R2 (repair-redundancy = DENSITY, the real wall, orthogonal to algebra). Do NOT cite my original single-axis framing as the mechanism; cite the algebra VERDICT. Net: a k=4 witness needs asymmetric AND dense → global-search territory, not an algebraic substrate.

## [algebra VERDICT, 2026-06-10] Realizability of R at level 3 — answer to the open handoff

Tested archivist's [INFERRED] spec computationally (all χ via hunter's checkers.py, backtrack+SAT
cross-checked). The "2D repair-redundancy without factoring 3" question splits into TWO requirements,
and the answer is SPLIT:

**R has two components:**
- R1 (symmetry-breaking): the substrate must NOT impose a single global shift-symmetry that forces
  edge-criticality to be orbit-uniform. [In the group case Z_3 gives one shift axis ⟹ the orbit
  obstruction. archivist's "1-dimensional shift axis" = my orbit obstruction, same phenomenon.]
- R2 (repair-redundancy): every edge must lie in ≥2 independent recoloring obstructions so deletion
  of any single edge is repairable (χ stays 4), WHILE deletion of any vertex is NOT (vertex-critical).

**R1 IS realizable at level 3 without factoring 3 — VERIFIED.** Non-associative quasigroups of order
3 exist (9 of 12 order-3 Latin squares). The quasigroup-circulant substrate (Cayley over a
non-associative quasigroup, `algebra_qcirculant.py`) has TRIVIAL automorphism group (|Aut|=1, verified
vs |Aut|=18 for the Z_9 group version) ⟹ NO global shift symmetry ⟹ the orbit obstruction is gone.
So the "single shift axis" failure archivist inferred for Z_3 is NOT intrinsic to level 3 — a
non-associative structure provides the missing independence WITHOUT a factorization. **This refines
the [INFERRED] mechanism: the obstruction is associativity-induced symmetry, not literally the
arithmetic non-factorability of 3.**

**R2 is NOT realizable by these substrates — VERIFIED (the real wall).** The repair-redundancy needs
DENSITY (every edge double-witnessed ⟹ min-degree ≥6, |V|≥11 per Skottova-Steiner Prop 5.1). The
level-3 quasigroup-circulants land on the wrong side: their 4-vertex-critical instances (n=7–10) are
near edge-critical (10–15 of ~12–21 edges critical) and FROZEN (0–6 valid redundancy-adding moves;
edge-adding descent makes ~0 progress — every addition pushes χ→5 or breaks vertex-criticality). At
n≥11 (where Prop 5.1 allows a witness) the construction cannot stay 4-vertex-critical at all.

**Net verdict on the handoff:** A level-3 algebraic substrate CAN supply R1 (symmetry-breaking)
without factoring 3 — so archivist's "Z_3-prime failure" is really a symmetry artifact, escapable.
But it does NOT supply R2 (repair-redundancy), which is a density requirement orthogonal to the
algebra. The two known templates' k=4 wall is thus TWO walls: symmetry (escapable, solved here) +
density-freezing (open, and the actual barrier). A k=4 construction needs a substrate that is both
asymmetric AND dense-enough — global search territory (forge SA / hunter SAT-CEGAR over 6-regular
n≥11 graphs), not a level-3 algebraic substrate. Full detail: analysis/e944/team/algebra_assault.md.
