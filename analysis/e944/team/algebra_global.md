# E944 — Invented GLOBAL χ=4 redundancy mechanisms (algebra)

Mandate (team-lead via forge): invent a SECOND, GLOBAL (parity/topology) χ=4 redundancy mechanism:
χ=4 reason that (i) is redundant through every edge, (ii) collapses on any vertex deletion,
(iii) is GLOBAL (no local subgraph witnesses it). Constraint (forge's theorem): NO degree-3 vertex
⟹ δ≥4. Tool: `algebra_global_mechanism.py`. All χ dual-verified (backtracking + SAT) via checkers.py.

## RESULT: a real global mechanism, achieving 50% edge-redundancy at δ=4 (best so far)

**Projective-planar quadrangulation (Youngs ℤ₂ family), "odd_wheel_quadrangulation":**
two concentric odd cycles C_{2t+1} (an "outer" o-layer and "inner" i-layer) joined by rungs
o_j–i_j and o_j–i_{j+1}. Youngs 1996: a non-bipartite quadrangulation of the projective plane is
χ=4 by a GLOBAL ℤ₂ monodromy invariant — locally it is 4-cycles (2-colorable); the χ=4 is not
witnessed by any local subgraph. Exactly a global obstruction.

| graph | n | m | χ | δ | vertex-critical | #critical edges |
|---|---|---|---|---|---|---|
| quad t=2 | 10 | 20 | 4 | 4 | yes | **10 (=50%)** |
| quad t=5 | 22 | 44 | 4 | 4 | yes | 22 (=50%) |
| ℤ₂-twisted double cover of K5 | 10 | 20 | 4 | 4 | yes | 10 (=50%) |

**Edge dissection of quad t=2 (the key structural finding):**
- outer cycle edges: **0/5 critical** (fully redundant)
- inner cycle edges: **0/5 critical** (fully redundant)
- rungs (both classes): **5/5 critical**

So the global ℤ₂ obstruction makes EVERY cycle edge redundant: delete any one cycle edge and the
OTHER odd cycle still carries the parity obstruction — a genuinely non-local redundancy, exactly
the invented mechanism the mandate asked for. This is qualitatively better than the quasigroup
substrate (which was ~0% redundant / near edge-critical). The "exactly 50% critical" recurs across
the family and in the ℤ₂-twisted double covers — the critical half is always the inter-layer
(rung / twist) edges.

## The remaining barrier (sharp) and why deepening fails

Only the rungs/twist-edges stay critical, because each is the unique connector at its position;
deleting it lets the parity obstruction relax locally. Attempts to make the rungs redundant too:

1. **More rungs (rung jump-sets |R|=2,3,4), t=2..4:** best #critical stayed at 10 — extra rungs
   either push χ>4, break vertex-criticality, or don't reduce criticality. No improvement.
2. **≥3 parity layers (cyclic in the layer index):** χ comes out 3 (too sparse), 5 (too dense), or
   4-but-NOT-vertex-critical — the extra layers add redundancy but make the graph too robust to
   vertex deletion. Lost vertex-criticality in every χ=4 case.
3. **Seeded local search (add/del 1 edge) from the 50%-redundant quad t=2:** FROZEN at 10 — no
   single-edge move keeps it 4-vertex-critical while lowering the critical count.

## Verdict

The global parity/topology mechanism is a genuine invention and the best redundancy generator found
on the algebraic side: it puts a non-local ℤ₂ obstruction into HALF the edges (all cycle edges) at
δ=4, vertex-critical. But it hits the SAME density-freezing wall that killed the quasigroup
substrate: the redundant half and the critical half are structurally locked, and pushing redundancy
into the remaining (rung) half requires density that destroys vertex-criticality. The 2-layer
quadrangulation sits exactly on the redundancy/vertex-criticality boundary (50%), and that boundary
appears to be a hard frontier for these symmetric/structured families.

**Honest assessment:** 50% redundancy is real progress and the mechanism is sound, but it does not
reach a witness. The recurring 50%/freezing pattern across THREE independent construction styles
(circulant, quasigroup, global-parity) is itself evidence: every structured construction lands on a
redundancy ceiling well above 0 critical edges. This suggests a witness, if it exists, needs an
IRREGULAR graph that breaks the 50% structural lock — forge's SA / hunter's SAT-CEGAR territory —
or, if no witness exists, the recurring ceiling is a hint toward an impossibility proof (hand to
wall: "every structured χ=4 vertex-critical graph has ≥ (some positive fraction) critical edges").

## Files
- `algebra_global_mechanism.py` — M1 (signed ℤ₂ double covers), M2 (Youngs quadrangulations),
  M2' (cyclic parity), all scored via checkers.py.
- The 50%-redundant seeds (quad t=2, K5-twist) are good STRUCTURED seeds for forge's SA — much
  closer to a witness than random or quasigroup starts (10 critical vs ~0% redundant).
