# E944 — L3 overlap-counting probe: it recovers the critical set but adds NO surplus (count, for wall)

**Verification:** `python3 analysis/e944/team/overlap_count.py` + set-equality check
across all seven n=7 4-vertex-critical graphs. Engine `critedge.py` (self-tested).

## What I tested
Wall's §1 decomposition: for each non-critical edge e of a 4-vertex-critical G,
G−e is 4-chromatic, so it contains a spanning 4-EDGE-critical subgraph H_e (e∉H_e).
Wall's §1.4: e is critical ⟺ e lies in EVERY spanning 4-chromatic subgraph ⟺
e ∈ ⋂_H E(H). L3 asks: can double-counting the H_e family force a contradiction?

I computed, for each edge f, whether f is "avoidable" = excluded from H_e for some
non-critical e (over multiple greedy-deletion orders), and counted the
"never-avoidable" edges (forced into every H_e).

## Result (exact, set-level)
**The critical-edge set EQUALS the never-avoidable-edge set, exactly, on every
4-vertex-critical graph tested:**

| graph | n | m | #critical | #never-avoidable | sets equal? |
|---|---|---|---|---|---|
| C₇(1,2) | 7 | 14 | 7 | 7 | YES |
| C₁₃(1,2,5) | 13 | 39 | 13 | 13 | YES |
| K₄ | 4 | 6 | 6 | 6 | YES |
| all 7 n=7 4-vtx-critical graphs | 7 | 11–14 | 7–12 | 7–12 | YES (each) |

This realizes wall's §1.4 characterization empirically: critical edges = ⋂_H E(H)
= exactly the never-avoidable edges.

## The negative finding for the impossibility side (load-bearing for wall L3)
Overlap-counting **recovers the critical set but produces NO surplus** beyond it.
For a hypothetical witness (0 critical edges):
- critical set = ∅ ⟹ never-avoidable set = ∅ ⟹ EVERY edge is avoidable by some
  spanning 4-edge-critical subgraph. This is **self-consistent**, NOT a
  contradiction.
- Σ_e |E(H_e)| / n-style double counts: each H_e has ≥ (5n−2)/3 edges (KY), but
  since every edge is avoidable, no edge accumulates forced multiplicity = "in all
  H_e". The double-count gives an averaged multiplicity but no edge is pinned to
  multiplicity = (#non-critical edges), so no edge is forced critical.

**Verdict: L3 (overlap counting) does NOT close the impossibility argument**, for
the same essential reason §2.1 failed — the construction has too much freedom.
The critical-edge count is an *output* of the structure, recoverable many ways,
but nothing forces it to be > 0.

## What this leaves
The impossibility direction cannot be closed by:
- (§2.1) global K-Y edge count — confirmed by wall.
- (L3) overlap/double counting of the H_e family — confirmed here.
Both fail because vertex-critical 4-chromatic graphs have unbounded density freedom
and "no critical edge" is an emptiness condition (⋂_H E(H)=∅) with no counting
obstruction. A genuine impossibility proof, if one exists, must use the FINE
structure of 3-colorings (potential method L2 / Gallai-tree local analysis L1),
not cardinality. This pushes the verdict-prior slightly toward TRUE (existence):
the absence of any counting obstruction is the hallmark of "the object can be
built, it's just hard to find."
