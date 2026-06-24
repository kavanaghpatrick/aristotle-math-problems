# E944 — Cayley graphs of non-cyclic abelian groups: a structural tension (count)

**Verification:** `python3 analysis/e944/team/cayley_search.py` + diagnostic.

## Motivation
Circulants (= Cayley graphs of cyclic Z_n) are empirically closed for the witness
(count_circulant_search.md). The next vertex-transitive family is Cayley graphs of
NON-cyclic abelian groups Z_a × Z_b (and Z_2^k etc.). archivist/algebra flagged
that the Brown k=5 witness might be a Cayley graph of a non-cyclic group, so this
is the natural extension.

## Result and the structural finding
Searched 6- and 8-regular Cayley graphs (Prop 5.1 min-deg≥6) over groups of order
12–36: Z₂×Z₆, Z₃×Z₄, Z₂×Z₈, Z₄×Z₄, Z₂×Z₂×Z₄, Z₂×Z₂×Z₅, Z₂×Z₁₀, Z₃×Z₆, Z₆×Z₆,
Z₃×Z₃×Z₃, etc.

**No witness found — but for a STRUCTURALLY INTERESTING reason:**
diagnostic over 6-regular Cayley graphs shows MANY are 4-chromatic (e.g. 200 of
252 on Z₂×Z₂×Z₄; 44 of 60 on Z₂×Z₈), but **NONE is vertex-critical**.

| group | #6-reg Cayley graphs | χ distribution | #4-vertex-critical |
|---|---|---|---|
| Z₂×Z₆ | 22 | {2:3, 3:7, 4:6, 6:6} | 0 |
| Z₃×Z₄ | 10 | {2:1, 3:5, 4:4} | 0 |
| Z₂×Z₈ | 60 | {2:12, 3:4, 4:44} | 0 |
| Z₄×Z₄ | 56 | {2:12, 4:44} | 0 |
| Z₂×Z₂×Z₄ | 252 | {2:52, 4:200} | 0 |

**The tension (a genuine finding):** in these highly-symmetric Cayley graphs,
4-chromaticity is common but vertex-CRITICALITY fails — the graphs are 4-chromatic
but NOT minimal (some vertex deletion keeps χ=4). Symmetry that would help make
edges non-critical (high regularity, transitivity) simultaneously creates
"redundant" vertices, breaking vertex-criticality.

This is the **dual obstruction** to the circulant plateau:
- Circulants achieve vertex-criticality but can't kill the last edge-orbit
  (the Hamilton-cycle orbit stays critical).
- Larger non-cyclic Cayley graphs kill edge-criticality (edges become non-critical)
  but lose vertex-criticality.
A witness must thread BOTH needles at once — vertex-critical AND no critical edge —
and vertex-transitive families tested so far satisfy at most one.

## Honesty caveat
This is a WEAKER negative than the circulant result: it only covers a finite list
of small abelian groups, only 6/8-regular, and the failure mode (no vertex-critical
graph) means I never reached the edge-criticality test for these groups. It does
NOT rule out a witness among:
- non-abelian Cayley graphs (dihedral D_n, S_4, etc.) — UNTESTED,
- larger abelian groups,
- non-vertex-transitive 6-regular graphs (the bulk of Prop-5.1 space; forge/hunter).

## Recommendation
The vertex-transitive route is showing a consistent double-bind. The witness, if it
exists, is plausibly **NOT vertex-transitive** — it likely needs asymmetric local
structure to be simultaneously vertex-critical and edge-redundant. This argues for
forge's gadget/gluing constructions and hunter's asymmetric 6-regular search over
continued symmetry-based searching.
