# Extremal section — E*-degree slope (jensen's half: verification + boundary)

Co-written with forge. forge owns the lemma statement + proof; jensen owns the
independent verification + the "where it stops" boundary analysis. Merges with
gallai/wall's global (q=3 Potts / cocycle) half.

## Lemma (forge, E*-degree slope) — INDEPENDENTLY VERIFIED (jensen)
In a 4-vertex-critical graph G, every vertex v satisfies
        **E\*-deg(v) ≥ max(0, 6 − deg(v))**,
where E\*-deg(v) = # critical edges incident to v.

**Proof** (forge): v critical ⟹ G−v 3-colorable; fix a 3-coloring c. χ(G)=4 ⟹ N(v)
meets all 3 colors under c (else recolor v, χ=3). So deg(v) neighbors split into 3
NONEMPTY classes. Min # singletons over partitions of deg(v) into 3 nonempty parts
= max(0, 6−deg(v)) [d=3→(1,1,1)=3; d=4→(2,1,1)=2; d=5→(2,2,1)=1; d≥6→(2,2,2)=0].
A singleton neighbor u ⟹ uv critical (per-vertex criticality lemma). ∎

## Independent verification (jensen, harness.py 2-engine χ, distinct from forge's checker)
Code: `jensen_code/verify_estar_slope.py`. **0 violations across 216 vertices:**

| family | n | violations | tight vertices (E*-deg = bound > 0) |
|---|---|---|---|
| complete census (atlas, 9 graphs) | 4–7 | 0 | 46 / 59 |
| Grötzsch | 11 | 0 | 5 |
| C_n(1,2,5) circulants | 13,16,19,25,31 | 0 | 0 (all δ=6 ⟹ bound 0) |
| wall WALL-5 plateau n19_mycC9 (δ=3) | 19 | 0 | 8 |
| wall WALL-5 plateau n23_mycC11 (δ=4) | 23 | 0 | 9 |

Pushed to **n=31** per wall's "small-n nulls aren't conclusive" lesson.

**Two kinds of tightness — only one is informative (jensen caveat):**
- TRIVIAL tightness: in a fully 4-EDGE-critical graph (Grötzsch, and several census
  graphs) every edge is critical, so E\*-deg(v)=deg(v) ≥ bound holds but is not the
  lemma constraining anything — the degree-3 vertices are "tight" only because all 3
  incident edges are critical anyway.
- INFORMATIVE tightness: in a graph with a MIX of critical and non-critical edges, the
  bound exactly PARTITIONS a vertex's incident edges. VERIFIED on wall's n=19 seed (24
  of 48 edges non-critical): the tight degree-4 vertices have E\*-deg = 2 = bound, with
  EXACTLY 2 incident edges critical and the other 2 NON-critical. The lemma forces the
  2 critical and permits the 2 non-critical — it bites precisely. THIS is the real
  content: it says a low-degree vertex CANNOT have all its edges non-critical (a witness
  needs that, hence δ≥6).
So the lemma's genuine content lives at low-degree vertices of MIXED graphs; it is sharp
there (wall's seeds), and vacuous (bound 0) at δ=6.

## q-indexing (k=4-specific, passes wall's k=5 reality filter)
The "3 nonempty parts" is the q=3 (=k−1) statement. At general k the neighborhood splits
into k−1 nonempty parts, giving **E\*-deg(v) ≥ max(0, 2(k−1) − deg(v))** [the singleton
floor for k−1 parts summing to deg(v)]. At k=5, deg=8 (e.g. the verified witness
G_{5,2,2}, δ=8): bound = max(0, 8−8) = 0, consistent with G_{5,2,2}'s |E\*|=0. So the
lemma does NOT wrongly force |E\*|≥1 at k=5 — it is genuinely k=4-specific.

## Corollary: witness ⟹ δ ≥ 6 (finer than δ≥4), via a per-coloring count
If G is a witness (every E\*-deg(v)=0), then max(0, 6−deg(v))=0 ∀v ⟹ deg(v)≥6 ∀v.
This re-derives the δ≥6 floor (= Skottová–Steiner Prop 5.1, gallai Thm 3) from a finer,
purely local per-coloring counting argument — and shows it is FORCED by the slope, not
assumed. A witness sits exactly at the slope's zero at EVERY vertex.

## WHERE IT STOPS — the boundary the local argument cannot cross (jensen)
The slope lemma is a PER-COLORING floor: for a FIXED 3-coloring c of G−v, a deg-6
vertex CAN be 2-2-2-balanced (bound = 0). So the local lemma is vacuous at deg-6 — it
dies EXACTLY at the degree where the witness lives. This is not a weakness of the proof;
it is the precise location of the entire remaining difficulty:

> **The witness requires every deg-6 vertex v to be 2-2-2-balanced in EVERY 3-coloring
> of G−v SIMULTANEOUSLY** (so that NO incident edge is critical via ANY coloring).
> The slope lemma gives this per-coloring "for free" at deg-6; the open question is the
> SIMULTANEITY over all colorings — an irreducibly GLOBAL condition.

This routes the whole problem into one global statement and connects the three lanes:
- = gallai Thm 4 (forced-2-2-2 at every vertex in every coloring),
- = gallai's q=3 Potts: E\*≠∅ ⟺ Σ_e P(G−e,3) > 0 (the simultaneity fails ⟺ some edge
  is the single bad edge of some coloring),
- = wall's cocycle f: witness ⟺ f≥2 (no 3-coloring has a single monochromatic edge),
  and the per-coloring slope is exactly "in THIS coloring, the monochromatic edges at v".

So the extremal/local side (this lemma) closes deg≤5 completely and hands the deg-6
simultaneity to the global q=3 lever — the honest division of the proof. The local half
is DONE and verified; the global half (does a deg-6 vertex's per-coloring 2-2-2 freedom
survive intersection over all colorings?) is the open core, and it is provably the LAST
thing standing (everything deg≤5 is killed locally).
