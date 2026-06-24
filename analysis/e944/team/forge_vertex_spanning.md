# forge — the "vertex-spanning E*" reformulation (2026-06-10)

## Empirical observation
In EVERY 4-vertex-critical graph tested, the critical-edge set E* is
**vertex-spanning**: every vertex is incident to at least one critical edge.
- n=7 (7 graphs), n=8 (8), n=9 (124): vertex-spanning in 100% of cases, min
  vertex-coverage fraction = 1.000.
- n=10 champions + full n=10 sweep: [verification running; champions all spanning].
- Jensen-Siggers H(m=3), n=67: E* spanning (touches all 67) AND connected —
  reproduces J-S's own "E* connected and even spanning" remark.

## The clean per-vertex lemma (PROVEN, elementary)
> Vertex v has a critical edge  ⟺  under SOME proper 3-coloring c of G−v, some
> color appears EXACTLY ONCE among N(v).

Proof: (⇐) Let color 1 appear once in N(v), at neighbor u. In G−vu, the
neighbors of v hit only {2,3} (we removed the unique color-1 neighbor edge), so
extend c by setting c(v)=1 → proper 3-coloring of G−vu → χ(G−vu)=3 < 4 → vu
critical. (⇒) If vu critical, a 3-coloring of G−vu sets v some color a; then in
G the only conflict was the edge vu, so c(u)=a and no other neighbor of v has
color a → color a appears exactly once (only at u) in N(v) under this coloring
of G−v. ∎

## Why this is a REFORMULATION, not new leverage (honest)
"Every vertex has a critical edge" (vertex-spanning E*)
  = "wall's witness criterion fails at every vertex"
  = "G is NOT a (4,1)-witness."
because wall's criterion is exactly "for every v and every 3-coloring of G−v,
each color appears ≥2× in N(v)" — the negation of the lemma's RHS at every v.

So the empirical vertex-spanning fact is LOGICALLY EQUIVALENT to "no witness on
these graphs" — it confirms the floor through a per-vertex lens, but proving
"vertex-spanning always" IS proving the impossibility direction. It is not a
strictly easier sub-lemma. (Flagged to avoid the trap of mistaking a restatement
for progress.)

## What WOULD be new leverage (for wall/skeptic) — and what's RULED OUT
A quantitative strengthening that is NOT just the restatement, e.g.:
- "Every vertex is incident to ≥2 critical edges" — **TESTED AND FALSE.**
  Counterexample at n=9: the 4-vertex-critical graph `HCp\`fr]` has a vertex of
  critical-degree exactly 1 (min critical-degree over n=7,8 is 2, but drops to 1
  at n=9). So the per-vertex bound is TIGHT at 1 — the impossibility argument
  CANNOT lean on a uniform ≥2; it must use exactly "≥1 at every vertex" = wall's
  criterion negated.
- "E* contains a spanning subgraph of min-degree ≥ d" — ruled out for d≥2 by the
  same counterexample.
- a lower bound |E*| ≥ f(n) with f→∞ would even kill the weaker Erdős f_4(n)
  question on the impossibility side — but vertex-spanning only gives |E*|≥⌈n/2⌉
  (= the spanning fact), and that is a fixed linear bound, not →∞ growth.
The per-vertex lemma reduces all of these to LOCAL color-counting over 3-colorings
of G−v — the tractable handle — but the easy strengthenings are now empirically
closed. The open quantitative question is whether |E*| can be forced to grow
super-linearly (which J-S's Θ(n) upper bound on the construction side bounds from
above: a witness-free world is consistent with |E*| as low as Θ(n)).

## PROVEN structural theorem (clean, self-contained) — the degree-3 mechanism
> **Theorem (forge).** If v has degree 3 in a 4-vertex-critical graph G, then ALL
> THREE edges at v are critical.
>
> Proof: v is critical ⟹ G−v is 3-colorable. In ANY proper 3-coloring of G−v, the
> three neighbors of v must get three DISTINCT colors — otherwise a color is free
> at v and the coloring extends to G, contradicting χ(G)=4. So each color appears
> exactly once in N(v); by the per-vertex lemma each of the 3 edges is critical. ∎
>
> **Corollary.** A (4,1)-witness has minimum degree ≥ 4 (it can have NO degree-3
> vertex, since a degree-3 vertex forces 3 critical edges).

Verified exactly: in ALL 4-vertex-critical graphs n=7,8,9 (139 graphs), every
degree-3 vertex has all 3 edges critical — 0 exceptions.

This is a clean, first-principles necessary condition (a weaker self-contained
cousin of Skottová–Steiner's δ≥6 from their Prop 5.1) and it pinpoints WHY the
Jensen–Siggers near-miss cannot reach E*=∅: H(m) is built from degree-3 transfer-
path vertices (44 of the 67 vertices at m=3 have degree 3), and EACH forces 3
critical edges. The whole gadget's criticality is the unavoidable price of its
degree-3 scaffolding. To kill E* you must raise every gadget vertex to degree ≥4
(really ≥6 per SkSt) WITHOUT breaking vertex-criticality — the same antagonism
wall that defeated all 5 of my construction lines.

## Pointer
Verification code inline in this campaign; champions checked in
forge_assault_findings.md. The lemma connects forge's construction failures to
wall's criterion and J-S's spanning conjecture into a single statement.
