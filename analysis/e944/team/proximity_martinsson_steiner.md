# E944 — Martinsson–Steiner deep dive + the fresh 2025 follow-up (proximity)

Mandate: absorb the newest tool (Martinsson–Steiner 2025, CPC 151–157), read the ACTUAL
proof, extract mechanism / k-vs-r tradeoff / failure-at-small-k / k=4 expert commentary, then
build a strength-graded interpolation ladder toward the k=4 witness.

## TL;DR for the squad

1. The "Martinsson–Steiner 2025 (CPC 151–157)" cited in the Lean file is the JOURNAL version of
   **arXiv:2310.12891** (Oct 2023). I read it in full.
2. There is a **fresher, more relevant paper by the same author**: Ema Skottova & Raphael Steiner,
   **"Critical edge sets in vertex-critical graphs," arXiv:2508.08703, 12 Aug 2025**. This is the
   current state of the art. It **resolves Erdős's problem for all k ≥ 5** (with quantitative
   bound f_k(n)=Ω(n^{1/3})) and **leaves ONLY k=4 open** — exactly our target. It contains the
   single most useful thing anyone has written about k=4: **necessary conditions (Prop 5.1)** for a
   (4,1)-graph, plus an explicit computational target.
3. **Expert prior on TRUE vs FALSE**: Steiner (Sec 5 of the 2025 paper) says for *circulant* graphs
   they "lean towards thinking that they do not exist." This opinion is **scoped to circulants only**,
   NOT to (4,1)-graphs in general. The case is genuinely open; nobody claims a resolution either way.
   → Squad prior should remain honestly uncertain, with a mild lean from the fact that 30+ years and
   two strong constructions have failed to reach k=4.

---

## Vocabulary (matches archivist + gallai, restated to be self-contained)

- A **(k,r)-graph** (Skottova–Steiner notation) = a k-vertex-critical graph G in which **no set of at
  most r edges is critical** (deleting ≤ r edges never lowers χ below k).
- Our target `∃ G, IsErdos944 4 1` is exactly the existence of a **(4,1)-graph**.
- (k,1)-graph = "k-vertex-critical with no critical edge" = the Dirac-1970 object.
- gallai's trap stands: `IsCritical` = VERTEX-critical. A (4,1)-graph is vertex-critical but NOT
  edge-critical, so EDGE-critical structure theory (Gallai low-vertex, Kostochka–Yancey density)
  does not apply to the target directly.

---

## PAPER 1 — Martinsson–Steiner 2023/2025 (arXiv:2310.12891)
### "Vertex-critical graphs far from edge-criticality"

**Theorem 1 (their main result).** For every r ∈ ℕ there is k₀ ∈ ℕ such that for every k ≥ k₀ there
exists a k-vertex-critical graph G with χ(G − R) = k for every R ⊆ E(G), |R| ≤ r.

### (1) Construction mechanism — PROBABILISTIC, via Shamir's hypergraph-matching problem

The construction is **complement of the 2-section of a random uniform hypergraph**. Concretely:

- Fix r. Set **s := r + 3** and **m := 2^{s+1}**.
- By **Lemma 3** (built on the Johansson–Kahn–Vu / Kahn solution of Shamir's problem), for every
  sufficiently large n with n ≡ 1 (mod s), there is an s-uniform hypergraph H on n vertices with:
  - (i) **H − v has a perfect matching for every vertex v** (the "near-perfect-matching" property);
  - (ii) **local sparsity**: ⋃_{e∈F} e ≥ (s−1)|F| for every F ⊆ E(H) with |F| ≤ m.
- Take **n := s(k−1)+1**. Define **G := complement of the 2-section G₂^H** of H.

**Why G is vertex-critical (χ(G−v) ≤ k−1):** a perfect matching of H−v partitions V(G)∖{v} into
(n−1)/s = k−1 hyperedges, each of which is an INDEPENDENT set in G (since G is the complement of
the 2-section, and a hyperedge is a clique in the 2-section). So k−1 colors suffice for G−v.

**Why no ≤ r edges are critical (χ(G−R) ≥ k):** they show **α(G−R) ≤ s** (no independent set of size
s+1 survives deleting r edges). An independent set of size s+1 in G−R would be an (s+1)-vertex set X
with ≤ r edges in G, hence ≥ C(s+1,2) − r = C(s,2)+s−r = C(s,2)+3 edges in the 2-section G₂^H[X].
But **Lemma 5** (the local-sparsity ⟹ edge-count bound) gives |E(G₂^H[X])| ≤ C(s,2)+2 — contradiction.
Then χ(G−R) ≥ n/α ≥ n/s > k−1.

This is **Recipe-A-flavored** (existence via the probabilistic method), NOT an explicit construction.

### (2) The k-vs-r tradeoff and "smallest k for r=1"

- The construction is governed by **n = s(k−1)+1 with s = r+3** and the requirement **n ≥ n₀(s,m)**
  where n₀ comes from Lemma 3, which itself inherits the *"sufficiently large n"* of the JKV/Kahn
  threshold (p(n) = C·log(n)/n^{s−1}).
- They set **k₀ := ⌈n₀/s⌉ + 1**. The value n₀ is the smallest n at which the random s-uniform
  hypergraph w.h.p. simultaneously has property (i) (near-perfect matchings) AND (ii) (local
  sparsity). This is a large, *non-explicit* constant — and the paper makes **no attempt to optimize
  it**, because their goal is "for all sufficiently large k."
- **For r = 1: s = 4.** The smallest k this construction reaches is k₀ = ⌈n₀(4, 2^5)/4⌉ + 1, where
  n₀(4,32) is the threshold size for a 4-uniform random hypergraph to have all the matching +
  sparsity properties. This is far above 4 — there is **no version of this argument that reaches
  k=4 for r=1**; for r=1 the case k=5 is already covered by Jensen/Brown/Lattanzio by direct means,
  and M–S only adds value for r ≥ 2 anyway. **Verdict: their r=1 specialization does not even
  recover Jensen at small k; it is purely a large-k existence theorem.**

### (3) The EXACT step where small k fails — "union bound needs room"

- The failure is **not a structural obstruction at k=4**. It is that **Lemma 3 needs n large**:
  the random-hypergraph properties (i)+(ii) hold only *with high probability for large n*, via union
  bounds over n vertices (property i) and over O(n^{(s−1)f−1}) vertex-subsets (property ii). Small n
  ⟹ the w.h.p. statement is vacuous; no hypergraph is guaranteed.
- Since n = s(k−1)+1, **small k ⟹ small n ⟹ the probabilistic existence engine simply does not
  fire.** The method is *fundamentally large-k*. There is no "the gadget needs many colors" or
  "iteration needs depth" obstruction — it is purely that the random object doesn't exist below
  threshold.
- **k-agnostic part?** The structural skeleton (complement-of-2-section, α-bound ⟹ χ-bound,
  perfect-matching ⟹ vertex-criticality) is **completely k-agnostic**. The ONLY k-dependence is the
  *existence* of the hypergraph, which is outsourced to a probabilistic threshold. **So if one could
  EXHIBIT an explicit 4-uniform hypergraph on n = 4·3+1 = 13 vertices with (i) all H−v have a
  perfect matching and (ii) local sparsity ⋃_{e∈F}e ≥ 3|F| for small F, then the SAME machinery would
  hand back a (4,1)-graph on 13 vertices.** ← This is a concrete, finite, checkable target. See
  the LADDER section, Rung H.

> Caveat on Rung H: for r=1, s=4, the α-bound needs α(G−R) ≤ 4 ⟹ χ ≥ 13/4 > 3 ⟹ χ ≥ 4, and the
> independent-set contradiction needs |E(G₂[X])| ≤ C(4,2)+2 = 8 for every 5-subset X. The Lemma-5
> hypothesis is "⋃_{e∈F} e ≥ (s−1)|F| for all |F| < 2^{s+1}", i.e. for all small F. On only 13
> vertices with 4-uniform hyperedges this is a TIGHT, possibly OVER-constrained finite system — it
> may be infeasible, which would explain (and localize) the small-k death precisely. Worth a SAT/ILP
> feasibility check (hunter/algebra). If infeasible, that's a clean partial impossibility result for
> the M–S route at k=4.

---

## PAPER 2 — Skottova–Steiner 2025 (arXiv:2508.08703) ← THE FRESH, ON-TARGET PAPER
### "Critical edge sets in vertex-critical graphs"

This is by the SAME second author (Raphael Steiner) two years later, and it is the paper that
**isolates k=4 as the sole survivor** and gives the only published guidance on attacking it.

- Defines **f_k(n)** = largest r such that a (k,r)-graph on n vertices exists (0 if none).
- **Theorem 1.2:** for every fixed k ≥ 5, f_k(n) = Ω(n^{1/3}). (Hence f_k(n)→∞, resolving Erdős's
  strongest form for k ≥ 5.)
- **Theorem 1.4 (upper bound, holds for ALL k ≥ 4 including k=4):** f_k(n) = O(n / (log n)^c) for an
  absolute c > 0. Proof uses a Conlon–Fox weak regularity lemma. → Even at k=4, IF (4,r)-graphs
  exist, the "r you can achieve" grows strictly sub-linearly in n.
- **k=5 construction** = modified Jensen circulants G_{k,m,q} with a richer distance set D=D1∪D2∪D3
  (they ADD edges to Jensen's graph to force periodicity of any (k−1)-coloring of G−R).

### THE k=4 SECTION (Section 5, "Conclusive remarks") — verbatim-faithful extraction

> "The only case of Dirac's conjecture and Erdős's problems that remains open is k = 4. ... the
> circulant graphs G_{k,m,q} considered here CANNOT settle this remaining case. This is due to the
> fact that for k=4 and m≥2 we have D2 = D3 = ∅, so the only distances we allow for edges are those
> in D1 = {1,…,2m−1}. It is then not hard to check that the so-defined circulant graph has chromatic
> number 3. ... This of course does not rule out that some other distance sets could yield circulant
> (4,1)-graphs, but we were not able to find them so far, and **we lean towards thinking that they do
> not exist.**"

**This is the most important sentence for the squad's prior.** Read carefully:
- The lean-NO is **only about circulant (4,1)-graphs**, a narrow family.
- They make **NO conjecture** that (4,1)-graphs in general are nonexistent.
- They frame k=4 as "intriguing open," not "probably false."

### THE GIFT — Proposition 5.1 (necessary conditions for a (4,r)-graph)

Let r ≥ 1 and let G be any (4,r)-graph. Then:
- **edge-connectivity (and min degree) ≥ 3r + 3** → for r=1: **min degree ≥ 6, λ(G) ≥ 6**;
- **max degree ≤ |V(G)| − (2r + 3)** → for r=1: **Δ ≤ |V| − 5**;
- consequently **|V(G)| ≥ 5r + 6** → for r=1: **|V| ≥ 11**.

Proofs (both rigorous, I checked):
- *Edge-connectivity*: for any cut (X,Y), 3-color G[X] and G[Y], apply a uniformly random S₃
  permutation to the Y-coloring; expected monochromatic crossing edges = (#cut edges)/3, so some
  permutation gives ≤ x/3 bad edges; but (4,r) ⟹ every 3-coloring has ≥ r+1 monochromatic edges,
  so x/3 ≥ r+1, x ≥ 3r+3.
- *Max degree*: longest-path / independent-set counting in the non-neighborhood W = V∖({v}∪N(v));
  if Δ too big, |W| too small to host the required independent sets.

### Problem 5.2 (their explicit computational target)

> "the sparsest option for a (4,1)-graph left by Proposition 5.1 is that of a **6-regular graph**, and
> from a computational viewpoint it seems natural to restrict the search to such graphs first.
> **Problem 5.2: Does there exist a 6-regular (4,1)-graph?**"

→ This is EXACTLY what hunter/forge should target first. A 6-regular graph automatically meets
min-degree-6; one then only needs χ=4, vertex-criticality, 6-edge-connectivity, and no critical edge.

### Bonus surgery primitive — Lemma 2.1 (order-manipulating gluing)

Given (k,r)-graphs G₁,…,G_t and a k-critical graph H with t edges, a Hajós-flavored gluing
produces a NEW (k,r)-graph of order h + Σ(nᵢ − 1). Preserves the (k,r)-property exactly. **Caveat:
it consumes (k,r)-graphs as input — useless for *finding the first* (4,1)-graph, but if ONE is
found it yields infinitely many of all large orders.** Hand this to forge for the "after first hit"
phase. (Open sub-question worth probing: is there a seedless degenerate case that builds a first one?)

---

## Who cites M–S / active ongoing work check

- The direct, most recent descendant IS the Skottova–Steiner 2025 paper (same author group, ETH
  Zürich). It explicitly continues the line and leaves k=4 open as of Aug 2025.
- The partial result Jensen–Siggers 2012 (Sib. Èlektron. Mat. Izv. 9, 156–160): for every ε>0 there
  is a 4-vertex-critical graph where < ε-fraction of edges are critical. This is the ONLY prior
  result *addressing k=4 directly* in the literature, per Skottova–Steiner. It says you can get the
  critical-edge fraction arbitrarily small but never (so far) to zero — a near-miss family worth
  studying as the top rung below the witness.
- No visible claim (as of the 2025 paper, the freshest) that anyone has resolved k=4 either way. No
  "someone is close" signal beyond Steiner's own group. → No need to alarm team-lead about a
  competitor; flagged the fresh paper instead.

---

## THE INTERPOLATION LADDER (the creative deliverable)

Strength-graded targets between "known 4-critical graphs" and "the full (4,1) witness." Each rung is
either provable, refutable, or a computational feasibility question with CURRENT tools. Ordered from
weakest (known) to strongest (the witness). r=1 throughout unless noted.

Let `c(G)` := number of critical edges, `cf(G)` := fraction of edges that are critical.

- **Rung 0 (known true).** A 4-critical (edge-critical) graph exists, e.g. K₄, odd wheels, Hajós
  joins. Here EVERY edge is critical: c(G)=|E|, cf=1. This is the FAR end from the target.
- **Rung 1 (known true).** A 4-vertex-critical graph with c(G) < |E| (at least one NON-critical edge).
  Vertex-critical-but-not-edge-critical graphs exist for k=4 (the converse-fails examples). First
  separation between vertex- and edge-criticality. EASY; pin a concrete small witness (forge/count).
- **Rung 2 (known true, Jensen–Siggers 2012).** For every ε>0, a 4-vertex-critical graph with
  cf(G) < ε. Critical-edge FRACTION → 0. This is the strongest published k=4 result. **Action:
  obtain/recreate the Jensen–Siggers family and measure how its critical edges are distributed —
  are they concentrated on a shrinking "core"? If the core can be surgically removed/redirected, that
  is the bridge to Rung 5.** (count has fraction data — coordinate.)
- **Rung 3 (provable target, NEW framing).** A 4-vertex-critical graph with an EXACT small count of
  critical edges, c(G) = t, for t as small as we can force (t = 3, 2, …). Whereas Rung 2 controls the
  *fraction*, Rung 3 controls the *absolute number*. **First genuinely new rung:** push c(G) down to
  a single-digit constant. Refutable side: is there a LOWER BOUND c(G) ≥ g(n) > 0 for all
  4-vertex-critical G? (If yes for all n, the target is FALSE.) Theorem 1.4 gives an UPPER bound on
  the size of the *smallest* critical set, not a lower bound on the *number* of critical edges, so
  this lower-bound question is open and is the natural impossibility-wall probe — hand to wall/gallai.
- **Rung 4 (computational, the 6-regular pin).** Does a 6-regular 4-vertex-critical graph on n≥11
  vertices with c(G)=0 exist? = **Steiner's Problem 5.2 = THE witness restricted to 6-regular.**
  Fully finite per n. hunter's geng/SAT floor should hit this first. Outcome either way is publishable.
- **Rung 5 (the witness).** A (4,1)-graph: 4-vertex-critical, c(G)=0, satisfying Prop 5.1
  (λ≥6, Δ≤|V|−5, |V|≥11). = `∃ G, IsErdos944 4 1`.
- **Rung H (orthogonal route, from M–S).** Does an explicit 4-uniform hypergraph on 13 vertices exist
  with (i) every H−v has a perfect matching and (ii) local sparsity ⋃_{e∈F}e ≥ 3|F| for all small F?
  If YES → complement-of-2-section gives a (4,1)-graph on 13 vertices for FREE via M–S machinery.
  If NO (SAT-infeasible) → clean localized impossibility for the M–S route at the minimal n. **This
  is a finite SAT/ILP feasibility instance — the single most direct computational shot at a witness.**

### First rung that is provable/refutable with current tools

**Rung 4 (Steiner's Problem 5.2) and Rung H** are the two sharpest, both purely computational and
both finite. Rung 4 is the literature-sanctioned target; Rung H is a free side-door that, if
feasible, hands a witness directly through a published existence machine. Rung 3's *lower-bound*
direction is the cleanest path to a FALSE answer if the squad's prior shifts that way.

**Recommendation to squad:** hunter prioritizes Rung 4 (6-regular, n=11,12,13,…) and Rung H (13-vertex
4-uniform hypergraph SAT). wall/gallai attack Rung 3's lower-bound question (is c(G) ≥ const forced?).
count maps the critical-edge distribution of the Jensen–Siggers Rung-2 family for a possible surgery
bridge to Rung 5.

---

## COMPUTATIONAL RESULTS I established on the ladder (proximity, 2026-06-10)

All χ cross-checked backtracking vs SAT via the squad's `checkers.py` (0 mismatches anywhere).

### Rung H (M–S hypergraph route) → EMPTY at k=4. (full writeup: `proximity_rung_h.md`)
- The route is rigid to the unique order **n=13** for (k=4,r=1).
- Reason 1 (exact counting): property (i) forces |E(H)| ≥ 5; property (ii) fails at |F|=5
  (need union ≥ 15 > 13). M–S sufficient condition infeasible.
- Reason 2 (degree, new bridge): the densest G the route can output has **min-degree ≤ 4 < 6** =
  Prop 5.1 floor. M–S graphs are structurally too sparse to be (4,1)-graphs. Re-derives Prop 5.1
  from the hypergraph side.

### Rung 4 (Steiner's Problem 5.2: 6-regular (4,1)-graph?) → NO for n=11, n=12 (n=13 running).
File: `proximity_6regular.py` (exhaustive via `geng -c -d6 -D6 n`, every iso class once).
- **n=11:** 266 connected 6-regular graphs; **0 are even 4-vertex-critical**; 0 witnesses.
- **n=12:** 7849 connected 6-regular graphs; **0 are 4-vertex-critical**; 0 witnesses.
- **n=13:** ~347,700 graphs; scan in progress.
- **Structural near-miss data — the binding failure is vertex-criticality, and the window OPENS with n.**
  For 6-regular χ=4 graphs, the maximum number of *critical vertices* over all such graphs grows:
  - **n=11:** max **4 / 11** critical vertices (157/177 χ=4 graphs have ZERO critical vertices).
  - **n=12:** max **8 / 12** critical vertices (one graph reaches 8; 5881/6498 have ZERO).
  So at the minimum order the binding failure is **vertex-criticality, not the no-critical-edge
  condition** — 6-regular graphs are simply too dense to be vertex-critical there. Consistent with
  Prop 5.1's Δ ≤ n−5 (= 6 at n=11) pinning 6-regular graphs to the extreme edge of the feasible
  window; the window slackens as n grows, and the data shows graphs climbing toward full
  vertex-criticality (4/11 → 8/12). A 6-regular witness, if it exists, must live at larger n where
  full vertex-criticality first becomes attainable.

This gives the squad a HARD lower bound on the order of a 6-regular witness: **n ≥ 13** (n=11,12
exhaustively cleared), with a clear structural expectation that the search must climb above the
Prop 5.1 floor of 11 before 6-regular graphs can even become fully vertex-critical (let alone
edge-redundant).

---

## Bottom-line answers to the four mandate questions

1. **Mechanism:** PROBABILISTIC (Shamir/JKV random-hypergraph matchings) + complement-of-2-section.
   Explicit only in skeleton; existence of the hypergraph is the non-explicit, k-large ingredient.
2. **k-vs-r tradeoff for r=1:** s=4, n=s(k−1)+1, k₀=⌈n₀/4⌉+1 ≫ 4. The r=1 specialization does NOT
   reach k=4 and does not even recover Jensen at small k. The structural skeleton is k-agnostic; only
   the random-existence step is not.
3. **Where small k fails:** union bound needs room — Lemma 3's w.h.p. existence is vacuous for small
   n=s(k−1)+1. NOT a structural k=4 obstruction. (Contrast: the *circulant* route in Paper 2 DOES die
   structurally at k=4 because D2=D3=∅ ⟹ χ=3.)
4. **k=4 commentary / prior:** open since 1970; sole survivor after Jensen (k≥5). Steiner leans NO
   only for circulants, makes no general conjecture. Only direct k=4 result is Jensen–Siggers 2012
   (critical-edge fraction → 0, never 0). No competitor claiming resolution as of Aug 2025.

## File pointers
- Papers (local): /tmp/ms2023.txt (arXiv:2310.12891), /tmp/ss2025.txt (arXiv:2508.08703).
- Lean defs: formal-conjectures/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring.lean
- Problem: formal-conjectures/FormalConjectures/ErdosProblems/944.lean
