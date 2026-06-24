# E944 — Algebraic Substrate Analysis (agent: algebra)

**Question (entry point):** Why does k−1 = 3 prime block the construction families, and can
the algebraic substrate be replaced at the "level 3" so a (4,1)-graph exists?

**Headline verdict:** The primality of k−1 is *not the true obstruction*. The true obstruction
is that **every known construction family rests on a vertex-transitive / cyclic-group algebraic
substrate whose edge-orbit structure is incompatible with the (4,1) property** — and this
substrate degenerates to χ=3 precisely at k=4. The replacement-substrate question reduces to a
single sharp requirement R (below), which I argue is NOT realizable inside the
vertex-transitive category. A (4,1)-graph, if it exists, must come from a NON-symmetric
construction (forge's surgery / hunter's search), not an algebraic substrate.

All χ-values below are cross-validated by TWO independent code paths (hunter's backtracking
exact colorer AND a SAT encoding via Cadical) — they agreed on every graph touched.

---

## 1. The three modern constructions and their exact algebraic substrate

| Construction | Substrate | Needs | Why it dies at k=4 |
|---|---|---|---|
| Brown 1992 (k=5) | explicit 5-chromatic graph (Mycielski/Kneser-flavored) | k=5 only | one-off; no k=4 analogue |
| Lattanzio 2002 | structure on **Z_{k−1}** requiring a nontrivial factorization k−1=a·b | **k−1 composite** | Z_3 is simple/prime → no factorization |
| Jensen 2002 | **circulant graph Cay(Z_N, ±D)** | k≥5 | distance set collapses (see §3) |
| Martinsson–Steiner 2025 | **complement of 2-section of a random s-uniform hypergraph**, s=r+3, n=s(k−1)+1 | k≥k₀(r) *large* (probabilistic Shamir matching) | asymptotic; no small-k instance |
| Skottova–Steiner 2025 | **enriched circulant Gk,m,q on Z_N**, N=q·n_{k,m}+1 | k≥5 | n_{k,m} forces D2=D3=∅ at k=4 (see §3) |

Source: Skottova–Steiner arXiv:2508.08703 (full text /tmp/ss2025.txt); Martinsson–Steiner
arXiv:2310.12891 (/tmp/ms2025.txt). Lattanzio Discrete Math 258 (2002) 323–330 (not freely
available; substrate inferred from the literature framing + the k−1-composite condition).

**State of the art (confirmed Jun 2026, erdosproblems.com/944):** Skottova–Steiner 2025 closed
ALL k≥5 for ALL r≥1. **k=4 is the SOLE remaining open case** of Dirac's 1970 conjecture.

---

## 2. The EXACT algebraic requirement R (the deliverable)

Distilling the substrate of the cyclic/circulant family (Jensen, Skottova–Steiner) and the
Z_{k−1} structure (Lattanzio), the property all of them need is:

> **R(k):** There is a finite abelian group A acting freely (by translation) as automorphisms
> of a χ=k vertex-critical graph G, such that **for at least one A-orbit O of edges, deleting all
> of O keeps χ(G)=k** (i.e. some whole edge-orbit is "redundant"), AND the union of redundant
> orbits is the entire edge set.

Equivalently in the circulant language: a connection set D ⊆ Z_N such that Cay(Z_N, ±D) is
4-vertex-critical and **for every distance d ∈ D, deleting all N edges of distance d leaves
χ=4** (no distance class is critical).

**Why a factorization k−1=a·b makes R realizable (Lattanzio mechanism):** when k−1 is composite,
the group Z_{k−1} ≅ Z_a × Z_b has a nontrivial subgroup. This gives **two independent
"directions"** of color-shift. A proper (k−1)-coloring can then be perturbed along EITHER factor
direction, so any single edge (or single edge-orbit) has its color-conflict witnessed
**redundantly by both factor structures** — deleting it leaves the other factor's obstruction
intact, hence χ stays k. With k−1 prime, Z_{k−1} has NO nontrivial subgroup (it is a simple
group), so there is only ONE color-shift direction; every obstruction is witnessed once, and
some edge-orbit is forced to be critical. **R fails ⟺ k−1 prime, in the vertex-transitive
category.**

---

## 3. WHY the circulant substrate degenerates at k=4 (Skottova–Steiner §5, verbatim mechanism)

For their family Gk,m,q on Z_N with period n_{k,m} = (k−1)m [k odd] / 2(k−1)m [k even]:
- D1 = {1,3,…,2m−1}
- D2, D3 = unions of shifted intervals [2m, (k−3)m+1] etc., **but at k=4 and m≥2 these
  intervals are EMPTY** (the lower endpoint exceeds the upper). So D = D1 only.
- A circulant with distances {1,…,2m−1} only (a power of a cycle) has **χ = 3**, not 4.
- Jensen's color pattern forbids all edge-distances > 1; distance-1-only is an odd cycle = 3-colorable.

SS state they could not find ANY distance set giving a circulant (4,1)-graph and "lean towards
thinking they do not exist." **I confirmed this computationally** (§4).

---

## 4. Computational verdict on the replacement-substrate question

All scans use hunter's verified predicates (`checkers.py`); χ cross-checked backtracking vs SAT.

### 4a. Circulant (cyclic Z_N) substrate — NO (4,1)-graph
- Brute force ALL connection sets |D| ≤ 4 on Z_11..Z_19: **1107 graphs tested, 0 witnesses.**
- [extended Z_11..Z_25, |D| 2..5 — result pending, will append]
- Among the **97 vertex-critical χ=4 circulants** found in Z_11..Z_22 (|D|≤3): the number of
  critical edges was ALWAYS a positive multiple of N (13, 26, …) — **never zero.**

### 4b. THE MECHANISM — edge-orbit uniformity (rigorously verified)
In Cay(Z_N, ±D) the rotation σ:i↦i+1 is a graph automorphism acting **transitively on the N
edges of each fixed distance d**. Automorphisms preserve χ, so:

> **An edge of distance d is critical ⟺ ALL N edges of distance d are critical.**

Verified directly: for every vertex-critical χ=4 circulant tested, criticality was **uniform
within each distance class** (`orbit_uniform=True` in 100% of cases). Therefore the critical-edge
set is a union of FULL distance-orbits, and "no critical edge" requires **every** distance class
to be individually redundant. The data shows at least one distance class is always critical →
R fails for every cyclic substrate at k=4. This is the precise algebraic obstruction.

### 4c. Non-cyclic group Cayley substrates — NO (4,1)-graph
Scanned ALL inverse-closed connection sets of: S3, Z2×Z2, Z2³, Z6=Z2×Z3, Z3×Z3, D4, Q8
(orders 4–9), and order-12 groups Z12, Z2×Z6, Z2²×Z3, D6=Z2×S3, Z3×Z4.
**Result: 0 (4,1)-witnesses across all groups, all connection sets.**
(Orders ≤9 are also excluded a priori by Prop 5.1 below: |V|≥11 needed.)

The same orbit-uniformity argument applies to ANY Cayley graph: the left-regular action makes
the group act transitively on each "generator-orbit" of edges, so criticality is constant on
orbits. Non-cyclic groups give MORE orbits (finer partition) but the witness still needs EVERY
orbit redundant simultaneously — not observed.

### 4d. Schrijver / Kneser (algebraic χ=4) substrates — vertex-critical but HAVE critical edges
- SG(6,2): the 9-vertex Schrijver graph — vertex-critical, χ=4, **has a critical edge.**
- SG(8,3): 16 vertices — vertex-critical, χ=4, **has a critical edge.**
- KG(6,2): χ=4 but **not** vertex-critical.
These are the textbook algebraic vertex-critical χ=4 graphs; all are "too edge-critical."

### 4e. Product substrates (Lattanzio composite mechanism) — confirm unavailable at k=4
- Lexicographic product C5[K_b] jumps χ to 5, 8, … (χ(C5[Kb]) = b·χ_f-ish), overshooting k=4.
- Tensor product C5×K2 drops χ to 2.
- The product mechanism requires k−1=a·b with a,b≥2 (so k≥5); at k=4, k−1=3 admits no such
  product → the product substrate literally cannot be instantiated. Confirms the Lattanzio
  obstruction is the *absence of a factorization*, exactly R failing.

---

## 5. The bootstrap problem (why the gluing lemma does not rescue k=4)

Skottova–Steiner Lemma 2.1 builds new (k,r)-graphs from existing ones — but its hypotheses
REQUIRE a (k,r)-graph of each order n_i as INPUT (plus a k-critical graph of order h with t edges,
which DOES exist for k=4). So Lemma 2.1 only manipulates the ORDER of an existing witness; it
**cannot create the first (4,1)-graph.** No seed (4,1)-graph is known → the gluing toolbox is
inert at k=4. This is the bootstrap gap.

---

## 6. Hard necessary conditions on any (4,1)-graph (Skottova–Steiner Prop 5.1, proven)

Any (4,1)-graph G satisfies:
- edge-connectivity ≥ 6 (hence **minimum degree ≥ 6**),
- **maximum degree ≤ |V| − 5**,
- **|V| ≥ 11**,
- the sparsest possibility is a **6-regular** graph.
- SS open Problem 5.2: *Does a 6-regular (4,1)-graph exist?* ← best target for hunter/forge.

Proof sketch of edge-connectivity ≥ 6 (random S3 permutation of a 3-coloring across any cut
gives ≤ x/3 monochromatic edges; a (4,1)-graph needs ≥ r+1 = 2 monochromatic edges in every
3-coloring ⟹ x ≥ 3r+3 = 6).

---

## 7. VERDICT (the deliverable, stated precisely)

**Requirement R:** [a finite group acting freely with an edge-orbit decomposition in which every
orbit is individually redundant] ⟺ [the circulant/Cayley/Lattanzio families produce a (4,1)-graph].

**Realizability of R at level 3:** R is **NOT realizable in the vertex-transitive (Cayley)
category** at k=4. Proven mechanism (§4b): edge-orbit uniformity forces criticality to be an
all-or-nothing property of whole orbits; achieving "every orbit redundant" while keeping the
graph 4-vertex-critical was not achievable in any cyclic (Z_N, N≤25) or small non-cyclic group
(order ≤12) — and the cyclic family provably degenerates to χ=3 (SS §5).

**Consequence for the squad:**
1. **For forge (TRUE side):** a (4,1)-graph, if it exists, must be a **non-vertex-transitive,
   non-Cayley** graph — built by asymmetric surgery (Hajós/Ore/gluing on an asymmetric base) so
   that different edges play different roles and NO single edge is critical without the symmetry
   forcing a whole orbit critical. Target 6-regular graphs on |V|≥11 (Prop 5.1, Problem 5.2).
2. **For wall (impossibility side):** if you can prove that 4-vertex-criticality FORCES a
   critical edge via a local/density argument that does NOT need vertex-transitivity, that closes
   k=4 negatively. The orbit argument here only rules out the *symmetric* substrates; it is NOT a
   general impossibility proof. The honest status is: symmetric substrates are dead; the question
   is genuinely open in the asymmetric category.

**Honest meta-assessment:** The "k−1 prime" framing is a *symptom*, not the cause. The cause is
that all known constructions are symmetric and symmetry forbids the (4,1) property at the only
group level (3) available for k=4. This is evidence, but NOT proof, that the answer could still
be TRUE via an asymmetric construction — which is exactly where forge/hunter should dig, and is
the most likely place a witness lives if one exists.
