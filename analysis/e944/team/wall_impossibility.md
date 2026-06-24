# E944 — Impossibility direction ("answer = NO"): structural attack

**Owner:** wall. **Entry point:** assume answer is NO — prove every 4-vertex-critical graph
has a critical edge. Equivalently: show no 4-vertex-critical graph with *no critical edge* exists.

**Status:** IN PROGRESS (2026-06-10). Live derivation log; conclusions marked [DERIVED]/[CONJECTURE]/[OPEN].

---

## 0. Locked target (from archivist_definitions.md, double-checked against Coloring.lean)

A witness G must satisfy:
- (a) χ(G) = 4.
- (b) **vertex-critical**: ∀v, χ(G−v) = 3 (deleting any vertex drops χ to 3; can't be <3 globally
  while staying 4-chromatic on the whole — but per-vertex only χ(G−v) < 4 is required).
- (c) **no critical edge**: ∀ edge e, χ(G−e) = 4 (deleting any single edge keeps χ = 4).

The impossibility claim: **NO finite G satisfies (a)∧(b)∧(c).**
(skeptic established finite suffices — via the Mathlib `Set.ncard`-of-infinite-set = 0 trap, NOT
de Bruijn–Erdős, which Mathlib lacks: any infinite-edge G has its full edgeSet as a critical set with
ncard 0, so clause (c) `1 < ncard` fails ⟹ not a witness. A witness has finite edgeSet, hence finite.
See skeptic_statement_lock.md §1.)

## 0.1 VOCAB TRAP (gallai) — pinned at the top so I never slip

- `IsCritical` = **vertex-critical** (χ=k, every vertex deletion drops χ). NOT edge-critical.
- "Edge-critical" / "k-critical" in the classical literature (Dirac, Gallai, Ore, Kostochka–Yancey)
  means χ=k AND χ(G−e)=k−1 for **every** edge e. That is the class where KY density |E|≥(5n−2)/3,
  Gallai trees, Ore degree bounds live.
- Edge-critical ⟹ vertex-critical. Converse FALSE.
- **The target is a vertex-critical graph that is explicitly NOT edge-critical** (it has NO critical
  edge — the maximal possible failure of edge-criticality).
- ⟹ I may NOT apply KY/Gallai/Ore directly to G. I may apply them only to genuinely EDGE-critical
  subgraphs I extract from G. The whole game is: extract edge-critical objects, bound those.

---

## 1. The spanning-critical-subgraph decomposition  [DERIVED]

This is the structural engine. Let G be a witness (4-vertex-critical, no critical edge), finite, n vertices.

### 1.1 Every 4-chromatic subgraph of a vertex-critical G is SPANNING

Claim: if H ⊆ G (subgraph, any vertex/edge subset) has χ(H) = 4, then V(H) = V(G).

Proof: suppose some vertex v ∉ V(H). Then H ⊆ G−v (as subgraphs, since H avoids v). Monotonicity of χ
under subgraph gives χ(G−v) ≥ χ(H) = 4. But vertex-criticality (b) says χ(G−v) = 3 < 4. Contradiction.
Hence V(H) = V(G): H spans. ∎

Corollary: every **4-critical (edge-critical) subgraph** of G is spanning, and every vertex of G has
degree ≥ 3 in it (edge-critical graphs have min degree ≥ k−1 = 3 — Dirac).

### 1.2 "No critical edge" forces a proper spanning 4-chromatic subgraph missing each edge

Fix any edge e ∈ E(G). Condition (c): χ(G−e) = 4. So G−e is a 4-chromatic graph on V(G).
Take any color-critical (edge-critical) subgraph H_e of G−e with χ(H_e) = 4 — every finite graph of
chromatic number 4 contains a 4-edge-critical subgraph (delete edges one at a time while χ stays 4;
when stuck, what remains is 4-edge-critical). [standard]

Properties of H_e:
- χ(H_e) = 4.
- H_e ⊆ G − e ⊊ G, so e ∉ E(H_e): **H_e misses the edge e.**
- By §1.1, H_e is **spanning** (V(H_e) = V(G)).
- H_e is **4-edge-critical** ⟹ min degree ≥ 3 in H_e, and KY density applies TO H_e:
  |E(H_e)| ≥ (5n − 2)/3.   ← legitimate KY use: H_e IS edge-critical. [gallai trap respected]

So: **for every edge e of G, there is a spanning 4-edge-critical subgraph H_e ⊆ G with e ∉ H_e.**

### 1.3 G is a union of its edge-critical spanning subgraphs; every edge is "redundant"

For each e, H_e ⊆ G omits e but is still 4-chromatic. So:
- Every edge e is omittable: lies outside some spanning 4-edge-critical subgraph.
- ⋃_e H_e ⊆ G and each H_e is 4-chromatic spanning. The edges of G NOT forced: an edge f is in H_e
  for the e's where the critical-subgraph-extraction kept it.

Define for each edge e the "critical core" H_e. The map e ↦ H_e gives a family of spanning
4-edge-critical subgraphs, each missing a designated edge. This family is the raw material.

### 1.4 Reformulation: G is "edge-critical-cover-redundant"

G has no critical edge ⟺ G−e is 4-chromatic for all e ⟺ for all e, e is not in EVERY 4-edge-critical
subgraph... more precisely: **e is critical ⟺ e lies in every spanning 4-chromatic subgraph ⟺ G−e is
3-chromatic.** So "no critical edge" = "no edge lies in all 4-chromatic subgraphs" = "the intersection
over all spanning 4-chromatic subgraphs of their edge sets is EMPTY."

Equivalently: ⋂_{H ⊆ G, χ(H)=4, H spanning} E(H) = ∅.   [DERIVED — clean characterization]

This is the precise structural meaning of the target. Each edge is avoidable by *some* 4-chromatic
spanning subgraph. The witness must arrange that no single edge is in all of them.

---

## 2. The Kostochka–Yancey squeeze — VERDICT: does NOT close on |E(G)| alone  [DERIVED]

### 2.1 The naive squeeze and why it fails

For each edge e, H_e is spanning 4-edge-critical ⊆ G, missing e. KY on H_e: |E(H_e)| ≥ (5n−2)/3.
H_e proper subgraph missing e ⟹ |E(H_e)| ≤ |E(G)| − 1. Combine:

    |E(G)| ≥ (5n−2)/3 + 1 = (5n+1)/3.       [DERIVED — a LOWER bound on |E(G)|]

This is necessary but **NOT a contradiction**. KY is a *lower* bound; a vertex-critical 4-chromatic
graph can be made *denser* freely (adding edges preserves χ=4 and can preserve vertex-criticality).
There is **no matching KY-style upper bound on |E(G)|** for vertex-critical (non-edge-critical) graphs.
So the squeeze on the global edge count CANNOT close. **[Pre-registered fatal obstruction #1 — CONFIRMED.]**

This is exactly the kind of failure the team-lead flagged: "If you instead discover the squeeze CAN'T
close (slack always suffices), that failure analysis is the existence-side spec." → handed to forge §5.

### 2.2 Min degree ≥ 3  [DERIVED]

Any 4-vertex-critical G has δ(G) ≥ 3. (If deg(v) ≤ 2, a 3-coloring of G−v — which exists since
χ(G−v)=3 — has a free color for v among 3, extending to a 3-coloring of G, contradicting χ(G)=4.)
So every vertex has degree ≥ 3. Combined with §2.1, n ≥ 4 and |E(G)| ≥ max((5n+1)/3, 3n/2).

### 2.3 The correct local characterization of critical vs non-critical edges  [DERIVED]

For an edge e = uv in 4-vertex-critical G (χ(G)=4):
- e **critical** ⟺ χ(G−e) = 3 ⟺ ∃ a 3-coloring of G−e, and every such coloring assigns u,v the
  SAME color (else it'd properly 3-color G).
- e **non-critical** ⟺ χ(G−e) = 4 ⟺ G−e is still not 3-colorable ⟺ removing the constraint uv
  does NOT unlock any 3-coloring.

**TARGET restated (the cleanest form):** G is 4-chromatic, vertex-critical, and **"3-coloring-robust"**:
no single edge deletion makes it 3-colorable. ⋂_{H spanning, χ(H)=4} E(H) = ∅ (no edge is in every
spanning 4-chromatic subgraph). This is the object to refute or construct.

### 2.4 The Grötzsch data point  [VERIFIED computationally]

Grötzsch graph (Mycielskian of C₅, n=11, triangle-free, 4-chromatic): vertex-critical ✓, but it
**HAS critical edges** (no-critical-edge = False). Confirms the standard observation that
Mycielski/triangle-free routes do not by themselves yield witnesses; consistent with k=4 being hard.

## 3. Where the squeeze MIGHT still close — the right leverage  [IN PROGRESS]

Since global |E| won't close, the leverage must be one of:
(L1) **Gallai's structure of low vertices** applied to the H_e's (the degree-3 vertices of each
     edge-critical H_e form Gallai trees — coordinate with gallai).
(L2) **The potential method (Kostochka–Yancey potentials)** — a finer functional than raw edge count;
     this is how KY actually prove tightness and characterize 4-Ore graphs. The potential of G itself
     (not just H_e) could be bounded.
(L3) **Overlap counting across the H_e family**: each edge e is missing from H_e but every OTHER edge
     might be forced into many H_f's. Double-count Σ_e |E(H_e)| vs n·(per-edge multiplicity).
(L4) **The k=4 arithmetic obstruction** (k−1=3 prime): why Lattanzio's algebraic construction needs
     k−1 composite. If the *only* obstruction is constructive (existence-side), there's no impossibility
     theorem and answer is likely YES — that itself is a finding to hand forge.

Pursuing L3 (overlap counting) next — it's the one genuinely new to the impossibility side.

## 3.5 L3 overlap-counting — DEAD END  [DERIVED]

Σ_e |E(H_e)| = Σ_f #{e : f ∈ H_e}. LHS ≥ m·(5n−2)/3 (m = |E(G)|). RHS ≤ m(m−1) (each edge in ≤ m−1
of the H_e). This re-derives m ≥ (5n+1)/3 — the SAME floor as §2.1, no new obstruction. L3 dead.

## 3.6 Gallai-forest tension — TOO WEAK  [DERIVED]  → pre-registered obstruction #2

Each H_e is 4-edge-critical; its degree-3 ("low") vertices induce a Gallai forest (Gallai's theorem).
Every low vertex of H_e has degree ≥4 in G (gallai δ≥4, now δ≥6), so lost ≥1 edge in G→H_e. But the
deletion set D_e need only have |D_e| ≥ ⌈(#low)/2⌉, and a 4-regular-or-denser G has ample slack to
host this. No contradiction. **Obstruction #2 CONFIRMED: the Gallai-forest/deletion count has slack.**

## 4. CONVERGENCE: δ≥6, 6-regular floor, and the CIRCULANT sub-problem  [KEY PIVOT]

Three independent results converged (2026-06-10):
- **gallai Theorem 3 + Skottová–Steiner 2025 (arXiv:2508.08703) Prop 5.1**: any witness has **δ ≥ 6**;
  the sparsest possible witness is **6-regular** (their open Problem 5.2: "does a 6-regular (4,1)-graph
  exist?"). So n ≥ 11, |E(G)| ≥ 3n.
- **proximity**: Steiner (Sec 5, 2025 paper) explicitly **leans toward NO for *circulant* graphs**
  specifically — but says nothing definitive about general (4,1)-graphs. The case is open.
- **wall (this file), computational**: the best low-critical-fraction circulants C_n(1,2,5,…) get
  arbitrarily close to being witnesses but exactly one orbit never releases. **REGULARITY CORRECTION
  (skeptic):** only the genuinely 6-regular rows sit at the δ=6 floor; the `s=n/2` antipodal collapse
  changes degree. Corrected table:

  | n  | best circulant       | degree | critical edges | % critical | at δ=6 floor? |
  |----|----------------------|--------|----------------|-----------|---------------|
  | 7  | C₇(1,2)              | 4-reg  | 7              | 50%       | no (below)    |
  | 10 | C₁₀(1,2,5)           | 5-reg  | 10             | 40%       | no            |
  | 13 | C₁₃(1,2,5)           | 6-reg  | 13             | 33%       | YES           |
  | 16 | C₁₆(1,2,5)           | 6-reg  | 16             | 29%       | YES           |
  | 19 | C₁₉(1,2,5,8)         | 8-reg  | 19             | 25%       | no (above)    |
  | 22 | C₂₂(1,2,5,8,11)      | 9-reg  | 22             | 22%       | no            |

  (Degrees re-verified by skeptic + me; the s=n/2 element contributes +1 not +2 to degree.) In each
  case **exactly n edges are critical** — one connection-orbit — and all other orbits are non-critical.
  The critical fraction → 0 but never reaches 0. No circulant witness for n ≤ 16 (full S-scan, |S|≤5)
  or n ∈ {10,13,16,19,22} (best-orbit scan). The clean δ=6-floor cases are the two 6-regular rows. ✓

**MY REFOCUSED IMPOSSIBILITY TARGET:** prove the *circulant* sub-case Steiner conjectured —
**no circulant graph is a (4,1)-witness** — by explaining the obstruction rigorously.
This is a genuine partial impossibility theorem (closes the sub-case the expert leans toward) even
though the FULL k=4 question may have a YES answer via a non-vertex-transitive graph (forge's domain).
See §5 for the analysis.

## 5. The CIRCULANT RIGIDITY obstruction  [VERIFIED computationally; proof sketch below]

### 5.1 The universal structural law  [VERIFIED n=11..22, all 52 four-vc 6-regular circulants]

> **Empirical Theorem (circulant rigidity).** Let G = C_n(S) be a 4-vertex-critical 6-regular
> circulant (|S|=3, no antipodal difference). Then:
> (i) G−v has EXACTLY 6 proper 3-colorings — i.e. its 3-coloring is **UNIQUE up to permutation of
>     the 3 colors** (rigid).
> (ii) the unique 3-coloring partitions V∖{v} into 3 color classes that are **arithmetic-progression
>      blocks of ℤ_n** (cosets of a structured subset).
> (iii) **exactly ONE connection-difference orbit is critical** (n edges); all other orbits are
>      non-critical. Hence #critical edges = n > 0 always → **G is NEVER a witness.**

Verified: ALL 52 four-vc 6-regular circulants on n=11..22 have exactly 6 colorings of G−v and exactly
n critical edges (one orbit). Method: dual-checker (`checkers.py`) + explicit 3-coloring enumeration.
The result holds whether or not {1,2} ⊆ S (e.g. C₁₃(2,3,4) crit-orbit=d2; C₁₃(1,3,5) crit-orbit=d5).

Higher-degree circulants (8-reg |S|=4, 10-reg |S|=5): almost none are even 4-vertex-critical
(extra edges push χ>4 or break vertex-criticality); those that are still have ≥ n critical edges.
NO circulant witness for n ≤ 25 across degrees 6/8/10. [VERIFIED]

### 5.2 Why the rigidity ⟹ a critical orbit (proof sketch)  [PARTIAL — gallai Thm 2 + algebra]

Let c be the (essentially unique) 3-coloring of G−v₀, with color classes A,B,C ⊂ ℤ_n forming AP-blocks.
By gallai Theorem 2, the edge v₀w is **critical** ⟺ in SOME 3-coloring of G−v₀, N(v₀)∖{w} is
non-rainbow (uses ≤2 colors). Because the 3-coloring is UNIQUE up to permutation, there is essentially
only ONE coloring to test. N(v₀) = v₀ + (S ∪ −S) hits a fixed multiset of residues among {A,B,C}.
Removing the neighbor w = v₀ + s collapses N(v₀)∖{w} to ≤2 classes **iff** the difference s is the one
whose two antipodal copies {+s,−s} are the ones carrying the "third" color singly — i.e. exactly one
orbit s* has the property that dropping its representative leaves N(v₀)∖{w} bichromatic. That orbit is
critical; all others stay rainbow (3 colors) under the unique coloring, hence non-critical (Thm 2).

The rigidity (uniqueness of c) is what makes "for SOME coloring" collapse to "for THE coloring," which
pins the critical orbit to exactly one. This is the precise mechanism behind Steiner's circulant lean.
**To finish into a full theorem: prove (i) the uniqueness-up-to-permutation of the 3-coloring of G−v
for ANY 4-vc 6-regular circulant.** That is the remaining gap (see §5.3). [OPEN — the one hard step]

### 5.3 The remaining gap & honest status

- (iii)⟸(i): GIVEN uniqueness of the 3-coloring, the one-critical-orbit conclusion follows by the
  Thm-2 argument above (modulo making "exactly one orbit collapses" fully rigorous via the AP-block
  structure — strongly supported by data, all 52 cases).
- (i) itself — **the uniqueness of the 3-coloring of G−v for every 4-vc 6-regular circulant** — is
  verified for n≤22 but NOT yet proven in general. This is the crux. It is plausibly provable via the
  rigidity of 3-colorings of dense circulants (the differences in S force a unique residue-class
  partition), but I do not yet have an n-uniform proof. Pre-registered as the fatal-or-finishable step.

**HONEST VERDICT on the circulant sub-case:** strong computational evidence + a mechanism that
no circulant is a (4,1)-witness, matching Steiner's stated lean. A complete proof needs the uniqueness
lemma (5.3-i). This is a real partial result; it does NOT settle the full k=4 question.

## 6. Existence-side spec handed to forge (where a witness CAN live)  [DERIVED]

Since the impossibility direction has NO density/counting obstruction (§2,§3) and the circulant
(vertex-transitive) route is blocked by rigidity (§5), a witness — if it exists — must be:
- **δ ≥ 6** (gallai/Skottová–Steiner), sparsest case 6-regular, n ≥ 11, |E| ≥ 3n.
- **NOT a circulant / not "too vertex-transitive"**: it must have a NON-rigid 3-coloring structure on
  G−v, i.e. G−v must admit ≥2 essentially-different 3-colorings so that for every edge there exists
  SOME coloring making the relevant neighborhood rainbow (Thm 2 ⟹ non-critical). **The witness needs
  3-COLORING FLEXIBILITY of every vertex-deleted subgraph** — the exact opposite of circulant rigidity.
- **SHARP LOCAL WITNESS CRITERION** [VALIDATED — 0 mismatches on all 4-vc graphs n=4,6,7]:

  > G (4-vertex-critical) is a (4,1)-witness  ⟺  for EVERY vertex v and EVERY proper 3-coloring c
  > of G−v, each of the 3 colors appears **≥ 2 times** among the neighbors N(v).

  This is gallai's Theorem 3 in tight local form, and it IS the witness predicate (proven equivalent
  to "no critical edge" by the rainbow-forcing Theorem 2: edge uv critical ⟺ some 3-coloring of G−u
  leaves N(u)∖{v} with ≤2 colors ⟺ some color appears only once in N(u) and v is its unique carrier).

  WHY circulants fail it: the rigid (unique) 3-coloring of C₁₃(1,2,5)−0 gives N(0) the color multiset
  {color0:1, color1:4, color2:1} — two colors appear only ONCE, so the two ±1 edges are critical.
  Circulant rigidity CONCENTRATES one color and starves the others. A witness needs every color
  BALANCED (≥2) in every neighborhood across every 3-coloring of every G−v.

  **Existence-side spec for forge (corrected & sharp):** search 6-regular (or denser) 4-vertex-critical
  graphs where each vertex's neighborhood is "color-balanced" — every 3-coloring of G−v hits each color
  ≥2 times in N(v). This is a LOCAL, cheap per-vertex predicate (no global edge sweep needed): for each
  v, enumerate 3-colorings of G−v, check the N(v) color multiset has min-count ≥2. Use it to PRUNE
  candidates fast. The criterion is NOT "many colorings" (raw count is anti-correlated at small n) — it
  is "every coloring is color-balanced on every neighborhood." Handed to forge + hunter (search prune).
