# E944 — Honest Residue of the Impossibility Direction (gallai)

Erdős #944 / Dirac 1970, sole open case k=4: **does a 4-vertex-critical graph exist with no critical
edge (every G−e still 4-chromatic)?** A "(4,1)-witness." This document is the consolidated, honest
residue of the impossibility attack: the proven structural theorems, the saturation map (every lever
tried + its exact death point), the irreducibility argument, and the empirical backbone. No witness
was found; no impossibility proof closed. The value is a sharp map of WHY, and a tight spec for the
witness if it exists.

Companion files: gallai_local_structure.md (theorems + proofs), gallai_assault_Estar.md (the E*≠∅
assault), INVENTIONS.md (gallai lane, 5 rounds), gallai_vertex_transitive.md, gallai_crit.py (tooling).
Definitions locked in archivist_definitions.md (IsCritical = VERTEX-critical).

---

## 1. PROVEN THEOREMS (the structural backbone)

All computationally verified on the complete 4-vertex-critical census (n≤8 exhaustive via geng; Thm 2
independently re-derived by skeptic to n≤9, 2303 edges, 0 mismatches). k=5 reality-checked throughout
against verified Jensen circulant (5,1)-witnesses.

- **Theorem 2 (rainbow-forcing certificate).** In a 4-vertex-critical G, edge uv is non-critical ⟺ in
  every proper 3-coloring of G−u, the neighbours N(u)∖{v} use all 3 colours. The exact LOCAL
  non-criticality test. [Independently confirmed by skeptic, from-scratch enumeration.]
- **Theorem 1 (low-vertex edge criticality).** deg(u)=3 ⟹ every incident edge is critical. (Special
  case of Thm 2: 2 neighbours can't be rainbow.)
- **Theorem 3 (witness min-degree ≥ 6).** Every (4,1)-witness has δ ≥ 6; generalizes to δ ≥ 2(k−1).
  Matches Skottová–Steiner 2025 Prop 5.1 at k=4 (elementary re-proof); STRONGER for k≥5. Validated:
  Jensen circulant G_{5,2,2} (N=17) has δ=8 = 2(5−1) exactly.
- **Theorem 4 (forced 2-2-2 rigidity).** At every degree-6 vertex of a witness, N(u) is colour-balanced
  2-2-2 in every proper 3-coloring of G−u. ("Every vertex is good/an absorber.")
- **Theorem 5 (family-intersection).** f critical ⟺ f in every spanning 4-chromatic subgraph; witness
  ⟺ ⋂_e E(H_e)=∅.
- **Theorem 6 (E* structure).** The critical-edge set E* is NONEMPTY and SPANNING for every
  4-vertex-critical graph n≤10 (skeptic dual-checker, 0 exceptions). "E* connected" REFUTED at n=10.

## 2. THE EXACT EQUIVALENT FORMS OF "E*≠∅ at k=4" (one statement, many languages)

All proven mutually equivalent (verified n≤8). A (4,1)-witness exists ⟺ each of these holds:
1. **Coloring/CSP form:** a 4-vertex-critical G where EVERY vertex is "good" (Thm 4): δ≥6 and every
   3-coloring of G−v balances N(v) with each colour class ≥2.
2. **Potts form (G-INV-3):** the q=3 Potts polynomial Z(G,t)=Σ_{3-col} t^{#mono edges} has a DOUBLE
   root at t=0 (B₀=B₁=0) for a vertex-critical G.
3. **Chromatic-polynomial form (G-INV-4):** Σ_e P(G−e,3) = 0 for a vertex-critical 4-chromatic G.
4. **Cocycle form (wall):** f(G)=min over ℤ₃-colorings of #mono edges ≥2, AND every vertex is an
   absorber (∃ 3-coloring with all conflicts co-located at it).
These are EXACT restatements (q=3-specific: all are realizable at q=4, where Jensen (5,1)-witnesses
exist). None is a reduction to anything easier — they relabel the same global object.

## 3. SATURATION MAP — every lever, with its exact death point

| Lever | Death point |
|---|---|
| Edge-count / KY density / potential method | VACUOUS: lower bounds; witness is dense (Thm 3: e≥3n; k≥5 witnesses e/n=4,5,6). No upper bound on e(G). = wall obstruction #1. |
| Kempe-chain pair-separation | Necessary but NEVER FIRES: criticality is single-neighbour color-isolation (Thm 2), not pair-separation. 0/8 n=8 graphs have a separable pair. |
| Local 2-2-2 rigidity (per-vertex) | SATISFIABLE per-coloring (k=5 achieves 2-2-2-2). Not a local obstruction. |
| H_e-family overlap (edge-count) | VACUOUS for dense witness (Gallai-forest count L_e≥4n−2e(H_e) goes negative). |
| ℤ₃ Fourier / character sum over colorings | CANCELS generically (|S|=0 on most graphs). |
| Tutte / Whitney at q=3 | Same object as Potts (G-INV-3). |
| Chromatic-root MULTIPLICITY at x=3 (G-INV-8) | Does NOT track B₁: 90/282 mismatches n=7; multiplicities 1,2,3 all occur for B₁>0. |
| Zero-free region / root structure NEAR x=3 (Route 5) | **STRONGEST kill:** B₁ is provably NOT a function of P(G,x) — chromatically-equivalent graphs (same P) have different B₁ (F?bnw=108, F?qnw=96). No analytic functional of the single polynomial P(G,x) can bound B₁. Also: simple root (P′(3)≠0) coexists with B₁=0 (FQyvw). archivist confirmed no joint-family zero-free result exists in the literature. |
| Absorber-set size bound (cocycle, R5) | Absorber threshold = deg≥6 = Theorem 4. CIRCULAR. |
| Rep-theory / Aut-module trivial-rep multiplicity | cnt(v₀) vanishing IS the witness condition; Burnside counts not bounds it. CIRCULAR; doesn't distinguish q=3/q=4. |
| Cocycle-RANK on ℤ₃ cut space (wall, the last non-circular handle) | DOES NOT REALIZE. (a) v absorbs ⟺ G−v cut space (dim n−2) has a NOWHERE-ZERO vector = 3-colorability (NP-hard), NOT a rank property — a rank bound cannot see it. (b) Absorber-independence cap FALSE: absorbers are never independent (16/16 n=8, 53/53 n=9 have adjacent absorbers), so no α(G) cap. |

## 4. THE IRREDUCIBILITY CLAIM (the honest core result)

**E*≠∅ at k=4 is equivalent to the global "every vertex good" 3-coloring CSP (Theorem 4), and is
provably NOT reducible to:** (a) any edge-count/density bound [vacuous against a dense witness],
(b) any Kempe-swap certificate [wrong mechanism, k=5-satisfiable], (c) any of the equivalent algebraic
restatements (Potts/cocycle/absorber) [they relabel, not reduce], or (d) any analytic functional of
the single chromatic polynomial P(G,x) [B₁ provably not a function of P(G,x)]. Every reduction we
constructed collapses back to "every vertex good." The k=4-vs-k=5 distinction (3 vs 4 colours) lives
ENTIRELY inside the global CSP — no local, counting, potential, Kempe, symmetry, or single-polynomial-
analytic certificate sees it. This is the precise sense in which the problem resists, and it is the
publishable residue: a map of the obstruction's irreducibility.

## 5. EMPIRICAL BACKBONE

- Complete census 4-vertex-critical graphs: n=4:1, n=5:0, n=6:1, n=7:7, n=8:8 — 0 witnesses; min
  critical edges 6/–/10/7/7. Extended (skeptic) to n≤10, 0 witnesses; E* nonempty+spanning throughout.
- Vertex-critical CIRCULANTS: 137 at n≤24, 0 witnesses, each ≥7 critical edges in exactly one distance-
  orbit. (count's 610 circulants + non-abelian Cayley + skeptic n=31 concur.)
- forge exhaustive (geng -d4 + exact χ + per-edge critical check): the localized impossibility
  "χ=4 ∧ |E*|=0 ⟹ NOT vertex-critical (has a removable vertex)" holds with ZERO exceptions over
  n=8:130, n=9:5,681, n=10:550,059 graphs (~556K total). Near-certain k=4 theorem.
- forge K₄-ROUTE DEAD (saved dead-end): there exist K₄-free (ω=3) |E*|=0 χ=4 graphs (e.g. GQyurg,
  n=8, 4-regular, every vertex removable). So 4-chromaticity is NOT clique-anchored — a clique-based
  impossibility proof is impossible. CONFIRMS the irreducibility claim: the proof must be
  COLORING-STRUCTURAL (the Potts/B₁/cocycle frame), not combinatorial-clique. Reinforces §4.
- Necessary witness profile (proven): δ≥6, edge-connectivity ≥6, Δ≤n−5, n≥11, sparsest = 6-regular
  (Skottová–Steiner Problem 5.2). Hand to hunter/forge as the live search target.

## 5b. ABSORBER ANTI-CORRELATION (joint with wall, structural data)
The two witness conditions are ANTI-CORRELATED: f(G)≥2 (the edge condition, = no near-3-coloring with
≤1 conflict) SUPPRESSES the absorber count (= vertex-critical vertices). Exhaustive data:
- Sparse (all 4-chromatic f≥2): max absorber-fraction n=7→1/7, n=8→3/8, n=9→3/9. 0 all-absorber.
- DENSE (δ≥5, f≥2): max absorber-fraction n=8→1/8, n=9→2/9, n=10→2/10 (wall, 30,288 graphs). 0 all-absorber.
  Density SUPPRESSES absorbers MORE (the witness regime is more hostile to all-absorber, not less).
ABSORBER-SET STRUCTURE (n=8 d4 f≥2, 130 graphs): absorber-set sizes {0:88, 1:41, 2:1} — MAX 2
absorbers, and the lone 2-absorber case has them ADJACENT (clique). Suggests absorbers form a small
(clique-like) bounded set when f≥2 at k=4 — but sample is small (1 multi-absorber graph), suggestive
not conclusive. k=5 reality check: the k=5 witness has ALL n absorbers (circulant, not a clique), so
any "absorbers bounded/clique" bound is necessarily k=4-specific (must fail at k=5, and does). The
open proof target (wall+algebra): bound #absorbers < n for f≥2 in the dense regime — large margin
(~0.8n gap) means a loose argument suffices. 
A witness needs f≥2 AND all-absorber simultaneously — empirically these pull apart. Triangle structure:
absorbers are the degree-6/7, triangle-RICH vertices (avg 10.16 edges in N(v) vs 5.25 for non-absorbers).
HONEST: no contradiction extracted — absorbers want dense triangle-rich neighborhoods, which a dense
witness (Thm 3 δ≥6) can supply; the anti-correlation is favorable EMPIRICAL evidence (n≤9), not a proof.
The witness regime δ≥6/n≥11 is beyond exhaustive reach. (wall pushing the cocycle-RANK version, which
is the one quantity not yet reduced to Theorem 4.)

## 6. WITNESS SPEC (if it exists) + REMAINING OPEN LEVERS

A witness is: dense (δ≥6, e≥3n), ASYMMETRIC (vertex-transitive is k=4-specifically forbidden
empirically — Jensen circulants ARE k=5 witnesses, so symmetry helps at k≥5 but the k=4 symmetric space
is empty through n≤24), with every vertex-deleted 3-coloring balancing every neighbourhood 2-2-2, and
NO local/counting/symmetry/single-polynomial structure to enforce it.

OPEN levers not killed (need tools outside this team's reach): (i) a JOINT zero-free region across the
edge-deleted family {P(G−e,x)} (single-polynomial version dead; joint version has no literature but
isn't ruled out); (ii) a ℤ₃ cocycle-RANK / cohomology-dimension bound on the absorber set (wall's lane,
distinct from the good-vertex count); (iii) the vertex-transitive theorem via rep-theory was tried and
died — but a non-character-theoretic symmetry argument is not formally excluded.

## 5c. CALIBRATION on the absorber-bound (anti-overclaim, IMPORTANT)
The n≤9 data shows absorbers bounded ≤2 (clique-structured) when f≥2 — but this is very likely a
SMALL-n ARTIFACT, not a near-provable theorem. A clean bound "f≥2 ⟹ #absorbers ≤ ω (or ≤ const)"
would prove no witness for ALL n≥5, i.e. resolve Dirac k=4 (60-year open) — too strong to be a real
provable bound at that strength. Evidence it's an artifact: absorbers DO exceed ω freely when f=1
(Hajós(K4,K4): n=7, f=1, 7 absorbers, ω=3); the f≥2 case looks bounded at n≤9 only because f≥2 graphs
are rare and small there. The true max-absorber count for f≥2 surely GROWS with n, invisibly below the
n≥11 witness regime. CONCLUSION: treat the bounded-absorber observation as suggestive of the
anti-correlation DIRECTION (f≥2 suppresses absorbers), NOT as a near-proof. The honest open quantity is
the asymptotic growth of max-absorbers(f≥2, n), which exhaustive small-n cannot determine. This keeps
the residue map honest: the absorber lever, like all others, does not escape the global CSP — its
small-n bound is an artifact, and the real behavior at the witness scale is unknown.

## 6b. FAMILY COMMON-ROOT reformulation (forge) — clean LANGUAGE, collapses to B₁ (closes the joint-family lever)
forge's family portrait: e critical ⟺ x=q is NOT a root of P(G−e,x); so **|E*|=0 ⟺ x=q is a COMMON
ROOT of the entire deleted-edge family {P(G−e,x) : e∈E}**. Clean, q=3-specific, passes the k=5 tripwire
(G_{5,2,2} HAS x=4 as a common family root AND is vertex-critical). This is the family form of the
joint-zero-free lever archivist had left conditionally-open.
VERDICT (closes it): at x=3 the family question COLLAPSES to the single number B₁. Since each
P(G−e,3) ≥ 0 (counts proper 3-colorings of G−e), the common root ⟺ Σ_e P(G−e,3)=B₁=0 — the SUM
vanishes iff each term does. So the family adds NO joint analytic structure at x=3 beyond B₁. And the
NEAR-x=3 family roots don't help either: each member is MONIC, so P(G−e,3)=∏_{ALL roots r}(3−r) —
far roots matter as much as near ones, so second-nearest-roots of family members do NOT bound B₁. The
family lever inherits the EXACT disconnect of the single-polynomial Route 5 kill. Both analytic versions
(single + joint-family) are now closed. forge's reformulation is valuable LANGUAGE, not new traction.

## 7. FINAL STATUS — impossibility framework exhausted (gallai + wall, joint verdict)

With the cocycle-rank lever now ruled out (wall §12), the impossibility framework is honestly exhausted
of provable leverage. EVERY handle on "E*≠∅ at k=4" has been mapped to its death point:
- counting → Theorem 4 (circular);
- density / potential → no obstruction (witness is dense);
- Kempe → wrong mechanism, k=5-satisfiable;
- single-polynomial analytic (zero-free/root) → B₁ not a function of P(G,x);
- rep-theory → multiplicity vanishing IS the witness condition (Burnside counts, not bounds);
- cocycle-RANK → the rank-expressible part (cut-space dimension) doesn't see the nowhere-zero /
  3-colorability condition (NP-hard) where the difficulty lives; absorber-independence cap is FALSE.

The f-cocycle / Potts framework is the best LANGUAGE for the obstruction (single integer, q=3-specific,
density-dodging, passes the k=5 check, correctly localizes via the absorber characterization) — but
every quantitative handle collapses to "is E*≠∅?" = Dirac k=4 itself.

WHAT THE JOINT EFFORT ACCOMPLISHED (real, even without the proof):
1. The cleanest known reformulation: witness ⟺ f(G)≥2 ∧ vertex-critical ⟺ q=3 Potts double-root at
   t=0 ⟺ Σ_e P(G−e,3)=0 ⟺ "every vertex is an absorber/good."
2. Proven structural backbone: δ≥6, the rainbow-forcing certificate, the family-intersection
   characterization, E* nonempty+spanning, all k=5-reality-checked.
3. Exhaustively-verified absorber-suppression in the dense regime (~0.2 fraction, 0 witnesses over
   30k+ δ≥5 f≥2 graphs at n≤10; ~556K graphs total via forge).
4. A sharp characterization of WHY the problem is k=4-specific (q=3 = 3 colours; every reduction is
   realizable at q=4, where the Jensen circulant (5,1)-witnesses live).
5. The irreducibility map itself: a rigorous account of why no local/counting/potential/Kempe/symmetry/
   single-polynomial-analytic/rank certificate can resolve it — the obstruction is the irreducibly
   global 3-coloring CSP, and that is the publishable honest residue of the impossibility direction.

The live frontier is the EXISTENCE search (hunter/proximity, dense asymmetric n≥11, 6-regular target),
not impossibility. Impossibility direction: DONE.

## 8. THE DENSITY/SPECIFICITY TRAP (meta-obstruction, unifies the saturation map)

Re-arm round (Alon–Tarsi/CN lever, gallai_alon_tarsi.md) yielded the deepest characterization of WHY
E944 resists every toolkit — a single meta-obstruction that explains the whole saturation map:

**The witness sits in a sweet spot between two unavoidable failure modes:**
1. **Sparsity tools fail by the degree/density wall.** Tools that certify 3-colorability or criticality
   from a bounded/sparse structure — Kostochka–Yancey density, the potential method, chromatic-poly
   zero-free regions, and now Alon–Tarsi/Combinatorial-Nullstellensatz (graph polynomial homogeneous of
   degree m needs m ≤ 2n) — all require the object to be SPARSE. But a witness has m ≥ 3n > 2n
   (Theorem 3, δ≥6). They are blinded.
2. **Density tools fail by k-uniformity.** Tools that exploit density — Turán/supersaturation,
   degeneracy, "dense ⟹ has a forbidden config" — are k-BLIND: the k=5 Jensen witnesses are even DENSER
   (e/n = 4,5,6) yet exist. So no density-only argument can be q=3-specific, and any valid impossibility
   proof MUST be q=3-specific (it must fail at k=5).

**Consequence:** an impossibility proof for k=4 requires a tool that is simultaneously DENSITY-ROBUST
(works at m ≥ 3n) AND q=3-SPECIFIC (uses 3 colours, fails at q=4). Every tool the squad has — across
chromatic-polynomial, cocycle/topological, graph-polynomial/algebraic, counting, Kempe, spectral,
symmetry — is either a sparsity tool (dies at the density wall) or a density tool (dies at k-uniformity)
or a restatement (dies at Theorem 4). NONE is both density-robust and q=3-specific. That conjunction is
the precise, toolkit-independent reason the problem is open, and it is the publishable core of the
impossibility residue: not "we couldn't find a proof," but "the proof must thread a needle no existing
technique threads — density-robust + q=3-specific simultaneously."

### 8a. Re-arm round confirmations (toolkit-independence of the trap)
The fresh-toolkit round tested two more toolkits against the density/specificity trap; both confirm it:
- **Alon–Tarsi / Combinatorial Nullstellensatz** (gallai_alon_tarsi.md): the graph polynomial's
  signed-orientation-parity NOVELTY lives in bounded-degree monomials (≤2n) that vanish for a dense
  witness (m≥3n); the density-robust part (Tarsi count identities) IS the banned B₁/Theorem-4 count.
  Novelty and density-robustness are MUTUALLY EXCLUSIVE in this framework — the trap, exactly. (Related
  prior art: "k-Alon–Tarsi-critical graphs," EJC 23(3) #P3.37 — does not change the verdict.)
- **Topological / Hom(K₂,G) neighborhood complexes** (wall's lane): DOUBLE mismatch — (1) WRONG TARGET:
  gives χ LOWER bounds (χ≥4 = the hypothesis), says nothing about edge-CRITICALITY (the complex barely
  changes under single-edge deletion); (2) k-MONOTONE: more-connected complexes at higher χ, so it
  "proves" χ≥5 for k=5 witnesses too — fails the k=5 check structurally. Topology is a chromatic-
  lower-bound theory; we need a criticality-forbidding, q=3-specific theory — orthogonal requirements.

**Unified verdict:** across ~10 toolkits now (counting, density/KY/potential, Kempe, chromatic-poly
analytic single+family, cocycle/absorber, rep-theory, Alon–Tarsi/CN, topological, spectral-pending),
EVERY one is exactly one of: a restatement (→ Theorem 4), a sparsity tool (→ density wall, m≥3n), a
density tool (→ k-monotone, k=5 witnesses denser), or wrong-target (→ bounds χ not criticality). The
needle a proof must thread — DENSITY-ROBUST ∧ q=3-SPECIFIC ∧ criticality-targeting — is threaded by
none of them. That conjunction is the toolkit-independent, publishable core of the impossibility residue.
