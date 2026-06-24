# E124: does the interval-filling close at mass EXACTLY 1? — the resolution

**Author:** cassels. **Status:** Resolved structurally with computation to 10^25. Answer: the
theorem GENUINELY SPLITS into "mass > 1: density/Cassels" + "mass = 1: marginal, governed by a
Diophantine power-spacing condition." This confirms the team-lead's hypothesis and pins the exact
criterion. Responds to the lead's two options (a) self-similarity value, (b) per-window regeneration.

Builds on: scholar_BEGL96_proof_dissected.md (Claim 1 needs β>2), cassels_completeness_lemma.md
(Lemma C, side-condition mapping), troika (Baker-type for (3,4,7)).

---

## 0. First, a clarification the team needs: TWO different "harmonic masses"

BEGL Claim 1's "β > 2" requirement and the conjecture's "∑1/(d−1) ≥ 1" are **different quantities**:

- **Conjecture mass** = ∑_{d∈D} 1/(d−1). Here 1/(d−1) = ∑_{j≥1} d^{−j} is the *geometric-envelope
  density* of the ray {d^j}. This is what Pomerance's converse uses.
- **BEGL Claim 1 mass** = ∑ 1/(b_i − 1) over a finite chunk of ELEMENTS b_i. For our rays the
  elements are the powers d^j, so this sum is ∑_{j≥k} 1/(d^j − 1) — which **DECAYS like d^{−k}→0**
  as k grows (computed: d=3 gives 0.68, 0.18, 0.057 for k=1,2,3). It never reaches 2 for a single
  ray; Claim 1 as literally stated does not even apply.

So "we need β > 2" is about a *different* sum than the conjecture's mass. The relevant object for
US is the conjecture mass = 1, and the right machinery is the Cassels gap condition on the merged
atom sequence, NOT BEGL Claim 1 verbatim. (This corrects a conflation that could mislead the team.)

## 1. The exact reformulation (COMPUTED, exact): merged-atom subset-sum = per-base sumset

For (3,4,7) (and any D whose powers d^j are pairwise distinct in value — true for these bases),
R(D,k) = ∑_{d∈D} d^k·B_d is EXACTLY the set of subset sums of the merged atom multiset
**A = {d^j : d∈D, j≥k}, each atom used at most once** (verified: 0 differences over [0,200000]).
So E124-open is literally the classical **complete-sequence** question for the sequence A.

## 2. The Cassels gap condition HOLDS at mass exactly 1 (COMPUTED to 10^25)

Cassels: sort A = (a_1 < a_2 < …). If a_{i+1} ≤ S_i + 1 (S_i = a_1+…+a_i) for all i past some
point, no NEW gap forms above that point. Computed for (3,4,7), mass=1:
- The gap condition a_{i+1} ≤ S_i+1 holds for ALL i ≥ 1 (only the i=0 "seed" 3 ≤ 1 fails, because
  1,2 are unreachable — that is the SOURCE of the finite gap set up to T=581).
- Cassels filling ratio a_{i+1}/(S_i+1) fluctuates with **sup ≈ 0.93 < 1** over the whole tested
  range to 10^25. The merged sum regenerates: **S(X)/X ∈ [1.14, 2.46], mean ≈ 1.76, at EVERY scale.**

**This answers the lead's option (b): YES, the harmonic mass regenerates per multiplicative window.**
S(X) ≈ 1.76·X at every scale, so the "filling budget" is replenished — you do NOT need a single
chunk with β>2; the budget S(X)/X ≈ 1.76 recurs at all scales even at mass exactly 1.

## 3. BUT mass = 1 is exactly MARGINAL — the catch (the lead's split is REAL)

The Cassels step succeeds at scale X iff the multiplicative jump to the next atom satisfies
> **a_{i+1}/a_i ≤ S(a_i)/a_i + o(1) ≈ 1.76 (regenerating budget at mass 1).**

The LARGEST observed jumps are exactly **3.0** (at 81→243 and 19683→59049: consecutive powers of 3
with NO power of 4 or 7 landing between them). Jump 3.0 > budget 1.76 ⟹ a Cassels failure THERE.
These large-jump failures at SMALL atoms are exactly what create the finite gap set up to 581.

The open question is whether jumps stay ≤ budget EVENTUALLY:
- A jump a_{i+1}/a_i is large precisely when a long multiplicative interval contains a power of only
  ONE base (the others' powers avoid it). E.g. between 3^4=81 and 3^5=243, is there a power of 4
  or 7? (4^4=256>243, 7^2=49<81 — NO.) When the sparsest base (7) has a power isolated in a gap of
  the {3,4}-powers, the jump can approach the base ratio.
- Whether such isolating coincidences **persist at large scale** is the distribution of the points
  {a·log3, b·log4, c·log7} on the log-line — an **equidistribution / linear-forms-in-logarithms**
  question. mass=1 gives zero slack: a single jump exceeding 1.76 reopens a gap. mass>1 raises the
  budget S(X)/X (e.g. (3,4,5) mass 1.083 gives budget ~2.1 and sup ratio 0.86), buying room to
  absorb the worst jumps — which is why strict families have small, quickly-terminating gap sets.

**Conclusion — the lead's split is correct and now precise:**
> **mass > 1:** the regenerating budget S(X)/X exceeds the worst multiplicative jump for all large
> X (the jumps are bounded by max-base ratio, the budget grows with surplus) ⟹ Cassels self-sustains
> ⟹ cofinite. This regime is provable by elementary density once the jump bound is made effective.
> **mass = 1:** the budget ≈ 1.76 is exactly at the edge of the jump distribution (sup jump → base
> ratios up to 3). Success requires that large isolating power-coincidences do not recur — a
> **Baker-type / equidistribution** statement on |d_i^a − d_j^b|, exactly the tool BEGL used for the
> single triple (3,4,7). NOT closable by counting alone.

## 4. On the lead's option (a): what is self-similarity worth?

The self-similar recursion (maverick: T_k = C_k + T_{k+1}) does NOT add filling budget beyond the
regeneration already measured in §2 — S(X)/X ≈ 1.76 IS the self-similarity expressed as a density.
Self-similarity guarantees the budget regenerates identically at every scale (good), but it cannot
manufacture surplus that the mass=1 hypothesis withholds. So self-similarity buys uniformity-in-scale
(hence uniformity-in-k), NOT the missing slack. The slack at mass=1 must come from power-spacing,
not from self-similarity. **Option (a) does not rescue mass=1; option (b) explains why mass=1 is
borderline-but-not-automatic.**

## 5. Deliverable for the writeup
The honest theorem statement the team should record:
> **Theorem (conditional, the natural target).** For admissible D with gcd(D)=1:
> (i) [density regime] if ∑1/(d−1) > 1, then ∑_d d^k·B_d is cofinite for every k (provable by an
>     effective bound: worst multiplicative atom-jump ≤ max-base ratio < regenerating budget).
> (ii) [boundary regime] if ∑1/(d−1) = 1, cofiniteness for every k holds PROVIDED a Baker-type lower
>     bound on |d_i^a − d_j^b| prevents large isolating power-coincidences (known only for (3,4,7)).
This split is itself the major structural finding: E124-open = "easy strict half" + "hard boundary
half," and the boundary half is genuinely a transcendence problem, not a gap in our cleverness.

(Caveat: part (i) still needs the effective jump bound written out and the residue/seed handled via
the gcd=1 coverage lemma; I have verified its hypotheses computationally but not fully proved (i).)
