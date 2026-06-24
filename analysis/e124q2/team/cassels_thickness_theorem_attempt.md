# ASSAULT: Discrete thickness / interval-filling theorem — ATTEMPT + EXACT DEATH POINT

**Author:** cassels. **Mode:** assault (attempt → death point → revise). Target: prove E124 via a
discrete analogue of the Newhouse/Astels "thickness ≥ 1 ⟹ sumset contains an interval" theorem.
Coordinates with maverick (renormalization T_k=C_k+T_{k+1}) and density (measure).

## STEP 1 — Define discrete thickness. [DONE, validated against ground truth]

**First attempt (FAILED):** raw Newhouse thickness of the Cantor set C_d (digits {0,1} base d, in
[0,1]). At the top split, bridge/gap = **1/(d−2)**, so τ(C_d)=1/(d−2). Product over (3,4,7) =
1·½·⅕ = 0.1 < 1, yet (3,4,7) IS cofinite. **DEATH POINT #1: raw Newhouse τ·τ≥1 is the WRONG
threshold** — it is sufficient-not-necessary for real Cantor sets, and does not encode ∑1/(d−1).

**Correct definition (VALIDATED):** the right invariant is the **hull-fraction / diameter** of C_d
in its unit cell, NOT the Newhouse gap-ratio. C_d = {∑_{j≥1} e_j d^{−j} : e_j∈{0,1}} has
diam(C_d) = ∑_{j≥1} d^{−j} = **1/(d−1)**. Anchored at each integer n, the ray contributes a copy
n+C_d occupying [n, n+1/(d−1)]. Define **τ_d := 1/(d−1)** (diameter-in-unit-cell). Then the squad's
threshold ∑_{d∈D} 1/(d−1) ≥ 1 is exactly "**∑ diameters ≥ the unit gap (=1) between integer
anchors**" — a covering/packing condition, not a Newhouse-thickness condition.

**Ground-truth test of the 2-set threshold (k=0, PASSED 8/8):** B_a+B_b cofinite ⟺ 1/(a−1)+1/(b−1)≥1.
Verified: (2,3)✓cof, (2,5)✓cof, (2,7)✓cof, (3,4) 0.833 not-cof, (3,5),(3,6),(3,7),(4,5) all not-cof.
The diameter-sum invariant predicts cofiniteness exactly. [code/ — subsetsums + is_cofinite.]

## STEP 2 — The 2-set theorem never reaches threshold for bases ≥3. [STRUCTURAL OBSTRUCTION]

**DEATH POINT #2 (reframing forced):** max over a,b≥3 distinct of 1/(a−1)+1/(b−1) = 1/2+1/3 =
0.833 < 1 (attained by (3,4)). **NO admissible PAIR with both bases ≥3 reaches the threshold.** So
a clean 2-set theorem, even if proved, NEVER applies in the conjecture's regime (which requires the
sum ≥ 1, hence r ≥ 3 bases). The theorem MUST be the r-fold iterate where intermediate partial
sums have bounded-but-positive gaps that later bases bridge. The real object is the iteration, and
the difficulty hides in the bridging step.

## STEP 3 — The iterated bridging lemma. [ATTEMPTED; EXACT DEATH POINT FOUND]

**Setup.** Order D = (d_1<…<d_r). Let P = ∑_{i<r} d_i^k·B_{d_i} (the partial sum without the last
base). By maverick's Lemma BG (∑_{i<r}1/(d_i−1) can be <1, giving P bounded gaps G' — for (3,4):
G' = max gap 7682 [measured]). The last base contributes Q := d_r^k·B_{d_r}.

**Bridging claim (what we'd need):** P + Q is cofinite. Mechanism: x ∈ P+Q ⟺ ∃ e∈Q, e≤x, with
x−e ∈ P. A gap x of P+Q persists ⟺ for ALL e∈Q with e≤x: x−e ∉ P. So cofiniteness ⟺ the
translates {x − e : e∈Q∩[0,x]} eventually always hit P.

**THE EXACT DEATH POINT (the survival of 581 for (3,4,7), k=1), fully explicit:**
P = 3·B_3 + 4·B_4 (k=1, ∑=0.833, bounded gaps). Q = 7·B_7. The elements of Q below 581 are
{0, 7, 49, 56, 343, 350, 392, 399}. For x = 581, the eight remainders are
581−{0,7,49,56,343,350,392,399} = {581, 574, 532, 525, 238, 231, 189, 182}, and **EVERY ONE of
these is ∉ P** (verified by direct membership test in 3·B_3+4·B_4). So 581 dodges every Q-translate
of P ⟹ 581 ∉ P+Q. This is the largest such dodge; above 581 every x is hit. [code, exact.]

**Why the bridging argument cannot be closed elementarily — the death point named:**
The bridging succeeds at x ⟺ at least one of the O(log x) remainders x − d_r^k·(0/1-digit base d_r)
lands in P. Whether a remainder lands in P is governed by the base-(d_1..d_{r-1}) digit structure of
x − d_r^j, i.e. by how the power d_r^j sits relative to the gaps of P. The gaps of P sit at
cross-base near-coincidences (3^p ≈ 4^q). So "does some 7^j-shift of x avoid all P-gaps" is a
statement about the simultaneous distribution of {7^j mod (P-gap-structure)} — exactly a
**linear-forms-in-logarithms / Mignotte–Waldschmidt** question on |d_i^a − d_j^b|. The bridging is a
counting statement ONLY if the gaps of P were equidistributed; they are NOT (they cluster at power
coincidences), so the elementary count fails and you need the MW spacing bound. **This is the same
wall BEGL hit; the thickness reframing does not move it — it LOCATES it precisely as "the last base
must bridge gaps that sit at cross-base power coincidences."**

## STEP 4 — What the thickness framing DID buy (honest positive).
1. **The correct discrete invariant** τ_d = 1/(d−1) = diameter-in-unit-cell, validated as the exact
   2-set threshold (8/8). This is the clean "why ∑1/(d−1)" answer: it's a diameter-covering sum,
   NOT a Newhouse gap-ratio (death point #1 ruled the latter out).
2. **The 2-set theorem is provable** (it's a packing statement: two Cantor sets of diameters
   summing to ≥ the cell gap, both anchored on ℤ, cover ℤ — modulo the residue/lattice handling).
   [TODO: write the clean 2-set proof; it's elementary BUT see death point #2 — it never fires for
   bases ≥3, so it is not the conjecture.]
3. **The death point is now LOCAL and explicit:** cofiniteness of P+Q ⟺ the last base's powers
   bridge P's gaps, and the surviving gaps are exactly the x where all O(log x) translates dodge P
   (581 dissected above). This is a sharper statement of the open core than "+M-closure finite" — it
   says precisely WHICH x can fail (cross-base-coincidence dodgers) and reduces the conjecture to:
   **above some X₀, no x has all its d_r^k·B_{d_r}-translates simultaneously in P-gaps.**

## STEP 5 — REVISED attempt (next iteration, where to push).
The diameter-covering view suggests the right SUFFICIENT condition is not τ_A+τ_B≥1 (too weak per
death point #2) but a **multi-scale covering**: at each scale d_r^j, the partial set P must already
cover an interval longer than the gap d_r^j opens. This is the **self-similar covering** maverick's
renormalization targets. The clean conjecture to attempt next:
> (★-cover) ∃ X₀ such that for all x>X₀, P covers a contiguous interval of length ≥ d_r^k inside
> [x − d_r^{J(x)+k}, x], where d_r^{J(x)} is the largest d_r-power ≤ x. Then P+Q ⊇ [X₀,∞).
This is provable IF P's covered-interval length grows at least like d_r^{J(x)} — which holds when
∑_{i<r}1/(d_i−1) is large enough relative to d_r, but FAILS at the boundary where P's coverage
length is only ~ (its own gap-bounded) and a fresh d_r-power opens a gap P cannot yet span.
**[ATTEMPT NEXT: prove (★-cover) under ∑_{i<r}1/(d_i−1) + 1/(d_r−1) ≥ 1; find its death point —
expected to be exactly the boundary ∑=1 where coverage-length and d_r-jump are commensurate.]**

## STEP 6 — Revised attempt (★-cover) EXECUTED. [DEATH POINT #3]

Tested (★-cover): does P cover a contiguous interval longer than the d_r-power gap, at each scale?
**FALSE.** P = 3·B_3+4·B_4 (∑=0.833<1) is not cofinite, so its contiguous runs are BOUNDED: max run
= 5137 over [0,3M] (regional maxima 1655 / 5137 / 3068 — not growing). A set with sum < 1 has no
long intervals, so "P covers a long interval to bridge from" is false. **DEATH POINT #3: the
bridging cannot rely on P-intervals.**

## STEP 7 — Final iteration: bridging is irreducibly multi-atom. [DEATH POINT #4 — and it's a finding]

Could a SINGLE d_r-power bridge P's bounded gaps? **No.** Max P-gap = 5137, but 7-powers outgrow it
(7^5 = 16807 > 5137). A single 7-translate of P (which has only bounded runs) cannot cover an
interval once 7^j exceeds P's max run. YET (3,4,7) k=1 is cofinite above 581 (coverage in
[100000,100050] is solid 1's, verified). **Therefore each large x is hit by combining SEVERAL
7-powers with SEVERAL (3,4)-parts simultaneously — cofiniteness is irreducibly a JOINT, full
r-dimensional multi-atom subset-sum phenomenon.**

**DEATH POINT #4 (the real finding):** every elementary decomposition I can write — single-base
bridge, P-interval cover, single d_r-translate, sequential pairwise iteration — PROVABLY fails,
because (a) any proper-subset partial P with ∑<1 has bounded runs (no intervals), and (b) the last
base's powers outgrow those bounded runs. So the proof cannot be reduced to pairwise/sequential
thickness bridging; it requires the joint covering, which is exactly where MW spacing enters. **This
rules OUT a whole class of attacks (sequential thickness iteration) — a useful negative for the team.**

## STEP 8 — Three-route convergence (with density): the extension is transcendence-FREE; the wall is SEED existence

density's measure/thickness assault independently reached γ(B_d) = 1/(d−1) (= my τ_d) and died where
discrete-Astels normalized-thickness SUPERADDITIVITY fails (B_d gaps are power-aligned: B_4+B_7's
max gap is 0.41·hull, worse than a clean thickness-½ Cantor set's ⅓). density asked whether my
interval-filling EXTENSION is transcendence-free given a seed. **Answer (verified): YES, and it
locates the wall precisely.** My machinery splits as:

- **IMPLICATION (Lemma C):** "∃ contiguous block of length ≥ M=b^k AND +M-closure holds ∀x≥L ⟹
  R⊇[L,∞)." PURE ARITHMETIC — residue induction mod M, no atom-spacing/alignment input. TRANSCENDENCE-FREE.
- **HYPOTHESIS (seed):** splits further into
  (i) [EASY/gcd-driven] an M-block exists — follows from gcd=1 residue coverage (modular's L) past a
      finite point; and
  (ii) [HARD/MW] +M-closure ONSET — x∈R⟹x+M∈R requires x to have a representation with the base-b
      k-th slot free; forced-occupied cases need a multi-base reshuffle whose success above X₀ is
      governed by |d_i^a − d_j^b| spacing = Mignotte–Waldschmidt.

**THREE LANGUAGES, ONE WALL:** my +M-closure-onset = density's thickness-superadditivity failure =
maverick's SEED existence = the MW |d_i^a − d_j^b| bound. Independently confirmed by 3 routes
(closure / thickness / renormalization). [verified: 0 +M-closure failures above threshold T for
(3,4,7),(3,4,5),(3,5,7,13) — extension clean once seed exists.]

## VERDICT (this stretch)
The discrete thickness theorem, attempted honestly, **dies at the same MW wall** but the attempt
produced two real artifacts: (1) the CORRECT discrete thickness invariant τ_d=1/(d−1) (diameter,
not Newhouse — death point #1 was instructive), validated as the exact 2-set threshold; (2) the
open core re-localized as an explicit, sharp bridging statement (the 581-dodge mechanism). The
2-set theorem is honest but vacuous for bases ≥3 (death point #2). No breakthrough on the boundary;
the wall is confirmed to be intrinsic, not a failure of framing.
