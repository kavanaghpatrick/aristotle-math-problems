# E124 strict-excess theorem — ASSAULT writeup (sumset, with carry)

**Goal:** ∑1/(d−1) ≥ 1+δ, gcd(D)=1 ⟹ T_k(D)=∑_{d∈D}d^k·B_d cofinite ∀k, elementary.
**Status: NOT closed — and the assault concludes NO elementary (MW-free) proof exists, even for
strict excess. Durable outputs: Lemma M (subset-monotonicity, new) + a sharp diagnosis that the
obstruction is INTERNAL gaps (top-gaps are automatically absent), so δ/density is not a shortcut.
An earlier "Theorem E" (single-block Cassels) is RETRACTED as vacuous (see Part II).**

Notation: b=min(D); atoms A={d^j:d∈D,j≥k}; B_d=0/1-digit base-d numbers; T_k=∑d^k·B_d; S_i=∑_{j≤i}t_j
for the sorted atoms t_1≤t_2≤….

---

## Part I — NEW elementary lemma (this is the genuine contribution of the assault)

### Lemma M (subset-monotonicity). [PROVED, trivial, but load-bearing]
For any D''⊆D and any k: **T_k(D'') ⊆ T_k(D)**, because dropping a base d means forcing a_d=0, and
0∈d^k·B_d (empty Finset). Hence:
> **T_k(D) is cofinite if SOME subset D''⊆D has T_k(D'') cofinite.**

This is new framing: prove cofiniteness of D by exhibiting ONE cofinite sub-family, NO need to control
the extra bases. (carry's two-phase route attacked D as a whole; Lemma M says we only need a good
sub-part.)

### The EXACT reach of Lemma M (carry's characterization, independently verified). [VERIFIED]
A cofinite subset D'' must itself be ADMISSIBLE (∑_{D''}1/(d−1)≥1 AND gcd(D'')=1 — Pomerance + gcd
necessity). So Lemma M only reduces D to a PROPER ADMISSIBLE subset, which often DOESN'T EXIST.
Enumerating all 115 strict-excess admissible D (d=3..11, r=3..5): **72 are NON-MINIMAL** (have a
proper admissible subset) → Lemma M reduces them; **43 are MINIMAL** (no proper admissible subset) →
Lemma M gives NOTHING. The split is EXACTLY easy-vs-hard (I independently re-verified both the
counts 43/72 and the dichotomy):
- NON-MINIMAL: max k=1 threshold = **74** (at (3,4,5,11)) — the EASY families.
- MINIMAL: max k=1 threshold = **986** (at (3,4,6)) — and ALL the {3,4}-clustering hard cases
  ((3,4,5), (3,4,6), (3,4,8,9), …; 8 of the 43 contain {3,4}) are minimal.

So Lemma M peels off exactly the easy (non-minimal) families and leaves the hard core — the 43
minimal D — UNTOUCHED. **Its value: it converts the vague "hard families" into a precise, finite,
enumerable combinatorial class (minimal = no proper admissible subset).** The minimal D still need a
direct argument (= the internal-gap/MW core; Parts II–III show no elementary one exists). Clean
theorem STRUCTURE (with carry):
> strict-excess theorem = [Lemma M: non-minimal D reduce to a dense admissible subset — trivial]
>                        + [minimal D: internal-gap problem, MW/Baker — OPEN].

### Lemma 1–3 (reduction scaffold — all previously proven by the team, re-used)
1. Cassels (cassels' Lemma C): b^k consecutive run + eventual +b^k-closure ⟹ cofinite.
2. Bounded gaps (maverick Lemma BG): ∑1/(d−1)≥1 ⟹ max gap ≤ Θ(b^k) after finite transient. Elementary.
3. Residue coverage (modular Lemma L): gcd=1 ⟹ all residues mod b^k hit. Elementary.

---

## Part II — What elementary route was attempted and where it died (NO Theorem E — retracted)

I attempted "Theorem E": if the sorted atoms satisfy a single-contiguous-block extension condition
(BLOCK) t_{i+1} ≤ block-length, then cofinite by classical block-Cassels. **RETRACTED — (BLOCK) is
VACUOUS:** rigorously verifying it (growing the block from a verified seed, atoms in order) STALLS for
EVERY admissible family, including the dense ones ({4,…,10}, {3,…,10}, {5,…,14}) — the stall is at
the first power-of-d_min-ish atom because single-block growth (×2 per absorb) cannot keep up with the
geometric atom ladder (ratio = base ≥ 3 > 2). This is maverick's ratio>2 stall, and it is fatal to
the single-block route. **The dense families ARE cofinite (threshold 3, verified) but via MULTI-atom
subset sums — the same (SEED) mechanism, not single-block Cassels.** So there is no elementary
single-block BASE CASE to feed Lemma M.

One genuinely clean elementary sub-fact (LOW range only, does NOT extend to powers): consecutive
bases {m,…,2m} have subset sums covering [m, Σ−m] contiguously (classical complete-from-bottom). This
handles small n but the interlocking of higher POWERS is again the multi-atom (SEED) problem.

---

## Part III — THE DEATH POINT (why strict excess / density does NOT close it)

The clean hope "∑≥1+δ ⟹ T_k cofinite elementarily" has no elementary proof, for a now-precisely-
located reason:

1. **Brown's criterion is only a TOP-gap condition.** The sorted atoms satisfy t_{i+1}≤1+S_i with
   ZERO violations to 10^12 even for the boundary (3,4,7). If that sufficed, (3,4,7) would be
   elementarily complete — contradicting its known MW-hardness. It does NOT suffice: t_{i+1}≤1+S_i
   forbids only gaps ABOVE the running sum S_i; the real obstruction is INTERNAL gaps (e.g. 581 for
   (3,4,7), which sits below S=1102). Internal gaps are exactly what (BLOCK) — the strictly stronger
   block-length condition — controls, and (BLOCK) FAILS whenever d_min=3 lacks enough in-between
   atoms (the 3→9→27 ratio-3 stall, maverick).

2. **Strict excess δ does NOT imply (BLOCK).** A strict-excess D can still have its harmonic mass
   concentrated so that some scale is under-populated (e.g. (3,4,6), δ=0.033, threshold 242,113 at
   k=2; (3,4,5), δ=0.083, threshold 77,613). For these the internal gaps persist far out and their
   finiteness is governed by 3^p≈4^q spacing — the Mignotte–Waldschmidt regime. δ only helps when it
   buys (BLOCK)-density; small δ on a clustered base set does not.

3. **The reduction to (RF) inherits the same wall.** Trying to fill internal gaps via "T'_k covers
   every residue mod b^k in a window of length b^k" (the (RF) lemma) requires T'_k=T_k(D∖{b}) to be
   dense — but T'_k may be sub-critical (∑'<1) and its own coverage windows blow up (same distant-gap
   phenomenon; e.g. T'=(4,5,6,7) shows no gap to 8·10^7 yet ∑'=0.95<1, a finite-range illusion).

**Net: the elementary core is exactly (BLOCK)/density, not δ.** The strict-excess theorem is TRUE
(every admissible family computes cofinite; answer almost certainly True) but its elementary
provability is gated by whether D supplies a (BLOCK)-dense subset. δ large enough to force a
consecutive-run subset with ∑≥1 DOES close it (Theorem E + Lemma M); δ small on a clustered set does
NOT, and there the gap-finiteness is genuinely the MW/Baker problem BEGL96 left open.

---

## Deliverables (rigorous, Lean-reachable)
- **Lemma M** (subset-monotonicity, T_k(D)⊇T_k(D'')): one line, new framing, removes the "control all
  bases" burden — reduces D's cofiniteness to ANY cofinite sub-family. Genuinely useful, but there is
  no elementary cofinite base case to feed it (see Part II), so it does not by itself close anything.
- **Exact death point (sharpened, independently confirmed):** the obstruction is INTERNAL gaps, NOT
  top gaps. Brown's criterion t_{i+1}≤1+S_i (top-gap-free) holds with ZERO violations to 10^12 even
  for boundary (3,4,7) — if it sufficed (3,4,7) would be elementary, contradiction. The strictly
  stronger single-block (BLOCK) condition that WOULD kill internal gaps is VACUOUS (stalls at ratio>2
  for every family). So internal-gap finiteness = the multi-atom (SEED) = 3^p≈4^q / MW spacing.
- **δ is the WRONG lever** (key correction): threshold collapses with δ empirically, but only because
  large δ tends to come with denser base sets; δ per se does not buy an elementary argument. The
  lever is base-DENSITY, and even maximal density (consecutive runs) still needs multi-atom interlock.

## Discriminator is LOG-CLUSTERING, not coprimality (refines scholar's winnable-tier)
scholar floated "pairwise-coprime D with δ bounded below" as the winnable tier. **Refuted:** (3,4,7)
IS pairwise-coprime (gcd of every pair =1) yet is the MW-hard boundary case — its 3^p≈4^q clustering
is LOGARITHMIC (log4/log3≈5/4 ⟹ 3^5=243≈4^4=256), independent of gcd. Coprimality is a gcd notion;
clustering is a notion of |log d_i/log d_j − p/q| being small = the Mignotte–Waldschmidt quantity.
So the real discriminator is δ VS log-clustering (= max over base pairs of how nearly their powers
coincide), exactly the MW spacing. Pairwise-coprime (3,4,5,7,11,13) δ=0.43 has k=3 threshold 6,720
(tiny); pairwise-coprime (3,4,7) δ=0 is MW-hard. Same gcd structure, opposite difficulty.

## carry's μ(δ) reconciliation — necessary, not sufficient (the last check)
carry supplied the residue-fix spare capacity I asked for: μ(δ) = min over residues r mod b^k of
#{cross-base small-atom subsets realizing r} grows EXPLOSIVELY with δ (7,168 → 8×10³¹ for δ:0.033→
0.829). Confirms exponentially many residue-corrections — but NECESSARY, NOT SUFFICIENT, same as "all
residues hit" was (maverick Result 2). Precise gap I verified: the mechanism needs, for every n, a
coarse part c (subset sum of atoms ≥ b^k; within G(k)=Θ(b^k) of n by Lemma BG) with offset (n−c)
EXACTLY a fix VALUE — not just the right residue class. The fix-VALUES of T' do NOT cover [0,G(k)]
contiguously: T'=(4,5,6,7) becomes value-contiguous only at 45 while G(k)=3, so a single coarse offset
is not always fillable. (3,4,5,6,7) is cofinite anyway because MULTIPLE coarse choices give multiple
offsets and one hits a fix value — but "some (coarse,fix) pair works for EVERY n" is exactly the
multi-atom (SEED)/equidistribution statement, NOT elementarily implied by μ(δ) large. So μ(δ)→∞
explains WHY it empirically works but is not a proof. Same wall, from the residue side.

**carry's correction + the decisive k-dependence (final nail).** carry re-measured with VALUE-bounded
corrections (value ≤ c·M, which is what the proof can actually use): full residue coverage mod M=b^k
needs a window factor c(D,k) = smallest c with {v∈T' : v≤c·M} covering all M residues. I then tested
the crucial question — is c(D,k) bounded in k? **NO, it GROWS:** for (3,4,5,6,7) c=2/15/154 at
k=1/2/3; even for the high-δ (3,…,10), c=2/15/49. So the correction window the bulk must supply is
c(D,k)·b^k with c(D,k)→∞ — the bulk must produce contiguous intervals growing FASTER than b^k. That
is precisely the (SEED) growth (threshold n₀(k)→∞ super-geometrically), which needs the analytic
input. **So even carry's corrected window statement does NOT give a uniform-in-k elementary theorem:
the window factor c(D,k) is unbounded in k, and bounding it is the (SEED)/MW problem.** Confirmed from
the residue side, the bulk side, and the value-coverage side — all three hit the same wall.

**density's thickness-margin / max-reach route — also confounded (4th angle, with density).** density
proposed closing step 2 via the Astels thickness-margin: at δ>0 the remaining mass over-covers the
power-aligned gap. I verified the margin-domination (binding gap)/(δ·scale) IS bounded & uniform in k
(~0.357 for (3,…,10) at k=2,3), and that high-δ binding gaps don't recur (vanish above a bounded
octave). BUT the route is confounded by the same trap: the candidate elementary criterion "reach/n ≥ 2
(double coverage)" is NOT sufficient — (5,6,7,8,9,10) has min reach/n = 2.06 ≥ 2 yet ∑=0.996<1, so it
is NOT cofinite (distant Pomerance gap). Worse, its TOP-OF-POWER margin stays positive even at 5^39 —
the max-reach/thickness analysis is BLIND to the internal gaps that actually obstruct. So density's
coarse coverage criteria (gap-prediction formula, reach ratio, thickness margin) handle the top-of-
power structure (easy, covered for all admissible D incl. boundary) but CANNOT detect the internal/MW
gaps that are the real content. Same wall, 4th angle.

**density's margin-growth composition — sharpened to the RUN-vs-SINGLETON distinction (5th angle).**
density's refined leg: surplus reach δ·U (grows linearly in U) overtakes the residual gap (claimed
O(d_max^k), U-independent), crossing at U₀∼C·d_max^k/δ ⟹ threshold ≤ C(δ)·(d_max·d_2)^k. I verified
the residual gap as a RUN length IS U-bounded and even shrinks: max missing RUN in [U,2U] is 0–3 for
(3,4,5),(3,4,6),(3,4,5,6,7),(4,5,6,7,8) at k=2, all scales. So the surplus DOES overtake the max-RUN.
**But cofiniteness needs NO missing POINTS, not just no long runs**, and ISOLATED SINGLETONS (run
length 1) persist far beyond C·d_max^k: (3,4,6) k=2 has last run≥2 at 44,817 but isolated single
misses up to 242,113 (d_max^k=36); (3,4,5) k=2 last run≥2 at 57,404, singletons to 77,613. A surplus
(=LENGTH) argument cannot fill a run-length-1 hole — that hole is a specific-VALUE miss
(residue-equidistribution = MW), not a length deficit. So density's composition rigorously gives "no
RUN above C·d_max^k/δ" (a clean elementary partial!) but NOT cofiniteness. The death point is now
localized with maximal precision: **the open core is exactly the ISOLATED SINGLE missing points
(run-length-1) between C·d_max^k and the true threshold — each an independent specific-value /
linear-forms-in-logs question.** 5th angle, same wall, sharpest localization yet.

## Honest verdict
The assault did NOT close the strict-excess theorem, and I now believe NO elementary (MW-free) proof
exists even for it — the dense families that looked elementary are cofinite via the same multi-atom
(SEED) mechanism that single-block Cassels cannot capture (verified: (BLOCK) stalls for all of them).
The one durable contribution is **Lemma M** (subset-monotonicity) as a reframing tool, plus the
sharpened death-point diagnosis (internal-gap, top-gap-free is automatic, δ is not the lever). This
CONVERGES with cassels/maverick/carry: the open core is MW/Baker for the internal gaps, uniformly in
D, with no elementary shortcut via excess or density. Recommend: do NOT claim any δ-theorem or
Theorem E; record Lemma M + the death-point sharpening as the honest output of the assault.
