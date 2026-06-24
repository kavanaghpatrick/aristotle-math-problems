# E124 open part — constructive/algorithmic attack (carry)

**Author:** carry. **Status:** BEGL96 confirmed empirically for all small admissible D (k=1,2);
proof skeleton pinned down and reconciled with lift/cassels/scholar; key error-corrections logged.

## Setup (builds on sumset's scaling reduction)

By sumset's lemma, target = `R(D,k) := ∑_{d∈D} d^k·B_d`, `B_d` = distinct-power sums (0/1 base-d
digits). E124-open ⟺ R(D,k) cofinite for every admissible D (all d≥3, ∑1/(d−1)≥1, gcd(D)=1).

**Clean reformulation:** E124-open ⟺ the merged atom multiset `A(D,k) = {d^j : d∈D, j≥k}` is a
COMPLETE sequence — every large n is a subset sum using each atom ≤ once. (= BEGL96 "if" direction
for finite A=D; matches scholar's dissection.)

## MAIN EMPIRICAL RESULT — BEGL96 holds for all small admissible D, k=1,2

Exhaustive scan of **all 45 admissible D with d≤12, r≤4**:
- **k=1: 45/45 cofinite** (max threshold 986, at (3,4,6)).
- **k=2: 45/45 cofinite**, max threshold **3,982,888** at (3,4,7), confirmed at N=4.1M; matches
  modular's independently-computed N0(2). (Several other D's k=2 thresholds I scanned at N≤1M are
  likewise lower bounds, not confirmed — see warning.)
- **No counterexample to BEGL96 anywhere in range. Disproof lane dead for small D.**

> **FALSE-CONVERGENCE WARNING (important, corrects my earlier 785743):** (3,4,7) k=2 looked
> "converged" at largest-missing **785743** for N=1M AND N=2M (stable across a full N-doubling), but
> a sparse high gap at **3,982,888** only appears at N≥4.1M. **Stability across one N-doubling is NOT
> proof of convergence in this problem** — gaps hide far above an apparently-stable threshold. The
> safe N is N ≫ d^{k+m} (modular's effective bound: residue-fixing can force a power at position
> ~k+m). VERIFIED N0 (breaker/density/maverick, strict 2-doubling): N0(1)=581, N0(2)=**3,982,888**,
> N0(3)=**166,025,260** for (3,4,7). (BOTH 785743 at k=2 AND 57,751,591 at k=3 were false-freeze
> traps — 57.75M broke at 166M, confirmed stable across N=256M/512M/1024M.) Growth k1→k2 = ×6855;
> law N0(k) ~ d_max^{(1+o(1))k}, d_max=7.

Structural facts:
- **No 2-base admissible D exists** (max ∑1/(d−1) with distinct d≥3 is 1/2+1/3=5/6<1). Minimal hard
  case is r=3. **(3,4,7) is the UNIQUE tightest 3-base boundary case (∑=exactly 1)** — explains why
  BEGL96 singled it out and why it has the largest threshold.
- Thresholds grow super-geometrically in k (N0(k)/7^k itself grows ×~1000 per k-step for (3,4,7));
  thr/maxd^k NOT stable. Tighter harmonic margin ⇒ larger threshold.

## The TWO-INGREDIENT proof structure (consensus with lift; my +b^k closure = ingredient A)

For R(D,k) cofinite, two independent things (lift's R/A split, which I independently reproduced):
- **(R) Residue covering** — hit every class mod m. At k=0 automatic (1=d^0∈B_d). At k≥1 each
  summand divisible by d^k destroys this; **gcd(D)=1 + lift's Residue Lemma** restores it.
- **(A) Class-wise filling** — within each covered class, all large n appear.

**My contribution to (A): the +b^k closure / per-class full-AP structure (b=min D), VERIFIED.**
- Each residue class mod b^k becomes a FULL arithmetic progression above its own per-class
  threshold thr_r. Overall threshold = max_r thr_r. For (3,4,7) k1, m=3: thr_0=264, thr_1=238,
  thr_2=581 → overall 581. ✓ all tested D.
- Equivalent statement: above threshold, R(D,k) is closed under +b^k with ZERO violations; the last
  +b^k-closure failure sits exactly at thr−b^k. **cassels promoted this to Lemma C (proved,
  Lean-ready): if R has M=b^k consecutive integers above T AND is +M-closed above T, then
  R⊇[T+1,∞).** He verified the threshold identity T(D,k)=v+M (v=last +M-closure failure) exactly
  across 7 families.
- **cassels' side-condition mapping (I independently re-verified):** the two hypotheses of Lemma C
  map onto the conjecture's two side conditions — **(a) eventually M consecutive reachable ⟺
  gcd(D)=1**; **(b) +M closure eventually ⟺ ∑1/(d−1)≥1.** Confirmed via controls: gcd=3 and gcd=2
  families have max-consecutive-run=1 (a fails) regardless of ∑; the ∑<1 family (3,5,9) has 423
  +M-closure violations high up (b fails); admissible (gcd=1, ∑≥1) has unbounded runs + 0 violations.
  This is (R)=(a) [residue covering, localised to a length-M run] + (A)=(b) [density, localised to
  one +M step], and explains why the hypotheses are exactly gcd=1 and ∑≥1, not ad hoc. So E124-open
  ⟺ "the +b^k-closure failures are FINITE for every admissible (D,k)."
- **Mechanism (carry):** within class r mod 3, atoms ≡0 mod 3 are {3^j} = 3·{1,3,9,…} (a sparse
  B_3-ruler); atoms ≡1 are {4^j,7^j}. Fix residue by choosing c base-4/7 atoms with c≡r (mod 3);
  their value V≡r; then need (n−V)/3 ∈ B_3 (0/1 base-3 digits). Filling works because the number of
  valid (V, B_3-target) decompositions GROWS with n (measured: 3→13 over n∈[600,2000]; window-min
  stays ≥1, mean ~6–11). This is BEGL96 Claim-1's density estimate, restricted to a class.
- **The thin margin (window-min #decomps = 1 near the boundary) is why (3,4,7) is extremal and why
  BEGL96 needed Mignotte–Waldschmidt linear-forms-in-logs** (|3^p−4^q| lower bounds control exactly
  when a B_3 target is hittable). The general-D rigorous version of (A) is the genuine open core.

**Carry-debt frontier (synthesis with modular's effective bound).** modular proved residue covering
mod m can REQUIRE a power at position ~k+m (a summand as large as d^{k+m}), and it is linear-in-m
tight when the only coprime base has order 2 mod p^a (e.g. (6,10,15), m=16: needs T=15 powers). Since
a valid representation needs every summand ≤ n, fixing a hard residue can force a power approaching n
itself — leaving no room to fill. **This is exactly why the threshold N0(k) ≈ (small const)×(largest
atom below N0):** verified, N0(2)=3,982,888 ≈ 2.5·3^13. The base-3 digits of 3,982,888 lead with a
forbidden digit 2, the structural signature of a number stranded at the carry-debt frontier. So (A)'s
genuine difficulty = a *size-bounded* local-solvability problem: cover residues using only powers
≤ log_d(n). The handoff from local theory (residue covering, modular) to global density (∑1/(d−1)≥1)
happens precisely at this frontier.

## Refinement of maverick's (★): the closer must kill ISOLATED late gaps (verified)

maverick's Lemma BG (rigorous, k-uniform) freezes the max gap at G(k)≈d_min^k after a ≤3-atom
transient, and his Result 2 warns "bounded gap + all residues ≠ cofinite." I verified this and
pinned the exact residual content:
- For (3,4,7) k=1, max gap in the scattered region [100,581] is exactly 3 = G(1) (Lemma BG ✓);
  above 581 the gap is 1 (consecutive).
- maverick's (★) at window length 2G=6 stops failing at n=261, but the TRUE threshold is 581.
  The values between are **isolated singleton missing points**: 264, 521, 581 — each has present
  neighbors on BOTH sides and its residue class is covered nearby (581≡2 mod 3, yet 578 and 584 ∈
  class 2 are present). **So all-residues-in-window + gap≤G genuinely does NOT imply cofinite —
  isolated points survive.** This refines maverick's warning into a mechanism: the closer must kill
  isolated late gaps, strictly harder than windowed-residue-coverage.
- **These isolated late gaps = my per-class threshold thr_r** (the last missing element of class r),
  occurring exactly where powers of different bases CLUSTER (3^5=243 ≈ 4^4=256, ratio 1.05),
  creating "coverage shadows." **This is precisely the Mignotte–Waldschmidt phenomenon:** the
  |3^p−4^q| lower bound quantifies the clustering and thereby caps where the last isolated gap sits.
  So the hardest residual of (A) = "no isolated gaps past n₀," and for the extremal (3,4,7) family
  that residual IS the linear-forms-in-logs content BEGL96 invoked.

## The LIFT k=0 ⟹ k≥1 (Observation 3 — connects to cassels' Birch note)

R(D,k) = "drop the bottom k atoms {d^0…d^{k−1}} from every base of the k=0 system." Dropping any
finite set of bottom atoms keeps the system cofinite *provided the residue condition survives*
(verified for many uneven drop patterns). **If the k=0 (Alexeev) covering only uses sufficiently
large powers asymptotically, k≥1 follows, with gcd(D)=1 the exact condition ensuring no dropped low
atom strands a residue class.** cassels cites Birch 1959 as precedent that "the method survives a
lower bound on exponents." This is the reduction to extract from the k=0 proof.

## gcd(D)=1 obstruction — PROVED (clean; confirms sumset & cassels)

g=gcd(D)>1, prime p|g ⇒ p^k | d^k | a_d ⇒ p^k | n for every representable n ⇒ all n∤p^k missing
⇒ NOT cofinite. Verified: (4,6,8) k1 has 0 odd representable; 3000 odd numbers in [0,6000] all miss.

## ERROR-CORRECTIONS logged (saved the team time)

1. **Naive Cassels filling-from-0 does NOT apply to raw atoms** (min atom b^k≥3>1 ⇒ interval [0,M]
   never grows). Cassels filling is only legitimate WITHIN a residue class mod b^k, after (R). I hit
   and corrected this; flagged to cassels.
2. **Brown/Sylvester contiguous-completeness inapplicable** (same reason).
3. **Greedy-from-top FAILS** (775 fails (3,4,7) k1); **two-phase greedy-small-last FAILS** (1285/1419).
4. **Three of BEGL96's stated largest-missing values are off by +1** vs exhaustive DP (flagged to
   scholar): Pow({3,4,5};1)=79 not 78; Pow({3,5,7,13};1)=112 not 111; Pow({3,6,7,13,21};1)=17 not 16.
   Pow({3,4,7};1)=581 MATCHES. The paper's value is representable in each off-by-one case; paper+1 is
   the true largest-missing. **Our Lean threshold for (3,4,5) should be 79.**
5. **Single-block interval-append CANNOT close (maverick's self-correction, I verified the root
   cause):** the max consecutive-atom ratio t_{i+1}/t_i in the sorted atom sequence is exactly **3.0**
   for any D containing base 3 (the pure-powers-of-3 gap, e.g. 81→243), since 3 is the smallest base
   and runs of its powers have no intervening atom. Cassels/Sylvester single-block append needs ratio
   ≤2 (next atom ≤ R+1); 3>2 STALLS it (e.g. a ~700M contiguous block cannot reach 4^15≈1.07e9 by one
   append). **So closure is intrinsically MULTI-atom (cross-base combinations), never a one-block
   greedy walk** — the structural reason my greedy-from-top got 775 failures and naive Cassels fails.
   Lemma BG (running-sum ≥ next atom) is necessary (no starvation) but NOT sufficient (doesn't forbid
   internal gaps).

## Excess δ TAMES the {3,4} clustering (sumset's refutation — CORRECTED, key theorem opening)

**CORRECTION (sumset, verified by me):** my earlier claim that the {3,4} clustering is
δ-INDEPENDENT was WRONG — it was an over-generalization from small-excess cases only. Exact data
shows the {3,4}-family k=2 threshold COLLAPSES monotonically as harmonic excess δ grows, even WITH
{3,4} present:

| D | excess δ | k=2 threshold |
|---|----------|---------------|
| (3,4,6) | +0.033 | 242,113 |
| (3,4,5) | +0.083 | 77,613 |
| (3,4,5,6) | +0.283 | 1,068 |
| (3,4,5,6,7) | +0.450 | 312 |
| (3,4,5,6,7,8,9,10) | +0.829 | 184 |

So clustering dominates ONLY at small δ. At large δ the extra bases fill the 3^p≈4^q shadow with
ALTERNATIVE representations before the clustering matters — the algorithm routes AROUND the shadow.
My old "even slack doesn't give an MW-free bound" was tested only at δ=+0.033, +0.083 (precisely the
small-δ regime where clustering still wins), so it does NOT generalize.

**This is the opening for the strict-excess theorem (sumset + carry, task #17):** with hypothesis
"δ large enough relative to the clustering pair," the threshold is bounded by an ELEMENTARY function
— no |3^p−4^q| linear-forms bound needed, because we never rely on the clustering region being thin;
we route around it.

> **UPDATE (k=3 REFUTES the clean general-k version).** This opening DOES work for non-minimal D
> (subset-monotonicity, below) and at k=1 (N₀≤0.27·C'/σ², clean & verified). But the k-uniform onset
> bound N₀≤K·(d_max·d_2)^k/σ² with absolute K is FALSE: K grows 0.046→1.347→3.759 (k=1,2,3 on (3,4,5);
> N₀(k=3)=4,330,731 verified at N=12M), and no clean base fits (N₀/(d_max²·d_2)^k oscillates). The
> k-scaling is number-theoretic (cross-base power clustering) = MW/transcendence, NOT elementary. So
> general-k minimal-D strict-excess hits the SAME MW wall. Honest status: strict-excess is elementary
> only for (i) non-minimal D, all k; (ii) all D at k=1. Converges with sumset (μ(δ) necessary-not-
> sufficient) and maverick (Result 2).

**Residue-fix capacity — the HONEST quantity (my half of task #17).** A first pass suggested the
residue-fix spare capacity is "explosive" (min-multiplicity 8×10³¹ at δ=0.829), but that counted
corrections of UNBOUNDED value (up to 8 powers/base), which the invariant cannot use. Re-measured
with VALUE-BOUNDED corrections (value ≤ c·M, the usable bulk-fill slack), k=2, M=b^k=9 for
(3,4,5,6,7): c=4 (cap 36) hits only 2/9 residues; c=8 (72) hits 6/9; c=16 (cap 144≈16M) finally hits
9/9 (min-mult 2). So full residue coverage requires a correction window of size ≥ c(D,k)·M with
c(D,k)≈M-ish (=16 here), NOT a small constant. **What δ actually buys is the SLACK window size, not
free small-slack capacity.** The correct invariant input: "δ must guarantee a usable correction
window ≥ c(D,k)·M, where c(D,k) = smallest c giving full residue coverage mod M from value-bounded
non-b atoms; c(D,k) is finite and computable." sumset owns the δ-margin / contiguous-interval
bookkeeping that must deliver a window ≥ c(D,k)·M; carry owns the residue-fix coverage lemma.
Scripts: /tmp/e124_residue_capacity.py (unbounded — overstated), /tmp/e124_capacity_bounded.py (the
honest value-bounded one — USE THIS).

> **FINAL (sumset, the closing nail): c(D,k) is UNBOUNDED in k.** sumset measured the window factor
> c(D,k) across k: (3,4,5,6,7) δ=0.45 → c = 2, 15, 154 (k=1,2,3); (3,4,5,6,7,8,9,10) δ=0.83 → 2, 15,
> 49; (4,5,6,7,8) → 2, 29, 128. So the correction window c(D,k)·b^k grows FASTER than b^k, i.e. the
> bulk must produce contiguous intervals growing super-geometrically — which IS the (SEED)/n₀(k)→∞
> problem. Bounding c(D,k) = bounding N₀(k) = the MW/Baker core. So my "window ≥ c(D,k)·M" is the
> correct formulation but its window factor is unbounded in k ⟹ NO uniform-in-k elementary theorem.
> **THE SAME WALL CONFIRMED FROM THREE INDEPENDENT ANGLES:** (1) residue side — μ(δ) value-coverage
> necessary-not-sufficient; (2) bulk side — single-block stalls (consecutive-atom ratio 3>2); (3)
> value-coverage side — c(D,k)→∞. Assault honestly concluded: no elementary proof even at strict
> excess; open core is MW/Baker (cross-base power spacing |3^p−4^q|). Converges with the whole squad.

(The boundary ∑=1 / δ=0 case still needs MW; that's separate from the strict-excess theorem.)

## Subset-monotonicity (sumset) reduces only NON-MINIMAL D — the hard core is the MINIMAL D

sumset's subset-monotonicity (VERIFIED): T_k(D) ⊇ T_k(D'') for any D''⊆D (drop a base ⟹ a_d=0,
always allowed since 0∈d^k·B_d). So cofiniteness of any subset ⟹ cofiniteness of D. BUT a subset D''
can only be invoked if D'' is ITSELF admissible (∑_{D''}1/(d−1)≥1 AND gcd(D'')=1 — both forced by
Pomerance + the gcd obstruction). Dropping bases reduces the harmonic sum, so a proper admissible
subset often doesn't exist.

**Enumeration (all 115 strict-excess admissible D, d<12, r≤5):**
- 72 have a proper admissible subset ⟹ subset-monotonicity reduces them (EASY: max k=1 thr = 74).
- 43 are MINIMAL (no proper admissible subset) ⟹ subset-monotonicity gives NOTHING (HARD: max k=1
  thr = 986, includes ALL {3,4}-clustering cases — (3,4,6)=986, (3,4,5)=79, (3,5,7,9)=112).

**The minimal/non-minimal split is EXACTLY the easy/hard split.** So subset-monotonicity peels off the
easy families and leaves the hard core untouched. This cleanly STRUCTURES the strict-excess theorem:
(i) non-minimal D — trivial via monotonicity to a dense admissible subset; (ii) MINIMAL D — needs the
direct class-onset bound N₀≤K·(d_max·d_2)^k/σ². The minimal D are characterized by a finite
combinatorial criterion (no proper subset has ∑≥1 ∧ gcd=1), mostly {3,4,x} and {3,5,x,y} — enumerable.
Script: /tmp/e124_subset_exists.py, /tmp/e124_minimal_hard.py.

## BEGL Claim 1 does NOT reach the conjecture's regime (refines cassels §4)

cassels §4 framed ∑>1 strict-excess as "more tractable via adapting BEGL Claim 1." This is too
optimistic. Claim 1 needs a finite POWER-chunk with harmonic mass β>2. The TOTAL harmonic mass of
ALL atoms {d^j : j≥k} of a single D is ∑_d d^{1−k}/(d−1) — which at k=1 equals exactly ∑1/(d−1), the
conjecture's own quantity. For admissible D that's in [1,2), so **β>2 is unattainable from a single D
anywhere in the conjecture regime ∑∈[1,2), boundary or strict-excess** (at k≥2 it's 0.27–0.42; the
smallest D reaching mass 2.020 is the 10-base (3,…,12) at k=1, collapsing to 0.42 at k=2). The right
bulk tool is therefore maverick's Lemma BG (needs only ∑≥1 — exactly the conjecture), which yields
bounded gaps ≤G but NOT cofiniteness. So strict excess only shrinks Lemma BG's constant G; it does
NOT close the isolated gaps. **The real tractable/hard split is not ∑=1 vs ∑>1 — it's whether D
contains a near-colliding base pair (the {3,4}/3^p≈4^q clustering), which is MW-hard for any ∑.**

## Bottom line

The team has a coherent proof skeleton: (R) lift's Residue Lemma (proved) + (A) per-class filling
(my +b^k closure, verified; quantitative core = BEGL Claim 1 within a class, thin at the (3,4,7)
boundary, needs Mignotte–Waldschmidt for the extremal family). The clean general theorem reduces to
making (A) rigorous for general admissible D — exactly the gap BEGL96 left open. No disproof exists
for small D. Aristotle should be pointed at: (i) lift's Residue Lemma in Lean, (ii) the per-class
+b^k-closure / Cassels-within-class filling lemma, (iii) the drop-bottom-atoms robustness of the k=0
proof.

## INVENTION BLITZ — INV-C1 (top-down peel) investigation: FINAL (algorithm, not proof)

INV-C1: represent n by peeling the largest atom a≤n s.t. (n−a) is a subset-sum of atoms STRICTLY
SMALLER than a; recurse. Full investigation (detail in INVENTIONS.md):
- **Verified properties:** O(1) lookahead (skip-depth ≤2, k-uniform, even at boundary (3,4,7) k=3 above
  the TRUE 166M threshold — breaker); geometric contraction (residual ≤0.66-0.72n, no step fails, 118k+
  chains — carry+scholar); sound + discriminating (fails exactly on β<1 non-representable n).
- **Verdict: INV-C1 is a CORRECT DECODING ALGORITHM for the representable set, NOT a cofiniteness
  proof.** Confirmed from 4 independent angles: (1) carry — contraction bounds residual SIZE, not
  REPRESENTABILITY; (2) scholar — Q-shrink (chain length, elementary) vs Q-exist (valid-peel existence,
  the wall); (3) breaker angle-3 — self-similar induction base "smaller-atom reach cofinite up to a" is
  FALSE (own_thr(a)/a > 0.99 every scale, =1.000 at pure powers; verified by carry); (4) the circularity
  (valid-peel choice needs the full reach).
- **scholar's coarse/interior split (tested, does NOT shrink the kernel):** 70% coarse / 30% interior of
  hard steps; S9 sum-budget holds 100% for coarse, BUT actual representability of coarse residuals is
  72% scattered-fine-structure + 28% recursive-conjecture (dead induction). S9 gives budget, not
  representability. Both halves of Q-exist = the same MW wall.
- **Precisely-localized open kernel (all angles agree):** Q-exist = "a residual just below a pure power
  d^j is representable by strictly-smaller atoms" — single-scale, elementary chain-length wrapper =
  cross-base power-spacing (Mignotte–Waldschmidt/Baker). The cofiniteness wall is untouched by any
  constructive route.
Scripts: /tmp/e124_C1_honest.py, e124_C1_k3.py, e124_skip_k.py, e124_ownthr_a.py, e124_S9_actual.py.
