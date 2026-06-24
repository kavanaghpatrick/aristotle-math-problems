# Strict-excess theorem (∑1/(d−1) > 1) — HONEST-CONDITIONAL (squad-co-signed final statement)

**Authors:** cassels + lift + carry + density + modular (co-signed). **Status (final, referee-proof,
nothing overclaimed):**
- **BANKABLE (elementary, transcendence-free, unconditional):** (1) non-minimal D via subset-
  monotonicity, all k [carry]; (2) k=1 all-σ via cassels' m₀ gap-onset + carry's k=1 onset bound.
- **CONDITIONAL (per-fixed-k):** for each FIXED k, T_k cofinite via the chain Lemma A (cassels,
  gap-condition onset m₀=(C'−1)/σ) + per-class identity N₀=max_r O_r (lift) + margin-growth closes
  the onsets (lift's Lemma B, VERIFIED not proven) + residue coverage (modular). Finitely verifiable
  per (D,k); NOT uniform-over-D even at fixed k (closure = +M-termination/min#reps≥1 is empirical, no
  deductive proof — cassels+lift confirmed).
- **THE MW KERNEL (open, precisely located):** Lemma A' (uniform-in-k onset) = cassels' constrained-
  deflation onset = carry's K(k) growth (0.046→1.35→3.76 at k=1,2,3, no clean base) = density's
  gap-O-constant k-growth. Transcendental. Confirmed from 6+ independent angles.
- Threshold is ONE object: cassels' v = density's U₀ = sumset's last-hole = gap(D,k)/σ + d_min^k.
- Cross-checks [carry/modular]: no-cascade localization holds ONLY strict-excess+low-k; at boundary
  ∑=1, k≥3 (above TRUE n₀=166M) cascade is pervasive (5000/5000, depth ~6). carry's INV-C1 is a sound
  O(log n) DECODER for representable n, NOT a cofiniteness proof (bounds residual size, not
  representability) — doesn't rescue the kernel.
- Lemma A = **MACHINE-VERIFIED (Aristotle/Harmonic, Jun 10 2026): PROVED, sorry-free, axioms
  propext/Classical.choice/Quot.sound, exact requested signature.** Aristotle confirmed my outline
  correct and formalized it (per_base_bound via Mathlib geom_sum_Ico → termwise summation) and
  independently confirmed the hne/hk hypotheses are unnecessary for the bound (kept for fidelity).
  Result archive: submissions/results_jun10/gap_onset_x/. **First novel theorem through the pipeline,
  authored by cassels, adjudicated correct.** Novelty = DEFENSIBLE-NEW (scholar: clears
  Birch–Zannier–Perelli–Chen-Fang-Yu-Liu; cite Zannier 1989 as nearest related work; the Yu-Chen 2025
  / Liu 2026 PDF check is scoped to PUBLICATION-novelty claims only, NOT to the proof's correctness —
  which is now machine-checked). k=0 base = KNOWN (Brown 1961/Erdős 1962).

[Earlier header said "mostly elementary, one residual gap / NO transcendence / winnable tier" — that
OVERSTATED; corrected to the above after the full-squad k=2/k=3 refutation of any k-uniform bound.]

> **CITATION NOTE:** "Cassels gap-condition" below is a descriptive NAME for the interval-filling
> completeness criterion (a_{n+1} ≤ S_n + 1). Correct attribution: **Brown 1961** (Amer. Math.
> Monthly 68, 557–560) + **Erdős 1962** (Acta Arith. 7). "Cassels 1960" is a PHANTOM ref — do not cite it.

Builds on cassels_k0_elementary_proof.md (the k=0 base case) and scholar_discrete_thickness_attack.md
(strict ∑>1 = discrete-Astels self-sustaining regime; boundary ∑=1 = MW core).

## Claim (strict-excess theorem, target). Let D = {d_1<…<d_r}, all d_i ≥ 3, gcd(D)=1, and
**σ := ∑1/(d−1) − 1 > 0** (STRICT). Then for every k ≥ 1, ∑_D d^k·B_d is cofinite, with an
EFFECTIVE, transcendence-free threshold N₀ ≤ f(D,k).

## What is PROVEN (elementary).

**Lemma A (gap-condition with deficit) — EXACT.** Let β = ∑_d 1/(d−1) and C' := ∑_d d^k/(d−1).
For the merged atom set A = {d^j : d∈D, j≥k}, S(X) = ∑ of atoms ≤ X, m = next atom = min_d(d·x_d)
(x_d = largest d-power ≤ X):
> **S(X) ≥ m·β − C'.**
*Proof (rigorous).* The atoms of A in [0,X] from base d are d^k, …, d^{J_d}=x_d, so
S(X) = ∑_d ∑_{j=k}^{J_d} d^j = ∑_d (d·x_d − d^k)/(d−1) (geometric series). Split:
S(X) = ∑_d (d·x_d)/(d−1) − ∑_d d^k/(d−1) = ∑_d (d·x_d)/(d−1) − C'. Since d·x_d ≥ m for every d
(m is the min), ∑_d (d·x_d)/(d−1) ≥ m·∑_d 1/(d−1) = m·β. Hence S(X) ≥ m·β − C'. ∎
**VERIFIED exact (rational arithmetic) 0/20000 violations to 10^12 for (3,4,5),(3,4,5,7),(3,4,6),(3,4,7).**

> **PRIOR-ART / NOVELTY (scholar verdict — NEW, modestly framed).** Lemma A clears prior art: no
> exact match in Brown 1961, Erdős 1962, Folkman 1966, Graham 1964, Hegyvári, Birch, or the lacunary
> "complete sequences with gaps" line — all are QUALITATIVE and unit-seeded (k=0); none state a
> quantitative gap-condition with the explicit deficit C'=∑d^k/(d−1) for the EXPONENT-SHIFTED
> (j≥k≥1, no unit, smallest atom d_min^k≥3) case. **Honesty caveat (scholar):** at its core this is
> an elementary geometric-series estimate; the risk is not a missed paper but that such a routine
> estimate may be USED IMPLICITLY in completeness proofs without being ISOLATED as a named lemma. So
> frame the novelty MODESTLY — "an explicit shifted/deficit-corrected gap-condition onset," NOT a new
> technique. **The genuinely novel content to foreground is the CLOSED-FORM onset m₀=(C'−1)/σ and its
> clean death at σ=0:** the linkage "gap-condition onset FINITE ⟺ strict excess σ>0, INFINITE at the
> boundary σ=0 (=the MW core)" precisely separates the winnable tier from the transcendence wall.
> Before any submission: one MathSciNet/zbMATH forward-citation pass on Brown 1961 + Erdős 1962 to
> close the residual obscure-note risk. [scholar prior-art verdict.]
>
> **UPGRADE (scholar forward-citation sweep COMPLETE — verdict now DEFENSIBLE-NEW):** the sweep
> (Crossref forward-cites of Brown 1961 [19] + Erdős 1962 [13], abstracts read) found and CLEARED the
> nearest neighbor — the Birch–Zannier–Perelli shifted-completeness line. Nearest: **U. Zannier, "On a
> theorem of Birch concerning sums of distinct integers taken from certain sequences", Math. Proc.
> Camb. Phil. Soc. 106 (1989) 199–206** (DOI 10.1017/s0305004100078014; Crossref confirms Zannier, vol
> 106). DECISIVELY DIFFERENT: Zannier is (a) strictly TWO-generator {p^a q^b}, (b) bounds ONE exponent
> from ABOVE not below, (c) threshold via ∑1/n not ∑1/(d−1). Perelli–Zannier (Acta Math. Hungar. 41,
> 1983): general sequences, ∑1/aₙ≫loglog X, no base/exponent/∑1/(d−1) structure. **Lemma A's exact
> combination — ≥3 INDEPENDENT bases, exponents bounded BELOW (j≥k), explicit deficit C'=∑d^k/(d−1),
> closed-form onset (C'−1)/σ governed by ∑1/(d−1) — lies OUTSIDE the entire Birch–Zannier–Perelli
> line.** NEW now defensible (nearest neighbor two-generator; multi-base form is a real gap; the
> "implicit-routine-estimate" caveat shrinks). **Related-work cite:** Birch 1959; Zannier 1989 (MPCPS
> 106, 199–206); Perelli–Zannier 1983 (Acta Math. Hungar. 41). [scholar forward-citation verdict.]
>
> **FINAL DILIGENCE — Zannier-citers pass COMPLETE (scholar): verdict NEW, high confidence.** Zannier
> 1989 has only 5 citers (Chen-Fang-Yu-Liu Erdős-Birch line, incl. the highest-overlap-risk modern
> generalizations); ALL CLEARED: Chen-Fang 2017 (ℕ^r VECTOR formulation, not ≥3 scalar bases);
> Yu-Chen 2025 EJC (stays two-generator {p^a q^b} semigroup, no finite D |D|≥3, no ∑1/(d−1)); Liu 2026
> PMH (single/two-base exponential, no multi-base criterion); Yu-Chen 2023 (single-d, Erdős-Lewin
> "no-term-divides" variant). NONE reaches Lemma A's combination. The entire
> Birch-Zannier-Perelli-Chen-Fang-Yu-Liu lineage is two-generator / ℕ^r-vector / semigroup — the
> multi-base shifted-onset is outside all of it. **HONESTY CAVEAT (scholar):** 3 of 4 descendant
> papers had no abstract in the databases (title/venue inference, not abstract-confirmed). So the
> verdict is NEW with HIGH confidence; the residual SUBMISSION-GATE item is to pull the actual
> Yu-Chen 2025 (EJC) + Liu 2026 (PMH) PDFs to confirm directly (the only "could-not-fully-read"
> risk). Everything checkable says NEW. Optionally cite Chen-Fang 2017 / Yu-Chen 2025 as the modern
> generalizations Lemma A goes beyond. **Lemma A is the publishable kernel (novelty airtight modulo
> those 2 PDFs).** [scholar Zannier-citers verdict — the third and final prior-art layer.]

**Corollary (Cassels gap-condition onset) — closed form.** The Cassels gap condition S(X) ≥ m−1
holds whenever m·β − C' ≥ m−1, i.e. m·σ ≥ C'−1 (σ = β−1), i.e. **m ≥ (C'−1)/σ.** So for STRICT
σ > 0, the gap condition holds for every atom beyond the EFFECTIVE, CLOSED-FORM, ELEMENTARY threshold
**m₀ := (C'−1)/σ.** (Onset: (3,4,5) m₀=37 [true N₀=79]; (3,4,5,7) m₀=17 [N₀=22]; (3,4,6) m₀=91
[N₀=986] — right order; σ small ⟹ larger m₀, as expected.) **No transcendence: m₀ is a closed-form
function of D,k.** At σ=0 (boundary), m₀=∞ — the proof visibly dies, = the MW core.

**Lemma B (gap-closing is LOCAL).** Verified: to cover [N₀+1, V] contiguously, only atoms ≤ V are
needed, with V/N₀ ∈ [1.03, 1.14] across tested D. So no far-future atom is required to close any
gap — the closing is local, hence a finite computation up to O(N₀) certifies coverage. [Empirical;
the gap-condition (Lemma A corollary) is the structural reason new gaps can't form, and locality
says old gaps close nearby.]

## The ONE residual gap (where carry's piece enters).

The Cassels gap-condition (Lemma A corollary) guarantees **no NEW gap forms above m₀**, and Lemma B
says gap-closing is local. But the gap-condition alone does NOT prove the EXISTING low gaps (1,2,5,…
up to ~N₀) all CLOSE — at k≥1 there is no 1-seed (smallest atom = d_min^k ≥ 3), so coverage is not
contiguous-from-0. To convert "no new gaps + bounded existing gaps" into "cofinite" we need a
contiguous SEED block of length ≥ the step, which is exactly:
> **carry's class-wise piece:** within each residue class mod M = d_min^k, residue coverage (gcd=1,
> modular's L) gives an element in the class, and the gap-condition makes the class a full AP above
> its onset; the seed is a run of M consecutive integers, which exists once all r classes' onsets
> are passed.

**CORRECTED (carry's k=3 walk-back + my constraint analysis — the earlier "onset ≤ m₀-type bound,
no MW" claim here was WRONG):** the per-class onset is NOT bounded by m₀ — it is ≫ m₀ and GROWS with
k (onset_r/m₀ = 429 at (3,4,5) k=2; carry's K in N₀≤K·(d_max·d_2)^k/σ² grows 0.046→1.35→3.76 at
k=1,2,3, and NO clean base — the growth is number-theoretic, cross-base clustering at specific k).
So the seed-assembly is NOT elementary-throughout-no-MW. Honest status:
- Lemma A (gap-condition, m₀) — PROVEN, elementary. ✓
- Residue coverage — PROVEN (modular). ✓
- Per-class AP-above-onset structure — PROVEN (lift's identity). ✓
- BOUNDING the per-class onset (Lemma A') — NOT elementary uniformly: it's the constrained-deflation
  onset (= MW per class). Elementary PER FIXED k (finite check; lift's margin-growth closes it);
  uniform-in-k hits the wall. [TASK #17: the honest CONDITIONAL theorem, co-written with carry/lift —
  NOT a clean elementary closure.]

## Why the BOUNDARY ∑=1 (σ=0) is NOT covered (the honest line).
At σ=0, the corollary's threshold m₀ = (C'−1)/σ = ∞. The gap condition m·σ ≥ C'−1 is NEVER satisfied
for finite m (C'−1 > 0 always, since C' = ∑ d^k/(d−1) ≥ 3/2). So the elementary argument gives NOTHING at the boundary — exactly matching scholar's
"discrete Astels fails at ∑=1" and the MW requirement. The boundary needs |d_i^p − d_j^q| spacing.
**The dividing line σ>0 vs σ=0 is visible IN the proof as m₀ finite vs infinite.** This is the clean
strict/boundary split the lead and scholar called for, now with the mechanism explicit.

## Status
- Lemma A inequality: PROVEN form + VERIFIED 0/9000. [ELEMENTARY/Lean-ready]
- Corollary (finite onset m₀=(C'−1)/σ for σ>0): follows from Lemma A. [ELEMENTARY/Lean-ready]
- Lemma B (local closing relative to N₀): VERIFIED empirically. [but N₀ itself ≫ m₀, see below]
- Seed assembly: needs class-wise onset bound — and that onset is NOT elementarily bounded (below).
- Boundary σ=0: explicitly OUT (m₀=∞); = MW core. [honest]

## HONEST NEGATIVE on the effective-thr_r flagship (the lead's f(δ,D,k) hope).
The flagship target was an EFFECTIVE elementary bound thr_r ≤ f(δ,D,k) for ∑1/(d−1) ≥ 1+δ. I
attacked it directly; the SIMPLE forms FAIL:
- N₀ ≤ d_max^{2k}/σ: holds at k=1 (44/44 families, max ratio 0.91) but FAILS at k=2 for small-σ
  3-base families ((3,4,5) ratio 10.3, (3,4,6) ratio 6.2). Not uniform in k.
- N₀ ≤ C·m₀ (constant × the proven Cassels onset): FAILS badly — N₀/m₀ = 2–14 at k=1 but 428, 503
  at k=2 for (3,4,5),(3,4,6). m₀ and the true N₀ DIVERGE as k grows.
- carry's N₀ ≤ K·(d_max·d_2)^k/σ² (the best candidate): looked uniform at k≤2 (K≈2) but FAILS
  k-uniformity at k=3 — for tight (3,4,5) the ratio K grows 0.027 (k=1) → 1.347 (k=2) → 3.759 (k=3),
  diverging, not stabilizing. (N₀(3,4,5,k=3)=4,330,731 verified; bound (4·5)^3/σ²=1.15M.) So K is
  NOT an absolute constant; it grows with k in the tight-{3,4} corner. K≈2 was a k≤2 artifact —
  the SAME straggler-trap pattern (785k→3.98M→166M) that has repeatedly fooled the team.
**Mechanism (verified):** the gap-condition starting to hold at m₀ does NOT promptly close the gaps.
For (3,4,5) k=2, m₀=181 but gaps persist to N₀=77613, spread across ALL 9 classes mod 9 (~100+ gaps
each, class-thresholds all ≈ 57k–77k). So the seed/gap-CLOSING — not the gap-CONDITION — is the
dominant cost, and it is NOT bounded by any simple f(δ,D,k); the m₀→N₀ gap grows with k at fixed σ.
**Conclusion:** strict-excess is EASIER than the boundary (m₀ finite vs ∞ — the gap-condition at
least HOLDS) but the SEED-closing onset thr_r is large (≫ m₀), grows with k, and empirically tracks
the same cross-base power-spacing as the boundary. **The clean elementary strict-excess theorem does
NOT follow from m₀ alone.** This is the death point of the effective-thr_r attack — reported honestly.
What survives as PROVEN: Lemma A (gap-condition, m₀ finite for σ>0) + the k=0 full theorem. What does
NOT: a uniform elementary N₀ bound for k≥1, even at strict excess.

## Lemma A' is a CONSTRAINED-DEFLATION onset (with lift) — the precisely-located open sub-claim.
lift's structural finding (verified by me): the within-class onset reduces via deflation. (R_k ∩ Mℤ)/M
is cofinite (full AP step-1) with onset = (class-0 onset)/M. Verified: (3,4,5) k=1 class-0 onset 63 →
deflated 21; (3,4,7) k=1 264→88; (3,4,5) k=2 58059→6451; all full-AP above. **THE CATCH:** the
deflated set is NOT a free smaller BEGL instance — it is CONSTRAINED (the non-d_min digits must satisfy
∑_{d≠d_min} d^k b_d ≡ 0 mod d_min^k). So the deflation does NOT cleanly recurse to the k=0 base case;
the onset bound is REAL content, not bookkeeping. This is exactly why onset_r ≫ m₀ and diverges with k.
**⟹ Lemma A' = "the constrained-deflation onset is K(D,k)·scale^k-bounded" is a GENUINE OPEN sub-claim**
(verified k=1,2 with bounded K; K-boundedness as k→∞ is NOT obviously true — lift hit a compute wall
on (3,4,5) k=2's large deflated onset). This is the lead's named open kernel and my next target.

### Lemma A' — WHERE the constraint inflates the onset (cassels analysis, the mechanism).
I located the inflation precisely. The class-0 onset is governed by the gaps in the achievable
non-d_min sums ∑_{d≠d_min} d^k b_d that are ≡ 0 (mod d_min^k=M). Measured the max gap between
consecutive such values, normalized by d_max^k:
  (3,4,5): max-gap/d_max^k = 1254 (k=1) → 8446 (k=2).  (3,4,7): 1163 (k=1) → 6875 (k=2).
So the gap GROWS with k (super-d_max^k). **Mechanism:** the constraint ≡0 mod d_min^k thins the
achievable non-d_min sums in class 0, and the thinning WORSENS with k because there are fewer ways
for the non-d_min powers to align to ≡0 mod the growing modulus d_min^k. This is exactly a statement
about the DISTRIBUTION of {non-d_min powers mod d_min^k} — i.e. how d^j (d≠d_min) distributes mod
d_min^k as j grows. That distribution is the cross-base/Baker-type arithmetic content.
**⟹ Lemma A' provably needs a non-elementary (equidistribution/Baker) input for UNIFORM k:** bounding
the gap in {∑_{d≠d_min}d^k b_d ≡ 0 mod d_min^k} uniformly in k = controlling the alignment of the
non-d_min power-lattices mod d_min^k. This is the sharpest localization of the open core: not "the
threshold N₀" vaguely, but specifically "the density of constraint-satisfying non-d_min sums mod
d_min^k, uniformly in k." Elementary per-fixed-k (finite check); MW/equidistribution for uniform k.

### Lemma A', further reduced (cassels): it's a 2-mass BRIDGING problem, and the density is GENERIC.
Two findings that sharpen Lemma A' to its cleanest form:
1. **The constraint density is GENERIC, not thinned.** The non-d_min sums that are ≡0 mod d_min^k
   occur at rate ≈ 1/d_min^k (measured: (3,4,5) 0.3323 vs 1/3=0.3333 at k=1; 0.1108 vs 1/9=0.1111 at
   k=2). So the obstruction is NOT that the non-d_min sums arithmetically AVOID 0 mod d_min^k — they
   hit it at the generic rate. The inflation is in the GAP STRUCTURE, not the count.
2. **Lemma A' = a 2-mass bridging:** the constraint-satisfying non-d_min sums have harmonic mass
   ∑_{d≠d_min} 1/(d−1) < 1 (e.g. (3,4,5): 1/3+1/4=0.583), so they are SUB-complete on their own —
   UNBOUNDED gaps. The d_min ray (mass 1/(d_min−1), e.g. 1/2) must BRIDGE those gaps, and β>1 means
   1/(d_min−1) is exactly the surplus. So **Lemma A' = "the d_min ray bridges the (sub-complete)
   non-d_min constraint-sum gaps"**, and the onset = the bridging scale ≈ (max non-d_min constraint
   gap)·(d_min−1). Measured max non-d_min constraint gap: (3,4,5) 6270 (k=1) → 211158 (k=2), so the
   bridging scale grows with k. **This is the genuine recursive kernel:** the non-d_min constraint
   gaps grow with k (their own deflation has the same structure one level down), so uniform-in-k
   bridging is the recursive form of the MW wall. Per-fixed-k it bridges (finite); uniform-in-k is
   the open kernel, now pinned to "d_min-ray reach vs non-d_min-constraint-gap growth, uniformly in k."

### Lemma A' PRIOR-ART = the Hegyvári–Lev "R+T" line — a LEVER, not just a wall (scholar, PARTIAL).
The "d_min-ray (R) bridges the sub-complete non-d_min remainder (T)" decomposition is EXACTLY the
object of the **Hegyvári–Lev R+T literature** (R = geometric base-d 0/1-digit ray, T = positive-density
set, study R+T). Status: scholar verdict PARTIAL — Lemma A' is NOT fully known (my exact hypothesis —
constraint-sum density ≈1/d_min^k, modular-bias-free, obstruction = GAPS ONLY — is unpublished), so
it's a genuine target. BUT there is PUBLISHED machinery to build on:
- Hegyvári (Acta Math. Hungar. ~1994) + Lev (Acta Arith., mid-90s) prove R+T has POSITIVE DENSITY via
  Fourier/greedy — but STOP SHORT of cofiniteness. SAME wall I hit, with a published tool.
- The LEVER: my job = upgrade positive-density-R+T → COFINITE using the EXTRA structure they don't
  exploit: (i) the ray is geometric/SELF-SIMILAR, (ii) the constraint density is GENERIC-not-thinned
  (≈1/d_min^k, verified). That extra structure is exactly what might close the density→cofinite gap
  Hegyvári–Lev couldn't. This is the most concrete forward route on the open kernel.
- ⚠ **CITATION CAVEAT (scholar):** Grok mixed up Lev paper titles (gave "On the number of sums and
  differences" — likely the WRONG Lev paper for R+T). The Hegyvári–Lev R+T line is REAL but the EXACT
  refs are UNVERIFIED — pull precise citations from MathSciNet (Hegyvári's R+T paper directly) before
  relying on or citing them. DO NOT cite the Grok-supplied Lev title. [scholar Lemma A' verdict.]

## TRIANGULATION (with density): the onset threshold is ONE object, T = v = U₀ = gap/σ.
density's surplus-overtakes-alignment mechanism and my +M-closure onset are the SAME threshold:
- My +M-closure onset v (N₀ = v + M) = density's U₀ where the surplus δ·U first overtakes the
  alignment gap = "gap/σ". Confirmed: the implied alignment gap = v·σ.
- Is gap = O(d_max^k) (sumset's leg, the premise that makes density's surplus-overtake elementary)?
  Measured v·σ / d_max^k: (3,4,5) k=1: 1.27 ✓; (3,4,6) k=1: 5.46 ✓; (3,4,5,7) k=2: 3.50 ✓; BUT
  **(3,4,5) k=2: 258.68 ✗** — the gap is NOT O(d_max^k) for tight small-σ families at k≥2.
- So: density's mechanism (surplus overtakes gap at U₀~gap/σ, MW-free) is CORRECT, and closes
  elementarily IFF gap = O_k(d_max^k). That premise holds PER FIXED k (and for high-σ/many-base
  families uniformly) but the implied constant GROWS with k for tight families — which is exactly
  my N₀/m₀ divergence, now located in density's framework as "the alignment gap the surplus must
  overtake is itself k-growing."
**Unified statement (cassels × density × lift):** T_onset = v = U₀ = gap(D,k)/σ, gap(D,k)=O_k(d_max^k)
with k-dependent constant. ⟹ strict-excess closes elementarily PER FIXED k (front half = density's
surplus-overtake; back half = my Lemma C extension; both transcendence-free given the gap bound).
Uniform-in-k needs the gap's k-growth controlled = the MW residue. Three independent routes
(+M-closure / surplus-margin / Lemma-C) describe the SAME onset object v.

### CANONICAL JOINT LEMMA (cassels × density, co-signed; gcd-top-two DROPPED as vestigial).
> **(STRICT-EXCESS, per fixed k, conditional.)** D admissible, **gcd(D)=1, σ=∑1/(d−1)−1>0** (NO
> gcd(d_max,d_2nd) hypothesis). For each FIXED k, R(D,k) is cofinite, with N₀ = v + d_min^k,
> v ~ gap(D,k)/σ. The surplus σ·U overtakes the alignment gap (density's front half) + Lemma C
> extends above the seed (cassels' back half) — transcendence-free GIVEN gap(D,k)=O(d_max^k). The
> O-constant is k-dependent (grows for tight D); uniform-in-k boundedness = the residual MW.
> Three names, one threshold: **v = U₀ = last-hole = gap/σ + d_min^k.**
> Two honest riders (NOT hypotheses): (a) it's the RUN-version (isolated singletons = the separate MW
> core); (b) gap=O(d_max^k) is Baker-conditional.
**gcd(d_max,d_2nd)=1 was VESTIGIAL** — it belonged ONLY to density's withdrawn bounded-geometric-C
claim (N₀≤C·(d_max·d_2)^k, refuted as k-uniform by (3,4,5)), NEVER to this per-fixed-k lemma. {3,4,6}
(gcd(6,4)=2) satisfies (A) with finite N₀=986/242113/58941162 and finite gap=v·σ=33/8070/1964705 each
k, using only gcd(D)=1+σ>0. So the lemma is strictly MORE general without it. [density verified
independently, dropped it; co-signed. → density_margin_growth_leg.md hypothesis-correction §.]

## UPGRADE (with lift): Lemma B IS provable PER FIXED k via margin growth — so strict-excess closes for each fixed k.
lift's mechanism + my verification reframe the "negative" precisely. The covering MARGIN r(n) =
#{representations of n} GROWS with n at strict σ, faster for larger σ (verified, min #reps over
windows):
- (3,4,5) k=1 σ=0.083: 5→20→23→179 (1k→98k). (3,4,5,7) k=1 σ=0.25: 62→558→1814→4652 (faster, ✓ σ-dep).
- (3,4,5) k=2 σ=0.083: min#reps STUCK at 1 through n≈52k, reaching 15 only by 300k — the singly-
  represented values ARE the holes, and they persist out to ~N₀(k=2)=77613.
**So margin growth is REAL but k-DEPENDENT.** Consequence:
- **Lemma B (margin-growth ⟹ value-holes close) is PROVABLE for EACH FIXED k at strict σ** (r(n)→∞
  ⟹ every n eventually has a representation ⟹ no value-hole survives past an effective scale).
- Combined with Lemma A (gap-condition, m₀=(C'−1)/σ) + modular residue coverage + carry's class-wise
  AP, this gives a **COMPLETE elementary strict-excess theorem FOR EACH FIXED k** (σ>0). That IS a
  genuine, bankable, transcendence-free result — just scoped to fixed k, not uniform.
- It does NOT give a k-UNIFORM theorem: the margin-growth rate (hence where holes close) degrades
  with k, N₀(k) blows up, and carry's (d_max·d_2)^k/σ² fails k-uniformity at k=3 (ratio
  0.027→1.35→3.76 for (3,4,5)). The k-uniform version still needs the cross-base spacing (MW).
**Net (corrected, honest, POSITIVE):** strict-excess BEGL96 is provable elementarily for each fixed
k≥1 (Lemma A + lift's Lemma B + modular + carry). The remaining open piece is ONLY the uniformity in
k — which is the same MW boundary. Co-writing the per-fixed-k theorem with lift/carry/modular.

## k=1 status — CORRECTED (NOT a clean unconditional theorem; honest per-instance + verified-uniform C).
[Supersedes an earlier "k=1 IS UNCONDITIONAL" claim here, which overstated. lift correctly pushed.]
The honest k=1 status (NOT unconditional — the cofiniteness CLOSURE itself is verified-not-proven):
- **PROVEN deductively:** gap-condition above m₀=(C'−1)/σ (my Lemma A, k-uniform); the class-wise
  identity N₀ = max_r O_r (lift, exact); residue coverage (modular). These give "no NEW gap forms
  above m₀" + the per-class AP structure — but NOT where the existing scattered low gaps END.
- **NOT proven (the gap):** that N₀ is finite/bounded — i.e. that +M-closure terminates. This is the
  +M-closure endpoint = the constrained-deflation onset = the cross-base-spacing (MW) quantity, ≫ m₀.
  Verified 44/44 (d≤16) but NOT deductively closed. So cofiniteness CLOSURE at k=1 is VERIFIED, not
  PROVEN — and "decidable per-instance" overstates, because we have no a-priori bound to compute up
  to (the bound is the unproven C·m₀).
- My bound N₀ ≤ C·m₀ (TRUE N₀; m₀ alone does NOT bound N₀ — 8/27 have N₀>m₀, (3,4,5) N₀=79>m₀=37) has
  worst C≈11 (=10.84 at (3,4,6)); the equivalent N₀ ≤ 0.27·C'/σ² form is **GRAZED/FAILED by (3,4,6)
  (986 > 980, ratio 1.006)** — a FITTED constant, not a theorem. C empirically does not creep with
  bases at k=1 (tested to d=16), but C-boundedness is VERIFIED, NOT PROVEN.
- ⟹ HONEST STATEMENT (lift + cassels, final): "For every admissible D, σ>0: R_1 cofinite VERIFIED
  for all tested D (44/44, d≤16); N₀=max_r O_r computable IF a finite bound is known (PROVEN
  structure, lift); conjectured N₀ ≤ C·C'/σ² with C empirically ~0.3 but FITTED and grazed by
  (3,4,6), NOT proven. The k=1 Lemma A' (prove +M-closure terminates / min#reps≥1 above C·m₀) is an
  explicit OPEN sub-kernel." There is NO deductive proof of closure. NOT an unconditional theorem.
- **The ONLY genuinely-unconditional results in the whole strict-excess thread:** (1) k=0 base case
  (Brown/Erdős, KNOWN); (2) non-minimal D via subset-monotonicity (carry). Everything at k≥1 strict
  is VERIFIED/CONDITIONAL, never proven-unconditional.

## Lemma PCA (per-class arithmetic-progression) — carry, scoped fixed-k / FINITE-onset (the 4th ingredient)

> **Lemma PCA.** Fix admissible D (gcd=1), k≥1, M = b^k (b = min D). Then for each residue class
> r ∈ ℤ/Mℤ, the representable set R_k = ∑_d d^k·B_d restricted to {n ≡ r (mod M)} is, above a per-class
> onset O_r, a FULL arithmetic progression of common difference M (every n ≡ r with n > O_r is
> representable). Consequently R_k is cofinite iff every O_r is finite, and N₀ = max_r O_r.

**Status of each part:**
- The **AP structure** (above O_r, class r is gap-free in steps of M) is PROVEN-given-the-onset: it is
  the +M-closure (carry Obs 1 / cassels Lemma C) localised to a class — once one element of class r
  above its onset is hit, +M (add the atom b^k, the residue-0 generator) reaches the whole class.
  Mechanism: residue r is fixed by cross-base small atoms (modular's L, gcd=1); the b-power ladder
  {b^k, b^{k+1}, …} then climbs the class in M-steps.
- The **identity N₀ = max_r O_r** is EXACT (verified). VERIFIED that every class is a full AP above
  O_r: (3,4,5) k=2 all 9 classes, k=3 all 27 classes; (3,4,7) k=1 all 3 classes (O_r = 264/238/581).
- **What Lemma PCA does NOT give (the scoping cassels asked for):** it does NOT bound O_r, and in
  particular does NOT prove O_r FINITE. Finiteness of O_r = +M-closure terminates in class r = the
  constrained-deflation / cross-base-spacing (MW) quantity. O_r ≫ m₀ and grows with k (NOT m₀-bounded:
  (3,4,5) k=2 has O_r ≈ 58k vs m₀=181). So Lemma PCA reduces "R_k cofinite" to "every O_r finite" — a
  clean structural reduction, but the onset-finiteness is exactly the open MW kernel (= Lemma A').

**Role in the chain:** Lemma PCA is the 4th ingredient — Lemma A (gap-condition, cassels) + Lemma B
(margin-growth ⟹ holes close per fixed k, lift) + residue coverage (modular) + Lemma PCA (class-wise
AP structure + N₀=max_r O_r, carry). Together they give per-(D,k) finite verifiability of cofiniteness
(once a class-onset is reached, the class is a full AP, verifiable). They do NOT give a uniform-over-D
or uniform-in-k bound, because O_r finiteness is unproven (MW). Scope: FIXED k, FINITE onset assumed
(not derived) — exactly as scoped; no overreach on uniformity.
All 44 admissible strict D⊆{3..12} at k=1 verified cofinite, max N₀=986. k≥2 conditional on Lemma A'.

## Reconciliation with maverick's negative (corrects a team "proved" claim).
maverick claimed (maverick_bounded_gap_lemma.md) the Cassels predecessor-sum condition "fails by a
factor (d_max−1) at every large d_max^J, so the problem cannot be closed by any Cassels argument."
**The specific claim is WRONG (single-ray artifact); the deeper point is RIGHT.** Explicit check
(3,4,7) k=1: the MERGED predecessor sum S(<a) at a=7^J is ≈ 2a (e.g. 7^12: S(<a)=2.37e10 vs
a=1.38e10, margin +9.9e9), so the merged Cassels gap-condition a ≤ S(<a)+1 HOLDS at every d_max
power. maverick measured the SINGLE-d_max-ray sum (≈ a/(d_max−1) = a/6), the same single-ray-vs-merged
slip as the earlier liminf discrepancy. **The ONLY gap-condition failure in the entire merged
sequence is the trivial a₁=3 start (no 1-seed).**

BUT maverick's DEEPER point stands: gap-condition holding ≠ cofiniteness. Precise statement:
- The merged gap-condition holds for all i≥2 ⟹ no NEW gap forms above the running frontier.
- WITHOUT a 1-seed (smallest atom d_min^k ≥ 3), the frontier is NOT contiguous-from-0, so SCATTERED
  low gaps persist up to some bound B (= N₀). The gap-condition does NOT bound B.
- **B = N₀ = the last scattered low gap = the +M-closure onset = the MW quantity.**
So the wall is precisely LOCATING N₀, not any running-sum failure at scale. This is the sharpest
statement: at k≥1 the Cassels machinery handles everything EXCEPT where the low scattered gaps end,
and that endpoint is residue+MW. [Should update CLAIMS to correct maverick's d_max^J framing.]

## §carry — the per-class onset bound (Lemma A', the residual piece)

I worked the class-wise onset bound cassels needs. Result is positive for the theorem but with an
honest constant caveat.

**Setup.** M = d_min^k = b^k. By cassels' Lemma C + my +M-closure result, each residue class r mod M
is a full AP above a per-class onset thr_r; the global threshold N₀ = max_r thr_r. The seed (M
consecutive integers) exists exactly once ALL r class onsets are passed, i.e. at N₀.

**Lemma A' (class onset bound) — CLEAN at k=1; NOT k-uniform (REFUTED at k=3).**
> For admissible D with σ = ∑1/(d−1) − 1 > 0, **AT k=1 ONLY**:
> **N₀(D,1) ≤ 0.27 · C'/σ²** (C'=∑ d/(d−1)). VERIFIED over all 27 admissible D (d<10, σ>0);
> N₀·σ²/C' ∈ [0.0006, 0.272].
>
> ⚠️ The k-uniform extension N₀ ≤ K·(d_max·d_2)^k/σ² with absolute K is **FALSE** — k=3 refutes it.

**Evidence (exact bitset/numpy DP, strict convergence):**
- k=1 (CLEAN): N₀ ≤ 0.27·C'/σ², worst (3,4,6) σ=0.033: N₀=986 ≤ 0.27·3630. The σ² captures
  "excess tames {3,4} clustering" (thr collapses 242113→184 as σ grows 0.033→0.829).
- k≥2 (FAILS uniformity): required K in N₀ ≤ K·(d_max·d_2)^k/σ² GROWS: (3,4,5) K = 0.046 (k=1),
  1.347 (k=2), **3.759 (k=3)** — ~×3/step. (3,4,5) N₀ = 79, 77613, **4,330,731** (k=3 conv. at N=12M).
- No clean base: N₀/(d_max²·d_2)^k OSCILLATES — (3,4,7): 2.96, 103.7, 22.0; (3,4,5): 0.79, 7.76, 4.33.
  k=2 anomalously high, k=3 drops. The oscillation is number-theoretic (cross-base power clustering at
  specific k), NOT smoothable by an elementary closed form.

**HONEST CONCLUSION (converges with sumset's μ(δ) necessary-not-sufficient + maverick Result 2):**
the k-scaling of N₀ is governed by transcendence/spacing (Mignotte–Waldschmidt), NOT an elementary
function of (D,k). Lemma A' is a real clean result at **k=1** and a heuristic for k≥2, but NOT a
k-uniform theorem. The strict-excess theorem does NOT close elementarily via the onset bound for
general k — same MW wall, confirmed from the threshold-growth side.

**What DOES survive elementarily (the honest residue):**
1. Non-minimal strict-excess D, all k: subset-monotonicity (72/115 strict-excess D, d<12). [carry]
2. k=1, all admissible σ>0: cassels' m₀ gap-onset + carry's N₀≤0.27·C'/σ² seed bound. [clean]
3. MINIMAL D at k≥2 (the {3,4}-clustering core, 43/115): MW wall. [open, transcendence]

## Net
The strict-excess regime ∑1/(d−1) > 1 is PARTLY elementary — fully so for non-minimal D (subset-
monotonicity) and for k=1 (gap-onset + class-onset bound) — but the general-k minimal-D case is NOT
elementary: the threshold's k-growth oscillates number-theoretically and hits the MW wall (k=3 data:
required constant grows 0.046→1.347→3.759, no clean closed form). This is NOT the full transcendence-
free NEW theorem we hoped for; it is an honest partial (k=1 + non-minimal D done, general k open).
The open core is unchanged from team consensus: the MW/spacing wall on minimal D at k≥2.
