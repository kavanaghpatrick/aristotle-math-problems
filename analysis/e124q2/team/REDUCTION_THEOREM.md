# REDUCTION_THEOREM.md — The E124 (BEGL96) Reduction

**Squad primary deliverable.** Authors: cassels (compiler), building on sumset, modular, lift,
maverick, carry, troika, scholar, breaker, density. Status: CHECKPOINT (review-ready core; TODOs
marked). Purpose: (A) paper-grade writeup "the BEGL96 conjecture reduces to one local Diophantine
condition"; (B) formalization package for adjudication.

The open target (formal-conjectures `124.lean`, `erdos124.ne_zero`):
> For every k≠0 and finite D={d_1<…<d_r}, all d_i≥3, with ∑_{d∈D} 1/(d−1) ≥ 1 and gcd(D)=1:
> every sufficiently large n lies in `∑_{d∈D} sumsOfDistinctPowers d k` (pointwise sumset).
> Answer (True/False) is itself unknown. Squad verdict: **almost certainly TRUE**.

Notation: `B_d := {0/1-digit numbers base d} = sumsOfDistinctPowers d 0`. `R(D,k) := ∑_{d∈D} d^k·B_d`
(the target sumset). `β := ∑_{d∈D} 1/(d−1)` (harmonic mass). `b := min D`, `M := b^k`.
`A(D,k) := {d^j : d∈D, j≥k}` (the merged atom multiset). `N₀(D,k)` = largest non-representable n.

Corrected constants used throughout (breaker N=1B + cassels N=700M; supersede all earlier numbers):
**(3,4,7): N₀(k=1)=581, N₀(k=2)=3,982,888, N₀(k=3)=166,025,260.** BEGL96 errata (§5): 79/112/17.

---

## PART 1 — THE PROVEN STACK (one coherent chain)

### Theorem 1 (Scaling). For all d,k:  `sumsOfDistinctPowers d k = d^k · B_d`.
Hence `R(D,k) = ∑_{d∈D} d^k·B_d`. [ELEMENTARY/Lean-ready — sumset, troika; proof = reindex
exponents j↦j−k, a bijection on {j≥k}.]

### Theorem 2 (Atom reformulation). If the values {d^j : d∈D, j≥k} are pairwise distinct, then
`R(D,k)` = subset-sums of the multiset A(D,k), each atom used ≤ once.
[ELEMENTARY/Lean-ready for the distinct-value case — cassels, verified 0 differences (3,4,7) on
[0,200000]. TODO: handle cross-base value collisions in general D (rare; e.g. could two d_i^a=d_j^b?
For multiplicatively independent bases never; for {d, d²,…} possible). Mark: needs a
distinct-values hypothesis or a multiset-aware statement.]

### Theorem 3 (Residue coverage ⟺ gcd=1). For gcd(D)=1, every k≠0, every modulus m:
`R(D,k) ≡ ℤ/m` (hits every residue). Conversely gcd(D)=g>1 ⟹ R(D,k) ⊆ (smallest prime p|g)·ℤ,
missing all residues ≢0.
[**MACHINE-PROVED in Lean (Aristotle, Jun 10 2026)** — sorry-free, standard axioms, exact iff:
`submissions/results_jun10/residue_coverage_x/…/RequestProject/Main.lean` (`erdos124_residue_coverage`).
CANONICAL PROOF = the **SUBGROUP** argument, NOT per-prime+CRT recombination (Aristotle caught a real
flaw in modular's Step-3 CRT recombination: a single base's contribution leaks into the other CRT
blocks and cannot be forced to vanish there). Correct argument: H = ∑_d (d^k·B_d mod m) is a submonoid
of finite ℤ/m hence a **subgroup**; gcd=1 gives, for each prime p|m, a base d_p with p∤d_p whose
contribution d_p^k mod m ∈ H is ≢0 mod p (per-prime witness); a subgroup of cyclic ℤ/m hitting a
non-multiple of every prime p|m must be all of ℤ/m. **DO NOT use the refuted "Lemma A" (CRT product
form) NOR the CRT-recombination Step 3 — both wrong; the subgroup route is canonical and formalized.**
Hypotheses d≥3 and D-nonempty are UNNECESSARY for residue coverage (holds for arbitrary finite D,
any k≠0).]

### Theorem 4 (Deconvolution / recursion). `R(D,k) = C_k + R(D,k+1)` where
`C_k = {∑_{d∈D} e_d d^k : e_d∈{0,1}}` (2^|D| offsets). Consequences: `R(D,k+1) ⊆ R(D,k)` (monotone,
so N₀ non-decreasing in k); no finite-N computation settles the conjecture (the answer is a
statement about all k). [ELEMENTARY/Lean-ready — maverick, sumset; from B_d = d·B_d ⊔ (1+d·B_d).]

### Theorem 5 (gcd necessity). gcd(D)=g>1, k≥1 ⟹ R(D,k) ⊆ g'^k·ℤ (g'=any prime|g) ⟹ NOT cofinite.
[ELEMENTARY/Lean-ready — sumset/troika/carry/modular all independently; every atom d^k divisible
by g'^k.]

### Theorem 6 (Lemma C — step-M completeness criterion). R(D,k) is cofinite ⟺ its +M-closure
failures are finite (M=b^k). Quantitatively: **N₀ = v + M, where v = max{n : n∈R, n+M∉R}** (the
largest gap is the last +M-closure failure, lifted by one step M).
[ELEMENTARY/Lean-ready — cassels; the forward induction (M consecutive present + eventual +M-closure
⟹ cofinite) is a trivial residue-class induction. Threshold identity verified exactly on 7 families.]

### Theorem 7 (Side-condition mapping). The two hypotheses of Lemma C correspond exactly to the two
side conditions, and they are independent:
- **gcd(D)=1 ⟺ (a)** eventually M consecutive integers all reachable [residue coverage];
- **β ≥ 1 ⟹ (b)** +M-closure eventually holds [density]. **NOTE the implication direction:** (b)
  is the +M-closure condition; β≥1 is the *necessary precondition* (the merged-atom Cassels
  partial-sum condition inf T(x)/x ≥ 1, T(x)=∑ atoms < x), NOT an equivalence. (b) is STRICTLY
  STRONGER than inf T(x)/x ≥ 1 — the gap between them is exactly the granular hole-filling that
  needs MW/Baker (troika: Cassels partial-sum test fails only ONCE for (3,4,7), at atom 3, yet
  N₀=581; partial-sum dominance does NOT fill specific skipped VALUES). [lift correction, decisive.]
[COMPUTED, control-family independence proved — cassels + carry re-verified: gcd=3 & gcd=2 families
give max-consecutive-run = 1 (fails (a)) at any β; (3,5,9) β<1 gives +M violations arbitrarily high
(fails (b)) with full residue coverage. So the conditions are orthogonal: (a) maps to gcd=1, (b)'s
NECESSARY precondition maps to β≥1, but (b) itself carries the residual MW content. (a)=lift's (R);
(b)=lift's (A). Do NOT state (b) as equivalent to the density/partial-sum condition.]

### Theorem 8 (Bulk bounded-gap, Lemma BG). β≥1 ⟹ sorting A(D,k) ascending, the running sum
satisfies T_n ≥ next_atom past a tiny transient ⟹ R(D,k) has all gaps ≤ G(k) ≍ d_min^k.
[ELEMENTARY/Lean-ready as a BOUNDED-GAP statement — maverick. **WARNING (maverick, proved): this
does NOT give cofiniteness.** Bounded gaps + all residues hit does NOT imply cofinite. The step
"gap ≤ G ⟹ gap = 1" is the open core. Do not claim "BG + Theorem 3 ⟹ done"; that inference is
INVALID.]

### Theorem 9 (Supercritical liminf, the analytic constant). Let T(x) = ∑ of atoms of A(D,k) that
are < x. Then `liminf_{x→∞} T(x)/x = β` asymptotically (Weyl equidistribution; bases multiplicatively
independent). Finite-range inf sits slightly ABOVE β and is approached slowly: by EXACT integer
arithmetic (lift, atoms to 5^120, no float) the true inf for {3,4,5} is ≈ **1.10** > β=1.083; in
general inf T(x)/x ≥ β. So inf T(x)/x > 1 ⟺ β > 1 (at the boundary β=1, inf → 1).
[ELEMENTARY-ish/Lean-HARD — lift (lift_cassels_liminf_theorem.md, corrected header). Uses
Weyl/equidistribution (heavy in Mathlib). **Consequence + CRITICAL CAVEAT:** the merged-atom Cassels
PARTIAL-SUM condition `a' ≤ 1+T(a')` holds eventually ⟺ inf T(x)/x ≥ 1 ⟺ β ≥ 1. BUT this
partial-sum/density condition is **NECESSARY, NOT SUFFICIENT** for cofiniteness (troika: it fails
only once for (3,4,7), at atom 3, yet N₀=581 — partial-sum dominance does not fill specific skipped
values). So β=1 is the threshold for this *necessary precondition* from both the Pomerance-necessity
side and this sufficiency-of-the-precondition side — a clean phase transition at β=1 — but Lemma C's
condition (b) is strictly stronger and carries the residual MW content. Do NOT conflate "inf T(x)/x≥1"
with "cofinite."]

### Theorem 10 (Average representation count diverges — the elementary supercritical fact). Let
r_D(n) = #{ (b_d)_{d∈D} : b_d ∈ B_d, ∑_d d^k b_d = n } be the representation count. Let e_d = log2/log d
be the counting exponent of B_d (|B_d ∩ [0,X]| ≍ X^{e_d}). Then:
> **(a) [PROVED, elementary — clean Lean-able form] e_d > 1/(d−1) for every d ≥ 3.** Proof:
>     log2/log d > 1/(d−1) ⟺ (d−1)·log2 > log d ⟺ **2^{d−1} > d**, which holds for all integers d ≥ 3
>     (trivial induction: 2^d = 2·2^{d−1} > 2d > d+1 for d ≥ 2; strict for d ≥ 3, equality at d=2). No
>     calculus, no floats — reduces to a Nat inequality. Hence **∑_d e_d > ∑_d 1/(d−1) = β ≥ 1** for
>     every admissible D — STRICTLY, even at the boundary β=1 (e.g. (3,4,7): ∑e_d=1.487, ε:=∑e_d−1=0.487).
> **(b)** The CUMULATIVE average of r_D over [0,X] — (total #reps of n≤X)/X = ∏_d|B_d∩[0,X/d^k]|/X —
>     is ≍ X^{ε}, ε>0, and ε is k-INDEPENDENT (cassels: log-log slope 0.521 (k=1), 0.520 (k=2) for
>     (3,4,5)≈ε=0.562). So **the cumulative average #reps → ∞ for every admissible D**, uniformly in k,
>     NO transcendence. (Use the cumulative/including-zeros average; the present-only window average is
>     dip-contaminated and is a DIFFERENT, non-k-independent quantity — cassels' convention.)

[ELEMENTARY — lift (lift_box_reformulation.md). The COUNTING/box-dimension exponent log2/log d (governing
#reps) strictly exceeds the COMPLETENESS/Astels-thickness invariant 1/(d−1) (governing cofiniteness) —
that gap is why the count is comfortably supercritical even when completeness is exactly critical (β=1).
**CAVEAT:** bounds the cumulative AVERAGE, not the MINIMUM; min r_D dips at power-coincidences ((3,4,7)
min/avg → 0.13 near the k=2 straggler ~4·10⁶). Cofiniteness needs min r_D ≥ 1 — the open core (Part 2).
**Prior-art (scholar verdict — present MODESTLY):** the inequality e_d>1/(d−1) is FOLKLORE (one-line
convexity); "avg supercritical, min dips" is recognized-but-unnamed (cite Erdős–Tetali, Erdős–Fuchs as
nearest on r(n) behavior); the GENUINELY NEW bit is the box-dimension-vs-Astels-thickness CONTRAST for
{B_d}, unmade in prior work. Frame as a clarifying elementary observation whose value is the synthesis.]

---

## PART 2 — THE OPEN CORE (one canonical statement; four equivalent forms)

> **CANONICAL OPEN CORE.** For admissible D (gcd=1, β≥1) and every k≥1: R(D,k) has only finitely
> many gaps. Equivalently (Theorem 6): the +M-closure failures are finite. Equivalently: there is
> ONE contiguous block of representable integers of length ≥ (the largest atom below it).

The four forms circulating in the squad and their relationship:
- **cassels (finite +M-closure failures)** [Theorem 6]: N₀ = v+M; cofinite ⟺ v finite.
- **maverick (★) / (SEED)** [maverick_seed_interval_pinned.md, sumset_deconvolution_reduction.md]:
  ∃ a contiguous representable block of length ≥ next-atom ⟹ full subset-sum is gap-free above it.
- **sumset (SEED) deconvolution**: R(D,k)=C_k+R(D,k+1) plus one gap-free seed propagates by the
  offset set C_k.
- **lift (KERNEL — the counting form)** [lift_box_reformulation.md]: cofinite ⟺ **min_n r_D(n) ≥ 1
  for all n > N₀**, where r_D is the explicit representation-count of Theorem 10. By Theorem 10 the
  AVERAGE of r_D → ∞ (PROVED, elementary), so the open content is exactly that the MINIMUM does not
  dip to 0 — equivalently, that min_{[X,2X]} r_D / avg_{[X,2X]} r_D stays bounded below as X→∞. This
  is the sharpest form: a single explicit, elementary counting function whose average provably
  diverges; the conjecture is that its minimum stays positive. **MW's role is transparent here:** it
  is exactly the bound on how deep r_D dips at the cross-base power-coincidences {3^p≈4^q≈7^r}. (The
  dips are real and verified — (3,4,7) min/avg → 0.13 at the k=2 straggler — so this is genuinely the
  same difficulty as the other three forms, now stated as "minimum of a divergent-average counting
  function," which is the most paper-ready and the most directly analytic-attackable.)

**Equivalence status [TODO — needs sumset + maverick sign-off]:** All four say "the gaps stop."
(lift's KERNEL: min r_D ≥ 1 ⟺ no n is a gap ⟺ no +M-failure above N₀ ⟺ the seed exists — trivially
equivalent as STATEMENTS; its value is the explicit divergent-average counting handle, not a new condition.)
cassels's form is the sharpest LOCAL statement (pins the exact threshold to the last +M-failure).
maverick's (SEED) is the sharpest CONSTRUCTIVE statement (a single sufficiently-long block).
I (cassels) believe they are equivalent: a contiguous block of length ≥ M with +M-closure above it
⟺ finite +M-failures ⟺ gap-free tail. The block-length-vs-M reconciliation: maverick's "≥ next
atom" is stronger than Lemma C's "≥ M" because at a power of d_max the next atom can be a large jump
(see Part 3). **ACTION: sumset + maverick verify these are the same condition, or flag the
inequivalence as a finding.** (Provisional: maverick's is sufficient; cassels's is exact; they agree
on admissible D in all computed cases.)

---

## PART 3 — THE HONEST FRONTIER (why the core is open)

**The single-pass Cassels/Birch running-sum argument provably does NOT close this.** [maverick,
troika, carry — converged.] Reasons, made precise:

1. **β is NOT >2 reachable.** [carry] BEGL Claim 1 needs a finite power-chunk with harmonic mass
   >2. The TOTAL mass of all atoms of a single admissible D is exactly β ∈ [1,2) at k=1 (and
   0.27–0.42 at k=2). So Claim 1's density engine never reaches its own threshold in our regime —
   boundary OR strict-excess. (Smallest D with total mass >2 is the 10-base {3,…,12}, and that
   collapses below 2 at k≥2.)

2. **The merged predecessor sum dips below the jump at every power of d_max.** [maverick/cassels
   reconciled] DISCREPANCY RESOLVED: lift's `liminf T(x)/x = β` (over continuous x) and maverick's
   `inf = 1/(d_max−1)` are DIFFERENT quantities. `1/(d_max−1)` is the contribution of the **d_max-ray
   ALONE** at x=d_max^J (verified: exactly 0.1667 for d_max=7); the MERGED sum there is ≈2.1 and the
   continuous liminf is β. **The Cassels condition uses the MERGED sum, governed by β (lift correct).**
   BUT at x=d_max^J the next atom can be another large d_max-power with no cross-base atom between, so
   the JUMP (not the predecessor sum) can exceed the budget — a LOCAL Cassels failure recurs at every
   scale, each repaired only by multi-atom (cross-base) combinations. So Cassels-single-append fails
   infinitely often; cofiniteness is a genuine multi-atom subset-sum phenomenon.
   [TODO: state this as a clean lemma "merged-Cassels-append fails at d_max^J i.o." — maverick has it.]

3. **The surviving isolated gaps are cross-base power coincidences.** [carry, troika, scholar] The
   late gaps (e.g. (3,4,7) k=1: 264, 521, 581) sit where powers of different bases nearly collide
   (3^p ≈ 4^q). Killing them = lower-bounding |d_i^a − d_j^b| = **Mignotte–Waldschmidt / Baker
   linear-forms-in-logarithms**. BEGL96 closed the SINGLE triple (3,4,7) k=1 exactly this way (their
   |3^p−4^q| bound + finite check to 581). Not in Mathlib; not bare-submittable.

4. **Scholar's non-uniformity guardrail.** [scholar_BEGL96_proof_dissected.md, scholar_upstream_
   overclaim_report.md] MW provably cannot do the general ∀D case: the MW constants grow with the
   base heights, and you'd need infinitely many per-D finite checks. So even the transcendence route
   does not uniformly close the conjecture — it closes one D at a time.

**The strict-vs-boundary question [unresolved within the squad — record both positions]:**
- lift/cassels (early): split β>1 (density-tractable) vs β=1 (transcendence-hard).
- carry/troika (refinement): the real split is whether D contains a near-colliding base pair
  (3^p≈4^q type), which is MW-hard REGARDLESS of harmonic slack; β=1.033 (3,4,6) has threshold 986 >
  β=1.000 (3,4,7) threshold 581, so strict excess does NOT monotonically ease it.
**RESOLUTION (cassels, provisional):** β>1 strict gives liminf T(x)/x>1 (Theorem 9), so the merged
predecessor sum eventually EXCEEDS x with a fixed margin (β−1)x — this kills the bulk failures, but
the ISOLATED cross-base-coincidence gaps can still occur until the margin (β−1)x exceeds the worst
jump d_max. So strict β>1 is provably cofinite ONCE x > x₀(β, d_max) AND no cross-base coincidence
sits above x₀ — the latter still needs a (weaker, non-tight) spacing input. Boundary β=1 has zero
margin so needs the tight MW bound everywhere. **Honest: strict is "easier" (finite explicit x₀
suffices for the bulk) but not trivially elementary; boundary is genuinely MW-hard.** [TODO: lift to
sign off that Theorem 9's margin closes the bulk for β>1; quantify the residual spacing requirement.]

### PART 3b — OPEN LEVERS / FUTURE WORK (for a future campaign or human reader)

The open core (Part 2: the per-class constrained-deflation onset / Lemma A' / the MW kernel) is NOT
being attacked further in this campaign — the hardness verdict is final (~8× independently confirmed:
every route reduces to Mignotte–Waldschmidt at the convergent arcs). We record the single most
concrete forward lever here so it can be picked up later with full context.

**LEVER — the Hegyvári–Lev "R+T" upgrade route.** [scholar Lemma A' prior-art verdict: PARTIAL.]
- *The lever (statement).* Lemma A' is exactly an "R+T" reachability question: R = a geometric base-d
  0/1-digit ray (self-similar), T = the (positive-density) set of constraint-satisfying non-d_min
  sums. The published **Hegyvári–Lev R+T line** (Hegyvári, Acta Math. Hungar. ~1994; Lev, Acta Arith.,
  mid-1990s) studies exactly this R+T object and proves R+T has **POSITIVE DENSITY** via Fourier/greedy
  methods.
- *Why it's plausible as a closer.* Our case has TWO pieces of extra structure the general Hegyvári–Lev
  setting does not exploit: (i) the ray R is **geometric / self-similar** (the T_k=C_k+T_{k+1}
  recursion), and (ii) the constraint density is **GENERIC, not thinned** (≈1/d_min^k, verified — the
  obstruction is gap-structure, NOT arithmetic avoidance). Upgrading their **positive-density → cofinite**
  using exactly this extra structure is the concrete open problem. The generic-density fact is the
  lever: it is the precise extra hypothesis that distinguishes our R+T from their general-T setting.
- *Exactly where scholar's assessment says it stops.* Hegyvári–Lev get positive density and **STOP
  SHORT of cofiniteness** — the same density→cofinite wall this whole document maps. So the lever does
  NOT by itself close Lemma A'; it provides published machinery to BUILD on rather than reinvent. The
  remaining work (positive-density + self-similar-ray + generic-constraint-density ⟹ cofinite) is
  unpublished and is the genuine target.
- ⚠ **CITATION CAVEAT.** The exact Hegyvári/Lev references are UNVERIFIED (a Grok-supplied Lev title
  "On the number of sums and differences" is likely the WRONG paper). Pull the precise citations from
  MathSciNet — Hegyvári's R+T paper directly — BEFORE citing or relying on them. The R+T line is real
  (Hegyvári's completeness work confirmed); only the exact refs need pinning. Step 1 of any future
  attack = pull the verified Hegyvári R+T paper; that is the most likely place a usable upgrade lemma sits.

(Other recorded routes that all reduce to the same wall, NOT pursued: troika's renormalization on the
T_k recursion — cell-state mod d_min^s is unbounded/non-automatic [maverick V2 death]; uniform
Fourier/circle-method on the digit indicator [Mauduit–Rivat / Maynard], multi-base decorrelation
unwritten; multiplicative-spread / S-unit, controls the wrong object. See scholar_prior_art_new_math_routes.md.)

---

## PART 4 — FORMALIZATION PACKAGE (lemma-by-lemma, Mathlib granularity)

| # | Lemma | Status | Mathlib needs |
|---|---|---|---|
| 1 | Scaling S(d,k)=d^k·B_d | [ELEMENTARY/Lean-ready] | Finset.sum reindex, pow_add |
| 2 | Atom reformulation (distinct case) | [Lean-ready w/ distinct-values hyp] | Finset subset-sum = sumset |
| 3 | Residue coverage gcd=1 (SUBGROUP argument) | [**MACHINE-PROVED**, Aristotle Jun 10] | ZMod, AddSubgroup of cyclic, orderOf (NOT CRT-recombination — refuted) |
| 4 | Deconvolution R(D,k)=C_k+R(D,k+1) | [ELEMENTARY/Lean-ready] | Set pointwise add, B_d digit split |
| 5 | gcd necessity | [ELEMENTARY/Lean-ready] | dvd, Finset.sum_dvd |
| 6 | Lemma C + threshold identity | [ELEMENTARY/Lean-ready] | Nat induction on residues mod M |
| 7 | Side-condition mapping | [COMPUTED; (a),(b) each Lean-ready given 3,6] | composition of 3 & 6 |
| 8 | Bounded-gap BG | [ELEMENTARY/Lean-ready as bounded-gap ONLY] | geometric series bound; NOT cofiniteness |
| 9 | liminf T(x)/x = β | [needs Weyl equidistribution] | Mathlib equidistribution (partial); HARD |
| — | OPEN CORE (finite gaps at β=1) | [needs Baker/MW — NOT in Mathlib] | linear forms in logs; per-D finite check |

**Adjudication-ready sub-package (fully elementary, no transcendence):** Theorems 1–8. These
establish: *the conjecture is equivalent to the finiteness of +b^k-closure failures, the two side
conditions are exactly the two hypotheses needed, and the bulk gaps are bounded.* This is a
publishable reduction. The ONLY non-elementary residue is the open core (isolated cross-base
coincidence gaps), which is Baker territory and is HONESTLY the same obstruction BEGL left in 1996.

---

## PART 5 — BEGL96 ERRATA & UPSTREAM (verified, for the writeup)
- BEGL96 §3 prints THREE wrong s=1 constants (cassels+scholar, two engines agree): (3,4,5) 78→**79**;
  (3,5,7,13) 111→**112**; (3,6,7,13,21) 16→**17**. (3,4,7)=**581** correct. Use the corrected values.
- BEGL96 proves (3,4,7) for **s=1 ONLY** (verbatim: "largest integer not in Σ(Pow({3,4,7};1)) is
  581"); "for any s" is only in the CONJECTURE. So `124.lean erdos124.ne_zero_three_four_seven`
  (all k≠0, tagged `research solved`, attributed [BEGL96]) is an **OVER-CLAIM**. Empirically true
  (cassels verified k=2,3 cofinite) but not a published BEGL result for k≥2.
  [scholar_upstream_overclaim_report.md — DO NOT file upstream without user approval.]

## OPEN TODOs IN THIS DOCUMENT
- [ ] Part 1 Thm 2: general cross-base-collision handling (or state distinct-values hypothesis).
- [ ] Part 2: sumset + maverick sign off that (finite +M-failures) ≡ (SEED) ≡ (★), or log inequivalence.
- [ ] Part 3 strict-vs-boundary: lift confirms Theorem 9 margin closes the β>1 bulk; quantify residual.
- [ ] Part 3 item 2: maverick supplies the clean "merged-Cassels fails at d_max^J i.o." lemma statement.
- [ ] Incorporate (lead's reconciliation list): troika multiplicative-independence lemma (every
      admissible D has an independent pair ⟹ MW always available); scholar prime-tower collinearity
      bound (mass ≤0.682, hard case localized to {2,3}/{2,5}/{3,5}-smooth); breaker coverage-lag c +
      threshold law d_max^{(1+o(1))k}; density's contribution. [Sections stubbed; pull from their files.]
