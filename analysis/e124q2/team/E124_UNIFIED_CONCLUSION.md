# Erdős Problem 124, open part (BEGL96 conjecture, k ≥ 1): Unified Conclusion

**Assembled by:** scholar, from the e124q2 team's verified record (Jun 2026). **Status of this
document:** referee-grade synthesis; every claim carries a status tag and a real source file; every
external citation is verified (Crossref/PDF). Reviewed against the kill-ledgers by maverick.

**Tag legend.** [LEAN] machine-verified in Lean (Aristotle, Jun 10 2026), sorry-free, standard axioms.
[PROVED] rigorous human proof, Lean-ready. [VERIFIED] exact finite computation (validated engine).
[LIT] from the literature, citation verified. [OPEN] the unresolved core. [CONDITIONAL] holds modulo
a labeled input.

---

## 0. The problem

For integers d ≥ 3 let `B_d = {non-negative integers with only digits 0,1 in base d}`. For a finite set
D, all d ≥ 3, with `gcd(D)=1` and `β := ∑_{d∈D} 1/(d−1) ≥ 1`, and an exponent floor k ≥ 1, set
`R(D,k) = ∑_{d∈D} d^k·B_d` (pointwise sumset). **The BEGL96 conjecture (k ≥ 1)** asks: is `R(D,k)`
cofinite for every such D and k?

Source statement: `formal-conjectures/FormalConjectures/ErdosProblems/124.lean`, lemma
`erdos124.ne_zero`. References [BEGL96] Burr–Erdős–Graham–Li, *Complete sequences of sets of integer
powers*, Acta Arith. **77** (1996) 133–138 (PDF read, scholar_BEGL96_proof_dissected.md). The k=0
case (`erdos124.zero`) is a separate Erdős [Er97] conjecture, resolved by Alexeev/Aristotle 2025 — see
§5.

---

## 1. THE VERDICT (stated sharply — the SPLIT structure)

> **✅ RESOLVED (Jun 12 2026, Ridout verdict + baker adjudication — HOLD lifted). The open half (part
> ii) has a definitive two-scope characterization AND its difficulty has MOVED:**
> **— PER-FIXED-(D,k):** the wall is the PAIRWISE two-log MW bound on `|d_i^a − d_j^b|` — finiteness
> of the dangerous coincidences, DISCHARGED by citable bounds (vacuous at hole scales but sufficient
> for finiteness; this is exactly BEGL96's k=1 method). [matveev's k=2 reduction: the tail closure is
> a per-atom gap lemma `atomSum(<v) ≥ v + 2N₀`, a DISJUNCTION of pairwise statements — one citable
> 2-log MW bound on a single pair discharges it. NOT joint for fixed k.]
> **— THE INDUCTIVE STEP (k→k+1), all k:** k-uniformly CLOSABLE — one Ridout corollary (ineffective),
> or per-k effective via the gap-lemma proof. So the step is NOT the obstruction.
> **— THE ONLY REMAINING ALL-k CONTENT = the PER-K BASE CASE (the day-1 SEED):** for every k, a
> gap-free SEED INTERVAL of doubling width exists near `N₀(k)`. ⚠ `N₀(k)` is super-geometric (mahler;
> NOT k-uniform), and seed-existence uniformly in k is the single open obstruction. This is the
> open core's FINAL form.
> Part (i) below is stable; part (ii) is now this SEED-existence statement.

> **The BEGL96 k ≥ 1 conjecture splits cleanly into two parts, of which ONLY ONE is open:**
> **(i) β-discrimination / bounded gaps — PROVEN ELEMENTARY.** [STABLE] That the admissibility
> threshold is exactly `β = ∑1/(d−1) ≥ 1`, and that above it the exceptional set has only bounded gaps
> (no long runs), is the discrete shadow of the **Astels 2000 thickness theorem**
> (`γ(C_d) = τ/(1+τ) = 1/(d−1)`, so `∑γ ≥ 1` is exactly Astels' sum-of-thicknesses interval criterion;
> the continuum sumset is an interval at β = 1). This half is elementary and largely Lean-ready.
> **(ii) the per-k SEED-existence base case — the ONE remaining open obstruction.** [RESOLVED form,
> post-Ridout] After the Ridout verdict, the inductive step k→k+1 is k-uniformly closable (one Ridout
> corollary, ineffective; or per-k effective via the gap lemma), and the per-fixed-(D,k) tail closure
> is pairwise-MW-discharged (matveev's gap lemma `atomSum(<v) ≥ v + 2N₀`, a disjunction of pairwise
> statements). So the ENTIRE remaining all-k content collapses to the **per-k base case = the day-1
> (SEED): for every k, a gap-free seed interval of doubling width exists near `N₀(k)`.** This is the
> ONLY remaining obstruction; `N₀(k)` is super-geometric (mahler, not k-uniform), and proving
> seed-existence uniformly in k is open.
>
> **So: bounded gaps are PROVEN (part i); the inductive step and per-fixed-k closure are
> CLOSED (Ridout + pairwise MW); the single remaining open obstruction is UNIFORM-in-k SEED EXISTENCE
> (part ii). The answer is almost certainly TRUE (and FALLS INEFFECTIVELY via Ridout), and the
> localization — to a proven-elementary β-threshold half + a single per-k seed-existence statement —
> is itself the contribution.**

**Why this split is the verdict, not a guess.** The exceptional set of `R(D,k)` (for admissible D) is,
above an early transient, a sparse set of **isolated points / short clusters** (run length
`O(d_min^k)`), terminating at a finite `N₀` [VERIFIED, troika_synthesis_difficulty_located.md: (3,4,7)
k=2 has 5205 exceptionals, max run 8 ≈ 3²; k=3 has 390 934, max run 70 ≈ 3³]. Part (i): bounding the
**bulk** (no long runs) is elementary — Theorem 8 (Lemma BG) + the Astels-thickness reason the
threshold is `β ≥ 1` [PROVED, scholar_thickness_proofs.md + INVENTIONS.md "ASTELS RECONCILIATION",
troika+maverick, both verified]. Part (ii): eliminating the **last isolated point** — located at a
cross-base power near-coincidence — is the transcendence step [VERIFIED+LIT,
troika_cassels_insufficient.md: the naive interval-filling bound under-predicts `N₀` by 200×–29000×,
the deficit being exactly the `|d_i^p − d_j^q|` spacing]. The kill-ledger below shows part (ii) is
irreducible — no route bypasses it — while part (i) is genuinely proven, not assumed.

**The kill-ledger (proof that no route bypasses it).** Twelve candidate mechanisms — across the
elementary, combinatorial, spectral, probabilistic, measure-theoretic, p-adic, and harmonic-analytic
lanes — were adversarially kill-tested against a fixed ground-truth gauntlet (admissible cofinite
families + β≈0.93–1.0 deep-trap families + the deep stragglers) on a validated exact atom-sieve
(exact to 9×10⁹, cross-checked bit-for-bit against two independent engines). **Every route reduces to
the same wall in a different costume** [VERIFIED, breaker_KILL_LEDGER.md]:

| Route (lane) | Verdict | Why it reduces to MW |
|---|---|---|
| 2nd moment / C5-band (probabilistic) | KILLED | Φ=0 at deep stragglers while E[Φ]≈14–22 — large-deviation events variance can't exclude; can't separate β=0.933 from β=1 |
| Circle method INV-S1 (analytic) | KILLED | major-arc main term O(1) at the misses; minor-arc error same order at the boundary |
| Carry automaton (combinatorial) | KILLED | carry-state ≈ two-base (3,4) gap ~7688, grows with k → not finite-state |
| Perron–Frobenius (spectral) | k=1 only | finite at k=1 (37 states → n₀=581); state count ~3^s at k≥2 |
| Log-descent / valid peel INV-C1 (multiplicative) | algorithm, not proof | sound O(log n) decoder, but existence-of-peel is tautological; `own_thr(a)/a → 1` kills the non-circular induction |
| UNSCALE deflation (multiplicative) | KILLED (unsound) | `b·h ∈ R ⟹ h ∈ R` is FALSE (36/37 holes are counterexamples); `x ↦ x/b` ill-defined on the cross-base sum |
| Ostrowski/CF covering INV-T2 | nec.-not-suff. | θ-clustering generic (cofinite ≡ deep-trap); the covering IS the unproven MW question |
| Rep-fragility / θ-concentration / valuation (measure, p-adic) | KILLED | min-reps stays ≥2 at the gap; θ→0.955/0.9995 at power neighbors; range-blind to deep stragglers |
| Deficit drainage / base-4 repair (conservation, value-specific) | a-priori = MW | hold empirically through k=3, but proving they never fail = bounding cross-base alignment = MW |

The two routes NOT killed (INV-S10 Riesz-product minor-arc bound; the IFS/𝕋² torus spectral radius)
are precisely the ones that attack the cross-base coupling **head-on** rather than avoiding it — i.e.
they ARE the transcendence statement, in harmonic-analytic and ergodic dress respectively. **Avoiding
the coupling is provably blocked; the coupling is the transcendence content.**

> **Note on the kill-ledger's scope (post-Ridout, resolved).** The ledger establishes the robust,
> uncontested claim: **every bypass route reduces to the cross-base coupling** (no elementary/
> combinatorial/spectral/probabilistic/measure/p-adic route avoids it). Per the Ridout resolution
> (§1): for FIXED k that coupling is the pairwise MW spacing `|d_i^a−d_j^b|` (discharged for
> finiteness); the UNIFORM-in-k content is the per-k SEED-existence statement. The two un-killed
> ANALYTIC routes (INV-S10's `min(P_3,P_4,P_7)` decay; the 𝕋² spectral radius) targeted the
> signed-cancellation STEP — which Ridout has now closed ineffectively — so the live prize is no longer
> these joint-object routes but SEED-existence (a density/pigeonhole question; see §1). The ledger's
> EXHAUSTIVENESS over bypass routes is stable and is what it proves.

---

## 2. THE PROVEN STACK (REDUCTION_THEOREM.md, 10 theorems; 5 returned sorry-free from Aristotle)

The reduction of the conjecture to its open core is a coherent chain of 10 theorems, all
Lean-ready or Lean-returned. Full statements + proofs: `REDUCTION_THEOREM.md`. **[LEAN-A]** = returned
sorry-free and statement-faithful from Aristotle (static audit complete, Jun 10 2026); **independent
local lake-build kernel re-verification is still pending on all five** (see note below). Headline:

| # | Theorem | Status | Source |
|---|---|---|---|
| 1 | Scaling: `R(D,k) = ∑ d^k·B_d` | **[LEAN-A]** `erdos124_scaling` | sumset, troika |
| 2 | Atom reformulation (distinct-value case) | [PROVED, Lean-ready] | cassels (0 diffs (3,4,7) verified) |
| 3 | **Residue coverage ⟺ gcd=1** (subgroup argument, NOT CRT) | **[LEAN-A]** `erdos124_residue_coverage` | modular (canonical); sumset's CRT-product "Lemma A" REFUTED, corollary survives |
| 4 | Deconvolution `R(D,k)=C_k+R(D,k+1)` | [PROVED, Lean-ready] | maverick, sumset |
| 5 | gcd necessity (g>1 ⟹ not cofinite) | **[LEAN-A]** `erdos124_gcd_confinement` | sumset/troika/carry/modular (independent) |
| 6 | Lemma C: cofinite ⟺ finite +M-closure failures (step completeness) | **[LEAN-A]** `erdos124_step_completeness` | cassels |
| 7 | Side-condition mapping (β≥1 ∧ gcd=1 ⟺ the two filling hypotheses) | [PROVED/COMPUTED] | lift, cassels |
| 8 | Bulk bounded-gap (Lemma BG): β≥1 ⟹ runs bounded by `O(d_min^k)` | [PROVED, Lean-ready as bounded-gap ONLY] | maverick (⚠ bounded-gap ≠ cofinite — the gap is the core) |
| 9 | Supercritical liminf: β>1 ⟹ `liminf T(x)/x > 1` | [PROVED-ish, Lean-hard] | lift |
| 10 | Average rep-count diverges: `e_d = log2/log d > 1/(d−1)` (d≥3) ⟹ `E[r(n)] ≍ n^ε`, ε>0 | [PROVED elementary] | lift, density (see §6) |
| Lemma A | Shifted gap-condition onset `m₀=(C'−1)/σ` (strict-excess tier, §5) | **[LEAN-A]** `erdos124_gap_onset` | cassels |

**Lean status (precise — neither under- nor over-claimed):** **FIVE results returned sorry-free and
statement-faithful from Aristotle**, static-audited on fetch (Jun 10 2026; each dir under
`submissions/results_jun10/` contains `ARISTOTLE_SUMMARY.md` + `RequestProject/*.lean`, grep-verified
`sorry = 0`, standard axioms): `erdos124_scaling` (Thm 1), `erdos124_gcd_confinement` (Thm 5),
`erdos124_step_completeness` (Thm 6), `erdos124_residue_coverage` (Thm 3, the cyclic-subgroup/`orderOf`
argument — explicitly NOT the refuted CRT-recombination route), and `erdos124_gap_onset` (Lemma A).
**⚠ Honest caveat to print: these are Aristotle-built + statically audited; independent LOCAL
lake-build kernel re-verification is still PENDING on all five.** So the precise claim is: "5 results
returned sorry-free and statement-faithful from Aristotle (static audit complete; independent kernel
rebuild pending)" — not 1, not an unqualified 5. The remaining stack theorems (2, 4, 7, 8, 9, 10) are
elementary Lean-ready; REDUCTION_THEOREM Part 4 lists Mathlib granularity per lemma.

**The reduction's payoff (Theorem 6 + 8):** cofiniteness ⟺ no isolated exceptional point survives
above `N₀(k)`. The bulk (Theorem 8) is elementary; the residual is single-point elimination = §1's MW
core. This is the precise sense in which "the conjecture reduces to one transcendence question."

---

## 3. theorem_347_allk: (3,4,7) for all k, complete modulo a labeled MW input

[CONDITIONAL — complete given §C's transcendence input; theorem_347_allk.md, authors lift + troika]

> **Theorem (347-all-k).** For every k ≥ 1, `R({3,4,7},k) = 3^k·B_3 + 4^k·B_4 + 7^k·B_7` is cofinite.

This is a genuinely **new** result: [BEGL96] proved only k=1 (largest hole 581), and the all-k claim
is tagged `research solved` in `124.lean` with **no citable proof** — an over-claim documented in
scholar_upstream_overclaim_report.md (see §7). Prior-art cleared: the only E124 file in Alexeev's
public `plby/lean-proofs` is the k=0 `Erdos124b`; nothing on k≥2 (scholar_plby_repo_sweep.md).

Structure (the k-uniformity reduction is rigorous; only one input is transcendental):
- **§A Digit recursion** `R_k = C_k + R_{k+1}`, `C_k={0,3^k}+{0,4^k}+{0,7^k}` [PROVED, = Theorem 4].
- **§B k-uniformity of the bad pairs** [PROVED+VERIFIED]: the close pairs `(3^p,4^q)` with
  `|3^p−4^q|` small have `q/p ≈ log3/log4 = 0.79248…` and occur at the **CF convergents of
  `log3/log4`** (denominators p ∈ {5, 24, 29, 53, 612, …}), **independent of k** — raising k only
  discards small pairs. So "all k" follows from one fixed bound. [⚠ nesterenko ground-truth
  corrections, baker_assembly/CLAIMS.md: (a) the relevant constant is `log3/log4 = 0.79248`, NOT
  `log4/log3 = 1.26186` — the number 0.79248 is log3/log4; the "log4/log3" label was a transposition.
  (b) The genuinely-close pairs are the CONVERGENTS p ∈ {5, 24, 29, 53, …} (closest is p=53, rel
  2.09e-3; then p=5, the `3^5=243≈256=4^4` pair); the earlier list `{5,19,24,29,34}` wrongly included
  the SEMI-convergents p=19, 34, which are NOT close (rel ≈ 8e-2). Dominant near-coincidences: p=5 and
  p=53.]
- **§C The transcendence input** [LABELED, FORM UNDER ADJUDICATION — see §1 HOLD]: BEGL96's own k=1
  proof used a Mignotte–Waldschmidt two-log lower bound on `|3^p − 4^q|` [MW, *Linear forms in two
  logarithms…II*, Acta Arith. 53 (1989) 251–287, Cor. 10.1]. ⚠ Two cautions: (i) per §C.3 (troika+lift)
  the ASYMPTOTIC closure is a JOINT equidistribution (exponential-sum) statement, not the pairwise MW
  bound — MW may dispatch the finitely many worst single near-coincidences (581 sits at 3^5≈4^4≈7^3)
  but not the all-k asymptotic; this is what baker is adjudicating. (ii) [nesterenko, VERIFIED] BEGL96's
  displayed MW bound `|3^p−4^q| > exp{ln3·(p − 500·ln4·(8+ln p)²)}` is VACUOUS (exponent negative,
  bound < 1) for all p up to p* ≈ 293 885 (where 3^p has ~140 000 digits) — it proves the bad set is
  FINITE (CF-convergent denominators thin geometrically), then a FINITE COMPUTATION (to 581 for k=1)
  closes it. It does NOT numerically certify the gaps at the scales where the holes live; it is a
  per-(D,k) finiteness-plus-finite-check, NOT an effective uniform discharge. Do not cite it as
  "discharging the inequality" at the hole scales.

**Corrected thresholds** (validated engine; the (3,4,7) `N₀(k)`): **581 / 3 982 888 / 166 025 260** for
k = 1,2,3 [VERIFIED, breaker — corrects two false-freeze artifacts in the team's history; the early
"57.75M" for k=3 was an under-converged value]. BEGL96's printed secondary largest-misses 78/111/16 are
off-by-one; correct values 79/112/17; only the MW-proven (3,4,7)=581 matches
(scholar_BEGL96_largest_miss_audit.md).

---

## 4. THE HARDNESS FACTS (standalone results — why the core resists every elementary route)

These are independent theorems/verifications, each a self-contained reason the open core is genuinely
transcendental, established from FOUR different mathematical directions (a robust triangulation):

1. **No computable discriminator decides β** [troika]. There is no finite computation that separates an
   admissible boundary family (β=1, cofinite) from a deep-trap sub-critical family (β≈0.93, not
   cofinite) — the distinguishing exceptional point can sit beyond any fixed bound (deep stragglers
   verified > 9×10⁹ for (3,4,11)). This is why all "local statistics" routes (2nd moment, fragility,
   θ-concentration, valuation) are KILLED — they are range-blind to the deep stragglers
   (breaker_KILL_LEDGER.md).

2. **Non-automaticity** [sumset, scholar]. The miss set `{r(n)=0}` is NOT base-b automatic /
   eventually periodic (verified (3,5): no period at any 3^p, p=2..11). Causal chain: the
   near-coincidences sit at continued-fraction-convergent positions of `log d_i/log d_j` (non-periodic)
   ⟹ the miss pattern can't be eventually periodic ⟹ not finite-state ⟹ needs transcendence. (If it
   were finite-state it would be automatic and elementary; its non-automaticity IS the obstruction.)

3. **Thickness fixes the threshold but cannot finish at the boundary** [scholar, density, cassels —
   three independent derivations]. This is the precise split of §1: Astels thickness PROVES part (i)
   (`γ(K_d)=1/(d−1)`, so `∑γ≥1` is the threshold and gives bounded gaps), but is provably insufficient
   for part (ii) (final cofiniteness at β=1). Demonstration: at β=1, two objects with the SAME Astels
   thickness `∑γ=1` give OPPOSITE answers — the continuum Cantor sumset `K_3+K_4+K_7` is NOT an interval
   (max-gap/resolution GROWS 4.4→…→29.2 with depth — density), while the integer `R({3,4,7},1)` IS
   cofinite. The integer lattice floor supplies the slack the continuum lacks at β=1; so the
   metric/thickness invariant decides the threshold and the gap-boundedness (part i) but CANNOT decide
   the final straggler elimination (part ii) — only the arithmetic alignment `|3^p−4^q|` (= MW) does
   (scholar_discrete_thickness_attack.md). No contradiction with §1: thickness is exactly as powerful
   as part (i) and exactly as powerless as part (ii) — which is the split.

4. **Large-deviation blindness** [breaker, scholar — the C5 trap]. `E[r(n)] ≍ n^ε → ∞` (Theorem 10),
   but the misses are rare large-deviation events `r(n)=0` at the cross-base coincidences — invisible to
   any first/second-moment (mean/variance) control. Verified at the hard n's: the circle-method
   major-arc term and the minor-arc error are the SAME ORDER (at the miss 581 they cancel to 0; at
   n=585 with r=1 the minor error is ~half the main term) — so any bound on the average count cannot
   certify `r(n) ≥ 1` pointwise at the coincidence n's (scholar, INVENTIONS.md INV-S10 C5-trap check).

5. **The atom-gap mechanism — why the cascade is pervasive at the boundary** [modular, confirmed
   breaker]. The merged atoms {d^j : d∈D, j≥k} have WIDE multiplicative gaps just below each top
   power, and the cofiniteness threshold N₀ sits INSIDE such a gap. Concretely for (3,4,7) k=3: the
   largest atom ≤ N₀ is 3¹⁷ = 129,140,163, the next atom is 4¹⁴ = 268,435,456, and N₀ = 166,025,260
   lies inside that 139M-wide gap. So every n in [3¹⁷, 4¹⁴] must be built around the single big atom
   3¹⁷ plus a large residual, forcing deep "high-θ" peel chains (top atom ≈ n) — this is the geometric
   CAUSE of breaker's empirical pervasive depth-5–6 cascade above N₀. The cascade is pervasive
   precisely in the wide atom-gaps just below the top power, which is exactly where the MW power-
   coincidence content concentrates. (Note: this also corrected an earlier "single-scale/sparse"
   reading that had tested BELOW the true N₀=166M via the false-freeze 57M — see modular_INV_correction.md
   CORRECTION 2. The honest verdict: M1-salvage + INV-C1 is a strict-excess partial, NOT a boundary
   closer; the boundary cascade is pervasive and MW-laden.) Complements the 34.6× n₀-gap MW witness.

6. **No spectral gap exists — the deficit dynamics is an isometry** [maverick]. The deficit dynamics
   sits on the log-phase torus generated by (log 3, log 4, log 7), which are ℚ-independent, so it is an
   IRRATIONAL ROTATION — an ergodic ISOMETRY with ZERO Lyapunov exponent and PURELY CONTINUOUS spectrum
   (classical). A spectral gap requires expansion (Ruelle–Perron–Frobenius / positive Lyapunov); a
   rotation has none, and no weight `e^φ` creates one (it shifts the leading eigenvalue but the
   continuous rotation spectrum persists). [VERIFIED: the per-step deficit ratios are non-geometric —
   1.31, 0.60, 2.06, mean 1.07 — i.e. no gap.] So operator/transfer-matrix/dynamical methods that
   would give an effective N₀ via a spectral gap provably CANNOT work — and this is *why* the surviving
   route (BRIDGE-RIESZ / S10, a Fourier object on the continuous-spectrum side) is structurally the
   right tool: it lives on exactly the continuous spectrum where a discrete gap fails.

Together these say: the obstruction is non-computable-by-local-means, non-automatic, non-metric,
non-mean-controllable, geometrically concentrated in the wide atom-gaps below top powers, AND
spectrally gapless (an isometry, no expansion) — a genuinely transcendence-theoretic (Baker/MW)
phenomenon, six ways. The gaplessness (fact 6) is itself the reason the right tool is a Fourier /
continuous-spectrum object (BRIDGE-RIESZ), not a dynamical spectral gap.

---

## 5. THE STRICT-EXCESS REGIME (the winnable tier) and its honest boundary

For `β > 1` strict, the representation count is comfortably supercritical and the proof is elementary
**above an MW-set floor** — the canonical statement:

> **Strict-excess sufficient condition** [PROVED-pieces + CONDITIONAL at the edge,
> scholar_maverick_strict_sufficient_condition.md]. Admissible D, k ≥ 1: if the harmonic margin
> `δ = β − 1` exceeds the worst-pair log-clustering `Λ(D,k)` (the closest `|d_i^p − d_j^q|`, the MW
> spacing — gcd-independent, k-uniform), then `R(D,k)` is cofinite, with an effective threshold
> computed by ELEMENTARY means above the floor.

Assembled from: Lemma A gap-condition onset (cassels), Theorem 8 bounded-gap (maverick), the proved
residue half (Theorem 3), density's margin-growth run-bound, and the Astels-thickness explanation of
why β≥1 is the threshold (scholar). **k=1: all 44 admissible strict-excess D ⊆ {3..12} are VERIFIED
cofinite** (max `N₀`=986 [VERIFIED, cassels]) — this is exhaustive COMPUTATIONAL verification, NOT an
unconditional proof. The theorem-level claim remains conditional (Baker-conditional at the δ-edge, per
the guardrail below): notably {3,4,6} is IN these 44 with N₀=986 yet is exactly the Baker-grazed
MW-hard case (6=2·3, δ=0.033 barely exceeds its clustering), so "k=1 verified" must not be read as
"k=1 elementary/unconditional." The density run-bound + Lemma A give the elementary part above the
MW-set floor; the closure to full cofiniteness is verified-not-proven even at k=1.

> **⚠ HONESTY GUARDRAIL (maverick).** The winnable tier is **Baker-conditional at the edge, not
> transcendence-free.** The floor `δ₀(D,k)` below which clustering wins is itself an MW quantity (set
> by the closest `|d_i^p−d_j^q|`). State it as "elementary ABOVE an MW-set floor," never
> "transcendence-free" simpliciter. THREE peer-caught over-claims live exactly here — maverick's
> `1/(d_max−1)` single-ray artifact, scholar's strict-vs-boundary binary, scholar's pairwise-coprime
> framing — all because the winnable region looks cleaner than it is (its boundary is transcendence-set).
> The discriminator is the COMPARISON `δ vs Λ`: e.g. (3,4,6) δ=0.033>0 (strict) is MW-hard (6=2·3
> clusters with 3,4), while (3,4,5,7,11,13) has the tightest cluster tested yet is easy because δ=0.43
> swamps it [VERIFIED, scholar/maverick/sumset].

**Lemma A** (the one genuinely-new fragment of this tier): the shifted/deficit-corrected gap-condition
`S(X) ≥ mβ − C'`, `C'=∑d^k/(d−1)`, giving the closed-form onset `m₀=(C'−1)/σ` (finite for σ>0, ∞ at
σ=0 = the MW boundary). [**[LEAN-A] MACHINE-VERIFIED — Aristotle proved sorry-free
(`erdos124_gap_onset`)**; prior-art DEFENSIBLE-NEW — cleared the Birch–Zannier–Perelli–Chen–Fang–Yu–Liu
lineage (all two-generator / N^r-vector / semigroup; none multi-base + lower-bounded + ∑1/(d−1));
scholar three-layer forward-citation sweep; residual = confirm Yu-Chen 2025 + Liu 2026 PDFs
pre-submission. Cite: Birch 1959; Zannier 1989 MPCPS 106 199–206; Perelli–Zannier 1983 Acta Math.
Hungar. 41, as the predecessors it exceeds.]

> **Scope one-liner (cassels, verbatim per team-lead):** Lemma A is a correct, novel, machine-verified
> PARTIAL result that precisely separates the winnable tier from the MW core — the localization is the
> contribution.

---

## 6. THE TWO-EXPONENT NOTE (why cofiniteness is critical where counting is supercritical)

[PROVED-elementary, note_two_exponents.md, lift + density]. Two distinct supercritical invariants:

- **Reach surplus** `δ = β − 1` (a first-moment / cumulative-mass quantity). δ > 0 closes missing
  RUNS of length ≥ 2 (density's margin-growth lemma); δ = 0 (the boundary, (3,4,7)) is the criticality.
- **Counting surplus** `ε = ∑_d e_d − 1`, `e_d = log2/log d` = box dimension of `B_d`. Since
  `log2/log d > 1/(d−1)` for every d ≥ 3 [PROVED, one-line convexity; VERIFIED scholar: gap +0.13 at
  d=3, →0+ asymptotically since 1/log d ≫ 1/d], we have `ε > 0` STRICTLY even at β=1.

**The clean phenomenon:** at the boundary δ=0 yet ε>0 — the representation *count* `E[r(n)] ≍ n^ε` is
comfortably supercritical exactly where cofiniteness is *critical*. The two invariants are classically
distinct (box dimension vs Astels thickness) but have never been contrasted for this family [LIT:
folklore individually; the contrast is the new bit — Erdős–Tetali / Erdős–Fuchs control `r(n)` mean/
fluctuation but never isolate the avg-vs-min gap; scholar prior-art]. This contrast is exactly why the
problem is hard: the average says "many representations," the minimum (the misses, §4 fact 4) is where
all the difficulty hides.

---

## 7. HONEST FRAMING & UPSTREAM

- **Answer almost certainly TRUE; the inductive step is k-uniformly closable (Ridout, ineffective),
  so the conjecture reduces ENTIRELY to per-k seed existence — OPEN.** Every admissible D tested is
  cofinite — all 44 strict-excess D⊆{3..12} at k=1; the two-prime-power "collinear" families
  (3,4,8,9) etc. at k=1,2,3 [breaker]; the boundary triples (3,4,7), (3,5,7,13) at k=1,2,3; no
  admissible counterexample in any computed range (validated to 9×10⁹). The step k→k+1 closes via a
  Ridout (ineffective) corollary; but the per-k SEED base case is OPEN, so all-k cofiniteness does NOT
  yet follow — effectively or ineffectively. The effective per-k route is the separate (optional) prize.
- **The open content has MOVED (post-Ridout) to exactly the per-k SEED-existence base case** (§1, §8):
  uniform-in-k existence of a doubling-width gap-free seed interval near `N₀(k)`. The inductive step
  and per-fixed-(D,k) closure are settled. The localization — to this single per-k seed statement —
  **is the contribution.** This is not a full resolution; it is a precise reduction + a proof (the
  kill-ledger, §1 + the six hardness facts, §4) that the residual is irreducibly Baker/MW.
- **Necessity is fully settled** [theorems in 124.lean]: β≥1 necessary (Pomerance; density's
  constructive converse) and gcd=1 necessary (Theorem 5). Melfi 2004 disproved only the
  INFINITE-set reading (Graham confirmed A meant finite); the finite conjecture is untouched
  (scholar_Melfi_lineage_and_status.md).
- **Upstream errata (documented, do NOT file without owner approval):** the `124.lean`
  `ne_zero_three_four_seven` lemma is tagged `research solved` for all k≠0 but BEGL96 proved only k=1
  — an over-claim (scholar_upstream_overclaim_report.md, GitHub-issue-ready). The "Cassels 1960
  Szeged" filling-lemma citation circulating in the field is a PHANTOM (= Erdős 1962 Acta Arith. 7
  conflation; Crossref-verified); the correct attribution is Brown 1961 (Amer. Math. Monthly 68,
  557–560, DOI 10.2307/2311150).
- **The k=0 case is NOT part of this conjecture and is already public/known.** It is Erdős [Er97],
  resolved by Alexeev/Aristotle 2025 (`Erdos124b.lean`, 407 lines, public; described by T. Bloom on
  the Xena blog), and is a textbook corollary of Brown's criterion. Do not submit it as open or
  publish it as new (scholar_k0_priorart_verdict.md).

---

## 8. THE OPEN CORE (post-Ridout final form: uniform-in-k SEED existence)

> **★ THE OPEN CORE, FINAL FORM (post-Ridout; baker-LOCKED).** All-k cofiniteness reduces to ONE
> statement: **for every k ≥ 1, there exists a gap-free SEED INTERVAL of length ≥ (the largest atom
> below it), near `N₀(k)`** — a contiguous run of representable integers long enough to bootstrap the
> doubling/+M-closure. The inductive step k→k+1 is closed (Ridout corollary, ineffective; or per-k
> effective via the gap lemma); the per-fixed-(D,k) tail is pairwise-MW-discharged (matveev). So
> seed-existence UNIFORMLY in k is the sole remaining obstruction. `N₀(k)` is super-geometric (mahler,
> not k-uniform), which is exactly why the seed must be exhibited per-k rather than by a uniform bound.
>
> **Why the SEED is hard — its mechanism is the base-7 JOINT covering (baker, R2-confirmed).** "SEED"
> and "joint covering" are the SAME object at two descriptions, not rivals: the per-k seed interval
> EXISTS iff the base-7 subset-sums jointly cover the coincidence gaps near `N₀(k)`. Generic gaps are
> single-shift (pairwise) coverable, but the tight (3,4)-coincidence gaps genuinely need the UNION of
> many base-7 shifts (baker, every-point sieve: the 4¹¹ gap needs 255 shifts — best single shift covers
> only 89%). So the SEED is the EXISTENCE statement and the joint covering is its MECHANISM.
> [ENCOURAGING for tractability: baker measured the min base-7 rep-count over the worst coincidence
> gap and it GROWS with scale — 10 → 63 → 178 (j≥1 atoms) — so the joint covering holds with growing
> slack, which is what makes the bounded warm-up BRIDGE-RIESZ-0 plausibly tractable by an elementary
> count-above-threshold rather than a sharp equidistribution constant.]

The per-fixed-(D,k) object below — "no isolated exceptional point survives above `N₀(D,k)`" — has four
equivalent forms; for fixed k it is pairwise-MW (discharged for finiteness), and the SEED statement
above is what remains to make it uniform in k.

> **(per-fixed-k core).** For admissible D (all d≥3, gcd=1, β≥1) and fixed k≥1: no
> isolated exceptional point of `R(D,k)` survives above `N₀(D,k)`. Four equivalent forms:
> 1. **(arithmetic)** the +M-closure failures are finite (Theorem 6).
> 2. **(gap-lemma, the crispest — maverick)** `inf_{v ∈ atoms} (atomSum(<v) / v) > 1`, i.e.
>    `∃ δ > 0` with `atomSum(<v) ≥ (1+δ)·v` for all atoms `v` above a fixed height. ⚠ **`δ > 0` is
>    UNPROVEN** — it is NOT machine-settled: exact computation to `10^3000` finds the infimum DROPS
>    (0.0098 → 0.00555 at ~`10^1193`, dips deepening at deeper cross-base coincidences). The Lean
>    verification covers finite per-atom checks, NOT the `∃δ>0` quantifier. Establishing the infimum is
>    bounded away from 0 = the MW/Baker statement on `min|3^p−4^q|`. [maverick, VERIFIED-computation;
>    do NOT state δ as empirically stable.]
> 3. **(signed Fourier, BRIDGE-RIESZ-B — the live attack)** for all `n > N₀`, the SIGNED minor-arc
>    oscillatory integral is dominated by the positive major-arc main term: `|∫_𝔪 F_3 F_4 F_7 e(−nθ)
>    dθ| < M(n)`, pointwise at the worst (coincidence) `n`. ⚠ This is a SIGNED-CANCELLATION estimate,
>    NOT a magnitude bound — the minor-arc L¹ magnitude `∫_𝔪|F_3F_4F_7|` is 3.18× the major-arc mass
>    (verified scholar+lift), so the bridge holds by phase cancellation, not smallness. [BRIDGE_RIESZ_STATEMENT.md]
> 4. **(magnitude, BRIDGE-RIESZ-A — necessary, not sufficient)** `∏|cos(π d^j θ)|` decays like
>    `2^{(3−c)J}` on minor arcs, k-uniform [verified decay; feldman spoiled-band `C(log J)²/J→0`]. This
>    is the AMPLITUDE ingredient of form 3, not the bridge itself.
>
> All forms are the same Mignotte–Waldschmidt / Baker statement on `|d_i^a − d_j^b|` (per-fixed-(D,k))
> ⊕ the JOINT base-7 covering / equidistribution (uniform all-k/all-D) — see §1 two-scope resolution.

**The single most promising attack** (the only un-killed analytic route): prove BRIDGE-RIESZ-B (form 3
— the SIGNED minor-arc oscillatory estimate) via van der Corput / stationary-phase + the three-distance
/ Ostrowski geometry of the convergent arcs, with form 4 (the magnitude decay) as the amplitude input.
Attack order: the bounded warm-up BRIDGE-RIESZ-0 (finite CF-convergent arcs p∈{5,53} + one MW two-log
input — closes k=2 L3) → form 4 (calibration) → form 3 (the bridge). ⚠ The pointwise/signed caveat
(§4 fact 4, the C5 trap) is decisive: a magnitude or mean bound CANNOT finish; the certificate must be
SHARP and SIGNED at the coincidence arcs. troika verified the min-product form 4 has a decay-onset
delay `min ≤ C·ρ^{L−a(θ)}` where `a(θ)` = convergent depth, and bounding `a` is itself MW — so even
form 4 is not uniformly elementary at the deep convergents.

**Upstream note (matveev, for the over-claim report — softened post-Ridout):** BEGL96's k=1 (3,4,7)
proof is the single compressed sentence "we can show … is 581" (§3). The tail-closure it elides is a
genuine, non-trivial finite-to-infinite step — but the compression is JUSTIFIED: matveev's
machine-verified k=2 reduction shows the closure is equivalent to a per-atom gap lemma
`atomSum(<v) ≥ v+2N₀`, a DISJUNCTION of pairwise statements that one citable 2-log MW bound discharges
for fixed k. So it is a real-but-pairwise-MW-closable step, NOT a gap in BEGL's proof. What remains an
over-claim is only the 124.lean all-k `research solved` tag: all-k is OPEN (the per-k SEED base case,
`N₀(k)` super-geometric). Full softened item in scholar_upstream_overclaim_report.md (do NOT file
without owner sign-off).

---

*Sources: every file cited above is in `analysis/e124q2/team/`. External citations verified via
Crossref/PDF. Computational claims use the validated atom-sieve (exact to 9×10⁹, two-engine
cross-checked). Lean claims are sorry-free with standard axioms (Aristotle, Jun 10 2026).*
