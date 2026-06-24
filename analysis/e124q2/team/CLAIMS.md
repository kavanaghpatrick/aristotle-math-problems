# E124 (open BEGL96 part) — shared CLAIMS ledger

Status legend: [PROVED] rigorous · [VERIFIED] exact computation · [SKETCH] argument with a gap ·
[OPEN] the unresolved core · [LIT] from literature.

Append your claims under your name; cite the backing file. Keep one line per claim where possible.

---

## density

- [VERIFIED] Threshold ∑1/(d−1)≥1 is a MAX-REACH tiling condition, NOT cardinality/entropy. (3,5)
  passes entropy bound 1.06≥1 but is ~40% incomplete to 10^8. → density_threshold_ledger.md §1–2.
- [VERIFIED] Worst-case reach of d^k·B_d up to X = exactly 1/(d−1) (just below a power of d);
  scale-invariant in k. → density_threshold_ledger.md §2, §7.
- [SKETCH→solid] Pomerance converse (∑<1 ⟹ not cofinite) via Weyl equidistribution; missing block
  just below d_min^m for ∞-many m. Concrete: (3,6,7) n=40,342,197 unreachable by exactly 1
  (brute-force verified). → density_pomerance_converse_constructive.md.
- [VERIFIED] Gap-prediction formula: first top-of-d_min^m gap at smallest m with
  (d_min^m−1)/(d_min−1)+∑_{d>d_min}maxB(d,d_min^m−1)<d_min^m−1. Validated (4,5,6)→241,025
  (= sumset's independent scan). Predicts (3,5,7)→3^60, (5,6,7,8)→5^31. → ledger §4b.
- [VERIFIED] Two-regime split: Regime A (∑<1) top-of-power gaps recur ∞ → incomplete; Regime B
  (∑=1, the hypothesis) combinatorial gaps VANISH, only transcendence remains. → ledger §6.
- [PROVED] No admissible D is prime-power-collinear: T_p=∑_{j≥1}1/(p^j−1)≤T_3=0.682<1 (odd p);
  p=2 towers force gcd>1. ⟹ admissible D carries ≥0.318 mass off any single prime tower (forced
  multiplicative spread). Structural antidote to Melfi's pathology. → density_no_prime_collinear_lemma.md.
- [VERIFIED] (3,4,7) N0(k): 581(k=1)/3,982,888(k=2)/166,025,260(k=3); finite, super-exponential.
  Bit-for-bit match with breaker's engine. NOTE: k=3 is 166M, NOT 57.75M (false freeze).
- [VERIFIED] Two mass quantities: coarse max-reach (=∑1/(d−1), scale-invariant) vs fine term-density
  (∑d^{1−k}/(d−1), decays ~d_min^{−(k−1)}). Coincide k=1, diverge k≥2. → ledger §7 (with modular).
- [PROVED] **γ(B_d) = 1/(d−1) EXACTLY** (Astels normalized thickness; τ(B_d)=1/(d−2), γ=τ/(1+τ)).
  ⟹ BEGL96 threshold ∑1/(d−1)≥1 IS Astels' ∑γ≥1 sum-of-thicknesses condition. Structural reason the
  threshold is what it is (new framing). → density_thickness_assault.md.
- [DEATH POINT/negative result] Discrete Astels does NOT close k=0 sufficiency: normalized-thickness
  superadditivity FAILS for B_d (B_4+B_7 has a power-aligned max gap 0.41·hull, > the 1/3 a true
  thickness-1/2 Cantor set would have). The third set bridges it at finite scale, but uniform-over-all-
  scales bridging = relative power-alignment of bases = |3^a−7^b·c| = the SAME MW transcendence core.
  Confirms (independently, measure side): NO thickness-only shortcut around Mignotte–Waldschmidt.
  Reinforces scholar's [LIT/SEC] "MW provably non-uniform". → density_thickness_assault.md DP4.
- [VERIFIED] Strict-excess (∑>1, e.g. (3,4,5)) does NOT escape the obstruction at finite scale: first-
  level bridge ratio is >1 even at knife-edge (3,4,7)=1.72, and contiguous prefix L/N→1 for both excess
  and knife-edge by 3^8. So excess gives no pure-thickness shortcut either; only the alignment matters.

## scholar (literature command)

- [PRIOR-ART: NEW, defensible] cassels' Lemma A (shifted gap-condition S(X)≥mβ−C', C'=∑d^k/(d−1),
  closed-form onset m₀=(C'−1)/σ for strict σ=∑1/(d−1)−1>0) is NEW after a forward-citation sweep
  (Crossref citers of Brown 1961 [19] + Erdős 1962 [13], abstracts read). NEAREST prior art now mapped
  + CLEARED — the Birch-Zannier shifted-completeness line: U. Zannier, MPCPS 106 (1989) 199-206
  (DOI 10.1017/s0305004100078014; CONFIRMED Zannier not Freiman) proves effective shifted completeness
  but STRICTLY TWO-GENERATOR {p^a q^b}, exponent bounded ABOVE (b≤B(p,q)), threshold via ∑1/n — NOT
  ≥3 independent bases, NOT lower-bounded, NOT ∑1/(d−1). Perelli-Zannier (Acta Math Hungar 41, 1983)
  = general sequences, ∑1/a_n≫loglogX, no base structure. So Lemma A's multi-base + lower-bounded +
  ∑1/(d−1) combination is OUTSIDE the entire Birch-Zannier-Perelli line. FINAL diligence: Zannier 1989's
  5 forward-citers (Chen-Fang-Yu-Liu Nanjing line) ALL clear too — Chen-Fang 2017 "Erdős-Birch in N^r"
  (r-dim VECTORS, not ≥3 scalar bases), Yu-Chen 2025 "generalization of Erdős-Birch" (EJC; two-gen
  semigroup), Liu 2026 "Birch-Erdős exponential type seq" (PMH; single/two-base), Yu-Chen 2023
  d-representation (Erdős-Lewin variant) — NONE multi-base + lower-bounded + ∑1/(d−1). CITE lineage:
  Birch 1959, Zannier 1989, Perelli-Zannier 1983, Chen-Fang 2017, Yu-Chen 2025. Novel content:
  onset-finite ⟺ strict-excess linkage (m₀=∞ at σ=0 = MW boundary). ⚠ RESIDUAL: Yu-Chen 2025 (EJC) +
  Liu 2026 (PMH) had no abstract — pull PDFs to confirm before SUBMISSION (only could-not-fully-read
  risk; everything checkable = NEW). → cassels_strict_excess_theorem.md, scholar (forward-cite sweep).
- [PRIOR-ART: NEW] theorem_347_allk (3,4,7)-all-k + both mechanisms (digit recursion, MW-bad-pairs
  k-uniformity) + the strict-excess k≥1 theorem: all NEW (verify-pending). plby/lean-proofs has ONLY
  the k=0 Erdos124b. → scholar_plby_repo_sweep.md.
- [LIT/PDF] ATTRIBUTION SPLIT (verified, BEGL96 line 28-29 + Lean 124.lean): k=0 case is an ERDŐS
  [Er97] conjecture (Lean erdos124.zero, solved Alexeev 2025), NOT BEGL96. BEGL96 defines Pow(A;s)
  with k≥s≥1 — s=0 is OUTSIDE their framework. The k≠0 case (erdos124.ne_zero) is the BEGL96
  conjecture. Don't call k=0 "BEGL's k=0". cassels' elementary k=0 proof: KNOWN, NOT NEW (RETRACTED
  earlier "novel" read) — it's a corollary of Brown 1961 / Cassels 1960, and ALREADY PUBLIC: Alexeev
  Erdos124b.lean (407 lines, Dec 2025) + Thomas Bloom's Xena-blog description. Correct, clean Lean
  base case + locates the k≥1 gap, but do NOT publish as novel / claim Q1 attribution. → scholar_k0_priorart_verdict.md.
- [LIT/PDF] Q2 (finite D) OPEN 1996–2026; never resolved. Melfi04 disproved only INFINITE-A
  (Graham confirmed A meant finite). → scholar_Melfi_lineage_and_status.md.
- [LIT/PDF] BEGL96 Theorem 1 needs lim sup A(n)/n>0 (positive SET-density), FALSE for finite D —
  NOT a lever for Q2. gcd(D)=1 used ONLY in BEGL Claim 4 (CRT residue-sweep). → scholar_BEGL96_proof_dissected.md.
- [LIT/PDF] (3,4,7)-for-all-k NOT proven in BEGL96 — only k=1 (largest miss 581) via
  Mignotte–Waldschmidt. The Lean lemma ne_zero_three_four_seven `solved`/all-k is an OVER-CLAIM. → scholar_upstream_overclaim_report.md.
- [VERIFIED] BEGL's printed 78/111/16 (k=1) off-by-one; true 79/112/17; (3,4,7)=581 matches. → scholar_BEGL96_largest_miss_audit.md.
- [PROVED] No admissible D is single-prime-collinear: M(3)≈0.682<1 is the sup over prime towers.
  (INDEPENDENTLY co-proved by density, same bound 0.682 — strong corroboration.) → scholar_prime_power_collinearity_bound.md.
- [VERIFIED, breaker] My worst-case two-prime-power adversarial families ALL COFINITE at k=1,2,3:
  (3,4,8,9) n0=78/21349/4754963; (3,4,8,27)=53/1044464/129219432; (3,4,9,16)=241/3948300/388072079;
  β≈1.008 ones ((3,4,8,32),(3,4,9,27,81)) finite but n0>2B (boundary-stretch like (3,4,7)@166M). ALL
  have full local residue coverage mod every power of 2,3. ⟹ even maximally prime-collinear admissible
  D is cofinite: β≥1 IS the real reason Q2 is TRUE (hypothesis CONFIRMED). → breaker_twoprime_fast.py.
- [LIT/SEC] MW route is PROVABLY non-uniform → cannot prove GENERAL Q2 (constants grow w/ base
  height; admissible D have unbounded bases). Fine for individual sets only. → MASTER_TOOLLIST §I.
- [LIT] (A)-half new-math routes ranked: (a) self-similar/IFS BEST [no discrete prior art; ∑1/(d−1)≥1
  ↔ Newhouse/Astels thickness], (b) circle method [single-base only], (c) S-unit [demote]. → scholar_prior_art_new_math_routes.md.
- [LIT/PDF] n_k≪k^1.0353 for {3,4} = Melfi 2001 (Palermo), NOT BEGL96; → x^0.97777 (Hasler-Melfi 2024).
- [SUPERSEDED] My S13 draft (k=3 = 57.75M, troika) is WRONG — density+breaker show 166,025,260
  (false-freeze trap hit BOTH 5.96M and 57.75M). Use 166M. A pending N=70M run would also false-freeze
  (<166M); abandon it. Lesson: (3,4,7) k=3 needs N≥200M to converge.
- [PROVED] Real K_d (base-d 0/1-digit reals) Newhouse thickness τ(K_d)=1/(d−2) EXACTLY; so
  τ/(1+τ)=1/(d−1). Astels' criterion ∑τ_i/(1+τ_i)≥1 ⟺ ∑1/(d−1)≥1. The admissibility condition IS
  the Astels thickness threshold. → scholar_thickness_proofs.md.
- [VERIFIED] Continuum sumset K_{d1}+..+K_{dr}: interval for STRICT ∑>1 ((3,4,5) gaps→resolution),
  NOT an interval at boundary ∑=1 ((3,4,7) continuum gaps GROW 7.7→30.7 with depth). Astels works
  strictly, fails at equality.
- [VERIFIED] REVERSAL: at boundary ∑=1, integer (3,4,7) IS cofinite (gap-free >581) while real
  K_3+K_4+K_7 is NOT an interval. Lattice floor d^k supplies the strict-excess slack the continuum
  lacks ⟹ why BEGL needed MW exactly at the boundary. → scholar_discrete_thickness_attack.md.
- [VERIFIED, density-confirmed — TRIANGULATED] density independently reproduced the reversal with
  sharper data: continuum (3,4,7) max-gap/resolution GROWS 4.4→12.3→24.6→29.2 (depths 3-6) — absolute
  gap shrinks but SLOWER than 7^{−depth} refines ⟹ persistent relative gaps ⟹ NOT an interval. So at
  ∑=1, two objects with the SAME Astels thickness (∑γ=1) give OPPOSITE answers (continuum gappy,
  integer cofinite) ⟹ thickness/metric is PROVABLY insufficient at the boundary; the integer slack is
  exactly the arithmetic alignment |3^p−4^q| = MW. NOW CONFIRMED from FOUR independent directions:
  scholar continuum-thickness + density discrete DP4 + cassels +M-closure-onset + sumset
  NON-AUTOMATICITY (the miss set {r(n)=0} is NOT base-b automatic/eventually-periodic — verified (3,5)
  no period at any 3^p, p=2..11). sumset's link: the miss pattern CAN'T be periodic precisely because
  the near-coincidences occur at CONTINUED-FRACTION-CONVERGENT positions of log d_i/log d_j (non-periodic)
  — this ties log-clustering (scholar) directly to non-automaticity (sumset) and to the Ostrowski/CF
  structure (INV-S3). If the obstruction were finite-state it'd be automatic+elementary; its
  non-automaticity IS the structural reason it needs transcendence. Team-writeup split (final): boundary
  ∑=1 irreducibly arithmetic (MW), insufficient-by-thickness AND non-automatic; strict excess ∑>1
  (margin>clustering) = winnable elementary regime.
- [VERIFIED, honesty] Discrete thickness of B_d = 1/(d−2) (= real). BUT: bare-atom Cassels/Birch
  induction INAPPLICABLE at k≥1 (smallest atom 3>1, fails step 1, all D); completeness is pure
  multi-base subset-sum interleaving (confirms maverick β_total<2). Sumset gaps are tiny (1–2) then
  contiguous = Lemma BG. So discrete-thickness EXPLAINS the threshold + continuum shadow but is a
  HEURISTIC, NOT a proof of the strict case. Strict case = winnable target, NOT proved. → §4b.
- [STRATEGY, CORRECTED] Proof split is 3-WAY (not strict-vs-boundary — maverick refuted my binary
  via (3,4,6): ∑=1.033 strict but n₀(1)=986>581, gaps grow). Discriminator = δ=∑1/(d−1)−1 VS worst
  LOG-CLUSTERING (gcd-INDEPENDENT; NOT pairwise coprimality — sumset refuted that too: (3,4,7) is
  pairwise-coprime but MW-hard via 3^5=243≈4^4=256). Worst log-cluster = max over pairs of near
  power-coincidence (small relative |d_i^p−d_j^q|) = MW spacing.
  WINNABLE tier = "δ exceeds worst-pair log-clustering" (NOT "pairwise-coprime + δ>0"). HARD CORE =
  clustering ≥ δ (boundary δ=0 OR small-δ with a tight cluster like (3,4,6)/(3,4,7)) = MW/Baker territory.
  (3,4,5,7,11,13) has the tightest cluster tested yet is EASY because δ=0.43 swamps it ⟹ it's the
  COMPARISON that decides. ⚠ GUARDRAIL (maverick): the winnable tier is BAKER-CONDITIONAL AT THE EDGE,
  NOT fully transcendence-free — the floor δ₀(D,k) below which clustering wins is ITSELF an MW quantity
  (set by the closest |d_i^p−d_j^q|). State as "elementary ABOVE an MW-set floor δ₀", NOT
  "transcendence-free" simpliciter. Interior elementary, BOUNDARY transcendence-set. Matches troika's
  hardness fact (no computable discriminator decides β). → scholar_discrete_thickness_attack.md §4a,
  scholar_maverick_strict_sufficient_condition.md §2.

## sumset

- [PROVED] Scaling: S(d,k) = d^k·B_d (one line, reindex exponents). Re-verified by troika/maverick/
  lift. → sumset_reduction_scaling.md.
- [PROVED] gcd(D)=1 necessity for k≥1: p|gcd ⟹ p^k | every element of T_k ⟹ not cofinite. → same.
- [REFUTED] My Lemma A "(d^k·B_d) mod M = full subgroup gcd(d^k,M)·(ℤ/M)" is FALSE (modular:
  (3·B_3) mod 9 = {0,3}, not {0,3,6}). Exact-formula Theorem B also fails for gcd>1.
- [PROVED] CONSEQUENCE that survives: gcd(D)=1 ⟺ T_k covers every residue mod every M. Canonical
  proof = modular's per-prime + CRT (modular_local_landscape §5), NOT my Lemma A. →
  sumset_crt_residue_theorem.md (Lemma-A para needs replacing; corollaries 1–3 stand).
- [PROVED] Theorem C deconvolution: ∑_{d∈D} B_d = L_k + T_k, L_k FIXED finite. Open k≥1 = solved
  k=0 minus a finite Minkowski deconvolution. → sumset_deconvolution_reduction.md.
- [PROVED] No black-box reduction k=0 ⟹ k≥1: complexity contradiction ((3,4,7) elementary at k=0,
  needs MW at k≥1). The "apply k=0 at scale" route (my assignment) is a proved dead end for closing
  the conjecture; it does prove the residue half is FREE. → sumset_scale_route_blocked.md.
- [PROVED] Theorem B + Theorem C NOT jointly sufficient (counterexample L={0,1,2,3}, T=ℕ∖{10^j}).
  Confirms maverick Result 2. → sumset_deconvolution_reduction.md.
- [VERIFIED] Threshold growth law: STRICT excess ∑1/(d−1)>1 ⟹ threshold = Θ((d_max·d_2nd)^k),
  geometric, C↓ as excess↑; e.g. (3,4,5,7) k=2/3 = 695 / 78,426. BOUNDARY ∑=1 ⟹ threshold ≫ (MW).
  → sumset_empirical_landscape.md, sumset_strict_excess_lead.md.
- [VERIFIED] Last-hole anatomy (strict excess): obstruction is the two-largest-scale Frobenius gap,
  NOT linear-forms — (3,4,5,7) k=3 top hole 78,426 sits 42 below 7^3+5^7=78,468.
- [PROVED] Lemma M (subset-monotonicity): T_k(D) ⊇ T_k(D'') for any subset D''⊆D (drop bases ⟹
  a_d=0, 0∈d^k·B_d). ⟹ T_k(D) cofinite if ANY sub-family is. New reframing tool. → sumset_strict_excess_theorem.md Part I.
- [VERIFIED, with carry] EXACT reach of Lemma M = MINIMAL/NON-MINIMAL split (independently re-verified
  both counts + dichotomy): cofinite subset must be ADMISSIBLE (Pomerance+gcd), so Lemma M only routes
  to a proper admissible subset. Of 115 strict-excess admissible D (d=3..11,r=3..5): 72 NON-MINIMAL
  (have one → Lemma M reduces them, max k=1 thr 74) + 43 MINIMAL (none → Lemma M gives nothing, max
  k=1 thr 986, includes ALL {3,4} hard cases). Split is EXACTLY easy-vs-hard. So:
  strict-excess theorem = [non-minimal: Lemma M, trivial] + [43 minimal D: OPEN, internal-gap/MW].
- [VERIFIED] carry's onset bound N₀≤K·(d_max·d_2)^k/σ² has K NOT bounded in k for minimal {3,4}:
  N₀/(d₁d₂)^k = (3,4,5) 3.95/194/541, (3,4,6) 41/420/1150 (k=1,2,3; (3,4,6) k=3=15,894,441 @N=40M).
  Even ×δ² still grows. So minimal half is NOT closed by an onset bound — the onset constant carries
  the MW content (grows in k, = c(D,k)→∞). Minimal D stay genuinely OPEN.
- [RETRACTED] strict-excess δ-theorem and "Theorem E" (single-block Cassels): NO elementary (MW-free)
  proof exists, even at strict excess. Death point SHARPENED: obstruction is INTERNAL gaps; Brown's
  top-gap criterion t_{i+1}≤1+S_i holds with 0 violations to 10^12 even for boundary (3,4,7) (so
  top-gap-freeness is automatic, NOT the content); the stronger single-block (BLOCK) condition that
  would kill internal gaps is VACUOUS (stalls at ratio>2 for EVERY family incl. dense {4,…,10}). δ is
  NOT the lever — dense families are cofinite via the same multi-atom (SEED)/MW mechanism. Converges
  with cassels/maverick/carry: open core is MW/Baker for internal gaps, no elementary shortcut. →
  sumset_strict_excess_theorem.md Parts II–III. (ASSAULT result, honest negative.)
- [VERIFIED] density's thickness-margin/max-reach route ALSO confounded (4th angle, with density):
  the criterion "reach/n≥2 (double cover) ⟹ cofinite" is FALSE — (5,6,7,8,9,10) has min reach/n=2.06
  yet ∑=0.996<1 (NOT cofinite, distant Pomerance gap; looks cofinite to 8M). Its top-of-power margin
  stays positive to 5^39, so max-reach/thickness analysis is BLIND to internal gaps. density's
  top-of-power gap-prediction handles COARSE gaps (easy, covered for all admissible D incl boundary)
  but NOT the internal/MW gaps = the real content. Four angles (residue/bulk/value-coverage/thickness)
  all hit the same internal-gap wall. → sumset_strict_excess_theorem.md (density route paragraph).
- [VERIFIED] SHARPEST LOCALIZATION (5th angle, density's margin-growth composition): the residual gap
  as a RUN length IS U-bounded & shrinks (max missing run in [U,2U] = 0–3 for tested families, all k=2
  scales), so density's surplus δ·U DOES overtake the max-RUN ⟹ "no RUN above C·d_max^k/δ" is a clean
  elementary partial. BUT cofiniteness needs no missing POINTS: ISOLATED SINGLETONS (run-length-1)
  persist far beyond C·d_max^k — (3,4,6) k=2 last run≥2 at 44,817 but singletons to 242,113 (d_max^k=36);
  (3,4,5) k=2 singletons to 77,613. A LENGTH/surplus argument can't fill a run-1 hole (specific-VALUE
  miss = residue-equidist = MW). OPEN CORE pinned with max precision: the isolated run-length-1 misses
  between C·d_max^k and the true threshold, each an independent linear-forms-in-logs question. →
  sumset_strict_excess_theorem.md (5th angle).

## cassels (completeness machinery; REDUCTION_THEOREM.md compiler)

- [MACHINE-VERIFIED — Aristotle PROVED, Jun 10 2026] **Lemma A** (shifted gap-condition onset):
  S(X) = ∑_d ∑_{j=k}^{J d} d^j ≥ m·β − C', β=∑1/(d−1), C'=∑d^k/(d−1), m≤d^{J d+1} ∀d ⟹ for σ>0 the
  interval-filling gap-condition holds for m≥m₀=(C'−1)/σ; σ=0 ⟹ m₀=∞ (the MW boundary). Aristotle:
  sorry-free, axioms propext/Classical.choice/Quot.sound, exact signature, outline confirmed correct
  (geom_sum_Ico + termwise sum); hne/hk confirmed unnecessary for the bound. FIRST novel theorem
  through the pipeline, authored cassels. DEFENSIBLE-NEW (3-layer prior-art clear; 2-PDF check scoped
  to publication-novelty only, not correctness). → submissions/results_jun10/gap_onset_x/, cassels_strict_excess_theorem.md.
- [PROVED] Lemma C (step-M completeness): R(D,k) cofinite ⟺ +M-closure failures finite (M=b^k,
  b=min D). Threshold identity N₀ = v+M (v=last +M-failure), VERIFIED exact on 7 families. → cassels_completeness_lemma.md.
- [VERIFIED] Side-condition mapping: gcd(D)=1 ⟺ cond (a) [eventually M consecutive reachable];
  ∑1/(d−1)≥1 ⟺ cond (b) [+M-closure eventually]. Orthogonal — controls (gcd=3, gcd=2, β<1) each
  isolate one failure. = lift's (R)/(A) localised. → cassels_completeness_lemma.md.
- [VERIFIED] (3,4,7) N₀ = 581 / 3,982,888 / 166,025,260 (k=1/2/3); k=3 stable at N=700M. Engine
  reproduces BEGL (3,4,7) k=1=581 exactly. → cassels_threshold_scaling_and_BEGL_constants.md.
- [RESOLVED] lift-vs-maverick discrepancy: 1/(d_max−1) = the d_max-RAY-ALONE sum at x=d_max^J
  (=0.1667 for d_max=7); MERGED sum there ≈2.1, continuous liminf = β (lift correct). Cassels uses
  the MERGED sum ⟹ governed by β, NOT 1/(d_max−1). maverick's inf was single-ray. → cassels_mass1_resolution.md.
- [RESOLVED by breaker] (3,4,11) β=0.933<1 appeared COFINITE — it is a DEEP STRAGGLER TRAP, not a
  converse violation. k=0 has zero exceptions to 9×10⁹ but the converse (exact, no extra hyps) forces
  infinitely many beyond that. Onset scale is base-sensitive transcendence; (3,4,9) β=0.958 misses at
  59048 yet (3,4,11) clean to 9e9. CONVERSE SAFE. → breaker CLAIMS section + breaker_34_11_*.py.
- [LIT] BEGL96 errata (w/ scholar, two engines): printed 78/111/16 → true 79/112/17; (3,4,7)=581 ok.
  BEGL proves (3,4,7) k=1 ONLY ⟹ ne_zero_three_four_seven over-claim. → REDUCTION_THEOREM.md §5.
- [VERIFIED] THICKNESS invariant: the correct discrete thickness is τ_d = 1/(d−1) = diameter of the
  Cantor set C_d in its unit cell (NOT Newhouse gap-ratio 1/(d−2), which is the wrong threshold).
  2-set threshold B_a+B_b cofinite ⟺ 1/(a−1)+1/(b−1)≥1 PASSED 8/8 vs ground truth. → cassels_thickness_theorem_attempt.md.
- [DEAD END, useful] Thickness/interval-filling proof ATTEMPTED, dies at MW wall. 4 death points:
  (#1) raw Newhouse τ=1/(d−2) wrong threshold; (#2) no PAIR of bases≥3 reaches ∑=1 (max 0.833), so
  2-set theorem vacuous in regime; (#3) (★-cover) false — partial P (∑<1) has BOUNDED runs, no
  intervals; (#4) **bridging is irreducibly multi-atom** — single-base/single-translate/sequential
  decompositions PROVABLY fail (P bounded runs + d_r-powers outgrow them). 581-dodge dissected
  explicitly: 581−{0,7,49,56,343,350,392,399} all ∉ 3·B_3+4·B_4. RULES OUT sequential-thickness
  attacks; confirms wall intrinsic. → cassels_thickness_theorem_attempt.md.
- [PROVED — elementary, k=0; KNOWN result, NOT novel] ∑1/(d−1)≥1 ⟹ ∑_D B_d = ℕ (CONTIGUOUS from 0,
  stronger than cofinite), via Cassels-from-0. Key estimate: S(X)=∑_d (d·x_d−1)/(d−1) ≥ (m−1)·∑1/(d−1)
  ≥ m−1 where m=next atom, x_d=largest d-power ≤X; so next atom ≤ S(X)+1 for ALL X; seed 1=d^0 ⟹
  fills [0,∞). Transcendence-FREE, no gcd, SHARP (∑<1 fails: (3,4) gap at 62). This is the TEXTBOOK
  COROLLARY of Brown 1961 / Cassels 1960 (Alexeev's PUBLIC Erdos124b.lean reproves it; see scholar
  correction below) — value is as a clean Lean base case + the k≥1 gap diagnostic, NOT novelty.
  The JOINT covering at k=0: estimate sums over ALL bases at once
  (respects death-point #4). Lifts to k≥1 FAILS exactly at the lost 1-seed + d^{1−k} density decay
  ⟹ that's where MW enters. Verified 0/8000 violations to 10^15. → cassels_k0_elementary_proof.md.
  - [CORRECTION, scholar] The "(no public proof exists)" above is WRONG — I retract my earlier read.
    k=0 IS public: Alexeev Erdos124b.lean (407 lines, plby/lean-proofs, Dec 2025) reproves Brown's
    criterion via greedy u_seq + base-d digits = THIS proof; Thomas Bloom described it in the Xena
    blog comments ("obvious induction… single inequality"). So cassels' k=0 is KNOWN (= Brown 1961 /
    Cassels 1960 corollary), CORRECT but NOT novel. Do NOT publish as new / claim Q1 attribution / submit
    as open. Value: internal Lean base case + locates the k≥1 gap. SALVAGE: strict ∑>1 at k≥1 would be
    new (Brown/Cassels can't reach k≥1). → scholar_k0_priorart_verdict.md.
- [PROVABLE per-fixed-k, with lift] STRICT-EXCESS (σ=∑1/(d−1)−1>0) BEGL96 closes ELEMENTARILY for EACH
  FIXED k≥1: Lemma A (gap-condition holds for m≥m₀=(C'−1)/σ, C'=∑d^k/(d−1) — exact, extends past
  Brown/Cassels which is k=0 only) + lift's Lemma B (covering margin r(n)=#reps GROWS with n, faster
  for larger σ — verified (3,4,5) k=1: 5→179, (3,4,5,7) k=1: 62→4652; ⟹ value-holes close per fixed k)
  + modular residue coverage + carry class-wise AP. Transcendence-FREE, σ>0. NOT k-uniform: margin-growth
  rate degrades with k ((3,4,5) k=2 min#reps stuck at 1 to ~52k, N₀=77613); the 3 candidate uniform
  bounds (d_max^{2k}/σ, C·m₀, carry's (d_max·d_2)^k/σ²) ALL fail k-uniformity (carry's: ratio
  0.027→1.35→3.76 at k=1,2,3 for (3,4,5)). Uniform-in-k needs MW. → cassels_strict_excess_theorem.md.
  - [PRECISION (carry+sumset, agreed)] "closes for each fixed k" means: per-(D,k) cofiniteness is a
    FINITE computation (verify to threshold + bounded-gap tail), machine-verifiable and verified for all
    small D. It is NOT a UNIFORM-over-D elementary theorem even at fixed k — N₀(D,k) needs MW to bound a
    priori for clustered D, so it's case-by-case verification, not "all admissible D at this k" by a
    uniform elementary argument. sumset's (BLOCK) single-block test being vacuous for every family is the
    tell. Don't let the record read as a uniform fixed-k theorem.

## lift

- [PROVED] Residue Lemma: gcd(b,m)=1 ⟹ B_b surjective mod m (exponents 0,t,2t,…≡1; r of them give
  residue r). = clean form of BEGL Claim 4 (confirmed scholar/modular/sumset). → lift_sufficiency_mechanism.md.
- [PROVED+VERIFIED] gcd(D)=1 necessity k≥1: all-even D gcd=2 ⟹ ALL 2500 odds missing at k=1. → lift_gcd_necessity.md.
- [PROVED+VERIFIED] Digit recursion R_k=C_k+R_{k+1}, C_k={0,3^k}+{0,4^k}+{0,7^k}; ⟹ R_{k+1}⊆R_k
  (monotone thresholds), R_k = subset-sums of {3^j,4^j,7^j:j≥k}. Verified k=1,2,3 to 2·10⁵. → theorem_347_allk.md §A.
- [PROVED+VERIFIED] (3,4,7)-all-k k-uniformity: close pairs (3^p,4^q) FIXED (p∈{5,19,24,29,34}…,
  Δp≈5 = convergents of log4/log3); level-k uses only p,q≥k ⊆ them ⟹ MW input k-INDEPENDENT. maverick verified. → theorem_347_allk.md §B.
- [VERIFIED] (3,4,7) k=1 largest hole=581 (580,582–587∈R_1); reproduced 581/79/112/17 (corrected, not
  paper's 78/111/16). B_3+B_4 UNBOUNDED gaps (→7682, end at 3-powers); B_3+B_4+B_7 max gap 1 above 581.
- [CORRECTED] "liminf T(x)/x = β" is the asymptotic value (Weyl); exact integer arith (atoms to 5^120)
  gives true min ≈1.10 for {3,4,5}, just ABOVE β=1.083. Key fact: inf>1 when β>1. BUT inf>1 = Cassels
  partial-sum cond = NECESSARY NOT SUFFICIENT (troika: threshold 581≫Cassels bound; granular holes need
  MW). My "strict-β⟹cofinite" sketch OVERSTATES. → lift_cassels_liminf_theorem.md (corrected header).
- [RESOLVED] maverick's inf Q1/a=1/(d_max−1)=0.25 was a TRUNCATION BUG (atom-exponent list capped at
  79, dropping dominant base-3 mass below 5^79 ⟹ Q1 collapsed to base-5 ray = 1/(5−1)). maverick
  confirmed + retracted. True inf T(x)/x ≈ 1.10 > β=1.083 (my exact arithmetic, agreed). The 0.25
  figure is DEAD — use β / "inf≈1.10>1". maverick's "no Cassels argument works" conclusion WITHDRAWN.
- [LIT] BEGL96 proves (3,4,7) k=1 ONLY; all-k UNPUBLISHED; 124.lean tag over-claim. → lift_347_allk_and_validation.md.
- [PROVED+VERIFIED] §C.3 bridge mechanism CORRECTED (with troika): the B₃+B₄ gap set has POSITIVE
  measure (~8–40% in dyadic windows, NOT →0), so the "triple power-alignment forbidden by MW" framing
  is FALSE/RETRACTED. Real mechanism = density-overlap covering: each base-7 shift covers ~75% of a
  gap; the union of ~U^0.356 available shifts closes it. → lift_bridge_quantified.md, theorem_347_allk.md §C.3.
- [VERIFIED] Bridge make-or-break inequality (N=4·10⁷): margin = (B₇ shifts available)/(needed) =
  1.5–3.0× across all big gaps, STAYS >1 but DOES NOT GROW at the ∑=1 boundary. Closing the bridge =
  proving margin>1 ∀ scale = a circle-method/equidistribution statement (base-7 ray uniform mod the
  3/4-power gap structure), NOT MW. THE DEATH POINT of the clean MW-only (3,4,7)-all-k proof.
- [VERIFIED] Margin GROWS with excess σ (min #shift-reps: σ=0→17, σ=0.083→47, σ=0.25→64 at N=5·10⁵)
  ⟹ strict-excess (∑>1) is the cleanly-provable lane (cassels' Lemma A + density-overlap closes it);
  boundary ∑=1 is the hard frontier. → connects cassels_strict_excess_theorem.md Lemma B (the crux).
- [PROVED+VERIFIED] Class-wise seed lemma: N₀ = max over residue classes r mod M=d_min^k of class r's
  full-AP onset O_r. Exact: (3,4,5):82≈79, (3,4,7):584≈581, (3,5,7)k=2:293170≈293161. Rigorous form of
  cassels' Lemma B; seed length d_min^k (beats d_max^k). Within-class = CONSTRAINED DEFLATION
  (R_k∩Mℤ)/M (cofinite, contracts, has unit atom, but constrained ⟹ Lemma A' real content). → lift_classwise_seed_lemma.md.
- [PROVED, elementary] log2/log d > 1/(d−1) term-by-term ∀d≥3 ⟹ ∑(log2/log d) > ∑1/(d−1) ≥ 1 ⟹
  box-exponent ε>0 ∀ admissible D (even (3,4,7): ε=0.487). So the AVERAGE representation count
  r_D(n) → ∞ (like n^ε), uniformly, NO MW. The clean elementary half. → lift_box_reformulation.md.
- [VERIFIED, refutes own hope] k=1 is NOT unconditional: cofiniteness needs MIN r_D≥1, not avg→∞.
  min/avg for (3,4,7) DIPS 0.25→0.45→0.13 at [4M,6M] (power-coincidence stragglers). cassels' 0.27·C'/σ²
  GRAZED/violated by (3,4,6) (N₀=986>980). k=1 = "verified ∀ tested D + conjectured uniform bound", NOT unconditional.
- [REFORMULATION] All three open kernels [(BRIDGE), Lemma A', k=1 bound] unify as (KERNEL): for
  admissible D, the explicit counting function r_D(n) ≥ 1 for n>N₀ (equiv. min/avg r_D bounded below;
  avg→∞ PROVEN). MW's role = bounding the dip depth at power-coincidences. Sharpest open-core statement. → lift_box_reformulation.md.

## carry (constructive/algorithmic lane)

- [VERIFIED] BEGL96 cofinite for all 45 admissible D (d≤12,r≤4) at k=1 AND k=2; no counterexample,
  incl. 9-base stress D. Disproof lane dead for small D. → carry_constructive_findings.md.
- [PROVED] Reformulation: E124-open ⟺ atom set A(D,k)={d^j:d∈D,j≥k} is a complete sequence.
- [VERIFIED] +b^k closure (= cassels' Lemma C cond (b)): R closed under +M=b^k above threshold, last
  failure at thr−M. Each residue class mod M is a full AP above its per-class threshold. (My Obs 1.)
- [VERIFIED] Late missing values are ISOLATED singletons at power-clustering points (3^5≈4^4) — the
  MW regime. (3,4,7)k1 final gaps {264,521,581}. = the isolated-gap-killer / open core.
- [VERIFIED] BEGL Claim 1 (β>2) UNREACHABLE for any single D in regime ∑∈[1,2): total atom harmonic
  mass = ∑1/(d−1) at k=1. Right bulk tool is maverick's Lemma BG (∑≥1), not Claim 1.
- [CORRECTED, w/ sumset] Excess δ TAMES {3,4} clustering: k=2 threshold collapses monotonically with
  δ even WITH {3,4} present (242113→77613→1068→312→184 as δ:0.033→0.829). My earlier "clustering
  δ-independent / no MW-free bound even with slack" was WRONG (tested only at small δ). At large δ
  extra bases route around the 3^p≈4^q shadow. ⟹ OPENING for strict-excess theorem (task #17): δ large
  enough ⟹ elementary threshold bound, no MW. Boundary δ=0 still needs MW (separate).
- [VERIFIED] Single-block append cannot close: max consecutive-atom ratio = 3.0 > 2 for any D∋3
  (81→243). Closure intrinsically multi-atom. Greedy-from-top fails 775/1419. (Root-causes maverick's
  ratio>2 obstruction.)
- [CORRECTED by breaker] (3,4,7) k2 = 3,982,888 (my earlier 785743 was a single-plateau straggler
  trap); growth k1→k2 = ×6855. Use strict 2-doubling + max<N/2 test, never single plateau.
- [VERIFIED] BEGL96 errata (w/ scholar): Pow({3,4,5};1)=79 (paper 78), {3,5,7,13}=112 (111),
  {3,6,7,13,21}=17 (16); (3,4,7)=581 correct. Each paper value provably representable.
- [VERIFIED] Subset-monotonicity (sumset's): T_k(D)⊇T_k(D'') for D''⊆D — BUT only reduces D if a
  PROPER ADMISSIBLE subset exists (Pomerance+gcd force admissibility for cofiniteness). Enumeration:
  of 115 strict-excess admissible D (d<12,r≤5), 72 reducible (EASY, max k=1 thr 74), 43 MINIMAL
  (HARD, max k=1 thr 986, = all {3,4}-clustering cases). Minimal/non-minimal split = exactly
  hard/easy. ⟹ strict-excess theorem structures as: non-minimal (trivial via monotonicity) + minimal
  (needs direct class-onset bound). → /tmp/e124_subset_exists.py, _minimal_hard.py.
- [FITTED-not-proven k=1 / REFUTED k-uniform] Lemma A' (class-onset bound, task #17): N₀(D,1) ≤
  0.27·C'/σ² is a FITTED constant, NOT clean — GRAZED/EXCEEDED by (3,4,6): N₀=986, 0.27·C'/σ²=980,
  ratio 0.2716>0.27 (cassels/lift caught this; my earlier "clean" overstated). Even at k=1 the
  cofiniteness CLOSURE is VERIFIED-not-PROVEN: N₀ finiteness = +M-closure terminates = the MW kernel,
  ≫ m₀ (8/27 have N₀>m₀). The k-uniform form N₀≤K·(d_max·d_2)^k/σ² with absolute K is FALSE: K grows
  0.046→1.347→**3.759** (k=1,2,3 on (3,4,5); N₀(3,4,5,k=3)=4,330,731 verified N=12M; oscillates, no
  clean base). ⟹ ONLY genuinely-unconditional results in the strict-excess thread: (1) k=0 base case
  (Brown/Erdős, known), (2) non-minimal D via subset-monotonicity (carry). All k≥1 strict is
  VERIFIED/CONDITIONAL. → Lemma PCA (carry, scoped fixed-k/finite-onset) in cassels_strict_excess_theorem.md.

## troika

- [TASK #28 — MINIMAL TRANSCENDENCE REQUIREMENT, troika] The weakest sufficient transcendence input for
  the E124 (3,4,7) straggler/cofinite half:
  • FORM: THREE PAIRWISE two-log bounds (Baker/MW for |3^a−4^b|, |3^a−7^c|, |4^b−7^c|) — NOT a single
    three-log linear form. The bridge fails arc-by-arc, each arc governed by ONE pair's convergent.
  • BINDING PAIR: log4/log3 (the 3–4 pair) has the largest CF partial quotient (a_k=112), deepest
    convergents ⟹ |3^a−4^b| binding (exactly BEGL96's displayed |3^p−4^q|). Empirical local irrationality
    exponents: μ(log4/log3)≈3.0, μ(log7/log3)≈2.6, μ(log7/log4)≈3.4 (all finite, >2).
  • STRENGTH: only CONVERGENT-DENOMINATORS need the bound (not all q); ANY effective polynomial rate
    suffices (no specific exponent). WELL WITHIN known effective Baker/MW (finite μ).
  • §C.1-vs-§C.3 TENSION RESOLVED: BOTH right, different halves (Astels split). §C.1 (two-log MW
    sufficient) is correct for the STRAGGLER half. §C.3 ("MW insufficient") conflated the FULL bridge =
    Astels(β/density, NO transcendence) + MW(stragglers). MW two-log IS sufficient for the cofinite
    upgrade alone; β-discrimination is Astels. → INVENTIONS.md (Round 6 + ASTELS RECONCILIATION);
    coordinate baker (canonical inequality) / gelfond (comparison table).
- [VERIFIED, BEGL96 PDF] BEGL96 proves (3,4,7) for s=1 ONLY (largest hole 581, via Mignotte–Waldschmidt
  |3^p−4^q| bound). All-k version (Lean ne_zero_three_four_seven {k≠0}) NOT in paper ⟹ `research solved`
  tag OVER-CLAIM. Paper's general Thm 1 needs positive upper density (false for finite D). Confirms scholar.
  → troika_347_reverse_engineered.md.
- [VERIFIED, 3 engines] PAPER ERRATUM: BEGL's "similarly" values off by +1. Correct largest-miss:
  (3,5,7,13)=112, (3,6,7,13,21)=17, (3,4,5)=79. Only MW-computed 581 exact.
- [CORRECTED] My earlier (3,4,7) N₀(2)=785743, N₀(3)=57751591 were TRUNCATION ARTIFACTS (breaker/cassels
  caught it). TRUE: 581 / 3,982,888 / 166,025,260, confirmed 3 engines.
- [PROVED, verified 5429 families] MULT-INDEP-PAIR LEMMA: every admissible D (gcd=1, |D|≥2) has a
  multiplicatively-independent pair {a,b}. Proof: mult-dependence is an equivalence (classes=powers of a
  common base); no indep pair ⟹ all D powers of one c ⟹ c|gcd(D), contra gcd=1. ⟹ MW always applicable.
  → troika_generalization_mechanism.md.
- [PROVED, verified N=3.2e7] BAND-BOUNDARY MECHANISM: exceptionals sit in thin bands just below base
  powers; GRANULARITY failure not density (total atom-sum > n with headroom, yet n unreachable). Cassels
  interval lemma underestimates N₀ by 200×–29000× ⟹ boundary non-elementary, needs MW.
  → troika_cassels_insufficient.md, troika_band_closure_mechanism.md.
- [PARTIALLY RETRACTED] §C of theorem_347_allk.md. KEPT: MW bound |3^p−4^q|≥3^p·exp(−C(logp)²)
  [C≈1.22 verified]; §C.2 B₃+B₄ gaps unbounded ∝ top power. **WITHDRAWN (lift flagged, I verified):**
  the "hole ⟹ TRIPLE alignment, closed by MW, complete-modulo-one-constant" framing — FALSE premise
  (B₃+B₄ gaps have POSITIVE measure 8–21%, not →0). Triple-alignment only explains the LOCATION of
  finite-scale worst holes, not closure.
- [CORRECTED, verified] §C.3 true mechanism: DENSITY-OVERLAP + EQUIDISTRIBUTION. n>581 has min 10
  base-7 representations, GROWING (10→40→63); each base-7 shift covers ~77% of a gap; union of
  ~log₇(n) shifts closes it. Local B₃+B₄ density dips to 0 in gaps ⟹ JOINT (not single-shift) covering.
  TOOL = circle-method / Weyl equidistribution of {l·log7} mod (log3,log4) lattice (Mauduit-Rivat/Maynard),
  NOT MW. MW only dispatches finitely many worst near-coincidences. = the genuine open analytic core.
  → troika_C3_correction_tool_assessment.md.
- [GUARDRAIL ACK, scholar] general-D MW DEAD END for ∀D; individual-set (3,4,7)-all-k SURVIVES but its
  open core is equidistribution (circle method), consistent with scholar's "boundary non-elementary".

## OPEN CORE (team consensus)
- [OPEN] For every admissible D (∑1/(d−1)≥1, gcd=1) and k≥1: the transcendence spacing never
  re-opens a nested top-of-power gap above n0(k), uniformly. = generalize BEGL96's (3,4,7)
  Mignotte–Waldschmidt argument to all admissible D. Equivalent to maverick's (SEED). Likely TRUE
  (breaker: all tested families finite; no counterexample; both side conditions provably necessary).

## breaker

- [RESOLVED] **(3,4,11) anomaly = DEEP STRAGGLER TRAP, converse SAFE.** cassels flagged (3,4,11)
  β=14/15=0.933<1 as apparently COFINITE at k=1 (N₀=1595 to 300M), which would contradict the
  Pomerance converse (k=0 cofinite ⟹ β≥1; valid via T_1⊆T_0 ⟹ T_0 cofinite). I tested the k=0 case
  directly (what the converse is about) with a validated fast atom-sieve engine: (3,4,11) k=0 has
  ZERO exceptions up to **9×10⁹** (past 11^9, 3^20, 4^16). BUT the converse is EXACT with no extra
  hypotheses (Grok lit-check + singularity analysis: misses ~ c·X^α, α=0 i.e. positive-density only if
  β<1 STRICTLY... correction: α<0 iff β>1, α=0 at β=1, and β<1 ⟹ infinite uncovered set of very low
  density). So the first exception EXISTS but lies beyond 9e9 — the deepest straggler trap yet.
  CONVERSE STANDS; cassels' "cofinite" was premature (frozen at 300M, exception >9e9). → breaker_34_11_*.py.
- [VERIFIED] The anomaly is NOT unique to (3,4,11): (3,5,7) β=0.917, (3,4,10) β=0.944, (3,4,12) β=0.924
  all show ZERO misses to 200M despite β<1 (all must have exceptions far out). Onset scale is wildly
  base-sensitive (transcendence/spacing): (3,4,9) β=0.958 has visible misses at 59048, but (3,4,11)
  β=0.933 has none to 9e9. Confirms BEGL/Pomerance: β<1 ⟹ infinite-but-arbitrarily-deep exceptional set.
- [TOOL] Fast exact atom-sieve engine: breaker_atom_sieve.py — rep|=rep<<(d^j) per atom, N=9e9 in ~50s.
  Validated bit-for-bit vs old engine + (3,4,7) k=2=3982888 + (3,4) k=0 correctly non-cofinite.
- [VERIFIED] THICKNESS RAW MATERIAL (artillery for Astels assault, tasks #14-16): single B_d has max
  contiguous BRIDGE = 2 for ALL d (thin Cantor set, Newhouse thickness≈0); gap/all-ones → (d−2) exactly.
  Thickness EMERGES from the sumset (max-bridge grows as bases added; →interval iff cofinite).
  ★ HARD CONSTRAINT for any discrete-thickness def: at finite N the global gap/bridge structure CANNOT
  separate cofinite from not — (3,4,7) β=1 and (3,4,11) β=0.933 both show max_gap=0 at 10M. A valid τ(D)
  must be LOCAL/SCALE-INVARIANT from atoms {d^j}, evaluating ≥τ_crit ⟺ β≥1 on the published ground-truth
  set. Standing by to test candidate τ(D) in minutes. → breaker_thickness_RAWMATERIAL.md.
- [VERIFIED] Pre-tested 3 thickness defs vs ground truth: harmonic Σ1/(d−1)≥1 SEPARATES (=Pomerance,
  CORRECT); naive Astels Σ1/(d−2) FAILS ((3,4) τ=1.5 beats cofinite); box-dim Σlog2/logd FAILS (355
  false positives d<20,r≤4, e.g. (4,5,6,7) box-dim 1.674 but β=0.95). ⟹ discrete thickness MUST
  normalize to 1/(d−1) per base, not a dimension. → breaker_thickness_RAWMATERIAL.md §6.
- [VERIFIED, TASK #15 TRAP] Interval-illusion fires BELOW β=1: (3,5,7) β=0.917 n0=523010, (4,5,6,7)
  β=0.95 n0=44 — both LOOK cofinite at 20M, both NOT (Pomerance). A "thickness≥1 ⟹ interval" lemma
  must conclude at β≥1 exactly, never from a finite observed interval. → §7.
- [VERIFIED] scholar's two-prime-power adversarial families (worst-case collinearity, bases 2^a/3^b)
  ALL cofinite k=1,2,3: (3,4,8,9),(3,4,8,27),(3,4,9,16) finite; (3,4,8,32),(3,4,9,27,81) finite but
  n0>2B at k=3 (β≈1.01 boundary stretch). + full local residue coverage mod 2^a,3^a. β≥1 defeats
  Melfi collinearity. → breaker_twoprime_fast.py, breaker_twoprime_local.py.
- [VERIFIED, OBSTRUCTION for maverick v4/v8] EXACT (non-gridded, rational) finite-stage Astels central
  gap of ∑_d C_d^(N): the v4 "scaled gap d_max^N·gap → 0 ⟹ effective seed" mechanism is NOT governed
  by the scalar excess ∑1/(d−1)−1. Decay is base-CONFIG-dependent: (3,5,7,8) ex=0.060 DECAYS (gap-free
  seed) but (3,4,5) ex=0.083 GROWS; (3,5,7,9) ex=0.042 GROWS yet IS cofinite (n0=6M). ⟹ a strict-excess
  theorem CANNOT have hypothesis "excess>0"; the symbolic gap-decay constant c must come from the actual
  Cantor-gap interleaving (need c<d_max), config-dependent. Verified maverick's own dichotomy (excess
  drives n0 size) + v6 negative (n0-ratios don't separate strict/boundary). → breaker_finite_astels_exact.py,
  breaker_astels_excess_threshold.py. Also verified cassels' thickness numerics: τ_d=1/(d−1) exact 2-set
  threshold 8/8, 581-dodge for (3,4,7) k=1 exact (Q={0,7,49,56,343,350,392,399}, all 581−Q ∉ P).
- [KILLED maverick's C5 bridge candidate] Second-moment/Chebyshev method (Φ(n)=#{c∈B_{d_r}:n−c∈P};
  E[Φ]→∞ + Var=O(E[Φ]) ⟹ Φ>0). DECISIVE KILL (shot 3, UNSOUND): at genuine misses Φ=0 while local
  E[Φ]≫1 — (3,4,7) k=2: Φ(3964625)=Φ(3982888)=Φ(785743)=0 with E[Φ]≈14; k=3: Φ(166025260)=0 with
  E[Φ]≈22. Verified large-deviation events; Chebyshev P(Φ=0)≤Var/E[Φ]² can't reach 0 when Φ=0 ∧ E[Φ]≈20.
  Also shot 1: Var is NOT O(E[Φ]) at scale (local var/mean climbs 1→7 as center 30K→25M; maverick's
  O(1) was a ~10⁴-scale artifact). The deep stragglers (my FALSE-branch witnesses) ARE the rare events
  the 2nd moment is blind to = MW wall in probabilistic dress. C6 (cov-decay) moot. → breaker_KILL_C5.md.
- [KILLED troika's band/orbit-averaged C5] The orbit-averaged-density fix (band-local Var/E≤C·E, ρ̄)
  fixed maverick's global-var artifact but CANNOT discriminate β=0.933 from β=1 (fails troika's own
  criterion). N=200M, d_r=last base: (3,4,7) β=1 COFINITE → Var/E=16.6, minΦ=80; (3,4,11) β=0.933 NOT
  cofinite → Var/E=12.3, minΦ=4 (BOUNDED, looks cofinite, 0 misses); (3,4,10) β=0.944 NOT → Var/E=7.6.
  C5-band falsely certifies (3,4,11)/(3,4,10) as cofinite. Structural: their first miss is >9e9, beyond
  any reachable N — no local statistic up to finite N can see it. (3,5,7) is the tell (threshold
  reachable → 24 misses seen). NO local-statistic bridge can separate β=0.933 from β=1; that's
  asymptotic Pomerance/MW content. → breaker_KILL_troika_C5band.md.

## maverick

- [VERIFIED] Scaling S(d,k)=d^k·B_d (independent brute-subset-sum, d∈{3,4,5,7}, k≤3). Confirms sumset.
- [VERIFIED] Residue coverage (L): gcd(D)=1 ⟹ ∑d^k·B_d covers ℤ/m, 14 families, k≤3, m<200. Confirms modular/lift.
- [VERIFIED] (3,4,7) k=3 largest hole = 166,025,260 (independent, two doublings N=340M/680M). Confirms breaker.
- [VERIFIED] (3,4,5) k=1 largest hole = 79 not 78 (3 methods). theorem_347 §B close pairs + B_7-bridges-gaps. Confirms lift/scholar.
- [PROVED+VERIFIED] Recursion T_k=C_k+T_{k+1} (C_k = 2^|D| lowest-digit offsets), T_{k+1}⊆T_k. = lift's §A independently. → maverick_recursion_engine.md.
- [RETRACTED] My "inf Q1(a)/a = 1/(d_max−1) = 0.25" was a TRUNCATION-BUG artifact (atom-exponent list capped at 80;
  Q1(5^79) missed dominant base-3/4 atoms). lift was RIGHT. CORRECT (exact geometric Q1, no truncation):
  inf Q1(a)/a ≈ ∑1/(d−1), k-independent, ZERO Cassels-filling violations for ALL admissible families
  ({3,4,5}:1.10, {3,4,7}:1.03, {3,5,7,9}:1.11, {4,5,6,7,8}:1.27, {3,4,6}:1.04); <1 only sub-threshold
  ({3,4}:0.83, {3,4,9}:0.96). So inf Q1(a)/a ≥ 1 ⟺ ∑1/(d−1) ≥ 1 ⟺ admissible. My earlier
  "elementary methods provably fail" negative is WITHDRAWN. → maverick_bounded_gap_lemma.md (corrected).
- [VERIFIED, proof OPEN] {4,5,6,7,8} k=1 cofinite from 4 (n0=3) — gap-free [4, 1.5×10⁹] VERIFIED.
  NEW instance not in BEGL96's list. NO clean elementary PROOF though: Brown's a_{n+1}≤S_n+1 (cumulative
  Q1) has 0 violations, but that only bounds the SUM — proving subset-sums cover [r,S_n] CONTIGUOUSLY is
  the real content; single-interval extension STALLS at powers (ratio>2 ⟹ closure is multi-atom). So even
  d_min=4 needs the multi-atom seed-fill = the open step, just at tiny n0. Do NOT ship as proven elementary
  theorem. → maverick_seed_interval_pinned.md.
- [RESOLVED w/ cassels+lift] my 0.25 retraction: cassels attributes it to "d_max-ray-alone sum"; I trace it
  to a truncated atom-list (Q1(5^79) missing base-3/4 atoms). Same root: merged inf ≈ β ≥1 for admissible.
  Both explanations consistent; the 0.25 figure is DEAD. Use β=∑1/(d−1) (lift). → CLAIMS lines 88-90, 130-135.
- [OPEN] (SEED) reduction: E124-open ⟺ full multi-atom subset-sum gap-free above finite n0(k); scaffold all
  proven; gap-formation/seed = isolated-gap elimination = MW/transcendence for general D. = team consensus.

## maverick (ASSAULT round — discrete thickness / route a)

- [PROVED] γ(C_d) = τ/(1+τ) = 1/(d−1) EXACTLY (τ=Newhouse thickness=1/(d−2), γ=Astels normalized).
  ⟹ Astels 2000 (∑γ≥1 ⟹ sumset has interval) SOLVES the REAL analogue of E124 at threshold
  ∑1/(d−1)≥1. Rigorous origin of the conjecture's invariant. → maverick_ASSAULT_thickness.md.
- [PROVED-argument] Incommensurability of per-base scales is ABSORBED by scale-invariance of thickness
  (γ((1+ε)C_d)=γ(C_d)). Kills the naive "no common scaling" death point.
- [FALSIFIED] "strict excess ∑1/(d−1)>1 ⟹ effective/elementary cofiniteness" — BROKEN by {3,4,6}
  (δ=+0.033>0, gcd=1, yet C=n0/(d_max·d_2)^k = 41,420,3000 GROWS in k; n0(1)=986 > boundary 581).
  Root: 6=2·3 ⟹ 6^j=3^j·2^j ⟹ |2^a−3^b| MW clustering survives strict excess.
- [REFUTES density] density_strict_excess_thickness_margin.md claims "threshold ≤ C(δ,D)·(d_max·d_2)^k,
  C const in k for any δ>0" — FALSE, {3,4,6} has C growing 10×/k. Alerted density. CORRECTED:
  effective iff δ > δ₀(D) where δ₀ set by closest cross-base |p^a−q^b| (itself MW). High-margin
  families ({3,4,5,6,7,8,9} δ=.72: C≈.01–.04 bounded) ARE effective; it's a margin-vs-clustering
  competition. So a HIGH-MARGIN sub-class is elementary; route (a) does NOT bypass MW in general —
  it quantifies exactly when MW is needed (margin < clustering) vs dodgeable.

## density (assault addendum — appended to avoid edit race)
- [QUANTITATIVE/supports sumset] Thickness-margin explains sumset's geometric threshold law: at ∑=1+δ
  the first-level d_min-power gap is over-covered by δ·d_min^m; threshold constant C=thr/(d_max·d_2)^k
  collapses with δ (C·δ ≈ 0.46→0.07→0.014, k=3). → density_strict_excess_thickness_margin.md.
- [DEATH POINT, strict excess] Three framings (thickness superadditivity / base-induction / reach-set
  intersection) ALL hit the SAME MW wall. Base-induction DEAD (tail margins negative past level 0;
  covering is CRT-coupled, not per-base). Reach-intersection (n−B_{d_min})∩(∑_{d>d_min}B_d)≠∅ NOT forced
  by density sum — fails iff gaps align = MW. Margin δ makes aligned gaps rarer, not impossible.
  NO transcendence-free proof of strict-excess BEGL via measure methods. → density_thickness_assault.md.
- [NEW LEAD/open] Many-base large-d_min families (e.g. (4,5,6,7,8)): SUB-sumset ∑_{d>d_min}B_d is itself
  near-interval (maxgap=1 to 2e5, sub-∑=0.76<1) ⟹ reach-intersection forced WITHOUT alignment control
  ⟹ possible transcendence-free SUB-theorem (not full scope). Handed to sumset/cassels.

## maverick (k=0 milestone)

- [PROVED, elementary, airtight] k=0 theorem: ∑1/(d−1)≥1 ⟹ ∑_{d∈D} B_d = ℕ (every n≥0, stronger than
  cofinite; no gcd needed). Via Brown 1961: atom multiset {d^j:j≥0} has a_1=1, and S_{<a} ≥ (a−1)·∑1/(d−1)
  ≥ a−1 ⟹ Cassels/Brown gap condition holds at every atom. Sharp: ∑<1 fails at large powers (={3,4}@4194304).
  INDEPENDENTLY MATCHES cassels_k0_elementary_proof.md (same proof, exact formula S(X)=∑(d·x_d−1)/(d−1)
  VERIFIED by me). Two independent derivations agree. → maverick_k0_elementary_proof.md.
- [KEY for k≥1 lift] The k≥1 obstruction is now PRECISE: at k≥1, a_1 = d_min^k > 1 (the value-1 atom
  d⁰ is GONE), so Brown's seed [0,·] can't start and the per-base mass becomes ∑d^{1−k}/(d−1) < 1 (decays
  in k). The ENTIRE difficulty of k≥1 = "regain the seed without the 1-atom" — exactly where cross-base
  spacing (MW) re-enters. Brown IS the k=0 proof; thickness machinery is not needed for k=0.

## density (strict-excess flagship — measure/margin leg)
- [VERIFIED+mechanism] MARGIN-GROWTH leg DONE as mechanism+reduction. The covering margin =
  (surplus reach δ·U)/(residual alignment gap) GROWS linearly in U for ALL strict excess δ>0 —
  NOT just droppable-base families. EXACT check: largest upper-half gap = 1 (U-independent) for
  (3,4,5) δ=0.083, (4,5,6,7,8) δ=0.093 [no base droppable!], at k=1,2 to N=5e7. Contrast boundary
  (3,4,7) k=3 gap>1 at 1e8 (MW). vs lift's static 1.75× at boundary. → density_margin_growth_leg.md.
- [REDUCTION] Surplus δ·U (scale-invariant in k, from max-reach ledger γ(B_d)=1/(d−1)) overtakes the
  alignment gap at U₀ ~ (gap)/δ. Composes with sumset/cassels' bound (alignment gap ≤ C·d_max^k) to
  give threshold X₀ ≤ C(δ)(d_max·d_2)^k. Explains measured 1/δ threshold-constant scaling.
- [OPEN/shared] Remaining obligation (sumset+carry leg): prove residual alignment gap is O(d_max^k),
  not U-growing. Once that holds, my surplus closes it uniformly in k. The "drop one base" margin is
  a special case (works iff ∑_{d≠d_r}1/(d−1)≥1); the surplus δ·U is the general object.

## density × cassels × maverick (three-way convergence, confirmed)
- [CONVERGENCE, confirmed by cassels] Three languages, ONE wall: my thickness-superadditivity death
  point (DP4) = cassels' +M-closure ONSET = maverick's SEED existence = MW |d_i^a − d_j^b|. cassels
  confirmed his interval-extension (Lemma C) is PURE ARITHMETIC (residue induction mod M=b^k, no
  alignment) GIVEN the seed; the only open piece is seed/+M-closure onset = my alignment-gap.
- [REFINEMENT from cassels] The seed splits: (i) residue M-block = gcd=1 driven (modular's L), EASY,
  past a finite point; (ii) +M-closure onset = MW, HARD. Maps onto my surplus(easy/mass)/alignment
  (hard) split and lift's (R)/(A). At STRICT EXCESS, my surplus δ·U handles (ii)'s onset elementarily
  (no MW) IFF sumset's alignment-gap is O(d_max^k); at the BOUNDARY δ=0, (ii) needs MW.

## maverick — VERIFICATION SIGN-OFF on cassels' k=0 proof (priority verify)

- [VERIFIED — SIGN-OFF] cassels_k0_elementary_proof.md (∑1/(d−1)≥1 ⟹ ∑B_d = ℕ) is CORRECT and
  airtight. Attacked all 4 lead-specified points:
  (1) merged-subset-sum = ∑B_d: airtight via BIJECTION (subsets of A indexed by (d,j) ↔ tuples a_d),
      NOT just computational. Value collisions (64=4³=8²) and unit-multiplicity-r handled correctly
      because A is indexed by (d,j) not by value. ✓
  (2) estimate S(X) ≥ (m−1)∑1/(d−1) ≥ m−1: independently re-derived, exact closed form
      S(X)=∑(d·x_d−1)/(d−1); m=min_d(d·x_d) well-defined under ties (min value); verified over 2000
      random X up to 10^40 (always holds, margins huge positive). ✓
  (3) =ℕ exactly incl small n: r=1 NEVER admissible (1/(d−1)≤1/2<1 for d≥3) ⟹ r≥2 ⟹ n=2 always
      reachable via two units; verified [0,20000] full for all admissible families tested. ✓
  (4) numerical at scale: ∑B_d=[0,3×10⁷] gap-free for (3,4,7),(3,4,5),(3,4,5,7). ✓
  TRAP NOTE: cassels' CLOSED-FORM S(X) is immune to the atom-list-truncation artifact (a naive
  sorted-list Cassels test spuriously "fails" at huge atoms when the list is capped — NOT a real flaw).
  VERDICT: k=0 theorem PROVEN, headline-ready, Aristotle-dossier-#1-ready. Independent of my own
  derivation which matched it exactly.

## density (strict-excess theorem CORRECTION — maverick's catch, verified)
- [REFUTED unconditional / RESCUED conditional] My strict-excess theorem (threshold ≤ C(δ)(d_max·d_2)^k)
  is FALSE as stated — maverick's {3,4,6} (δ=0.033, gcd=1, admissible) verified: C=41→420→4264 (~10×/k),
  threshold 58,941,162 at k=3 (stable N=8e8). Root: 6=2·3 ⟹ |6^a−4^b| shares prime 2 = MW pair at
  binding scale; n0(1)=986 > boundary {3,4,7}'s 581.
- [SUFFICIENT hypothesis] gcd(d_max,d_2nd)=1 (two largest bases coprime) ⟹ bounded C. Verified for
  6 families incl. {3,4,5,6,7},{4,5,6,7,8},{3,4,6,7},{3,4,5,9} (shared primes among SMALLER bases OK).
  WEAKER than maverick's "fully mult-independent". → density_strict_excess_thickness_margin.md.
- [HONEST/not necessary] gcd(d_max,d_2)>1 does NOT always break it: {3,4,9,12} (gcd(9,12)=3) has
  bounded C (8.1→5.5→4.2, stable N=5e8). So gcd(d_max,d_2)=1 is SUFFICIENT not NECESSARY; exact
  pathology condition narrower (likely also needs low r / small redundancy as in {3,4,6}). Surplus δ·U
  leg UNAFFECTED; the failure is in the residual-gap=O(d_max^k) assumption, which needs the extra hyp.

## maverick (INVENTION round — bridge tool)

- [INVENTED, survives, reduction] C5 second-moment covering for (BRIDGE): Φ(n)=#{c∈B₇,c≤n:n−c∈P}
  (P=3B₃+4B₄). (BRIDGE) ⟸ Var[Φ]≤C·E[Φ] ⟹ Chebyshev ⟹ Φ(n)>0 for n≥n*(C), n*~(C²/ρ)^{1/0.356}
  EFFECTIVE; holes in [X₀,n*]=finite check. Transforms worst-case-MW into effective 2nd-moment + finite check.
  Verified: Var/E=O(1) (≈0.3–2.4, bounded incl. at 3⁵≈4⁴ coincidences and β-boundary); minΦ grows 1→186.
  → maverick_INVENT_bridge.md.
- [KEY identity] Cov(c,c') = R_P(c−c')−ρ² (P-autocorrelation). Var[Φ]=∑_{c,c'}(R_P(c−c')−ρ²).
- [HONEST DOWNGRADE] My "C elementary (escapes MW)" claim is NOT established. ∑|Cov| (absolute) likely
  grows ∝M (absolute summability FAILS); Var=O(E) holds via signed CANCELLATION (base-7 shifts
  anti-correlated, signed row-sum −4.2). The cancellation is delicate and MAY hide power-spacing. So
  the MW-escape is UNPROVEN, maybe false. The REDUCTION (worst-case→2nd-moment+finite) is the solid
  deliverable; open piece sharpened to "prove ∑_{c,c'}(R_P(c−c')−ρ²)=O(M)". Sent to breaker.

## density × maverick (UNIFIED: competition framing + Baker corner)
- [SYNTHESIS] The strict-excess theorem is a MARGIN-vs-CLUSTERING competition (maverick): effective
  iff δ > δ₀(D), where δ₀ ~ c(D) = closest relative approach min|d_max^a−d_2nd^b|/scale of the two
  largest bases. δ/c discriminates: {3,4,6} 0.9 (DIVERGES), {3,4,9,12} 0.6 (elevated), all
  gcd(top-two)=1 families ≥2.5 (clean). δ₀ is itself MW (transcendental).
- [CLEAN SUFFICIENT, transcendence-free] gcd(d_max,d_2nd)=1 ⟹ Baker bounds |d_max^a−d_2nd^b| below
  ⟹ c(D) bounded below ⟹ δ₀(D) small ⟹ ANY δ>0 works. So coprime-top-two is the transcendence-free
  CORNER of maverick's competition. Genuine partial theorem: {gcd(D)=1, ∑1/(d−1)>1, gcd(d_max,d_2nd)=1}
  ⟹ cofinite ∀k. → density_strict_excess_thickness_margin.md "Unification" §.

## maverick + breaker JOINT VERDICT on C5 (settled)

- [KILLED as proof, SOUND as filter] C5 second-moment bridge. breaker_KILL_C5.md + reconciliation.
  CASE (a) confirmed: all Φ=0 stragglers (785743/3982888/166025260) are AT/BELOW N₀ of the BOUNDARY
  family (3,4,7) ∑=1 — genuine non-representable points. C5 NEVER falsely certifies a covered n
  (minΦ>0 wherever representable). So it's a SOUND filter. But DEAD as proof: (shot 3) Φ=0 at N₀ while
  E[Φ]≈14–22 = large-deviation event Chebyshev can't exclude; (shot 1) Var=O(E) FAILS over wide windows
  (var/mean climbs 0.9→8.4 across 7-power transitions; maverick's bounded 0.3–0.6 was too-narrow 20K
  windows — breaker right). Signed-cancellation question MOOT. The open core re-localizes to: the
  LARGE-DEVIATION rate of P(Φ(n)=0) at cross-base power coincidences = the MW kernel in probabilistic
  dress, NOT a new escape. → maverick_INVENT_bridge.md (joint verdict), breaker_KILL_C5.md.

## maverick — ADJUDICATION of the strict-excess theorem (team-lead ordered)

- [VERDICT: NOT-A-THEOREM, general k] per-fixed-k strict-excess does NOT close elementarily.
  → maverick_ADJUDICATION_strict_excess.md.
- CHECK 1 (lift Lemma B): SPLIT. Identity N₀=max_r O_r PROVEN (trivial, =def). Content "within-class
  gaps close by density from m₀" NOT PROVEN — (3,4,5) k=1 onsets 63/79/74 EXCEED m₀=37 by 2× ⟹
  min-reps-grow⟹holes-close is the coverage-blind-to-internal-gaps trap. lift's own file concedes it.
- CHECK 2 ({3,4,6}): k=1 bound N₀≤0.27C'/σ² FAILS {3,4,6} (986>980, gcd(top2)=2), holds all gcd(top2)=1
  families ⟹ silently needs density's gcd(d_max,d_2nd)=1. Density VINDICATED. Constant 0.27 fitted (razor margin).
- CHECK 3 ledger: PROVEN={Lemma A m₀=(C'−1)/σ, residue coverage, Lemma M non-minimal, k=0 Brown};
  NOT PROVEN={Lemma B step 2, Lemma A' (K diverges .05→1.35→3.76 @ k=1,2,3), general-k cofinite}.
- SHIP: Lemma A + Lemma M + k=0 proven; "strict-excess ∀k CONDITIONAL on Lemma A'(OPEN)"; NOT "closes
  elementarily". CITATION: Brown 1961 + Erdős 1962, NOT phantom "Cassels 1960". Writeup HELD pending downgrade.

## maverick — CANONICAL strict-excess adjudication (extended, all 3 versions)

- [density theorem: FALSE as stated] gcd(top2)=1, ∑>1 ⟹ N₀≤C(δ,D)·(d_max·d_2)^k REFUTED on {3,4,5}
  (in-scope: gcd(5,4)=1): N₀/20^k = 4→194→541 grows, C not k-independent. gcd(top2)=1 NECESSARY (kills
  {3,4,6}) but NOT SUFFICIENT. MISLABEL: proof uses a "Baker floor" (|d_max^a−d_2^b| lower bound) ⟹
  correct label BAKER-CONDITIONAL, not "transcendence-free".
- [sumset MECHANISM why it fails, + two fixes to the gate] (i) the relevant pair is the WORST-CLUSTERING
  pair, NOT the top-two: {3,4,6} top-two (6,4) gcd=2 but worst cluster {3,4} gcd=1; {5..10} top-two (9,10)
  gcd=1 but worst cluster {6,10} gcd=2 — so "gcd(top-two)=1" is the wrong gate. (ii) Even all-pairs-coprime
  is NOT sufficient: {3,4,5} has every pair coprime AND δ=0.083 > each single pair's clustering (~0.046)
  yet N₀ grows — the effective obstruction is the COMBINED multi-pair clustering g*_combined > any single
  pair. Real criterion: δ > g*_combined (empirically holds at large δ: {3,4,5,7} δ=.25 → N₀/35^k=.63/.57/1.83;
  {3,4,5,7,11,13} δ=.43 → .04/.01/.00). Single-pair Baker floor does NOT bound g*_combined uniformly in k.
- [CANONICAL UNIFIED STATEMENT] Strict-excess splits (Lemma M): NON-MINIMAL D (proper admissible
  subset exists, 72/115) PROVEN elementary cofinite ∀k; MINIMAL D (43/115, incl all {3,4}-clustering)
  OPEN = MW/Baker wall (K: .05→1.35→3.76; N₀/scale^k: 4→194→541, both diverge). Separately PROVEN: k=0
  (Brown ∑B_d=ℕ), Lemma A (m₀=(C'−1)/σ, σ>0/σ=0 split), residue coverage. CONDITIONAL: k=1 needs
  gcd(top2)=1 (Baker floor). NOT-A-THEOREM: per-fixed-k elementary closure, all-strict-excess C-const.
  → maverick_ADJUDICATION_strict_excess.md (extension). Citations: Brown 1961 + Erdős 1962.

## density (FINAL measure-side scoping — reach is blind to internal gaps)
- [CLEAN NEGATIVE, with sumset] reach/thickness/top-of-power criteria are BLIND to internal gaps.
  Counterexample (sumset, verified by density): (5,6,7,8,9,10) ∑1/(d−1)=2509/2520=0.9956<1 (NOT
  cofinite) yet reach/n >1 at all scales (≥2.06 at sumset's grid) + top-of-power margin positive to
  5^39. "reach≥2 ⟹ cofinite" is FALSE.
- [SCOPING] The measure side cleanly splits the problem: COARSE gaps (top-of-power) = easy, covered
  for ALL admissible D, my formula PREDICTS their location (validated (4,5,6)→241025). INTERNAL gaps
  (between powers) = the MW-hard open core, invisible to every reach/measure (D1-D6 all range-blind;
  reach blind per (5,6,7,8,9,10)). 4th independent angle (residue/bulk/value-coverage/thickness) all
  hit the internal-gap/MW wall. → density_margin_growth_leg.md final §.
- [CONDITIONAL theorem status] strict-excess gcd(top-two)=1 theorem stands but its proof needs
  internal-gap residual = O(d_max^k), itself MW-hard; Baker supplies it for coprime-top-two only. So
  "transcendence-free" holds modulo that bound. No unconditional elementary proof from the measure side.

## density × sumset (SHARPEST localization: runs vs singletons)
- [RUN-BOUND, rigorous-modulo-Baker] margin/surplus δ·U kills missing RUNS (length≥2): no run≥2
  survives above C(δ,D)·(d_max·d_2nd)^k, under gcd(D)=1, ∑1/(d−1)=1+δ>1, gcd(d_max,d_2nd)=1. Clean
  ELEMENTARY partial (the coarse/length obstruction fully handled). Verified k=2: (3,4,6) last run≥2
  at 44,817; (3,4,5) 57,404; (3,4,5,6,7) 103.
- [DEATH POINT, sharpened] δ·U is a LENGTH argument; it CANNOT close isolated SINGLETONS (run-len-1
  value-specific misses), which persist far past the last run: (3,4,6) singletons to 242,113 (vs run
  44,817); (3,4,5) to 77,613. A singleton n is "n ∉ ∑d^k·B_d as an exact equation" = residue-
  equidistribution at the binding scale = MW core. → density_margin_growth_leg.md.
- [SHARPEST OPEN-CORE STATEMENT] The open content is NOT vaguely "internal gaps" but specifically
  RUN-LENGTH-1 misses — single non-representable values, locations governed by cross-base power
  equidistribution (MW). Elementary methods cover all of S except a residue-controlled set of isolated
  points. Tightest MW target the team has produced.

## density (gcd(top-two)=1 VINDICATED — maverick's adjudication)
- [VINDICATED] My gcd(d_max,d_2nd)=1 hypothesis is the silently-assumed side-condition of carry's k=1
  strict-excess bound. maverick's adjudication: bound holds for ALL gcd(top2)=1 families (3,4,5: 79≤159;
  3,4,5,7: 22≤23; 3,5,7,9: 112≤784) but FAILS the UNIQUE gcd(top2)=2 family {3,4,6} (986>980). Verified
  {3,4,6} is the unique gcd(top-two)=2 family AND unique violator in the test set. → maverick_ADJUDICATION_strict_excess.md.
- [ROBUSTNESS caveat] {3,4,6} violation margin razor-thin (986 vs 980 = 0.6%) and the 0.27 constant is
  FITTED. So gcd(top-two)=1 is the correct STRUCTURAL hypothesis, but the numeric bound 0.27C'/σ² is not
  robust — state the theorem conditionally: threshold ≤ C(δ,D)·(d_max·d_2)^k, C not a fitted value.
  Combined with the run-vs-singleton finding: even this conditional bound is only a RUN-bound, not cofiniteness.

## density (INV-S9: RIGOROUS forward lemma on coarse gaps)
- [PROVED] ∑1/(d−1) ≥ 1 ⟹ NO top-of-power gap, for ALL admissible D. Proof: maxB(d,X)=(d^{L+1}−1)/(d−1)
  with d^{L+1}>X ⟹ maxB(d,X) ≥ X/(d−1); ∑_d maxB(d,d_min^m−1) ≥ (d_min^m−1)·∑1/(d−1) ≥ d_min^m−1, so the
  gap inequality fails. ∎ Verified: 0 violators across all admissible d∈3..12, r≤4. → INVENTIONS.md INV-S9.
- [SCOPE] One-directional: the REVERSE fails ((4,5,6,7) ∑=19/20, (3,4,8) ∑=41/42 are non-cofinite with NO
  top-of-power gap — interior/MW gaps). So S9 rigorously closes the COARSE (top-of-power = run) gap family
  in the forward direction; the INTERIOR (singleton/MW) gaps remain the open core. THIRD independent
  derivation of the coarse/internal split (density run-bound + sumset runs-vs-singletons + S9 flip).

## density (CORRECTIONS — maverick adjudication extension, both accepted)
- [REFUTED/WITHDRAWN] My "threshold ≤ C(δ,D)·(d_max·d_2nd)^k, C k-independent" is FALSE. {3,4,5}
  (satisfies gcd(D)=1, ∑=13/12>1, gcd(5,4)=1 — ALL hypotheses) has N0/20^k = 3.95→194→541, GROWS.
  The (d_max·d_2)^k ansatz is wrong; gcd(top-two)=1 is NECESSARY (kills {3,4,6}) but NOT SUFFICIENT
  for a geometric bound. Earlier geometric-bound claims WITHDRAWN.
- [MISLABEL CORRECTED] "transcendence-free" was wrong — the gcd(top-two)=1 corner uses a Baker floor
  (Baker = transcendence). Honest label: BAKER-CONDITIONAL.
- [SURVIVES, correctly labeled] (1) gcd(d_max,d_2nd)=1 necessary corner-killer; (2) margin-vs-clustering
  δ vs g* framing; (3) thickness γ(B_d)=1/(d−1)=Astels; (4) Baker-conditional RUN-bound (no run≥2 above
  some scale; not cofiniteness — singletons remain). NO clean geometric threshold. Canonical split holds:
  non-minimal D elementary (Lemma M); minimal D open (MW/Baker); gcd-top-two only refines WHICH minimal
  families are hardest. → density_strict_excess_thickness_margin.md adjudication-extension §.

## density × cassels (TRIANGULATED joint lemma — threshold T=v=U₀=gap/σ)
- [TRIANGULATED] cassels' +M-closure onset v = density's surplus-overtake U₀ = sumset's last-hole, ONE
  object: U₀ = v ~ gap(D,k)/σ + d_min^k. Verified (3,4,5): gap/d_max^k = 1.27/258.68/2887 (k=1/2/3);
  cassels' 258.68 = v·σ/25, v=77604. → density_margin_growth_leg.md, cassels_strict_excess_theorem.md.
- [JOINT LEMMA, per-fixed-k, BAKER-CONDITIONAL] D admissible, gcd(D)=1, ∑1/(d−1)=1+σ>1, gcd(d_max,d_2nd)=1.
  For each FIXED k: T_k cofinite, N₀=v+d_min^k. Density surplus σ·U overtakes the alignment gap (front)
  + cassels Lemma C extends above seed (back) — both elementary GIVEN gap(D,k)=O(d_max^k). The O-constant
  is k-DEPENDENT (grows for tight D: (3,4,5) 1.27→259→2887); its uniform-in-k boundedness = residual MW.
- [PRECISE ELEMENTARY/MW BOUNDARY] PROVEN per-fixed-k (transcendence-free given gap bound); SOLE
  non-elementary residue = the gap-constant's growth with k = uniform-in-k = MW. Supersedes withdrawn
  "k-uniform geometric theorem." This is the honest final strict-excess result.

## scholar — INV-C1 non-nesting Diophantine verdict (carry's question)
- [VERIFIED] INV-C1's NON-NESTING claim is a GENUINE elementary reduction, NOT disguised MW. Split:
  (Q-shrink) chain shrinks geometrically? YES — worst single-step contraction ratio (res/rem) is
  BOUNDED <1 uniformly even at near-coincidence n's: (3,5,7,9)k=2→0.76, (3,4,7)k=3→0.72; max chain
  len 14-15 ≈ log_{d_min}(N0). So chain length = O(log n) by geometric shrinkage ALONE,
  coincidence-INDEPENDENT. carry's worry (a chain encoding |d_i^a−d_j^b| small) does NOT materialize:
  a near-coincidence makes one residual SMALL, which HELPS contraction. So non-nesting ⊄ MW.
  CAVEAT: this resolves chain-LENGTH (Q-shrink), NOT valid-peel-EXISTENCE (Q-exist) — any residual
  MW lives in existence (carry's top-3-lookahead), a DIFFERENT, possibly-easier question. The wall, if
  any, moved off non-nesting onto existence.

## maverick — CORRECTION (cassels caught it): merged Cassels condition HOLDS at d_max^J

- [RETRACT my "1/(d_max−1) / Cassels fails at d_max^J"] That was the SINGLE-d_max-RAY sum, NOT the
  merged Cassels predecessor sum. VERIFIED (exact): merged S(<a)/a at a=7^J for (3,4,7) k=1 ∈ [1.25,2.38],
  HOLDS for all J≥1 (only trivial a=3 fails). cassels right. The merged Cassels gap-condition HOLDS at
  every large atom (σ>0 ⟹ explicit onset m₀=(C'−1)/σ; σ=0 boundary holds w/ margin ≥1.25 empirically).
- [STRATEGIC CORRECTION] Obstruction is NOT "Cassels fails at scale" — it's PURELY seed/low-gap-closing
  (gaps below n₀ need residue coverage). For σ>0 the m₀ onset is clean (only trivial start fails),
  STRENGTHENING the strict-excess picture. My surviving Result-2 point (gap-condition holds ≠ cofinite,
  low gaps below n₀ are real) STANDS; the "1/(d_max−1) Cassels-fails" claim is WITHDRAWN.
  → maverick_bounded_gap_lemma.md (authoritative-correction header).

## scholar × density — INV-S9 RESULT (rigorous forward lemma on coarse gaps)
- [PROVED, scholar-verified] INV-S9 (transfer density's converse backward) WORKS and is RIGOROUS:
  ∑1/(d−1)≥1 ⟹ NO top-of-power gap, ALL admissible D. Proof (density): top-of-power gap at d_min^m
  exists iff ∑_d maxB(d, d_min^m−1) < d_min^m−1; but maxB(d,X) = (d^{L+1}−1)/(d−1) ≥ X/(d−1) [since
  d^{L+1}>X ⟹ d^{L+1}−1≥X], so ∑_d maxB ≥ X·∑1/(d−1) ≥ X. No gap. ∎ I independently VERIFIED:
  maxB(d,X)≥X/(d−1) (2000 random, 0 viol) + 0 top-of-power-gap violations across all 45 admissible
  D (d∈3..12, r≤4). SCOPE: closes the COARSE/top-of-power gap family (= the "runs") in the forward
  direction, ELEMENTARILY, for free — the cheapest real partial on the board. Does NOT touch the
  interior/MW-clustered singleton gaps (the open core). Confirms coarse/interior split from a THIRD
  derivation (density run-bound + sumset runs-vs-singletons + this S9 flip). One-directional: ∑<1 does
  NOT ⟹ top-of-power gap ((4,5,6,7),(3,4,8) have interior gaps only). → INVENTIONS.md INV-S9 RESULT.

## scholar — Lemma A' (2-mass bridging) prior-art verdict
- [PRIOR-ART: PARTIAL] cassels' Lemma A' (d_min-ray d_min^k·B_{d_min} bridges the gaps of the
  sub-complete constraint-sum set ∑_{d≠d_min}d^k·B_d; constraint density generic ≈1/d_min^k, obstruction
  = gap-structure not count) is NOT fully known, but has a real nearest-neighbor LEVER: the
  Hegyvári–Lev "R+T" line (R = geometric base-d 0/1-digit ray, T = positive-density set) proves R+T has
  POSITIVE DENSITY (Fourier/greedy) but STOPS SHORT of cofiniteness — same wall, but published machinery
  to build on. Lev "Optimal representations by sumsets" (J.Number Theory 52, 1995) + Nathanson
  restricted-bases use COUNTING-density thresholds, not the finer generic-density+gap-only distinction.
  The "one ray bridges sub-complete remainder" decomposition appears as a technical lemma in
  Cassels-type proofs ({2,3} case) but is NOT a named principle in this form. LEVER for cassels: upgrade
  Hegyvári-Lev positive-density-R+T to cofinite using the EXTRA structure (ray is self-similar/geometric
  + constraint density generic-not-thinned). ⚠ verify exact Hegyvári/Lev refs from MathSciNet (Grok mixed
  up Lev titles); pull Hegyvári's R+T paper directly. → cassels (Lemma A' localization).

## scholar — lift's Theorem 10 (counting-exp vs completeness-threshold) prior-art verdict
- [VERIFIED inequality + PRIOR-ART: folklore/folklore/known-uncontrasted] log2/log d > 1/(d−1) for all
  d≥3 VERIFIED (gap +0.13 at d=3, →0+ asymptotically since 1/log d ≫ 1/d; ε=∑log2/logd−1 >0 strictly
  even at β=1; (3,4,7) ε=0.487). PART 1 (inequality): FOLKLORE — one-line convexity, true, but NOT
  stated in complete-seq/restricted-digit lit as the reason avg rep-count diverges. PART 2 (avg r(n)→∞
  but min dips at power-coincidences): FOLKLORE-partially-recognized, NOT a named crux — visible in
  Erdős-Tetali (1990, avg r(n)≍(log n)^C), Erdős-Fuchs (L² fluctuation of r(n)), Nathanson/Vu
  (variance/concentration), but NONE isolate "avg supercritical, min critical" as the decisive
  completeness mechanism. PART 3 (counting exp log2/logd = box-dim vs completeness 1/(d−1) = Astels
  thickness as DUAL invariants): KNOWN individually (Hausdorff/Besicovitch dim; Astels/Newhouse
  thickness), NEVER CONTRASTED for {B_d} — fractal-sumset work (Moreira-Yoccoz, Peres-Shmerkin,
  Hochman) treats them independently. NET: present Thm 10 as a CLARIFYING elementary observation; the
  novel bit is the dimension-vs-thickness CONTRAST (unmade for this family) explaining why avg is
  supercritical while completeness is critical. Cite Erdős-Tetali, Erdős-Fuchs, Astels, box-dim
  classics. Do NOT claim inequality/avg-min as novel (folklore). ⚠ verify Erdős-Tetali/Erdős-Fuchs
  exact refs from MathSciNet. → REDUCTION_THEOREM Theorem 10 (lift).

## density × cassels (gcd-top-two DROPPED from joint lemma — cassels's catch)
- [CLARIFICATION] gcd(d_max,d_2nd)=1 is NOT a hypothesis of the per-fixed-k cofiniteness joint lemma.
  Disentangled: (A) per-fixed-k cofiniteness (N₀=v+d_min^k finite each k) needs only gcd(D)=1 + σ>0
  (+ Baker for gap finiteness); {3,4,6} SATISFIES (A) (N₀=986/242113/58941162 all finite). (B) bounded
  geometric C is where {3,4,6} fails and where gcd(top-two)=1 was the (sufficient-not-necessary) attempt
  — but (B) was refuted k-uniformly by {3,4,5} and WITHDRAWN. So gcd(top-two)=1 belonged only to the
  withdrawn (B); it is VESTIGIAL in the joint lemma (A) and DROPPED. The joint lemma is strictly more
  general without it. → density_margin_growth_leg.md hypothesis-correction §.
- [CANONICAL joint lemma, co-signed density+cassels] D admissible, gcd(D)=1, σ=∑1/(d−1)−1>0. Per FIXED k:
  T_k cofinite, N₀=v+d_min^k, v~gap(D,k)/σ. Surplus σ·U (density front) + Lemma C (cassels back),
  transcendence-free GIVEN gap=O(d_max^k); O-constant k-dependent, uniform-in-k = residual MW. RUN-version
  (singletons = MW core); Baker-conditional. v=U₀=last-hole=gap/σ+d_min^k.

---

## baker — CLAIM (keystone): the EXACT inequality the reduction requires (canonical target)

**Thread claimed:** formalize the precise MW/Baker input of theorem_347_allk §C / REDUCTION_THEOREM
(KERNEL). Status of sub-results tagged inline. This is the canonical target everyone else compares
known Baker bounds against. Work in `analysis/e124q2/baker_assembly/`.

### [VERIFIED] The CF structure (re-derived independently, mpmath dps=300)
- CF(log4/log3) = [1,3,1,4,1,1,**11**,1,**46**,1,5,**112**,1,1,…] — matches troika INV-L6 exactly.
- Convergents p/q (p=exp of 3, q=exp of 4): 1/1, 4/3, **5/4**, **24/19**, **29/23**, **53/42**,
  612/485, **665/527**, 31202/24727, 31867/25254, **190537/150997**, …
- At convergent p_k/q_k: linear form `Λ_k := |p_k·log3 − q_k·log4| ≈ 1/(a_{k+1}·q_k)`, and the
  **relative gap** `|3^{p_k} − 4^{q_k}| / 3^{p_k} ≈ Λ_k` (verified to dps=300):
  | p | q | a_next | Λ = \|p ln3 − q ln4\| | rel gap |
  |---|---|---|---|---|
  | 5 | 4 | 4 | 5.21e-2 | 5.35e-2 |
  | 53 | 42 | **11** | 2.09e-3 | 2.09e-3 (deepest ≤ p=80) |
  | 665 | 527 | **46** | 4.37e-5 | — |
  | 190537 | 150997 | **112** | 6.45e-8 | — |
  The deep collisions sit at the LARGE partial quotients (11, 46, 112). This is the irrationality-
  measure content in plain sight.

### [OPEN — the canonical target f] THE EXACT NEEDED INEQUALITY

The reduction (theorem_347_allk §A+§B + REDUCTION_THEOREM Thm 6,8,10) requires, k-uniformly, a lower
bound on the **relative cross-base spacing** at every power pair. State it in the requested form:

> **(NEEDED-MW).** There exist effective constants κ, q₀ and an exponent rate `f` such that for every
> pair of exponents (p,q) with p,q ≥ 1 and max(p,q) > q₀,
> ```
>     |3^p − 4^q| / min(3^p, 4^q)  ≥  f(max(p,q)).
> ```
> The reduction closes (3,4,7)-all-k iff `f` is summable-against-the-gap-structure in the precise sense
> below (§ "what rate the reduction needs").

**What rate `f` the reduction actually needs (k-uniform).** From REDUCTION_THEOREM Thm 6 (N₀ = v+M)
and Thm 8 (bulk runs ≤ O(d_min^k)), the ONLY way a hole survives above N₀ is an isolated point at a
cross-base coincidence. The bridge (theorem_347_allk §C.2/§C.3) needs: at scale n, the B₃+B₄ gap of
width ≈ ½·(top 3-or-4 power ≤ n) is covered by the base-7 ray. The relative spacing must merely be
**bounded below by an inverse-polynomial in the exponent** — i.e. the reduction needs

> **`f(m) ≥ m^{−A}` for SOME effective absolute constant A** (any finite A suffices; the target is
> cofiniteness so an enormous threshold q₀ is acceptable).

This is because: exponent m ≈ log₃(n), so `f(m) ≥ m^{−A}` translates to relative gap ≥ (log₃ n)^{−A},
which is ≫ 1/n — vastly larger than the 1/n resolution of the integer lattice. **The integer floor
only needs the gap to not be SUPER-exponentially small in the exponent** (i.e. not smaller than any
1/n^c at the actual integer n=3^p). [CLAIM, to be hardened by the bridge-quantification leg — flagged
for maverick/density cross-check: is inverse-poly-in-exponent genuinely sufficient, or does the
flat-margin criticality (§C.3) demand a SHARP constant, not just a rate? This is the one open hinge.]

### [CITED — verifying next] What KNOWN Baker bounds deliver

Matveev (2000) / Laurent–Mignotte–Nesterenko give, for the two-log linear form Λ = |p log3 − q log4|:
> `log Λ ≥ −C · (log 3)(log 4) · log(max(p,q))`  (shape: `Λ ≥ max(p,q)^{−C'}`, C' effective absolute).

**This is exactly inverse-polynomial in the exponent** — rate-SHAPE MATCH with the `f(m) ≥ m^{−A}`
the reduction needs (if the inverse-poly rate is what's needed). The relative gap `|3^p−4^q|/3^p ≈ Λ`
inherits the same `max(p,q)^{−C'}` lower bound. So **on the rate-shape axis, known Baker bounds are the
right shape.** The open hinge is whether the reduction needs the rate (✓ known) or the sharp constant
at the coincidence arcs (✗ not known elementarily) — §C.3's flat-margin criticality is the crux I'm
adjudicating next.

**Death-point / honesty flag:** the keystone tension between (a) UNIFIED_CONCLUSION/KILL_LEDGER framing
("the core IS the two-log MW bound, which is PUBLISHED") and (b) theorem_347_allk §C.3 RETRACTION ("the
core is JOINT equidistribution of the base-7 ray, NOT pairwise MW") is UNRESOLVED and is the load-
bearing question. I am adjudicating it now. If (a): known bounds discharge it → theorem falls. If (b):
no two-log bound suffices → document the rate-shape mismatch. — baker

## baker — NEEDED-vs-KNOWN comparison (task #30 deliverable) + BEGL96 tension RESOLVED
Full table + code in baker_assembly/CLAIMS.md (gelfond TABLE 1/2 + baker resolution). Headline:

**THE TENSION (UNIFIED_CONCLUSION "core IS two-log MW" vs theorem_347_allk §C.3 "core is joint
equidistribution") IS RESOLVED by the BEGL96 verbatim mechanism** (team/_raw_begl96_fulltext.txt
L229-233, re-read): BEGL96 closed (3,4,7) k=1 with the pairwise bound `|3^p−4^q| > exp{ln3(p−500 ln4
(8+ln p)²)}` (MW Cor 10.1) + a FINITE CHECK to 581 — NO equidistribution estimate. Reconciliation:
> Pairwise MW gives FINITENESS of dangerous (3,4) coincidences; a FINITE COMPUTATION discharges the
> tail covering for a FIXED triple. The joint base-7 equidistribution (§C.3/FACE 2) is the mechanism
> that makes the tail TRUE, but is replaced by direct verification for any fixed (D,k). Only the
> UNIFORM all-k/all-D covering needs the new joint lemma. Both framings stand at different scopes.

| Face | NEEDED inequality | KNOWN bound | Verdict |
|---|---|---|---|
| FACE 1 pairwise \|3^p−4^q\| | rel gap ≥ exp(−C(log p)²), k-uniform | Matveev 2000 / MW 1989 (CITED, constants verified) | **DISCHARGED** (finiteness; p*≈2.94e5 MW / 2.67e10 Matveev). Fixed triple per-k closes = BEGL96. |
| FACE 2 joint B₇ covering | min(P₃,P₄,P₇)≤Cρ^L on CF arcs of log3/log4; OR r_{B₇}(n)≥1 uniformly | NONE citable (new harmonic-analysis estimate) | **OPEN** — the wall. Needed rate POLYNOMIAL (not super-poly), so missing-LEMMA wall, not shape-wall. |

VERIFIED-fresh by baker: B₃+B₄ covered fraction oscillates 0.67–0.97 (positive-measure complement,
non-vanishing → no density-1 shortcut); B₇ subset-sums sparse (~N^0.356); worst-gap min B₇-rep floors
at 10 (k=1), flat; k=2 straggler 3,982,888 is an isolated single-point miss (neighbors covered).
Outcome: **(b) sharp-conditional** — fixed-triple per-k discharged by cited Matveev/MW + finite check;
all-k/all-D reduces to ONE new polynomial-shape k-uniform joint-covering lemma. Task #30 → COMPLETE.

## schneider — REQUIREMENTS MAP: weakest sufficient input (resolves §C.1-vs-§C.3 hinge)

Full: schneider_requirements_map.md. Seed = weakest sufficient transcendence input across forms.

- [RESOLVED — the load-bearing §C.1-vs-§C.3 tension] §C.1 (2-log MW) and §C.3 (equidistribution) are
  BOTH right, about DIFFERENT locations with DIFFERENT cost. The reduction needs TWO separable inputs:
  (I) a GAP-WIDTH bound — cheap: 2-log, inverse-poly RATE, CONVERGENT-DENOMINATORS-ONLY (sparse,
  density 0); and (II) a LAST-HOLE/margin-floor bound — expensive: the flat-margin spot, base-7-vs-S34
  alignment, but FINITE-per-(D,k). Team has been conflating them.
- [VERIFIED, exact int] The big B₃+B₄ gaps are PURE 2-log gap-width phenomena: largest k=1 gap
  [3789586,4194303] ends at 4^11, width 404728 = 4^11 − (sum-of-4-atoms + best-3-fill); residual =
  granularity of base-3 subset-sums = O(3^13) = |3^p−4^q| 2-LOG quantity. NO base 7 in the gap WIDTH.
  ⟹ refutes the part of §C.3 implying the gap STRUCTURE needs equidistribution — it does not.
- [VERIFIED] Base-7 covers the big gap from OUTSIDE with GROWING margin: inside the largest k=1 gap,
  every pt has ≥63 base-7 reps (min 63, median 124); ZERO base-7 subset-sums land in the gap. Bulk
  cover is ~63× redundant, NOT a delicate single-shift event. min r(n) over (581,4M] dips to 10 only
  in the early transient (n≈611,54739) then GROWS to ≥63. Dangerous region = finite early transient
  = exactly BEGL's "computation to 581". Corroborates breaker S10 (decorrelation rate c bounded below+growing).
- [VERIFIED] The last hole IS the flat-margin spot, and it's FINITE-per-instance: largest k=2 hole
  n=3982888 = N₀(k=2) EXACTLY. Persists by (1) sitting in the big two-base gap [3789577,4194303] (4^11
  band, 2-log input I) AND (2) of 32 "reaching" base-7 shifts, NONE hits an S34 pt (3-base alignment,
  input II). Input (II) bites ONLY at the single last hole; above N₀ margin grows. ⟹ input II = finite
  check, NOT a uniform transcendence theorem (unless you demand effective uniform N₀(k)).
- [ANSWER to baker's open hinge] "inverse-poly rate sufficient, or sharp constant?" → RATE is
  sufficient for cofiniteness with a (huge, k-dependent) N₀(k) [goal a]; SHARP constant needed ONLY
  for an effective uniform N₀(k) formula [goal b]. Rate ⟹ cofinite + finite check; sharp constant ⟹
  effective bound. Goal (a) closes on the RATE — which is PUBLISHED (Laurent/Matveev, baker+gelfond).
- [WEAKEST SUFFICIENT INPUT, the deliverable] For (3,4,7)-all-k cofinite: |3^p−4^q|/3^p ≥ max(p,q)^{−A}
  (effective absolute A) — 2-log, convergent-denominators-only, any poly rate — PUBLISHED — PLUS finite
  check [N_eff,N₀(k)] per k (k-uniformity by lift §A+§B). Strictly weaker than the team's stated open
  core on ALL THREE axes (2 not 3 logs; convergents not all q; rate not sharp constant). This MATCHES
  BEGL96's actual k=1 proof. The expensive inputs (3-log alignment, sharp minor-arc constant, uniform
  N₀(k)) are needed ONLY for goal (b) effective-uniform-threshold, NOT for the cofiniteness theorem.
  HONEST CAVEAT: on the 2-log input alone, N₀(k) is finite-but-not-a-priori-bounded (same honesty line
  as cassels strict-excess: cofinite VERIFIED, effective bound needs input II). Outcome = (a)/(b), NOT a shape-wall.

- [HONEST REFINEMENT — do not overstate input (I), schneider §5a] The crossover "gap bounded → gap
  covered" is NOT pure gap-width; it is THREE-layered. (I) gap-width [2-log, published] bounds each
  S34 gap by O(3^p). (I′) covering redundancy [elementary]: #reaching base-7 shifts ~ n^0.356 → ∞,
  vs input-(I)-bounded gaps — VERIFIED 128 reaching shifts at n≈3.99M, 119 hit S34. (II) alignment
  [§C.3, sharp]: that the n^0.356 shifts don't ALL miss simultaneously = joint equidist of base-7 vs
  S34 gap pattern. ⟹ CORRECTED net: §C.3 IS right that MW-alone doesn't RIGOROUSLY close it (the
  asymptotic closure needs (II)); §C.1 IS right that the gap WIDTHS are pure 2-log. The residual (II)
  is a REDUNDANT-covering statement (60–120× empirical margin), tight only at the single last hole =
  N₀, NOT everywhere-sharp. Large margin at generic gaps + tight only at the last hole = why the
  finite check works = why this is easy-tail, not a hard everywhere-sharp transcendence problem.
  schneider_requirements_map.md §5a.

- [MAGNITUDE CORRECTION + baker k=1 verified, schneider] My earlier "min rep ≥63 / dips to 10" figures
  used units-inclusive B_d (j≥0) — WRONG (spurious d^0=1 atom inflates counts). Corrected to BEGL's
  j≥k convention: largest k=1 hole = 581 EXACTLY (matches BEGL), r(581)=0, neighbors r(580)=5/r(582)=4
  — a genuine ISOLATED single-point miss. This VERIFIES baker's k=1 claim (581 is a 0-rep miss, same
  signature as k=2 straggler) ⟹ BEGL's finite check to 581 already discharged input (II) at k=1 ⟹
  per-fixed-k assembly (TARGET-2) is sound. Corrected bulk margins (j≥1): near 4^11 min rep=24
  (median 55), at 1M min rep=64 — still supercritical + growing, zero bulk holes. Structural
  conclusions UNCHANGED (gap-width 2-log; margin grows; danger = isolated last holes only).

## schneider — RIDOUT/INEFFECTIVE ROUTE verdict (task #41, +matveev/nesterenko)

Full: schneider_ridout_verdict.md. VERDICT: ineffective route does NOT frame-break all-k. TWO-PRONGED KILL.

- [VERIFIED — confirms matveev, prong 1] Per-k BASE CASE does NOT uniformize. Precise step/base split:
  the inductive STEP (seed-run → cofinite tail) is ELEMENTARY — above N₀=581 the +M-closure has ZERO
  failures (pure residue coverage, gcd=1, NO Ridout). [Precision-fix to matveev's "Ridout closes the
  step": cross-base content is entirely in the BASE CASE = reaching N₀.] Base-case uniformization
  minimality kill: Option A (effective uniform V₀(k)) = the goal-(b) transcendence core, not from
  Ridout. Option B (per-k finite) = infinitely many computations, not a proof. Option C (recursive
  seed k→k+1) REFUTED: deconvolution makes R_{k+1} SPARSER; run of 11 in R_2 → only 1/11 survive to
  R_3; at k=3 longest low-range run = 13 < M=27 (seed near 166M). NO minimal input uniformizes short
  of goal (b). matveev's base-case objection STANDS.
- [VERIFIED — independent, prong 2] Even per-k, Ridout controls the WRONG object. Holes are NOT at
  tighter |3^p−4^q| (k=1 holes cluster at the LOOSE convergent 3^5≈4^4 rel 0.051; tighter pair
  3^10≈4^8 rel 0.099 above 581 has min-rep 19, NO hole). Small |3^p−4^q| is NEITHER necessary NOR
  sufficient for a hole. A hole = all ~n^0.356 base-7 shifts miss simultaneously = 3-TERM joint
  covering (subspace/Evertse), NOT 2-term Ridout. Effective MW & ineffective Ridout bound the SAME
  pairwise quantity (input I, the gap WIDTH) which is NOT the bottleneck; input II (joint covering) is
  not a pairwise statement. Ridout's ineffective UPGRADE is on the wrong axis.
- [Q1, LIT] Ridout 1958 (NOT 1957) Mathematika 5:40-48. Corollary |2^m−3^n| > C(ε)·max^{1−ε}, all but
  finitely many, INEFFECTIVE. Cannot take α=1 (Roth vacuous for rationals); it's the S-unit degenerate
  form, S-restriction on both terms. nesterenko pulls exact Bugeaud corollary.
- [Q3, LIT — NO, tag is unsupported over-claim, NOT folklore] erdos124.ne_zero (general all-k) tagged
  research OPEN; ne_zero_three_four_seven ((3,4,7) all-k) tagged research SOLVED [BEGL96] — but BEGL96
  proved k=1 ONLY. Tag added in formal-conjectures PR #1420 with EMPTY body, NO comments, NO cited
  proof (verified via gh). Not folklore: Tijdeman/Stewart S-unit = atom spacing (wrong object);
  complete-sequence lit (Brown 1961/Honsberger) has no multi-base all-k; BEGL-citers none. ⟹ tag is
  UNSUPPORTED EXTRAPOLATION, over-claim report STANDS (strengthened), do NOT revise to "tag fine".
- [obstruction BEGL saw] None hidden. BEGL used effective MW because they wanted EXPLICIT N₀=581 (a
  finite checkable claim); ineffective gives "finite, value unknown" — useless for "largest miss is
  581". Failure is at all-k base-case uniformity (prong 1) + object mismatch (prong 2), NOT at k=1.
