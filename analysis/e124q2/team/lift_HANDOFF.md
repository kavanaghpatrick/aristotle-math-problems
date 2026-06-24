# lift — HANDOFF (E124 / BEGL96 conjecture)

## 1. Proved / verified results (file pointers)

- **Residue Lemma** (gcd(b,m)=1 ⟹ B_b surjective mod m), clean form of BEGL Claim 4. PROVED.
  → `lift_sufficiency_mechanism.md`.
- **gcd(D)=1 necessity for k≥1** (p|gcd ⟹ p^k | every n; verified all-even gcd=2 kills all odds). PROVED+VERIFIED.
  → `lift_gcd_necessity.md`.
- **Digit recursion R_k = C_k + R_{k+1}** (C_k={0,3^k}+{0,4^k}+{0,7^k}); ⟹ monotone R_{k+1}⊆R_k;
  R_k = subset-sums of {3^j,4^j,7^j: j≥k}. PROVED + verified k=1,2,3 to 2·10⁵. → `theorem_347_allk.md` §A.
- **k-uniformity of the MW input** for (3,4,7)-all-k: close pairs (3^p,4^q) are a FIXED finite set
  (p∈{5,19,24,29,34,…}, Δp≈5 from convergents of log4/log3); level k uses only p,q≥k. PROVED. § B.
- **Boundary criticality**: ∑1/(d−1)=1 is exactly the critical branching ratio (min #reps = O(1)),
  which is why the boundary needs MW not soft counting. → `lift_boundary_criticality.md`.
- **Ground-truth validation**: reproduced BEGL96's 581 exactly (and 79/112/17 corrected). Engine sound.
  → `lift_347_allk_and_validation.md`. **Provenance flag:** BEGL96 proves (3,4,7) k=1 ONLY; the
  124.lean `research solved` tag for all k≠0 is an over-claim (scholar drafting upstream report).

## 2. Work in flight + exactly where I stopped

**theorem_347_allk.md** (co-authored with troika; team's intended FIRST FINISHED THEOREM):
- §A (recursion), §B (k-uniformity), §D (assembly) are RIGOROUS + verified — my half is DONE.
- §C (the Mignotte–Waldschmidt gap-control lemma + bridge + effective N₀(k)) is the OPEN placeholder.
  I drafted the §C *target* and a "bridge note" (B_3+B_4 has unbounded gaps ending at 3-powers;
  B_3+B_4+B_7 has max gap 1 above 581; base-7 bridges). MW usable form (from grok/lit):
  |3^p−4^q|/3^p ≥ exp(−C(log p)²), C≈1.2 empirically; source MW Math.Ann.231 (1978) + 1994 Acta sequel.
  **STOPPED**: had a background numpy run (`/tmp/e124_C_argument.py`) testing 3-ray coverage to N=5M —
  status unknown at snapshot; not load-bearing (just re-confirms cofiniteness, already known).
- troika pivoted to general-D (task #11); I told them I'd draft §C myself. §C is NOT written yet.

## 3. Precise next steps for a successor

1. **Finish §C of theorem_347_allk.md.** Either (a) reconstruct BEGL's compressed MW→bridge argument
   into a written effective N₀(k) (genuinely hard, transcendence-theoretic), OR (b) per team-lead,
   state §C as a clearly-labeled MW input (cite MW + the relative-gap form), prove everything else
   rigorously, and present the theorem as "complete modulo one explicit transcendence constant." The
   team-lead BLESSED (b) for individual sets (scholar's guardrail only kills MW for GENERAL ∀D).
   Effective N₀(k) must DOMINATE the corrected thresholds 581 / 3 982 888 / 166 025 260 (k=1,2,3).
2. **Add to the discussion section** (team-lead directive): troika's thin-band fingerprint +
   multiplicative-independence lemma; and the sharp articulation that non-uniform N₀(D) is logically
   fine for ∀D — the real obstruction is the below-threshold finite check can't be done for ∞-many D.
3. Adopt breaker's verification standard for any finite check (two doublings + max < N/2).

## 4. Traps / unverified claims to beware

- **[RESOLVED] maverick's inf = 1/(d_max−1) = 0.25 was a truncation bug** (atom-exponent list capped
  at 79, dropping base-3 mass below 5^79 ⟹ collapsed to base-5 ray = 1/(5−1)). maverick confirmed +
  retracted; the "no Cassels argument works" conclusion is WITHDRAWN. TRUE inf T(x)/x ≈ 1.10 > β=1.083
  (my exact arithmetic, now agreed). Use β / "inf≈1.10>1". The 0.25 is DEAD — don't revive it.
  (Still: inf>1 is NECESSARY NOT SUFFICIENT — troika's threshold-581 point stands; granular holes need MW.)
- **My own "liminf T(x)/x = β" was imprecise:** β is the asymptotic (Weyl) value; the realized min
  over finite range is ≈1.10, just above β=1.083. Fixed in `lift_cassels_liminf_theorem.md` header.
- **CRITICAL (troika):** inf T(x)/x > 1 (the Cassels partial-sum condition) is NECESSARY, NOT
  SUFFICIENT for cofiniteness — the merged-atom Cassels test fails only once (atom 3) yet threshold
  is 581. The granular value-holes need MW. So "strict β>1 ⟹ cofinite" is NOT established by soft
  means. Any successor must not over-claim a soft strict-β theorem.
- Threshold constants: use 581 / 3 982 888 / 166 025 260 (k=1,2,3). The old 785 743 (k=2) and
  57 751 591 (k=3) are FALSE-FREEZE artifacts — never cite them. (3,4,7) k=3 needs N≥200M to converge.
- BEGL96 paper errata: printed 78/111/16 are off-by-one; true 79/112/17 (maverick/scholar/me agree).
