# schneider — RIDOUT / INEFFECTIVE ROUTE: verdict (task #41, co-owned with matveev)

**Question:** does the ineffective Diophantine toolkit (Ridout 1958 p-adic Roth; S-unit/subspace)
close the FULL (3,4,7)-all-k conjecture, exploiting that `∀ large n` permits ineffectiveness?

**VERDICT: NO. The ineffective route does NOT frame-break all-k.** It dies twice — once at the per-k
base case (matveev + my minimality kill-test), and again at the object level (the binding input is
3-term joint covering, not Ridout's 2-term pairwise bound). Effective MW and ineffective Ridout
control the SAME pairwise quantity, which is NOT the bottleneck. Triangulated with matveev (Q1/Q2)
and nesterenko (citation).

Tag legend: [VERIFIED] exact computation here; [DERIVED] from proven stack; [LIT] literature.

---

## The two-pronged kill

### Prong 1 — the per-k BASE CASE does not uniformize [VERIFIED — confirms matveev]
The reduction splits into STEP (seed-run → cofinite tail) and BASE CASE (the seed run exists / reach
N₀). I verified the split precisely:
- **The STEP is elementary and needs NO transcendence.** Above N₀=581 (k=1), the +M-closure has
  **ZERO failures** — the tail is pure residue coverage (gcd=1, modular's L). So Ridout is NOT in the
  step. [This is a precision-correction to matveev's "Ridout closes the step": the step is residue
  coverage; the cross-base content is entirely in the BASE CASE — reaching N₀ by killing scattered
  holes below it. matveev and I agree once step/base is split sharply.]
- **The BASE CASE does not uniformize in k.** Minimality kill-test of every uniformization route:
  - *Option A (effective uniform V₀(k)):* this IS the transcendence core (goal b) — the per-class
    onset grows number-theoretically (cassels strict-excess: K = 0.046→1.35→3.76 at k=1,2,3, no clean
    form). NOT supplied by Ridout. DEAD.
  - *Option B (ineffective "V₀(k) finite for each k"):* per-k finite — exactly what we already have;
    gives "all k" only via infinitely many separate computations. NOT a proof. DEAD.
  - *Option C (recursive seed transfer k→k+1):* REFUTED [VERIFIED]. Deconvolution `R_k = C_k + R_{k+1}`
    makes `R_{k+1}` SPARSER (wrong direction). A run of 11 consecutive in `R_2` has only **1/11**
    survive to `R_3`. At k=3 the longest run in [0,50000] is **13 < M=27** — the seed doesn't even
    exist in the low range; it sits near N₀(3)=166M. No recursive base case. DEAD.

  **⟹ No minimal extra input uniformizes the base case short of the effective-N₀(k) core itself
  (goal b), which is the open problem. matveev's base-case objection STANDS.**

### Prong 2 — even per-k, Ridout controls the WRONG object [VERIFIED — my independent kill]
Suppose we accept per-k (give up uniformity). Does Ridout even discharge the per-k base case? **No.**
- The scattered holes below N₀ are NOT located at progressively tighter `|3^p−4^q|` coincidences.
  [VERIFIED] The k=1 holes (239–581) all cluster around the LOOSE convergent `3^5≈4^4` (rel gap
  **0.051**, not tight); above 581 there are tighter-scale pairs (`3^10≈4^8`, rel 0.099) with min-rep
  19 and **NO hole** — base-7 bridges them. So small `|3^p−4^q|` is **neither necessary nor
  sufficient** for a hole.
- A hole requires **all** ~`n^{0.356}` base-7 shifts to simultaneously miss the S34 dense region.
  That is a **3-term S-unit / joint-covering** statement (`|3^a4^b − 7^c|`-flavored), i.e. SUBSPACE
  THEOREM (Schmidt/Evertse) territory — **not Ridout's 2-term `|3^p−4^q|`.** Ridout says nothing
  about base-7 vs S34 correlation.
- **Effective MW and ineffective Ridout bound the SAME 2-term pairwise quantity.** So Ridout buys
  nothing MW didn't already give for the part it controls (input I, the gap WIDTH). The genuine open
  core (input II, joint covering) is not a pairwise bound at all. **The ineffective UPGRADE (Ridout ≫
  MW) is on an axis that is not the bottleneck.**

---

## Q1 — exact Ridout statement & the corollary [LIT, verified with matveev/nesterenko]
**Ridout (1958), "The p-adic generalization of the Thue–Siegel–Roth theorem", Mathematika 5, 40–48**
(NOTE: **1958**, not 1957 as the seed said). The usable corollary (S-adic Roth): for `α` real
algebraic, `S` a finite prime set, `ε>0`, there are only finitely many rationals `p/q` (lowest terms,
both `p,q` `S`-units) with `|α − p/q| < q^{−ε}` — the exponent drops from Roth's `2+ε` to `ε` because
BOTH numerator and denominator are S-restricted.
- **Corollary used:** `|2^m − 3^n| > C(ε)·max(2^m,3^n)^{1−ε}` for all but finitely many `(m,n)`,
  **INEFFECTIVE** `C(ε)`. [VERIFIED numerically: the implied deficit exponent stays bounded, ~0.05–0.5,
  dominated by small `m,n` — consistent with `max^{1−ε}`.] nesterenko pulls the exact Bugeaud
  ("Approximation by Algebraic Numbers") corollary statement.
- **The hypothesis subtlety the seed flagged:** one canNOT take `α=1` (rational → Roth vacuous); the
  bound is the S-unit/linear-forms degenerate form, applied with the S-restriction on both terms. The
  statement above is the correct one; its ineffectiveness is intrinsic (Roth/Ridout give no size bound).

## Q3 — is ineffective all-k FOLKLORE? [LIT — NO, the tag is an unsupported over-claim]
- **`erdos124.ne_zero` (the general all-k conjecture) is tagged `research OPEN`** in `124.lean`
  (verified, lines 57–61). **`erdos124.ne_zero_three_four_seven` (the (3,4,7)-all-k) is tagged
  `research solved` attributed [BEGL96]** (lines 69–73) — but BEGL96 proved (3,4,7) for **k=1 ONLY**
  (verbatim "largest integer not in Σ(Pow({3,4,7};1)) is 581"). The tag is the documented over-claim.
- **No justification exists for the tag.** The (3,4,7)-all-k lemma was added in formal-conjectures PR
  **#1420** ("more statements") with an **empty PR body and no comments** [VERIFIED via gh]. No cited
  proof, no ineffective-all-k note, nothing in git history.
- **Not folklore.** Tijdeman/Stewart S-unit bounds control ATOM spacing (wrong object — completeness
  is a SUBSET-SUM property, not atom spacing). The completeness/complete-sequence literature
  (Brown 1961, Honsberger; Wikipedia) has no multi-base power-sum all-k result and no Ridout-based
  completeness argument. BEGL-citers (scholar's route, relayed by matveev): no ineffective-all-k claim.
- **⟹ The `research solved` tag is an UNSUPPORTED EXTRAPOLATION, not "sloppy-but-right."** There is no
  published or folklore ineffective-all-k proof. The upstream over-claim report STANDS (do NOT revise
  it to "tag is fine"); if anything this strengthens it — the tag should be `research open` (matching
  `ne_zero`) or carry an explicit "k=1 only, all-k unverified" note. [DO NOT file without user approval.]

---

## Why BEGL96 used EFFECTIVE MW when ineffective Ridout was available (the seed's "find the obstruction")
This is NOT evidence of a hidden obstruction to the ineffective route — it is consistent with the kill
above. BEGL needed the (3,4,7) k=1 result with an **explicit N₀=581** (a finite, checkable claim).
Effective MW gives the explicit bound enabling the finite computation to 581; ineffective Ridout would
give "N₀ finite, value unknown" — useless for stating "the largest non-representable is 581." So BEGL
used effective MW because they wanted the EXPLICIT k=1 constant, not because ineffectiveness fails at
k=1. **The ineffective route's failure is at the ALL-K base-case uniformity (prong 1) + the object
mismatch (prong 2), NOT at k=1.** No hidden single-scale obstruction; the obstruction is the per-k
non-uniformity that this whole campaign already mapped.

---

## Net
The ineffective frame-break is **sound logic applied to the wrong axis.** `∀ large n` does permit
ineffectiveness, and the ineffective toolkit IS stronger on the pairwise-spacing axis — but (a) the
all-k difficulty is base-case UNIFORMITY, which no ineffective pairwise bound touches, and (b) the
binding per-k object is 3-term joint covering, not the 2-term quantity Ridout/MW share. **The unified
doc's part-(ii) headline stands: all-k is per-k (infinitely many base computations), not closed by one
ineffective application.** Effective vs ineffective is a real distinction for goal (b)'s threshold, but
neither version closes all-k. Consistent with my requirements map: input (I) [pairwise, 2-log] is
published and not the bottleneck; input (II) [joint covering] is the open core and is not a pairwise
Diophantine statement at all.
