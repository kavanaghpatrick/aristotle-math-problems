# Statement-Repair Screen — V0 Phase 2 (2026-06-10)

Executed per `analysis/fable_aristotle_attack_plan_20260609.md` §V0 Phase 2 and §3 Target 5(b).
**Zero submissions made. Zero arguments authored.** Screening only.
Screener: Fable 5 statement-repair subagent. All web statuses fetched 2026-06-10.

---

## 0. Contingent-Slot Recommendation (ranked)

| Rank | Problem | Verdict | Slot action |
|---|---|---|---|
| 1 | **erdos_307 (PRODUCT framing)** | **OPEN — survivor** | **Conditional fill**: fill Target 5 with erdos_307 only if the slot734/735 autopsy (plan priority 5(a)) does not fill it. Enters the full §4 Stage A–H loop as a V2/V3-shaped witness-search target. No fast path to submission. |
| 2 | erdos_97 | OPEN — but do not fill | Plan default upheld: ℝ²-geometry is an Aristotle hard-zero; informal-only, post-campaign at best. **Do not fill the slot.** |
| 3 | erdos_707 | **KILL — literature-closed (disproved + Lean-formalized)** | Dead permanently. Hall 1947 counterexample; Alexeev–Mixon arXiv:2510.19804 (v2 2026-01-16) with complete Lean proof. |
| 4 | erdos_590 | **KILL — literature-closed (proved 1972)** | Dead permanently. Chang 1972; erdosproblems.com marks PROVED. Formalization-only value = Hard Rule 1 violation. |

If slot734/735 fills the slot first, erdos_307 stays in candidate_queue with verified-open literature status (recorded this screen) for a future cycle. If neither fills it by Friday 2026-06-12, the slot closes empty per plan §3 Target 5(c).

---

## 1. Root Cause: why 31/31 never typechecked

DB rows: erdos_707 ids 334–340, 381–387 (14); erdos_97 ids 286–288, 294–296, 347–349 (9); erdos_590 ids 322–325, 369–372 (8). All `compile_failed`, all `lane='bare'`, all submitted 2026-01-04 (97 v1 batch undated, noted "v1 import error").

The 2026-01-04 batch generator copied files out of `formal-conjectures` and submitted them as standalone `.lean` with **`import Mathlib` substituted for `import FormalConjectures.Util.ProblemImports`**. Everything repo-specific then failed to resolve:

1. **Attributes**: `@[category research open/solved, AMS …]` is defined in `FormalConjectures.Util.Attributes` — unknown attribute under bare Mathlib. (DB notes on ids 294–296: "Internal Aristotle error - likely due to @[category] attributes and answer(sorry)".)
2. **`answer(...)` elaborator**: repo-specific; unresolvable under Mathlib.
3. **Repo-defined terms**: `IsSidon`, `IsPerfectDifferenceSet` (707); `OrdinalCardinalRamsey` (590); `ℝ²` notation, `ConvexIndep` (97) — none exist in Mathlib.
4. **Generator-injected comment blocks** ("FORMALIZATION SKETCH" / "FALSIFICATION SKETCH"): in `erdos_590_for.lean` the block was spliced *inside* the module docstring; in 707 between attribute and theorem.
5. **Statement drift (97 v1)**: the archived tier1 `erdos_97.lean` *stripped* the `answer(sorry) ↔` wrapper, submitting the bare universal — i.e. asking Aristotle to *prove* the "yes" direction of an open question rather than decide it.

Conclusion confirmed: **these three problems were never mathematically attempted.** The 31 rows are pipeline noise, correctly terminal at `compile_failed`. No re-dating or status change needed.

This failure mode is structurally extinct: the pipeline is INFORMAL `.txt`-only (Hard Rule 5) and the bare lane is closed for the campaign (§5).

---

## 2. Per-problem screens

### 2.1 erdos_707 — KILL (disproved, formalized; $1000 prize question dead)

**Archived vs upstream diff.** Archived (submissions/erdos/tier2+tier4, Jan 2026) statements match upstream modulo the import/attribute breakage above and variant renames. Upstream `707.lean` (last commit `ab84c073cd`, 2026-04-29) now carries on the main theorem:
`@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos707.lean"]`
with statement `erdos_707 : (∀ A finite Sidon, ∃ B ⊇ A perfect difference set mod n) ↔ False` — the conjecture is FALSE, and that falsity is *fully formalized*.

**Literature verdict (the plan's "Alexeev 2026" — CONFIRMED, with date precision).** Boris Alexeev and Dustin G. Mixon, *Forbidden Sidon subsets of perfect difference sets, featuring a human-assisted proof*, arXiv:2510.19804 — v1 2025-10-22, **v2 2026-01-16** (v2 adds the Lean ancillary files `Erdos707.lean`, lakefile, toolchain). Counterexamples: {1,2,4,8,13} (Mian–Chowla prefix, no perfect difference set extension for any modulus) and Hall 1947's {1,3,9,10,13} (shifted from {−8,−6,0,1,4}, *Cyclic projective planes*, Duke Math. J. 14) — the problem was answered ~30 years before Erdős posed it. Verified artifacts:
- `plby/lean-proofs` `Erdos707.lean`: fetched 2026-06-10, **6359 lines, self-contained `import Mathlib`**, own `IsSidon` / `IsPerfectDifferenceSetModulo` definitions.
- Tao wiki (AI-contributions): #707 listed under §2(b) Formalization, GPT formalization dated 2025-11-23, green marker "🟢 Hall (1947)", no red marker.

**Slot case.** None. Both truth directions are closed and machine-verified by others. Any further work is re-formalization of known mathematics (`compiled_no_advance` by our own rules). The do-not-repeat entry "erdos_707 … rewrite before any resubmit" is hereby **upgraded: do not rewrite, do not resubmit — the problem is dead.** One tactical note: the 6359-line self-contained Alexeev file is a useful *style exemplar* for decide-shaped certificate files (V2/V3/V4), nothing more.

### 2.2 erdos_590 — KILL (proved 1972; nothing open in any framing)

**Archived vs upstream diff.** Statement-identical to upstream (last file commit `bdd632a698`, 2025-12-23) modulo the breakage in §1. All four upstream theorems are `@[category research solved]`: main `erdos_590 : OrdinalCardinalRamsey (ω ^ ω) (ω ^ ω) 3` (Chang [Ch72]); `variants.two` (Specker [Sp57]); `variants.ge_three_false` (Specker); `variants.finite_cardinal` (Milner; shorter proof Larson [La73]).

**Literature verdict.** erdosproblems.com/590 (fetched 2026-06-10): badge **PROVED** — "This is true, and was proved by Chang [Ch72]." The $250 question has been settled for 54 years. The 2026-01-04 tiering machine itself knew this ("Tier: 4 - Already Proved/Disproved").

**Slot case.** None. "Statement repair" here can only produce a formalization exercise on known set-theoretic Ramsey theory — Hard Rule 1 violation, and ordinal partition calculus is far outside Aristotle's verified envelope (hard zeros on quotients/novel induction measures; group theory ≈ 1). Out-of-scope observation, not a recommendation: the page cross-references [591]/[592] (the ω^{ω²} analogue family) — those are *different problems*, were not part of this screen, and would need their own full screen before anyone breathes on them.

### 2.3 erdos_97 — OPEN, but DO NOT FILL the slot (plan default upheld)

**Archived vs upstream diff.** Upstream main statement (file last commit `0137b96de1`, 2026-02-03) is
`erdos_97 : answer(sorry) ↔ ∀ A : Finset ℝ², A.Nonempty → ConvexIndep A → ¬HasNEquidistantProperty 4 A`
(`HasNEquidistantProperty n A` = every point of A has ≥ n other points of A equidistant from it, at some r > 0 that may depend on the point). The archived v1 stripped `answer(sorry)` (proving the "yes" direction of an open question); v3 batch kept broken attributes. The `variants.k_equidistant` ("is there any k for which it holds") is also `research open`.

**Literature verdict.** erdosproblems.com/97 (fetched 2026-06-10): badge **FALSIFIABLE, $100**, last edited 2025-10-27, "There are no solutions, partial or complete, claimed in the comments." Known: Danzer's 9-point convex polygon with every vertex having 3 equidistant neighbors (variant solved, NO for k=3); Fishburn–Reeds 20-point same-distance version [FiRe92]; Erdős's claim that Danzer disproved every k "presumably mistaken" per Bloom; non-convex answer NO (hypercube embedding trick, credited Alexeev–Mixon). arXiv sweeps (convex+equidistant, Fishburn+unit distances) surface nothing post-2010. **Genuinely open, lightly attended.**

**Corrected formal statement** (for the record, NOT for submission): upstream 97.lean verbatim — guaranteed typechecking by upstream CI at HEAD `4f866bec76` (2026-06-09). Note local fork checkout still carries `![…]` vector literals where upstream now uses `!₂[…]` (EuclideanSpace literal); any future use must take the upstream form.

**Slot case (against — adopted).** A k=4 disproof needs a convex polygon in which *every* vertex has 4 equidistant co-vertices — an exact-real-coordinate construction whose Lean certificate requires algebraic distance identities, not `decide`. Calibrating fact: formal-conjectures itself has Danzer's *fully explicit* 9-point witness sitting under `sorry` — given the coordinates, nobody has pushed the verification through. Aristotle's capability envelope (evidence brief §3: hard zeros on analytic estimates; entire verified corpus is finite NT computation) gives this a ~0 adjudication prior in both directions, and the campaign holds zero geometry assets or sibling proofs to seed an authored argument. The for-case (it is open, cheap-prized, and a construction would be publishable) does not overcome the instrument mismatch. **Verdict: leave open in candidate_queue with verified literature status; informal-only if ever revisited; do not fill Target 5.**

### 2.4 erdos_307 (PRODUCT framing only) — OPEN SURVIVOR; conditional Target-5 fill

**Ban boundary honored.** Plan §7 bans only the *sum framing* (Liu–Sawhney 2024). The PRODUCT framing — which IS the literal erdosproblems.com #307 / formal-conjectures `erdos_307` statement — is explicitly screen-don't-pre-kill, and it survives.

**Statement + diff.** Upstream (file last commit `754010872d`, 2026-05-27; HEAD `4f866bec76`):

```lean
@[category research open, AMS 11]
theorem erdos_307 : answer(sorry) ↔ ∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by sorry
```

plus a second open variant `erdos_307.variants.coprime_one_notMem` (pairwise-coprime sets, 1 ∉ P∪Q) and a now-*solved* textbook variant (`coprime`, Cambie's 1 = (1+1/5)(1/2+1/3), proof included upstream — do not mistake it for the open problem). Local fork copy differs only cosmetically on the main theorem (parentheses) but predates the Cambie split — **use upstream**.
**Typecheck: PASSED locally.** Both open statements, upstream-verbatim, ran through `lake env lean` against the cached formal-conjectures build (fork checkout `aa91edc`, toolchain v4.22.0): only copyright-style lints + expected `sorry` warnings. (Test file deleted after the check.)

**Literature verdict.** erdosproblems.com/307 (fetched 2026-06-10): badge **VERIFIABLE** ("Open, but could be proved with a finite example"), Barbeau [Ba76], "There are no solutions, partial or complete, claimed in the comments." Known structure on the page: P, Q forced disjoint; ∑_{p∈P∪Q} 1/p ≥ 2; hence **|P∪Q| ≥ 60**. Absent from Tao's AI-contributions wiki (no red markers). arXiv sweeps (prime reciprocals / unit fractions+primes / Barbeau) surface nothing touching the product question through 2026-06.

**Prior-attempt audit (this project).** Two submissions, zero mathematical progress, one active hazard now defused:
- slot576 (DB id 1090, `compile_failed`, UUID `e44797f4`): the result file's informal preamble claims "the answer is YES" via P={2,3,7,43}, Q = P∪S — **triply impossible**: (i) P∩Q ≠ ∅ violates forced disjointness; (ii) target S_Q = 1806/1805 has denominator 1805 = 5·19², non-squarefree, while any finite sum of distinct prime reciprocals has squarefree lowest-terms denominator; (iii) the residual 3611/3259830 has 2-adic valuation −1, unreachable by odd primes. The 541-line Lean file proves **no theorem** (pure `def`/`#eval` greedy-search scaffolding). Logged as **false_lemmas id 49**.
- slot597 (DB id 1116, UUID `3be49710`, status-polled 2026-06-10: **ERROR** at Harmonic; never completed; terminal disposition belongs to Phase 1's sweep, and so does the row's `problem_id='597'→'erdos_307'` relabel). Its sketch's load-bearing "Result 3" (every positive rational is a sum of distinct prime reciprocals) is **false** (1/4 counterexample, same squarefree obstruction) — and is precisely the banned sum-framing route. Logged as **false_lemmas id 50**.

**Case FOR filling the slot.** This is the only screened problem matching the campaign's winning shape (V2/V3: Fable authors a search; the Lean kernel adjudicates a finite witness with zero Rivin gap). The certificate is exact rational arithmetic over explicit prime sets — `norm_num`/`decide` territory, locally verifiable before any Aristotle spend (Stage E local-first), squarely inside the one zone where Aristotle reliably verifies (S7 witness checking). The statement is upstream-verbatim, already typechecked, with a pre-registerable audit predicate (the `answer(sorry) ↔ ∃ P Q …` form plus the sanity gates below). The algebra hands Fable real authored content: necessary conditions P∩Q=∅; S_P = a/b lowest terms with b | ∏P (auto-squarefree), **a squarefree** and rad(a) ⊆ Q; symmetric constraints on Q; |P∪Q| ≥ 60; an exact p-adic cancellation condition at every prime of P∪Q. These prunings make a structured search (not blind greedy — greedy provably fails) genuinely novel relative to Barbeau's 1976 "computer challenge corner" origin. History is clean: no failed_approaches rows, no genuine prior mathematical attempt here or (visibly) anywhere.

**Case AGAINST.** "Verifiable" does not mean "small": the constraints force ≥ 60 primes and simultaneous exact valuation cancellations at every used prime — the witness, if it exists, may be astronomically large, and 50 years of silence on an explicitly computational challenge is adverse selection (Bloom's rule). If the answer is NO, no finite certificate exists and the disproof is a structural impossibility argument — exactly the class where this pipeline is 0-for-everything. Expected-count honesty (the V3 sieve precedent) is mandatory *before* any long run, and no density heuristic is in hand today; the slot could consume the week building one. Aristotle contributes nothing until a witness exists.

**Net.** Conditional fill at rank 1, strictly behind plan priority 5(a) (slot734/735 autopsy). If filled: full §4 loop, Stage A pre-registration = the upstream `answer(sorry) ↔ ∃ P Q …` statement + the valuation/squarefree audit gates above; first deliverable is the authored feasibility/expected-count memo, $0 Aristotle.

---

## 3. Cross-checks (task item 4)

- `failed_approaches`: **0 rows** for erdos_707 / erdos_97 / erdos_590 / erdos_307 (and no keyword hits on sidon/reciprocal/equidistant).
- `false_lemmas`: before this screen, only tangential row 19 (`sum_distinct_implies_sidon`, Tuza-era, irrelevant). After this screen: rows **49** and **50** added (see §2.4) — both erdos_307 hazards, both refutations that *shrink the search space* (loop progress per §4 doctrine, not failure).
- knowledge.db (`mk find`): no findings for any of the four problems.

## 4. DB actions taken (all SELECT-verified before write; old → new)

| Table.row | Field | Old | New |
|---|---|---|---|
| candidate_queue `erdos_307` | literature_status | `UNKNOWN` | `OPEN (verified 2026-06-10: erdosproblems.com #307 VERIFIABLE, no claimed solutions; arXiv sweep clean; PRODUCT framing only — sum framing banned per plan §7)` |
| candidate_queue `erdos_307` | prior_attempts | `1` | `2` (slot576 id 1090 + slot597 id 1116; V4-precedent correction) |
| candidate_queue `erdos_97` | literature_status | `UNKNOWN` | `OPEN (verified 2026-06-10: erdosproblems.com #97 FALSIFIABLE, last edited 2025-10-27, no claimed solutions; arXiv sweep clean; R2-geometry = Aristotle hard-zero, informal-only per plan V0 — do NOT fill Target-5 slot)` |
| false_lemmas id 49 | (INSERT) | — | `erdos307_slot576_PQ_overlap_construction` (slot576, UUID e44797f4; reasoning_based) |
| false_lemmas id 50 | (INSERT) | — | `erdos307_slot597_result3_prime_egyptian` (slot597, UUID 3be49710; reasoning_based) |

**Deliberately NOT touched**: the 31 `compile_failed` rows (already correctly terminal); submissions row 1116 (`problem_id` relabel + ERROR-state disposition = V0 Phase 1 scope); candidate_queue has no erdos_707/erdos_590 rows to terminalize (kills recorded here and via the do-not-repeat upgrade in §2.1/§2.2). **Zero submissions to Aristotle.** Nothing committed to git.

## 5. Sources

- erdosproblems.com /97, /590, /307 — fetched 2026-06-10 (curl + browser UA; WebFetch 403s on this domain).
- Alexeev & Mixon, *Forbidden Sidon subsets of perfect difference sets*, arXiv:2510.19804 (v1 2025-10-22, v2 2026-01-16 with Lean ancillary files).
- github.com/plby/lean-proofs `src/v4.24.0/ErdosProblems/Erdos707.lean` (6359 lines, fetched 2026-06-10).
- Tao, AI-contributions wiki (github.com/teorth/erdosproblems/wiki): #707 §2(b) green "Hall (1947)"; 97/307/590 absent.
- google-deepmind/formal-conjectures: HEAD `4f866bec76` (2026-06-09); file commits 97 `0137b96de1` (2026-02-03), 590 `bdd632a698` (2025-12-23), 707 `ab84c073cd` (2026-04-29), 307 `754010872d` (2026-05-27). Local typecheck against fork checkout `aa91edc` (toolchain v4.22.0): PASS for both open 307 statements.
- Hall, M. Jr., *Cyclic projective planes*, Duke Math. J. 14 (1947) 1079–1090. Chang [Ch72]; Specker [Sp57]; Larson [La73]; Barbeau [Ba76]; Fishburn–Reeds [FiRe92] — as cited on the respective erdosproblems.com pages.
