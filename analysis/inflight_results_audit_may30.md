# Inflight Aristotle Results Audit — 2026-05-30 (Agent E2)

Audit of all 6 inflight Aristotle submissions (slots 741-746) using the new F-mode
detectors (S7, `audit_proven.py`) + closure-axis labels (S4, `.closure.json`).

Pipeline state at audit time:
- 5/6 result archives downloaded but never registered in DB (S4 noted backfill needed).
- Only slot 746 has a `submissions` row (the first submission through the new closure-axis gate).
- All 6 tarballs extracted under `submissions/nu4_final/slot{741..746}_extracted/`.
- F-mode detectors run against each `Main.lean` (or `OddMultiperfect.lean` for slot 746).

Status enum: `submitted | compile_failed | compiled_partial | compiled_no_advance | compiled_advance | disproven`.
`compiled_advance` is opt-in and requires `target_resolved=1 AND axiomatizes_prior_work=0 AND contribution_statement NOT NULL`.

---

## slot 741 — E647 Cunningham residual 35

UUID: `7031f637-54ed-4362-9456-5b4e27e038e0`
Sketch: `submissions/sketches/erdos647_cunningham_residual_35.txt`
Closure label: `CS=sub_claim_closure / CM=witness_table_chunked / CR=clean_decidable / HM=journal_subclaim` (real_closure_candidate=true)
Result file: `submissions/nu4_final/slot741_extracted/9fa69652-7f15-4ebc-8c5c-16e4dd35f7c3_aristotle/RequestProject/Main.lean`

**What Aristotle produced.** A 25-line proof. Private lemma `erdos_647_witness_table` discharges the full disjunction `(n+2 < (n-5) + σ₀(n-5)) ∨ (n+2 < (n-6) + σ₀(n-6))` over `n ∈ Finset.Icc 3000 1000000` filtered by the four primality constraints, via a single `native_decide`. Main theorem `erdos_647_cunningham_residual_bounded` case-splits on the disjunction and constructs the existential `Fin n` witness as `n-5` or `n-6`. sorry=0, axiom=0, native_decide=1, only standard axioms (propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound).

**F-mode failures.** F9 (HIGH) — bounded native_decide pattern (`n ≤ 1000000` + `native_decide`). This is a *correct* F9 detection in the sense that the theorem IS bounded, but the closure JSON explicitly tags it as a `sub_claim_closure` of the bounded family (not the unbounded conjecture), so the F9 flag is informational rather than disqualifying.

**Honest status.** `compiled_no_advance` of the unbounded E647 conjecture, but **`compiled_advance` of the bounded sub-claim** ("35 Cunningham configurations in [3000, 10^6] all admit witness m ∈ {n-5, n-6}"). Per the CLAUDE.md gate (target_resolved=1, axiomatizes_prior_work=0, contribution_statement set) this can be promoted manually. For now: **`compiled_no_advance`** (no manual promotion done).

**Math content score.** 6/10. Real bounded resolution of a 35-case region carved out by slot737. Witness-table is mechanical but exhaustive on the structurally significant Cunningham-chain residue. Not novel mathematics but a publishable journal sub-claim.

**Resubmission?** No — the bounded version is settled; the unbounded version requires structural mathematics, not more witness tables.

---

## slot 742 — E203 1D Sierpinski Artin benchmark

UUID: `bdc60eff-04a7-4c15-b469-bcd118b443c6`
Sketch: `submissions/sketches/erdos203_sierpinski_1d_benchmark.txt`
Closure label: `CS=formalization_only / CM=witness_table_chunked / CR=clean_decidable / HM=calibration_only` (real_closure_candidate=false)
Result file: `submissions/nu4_final/slot742_extracted/be1e80e5-e7b7-4066-9fad-79552cffc155_aristotle/RequestProject/Main.lean`

**What Aristotle produced.** **Disproof.** Counterexample m=4643: for every k ∈ {0,…,31}, some Artin prime p ≤ 500 divides 2^k · 4643 + 1. The original theorem statement is commented out with explanation; the actual theorem `index1_sierpinski_insufficient_K32_B500_counterexample : counterexampleCheck = true` is proved by `native_decide`. sorry=0 in code (1 sorry in the *commented-out* original statement). Uses only standard axioms.

**F-mode failures.** None on the actual code. (audit_proven.py reports `sorry=1` because it counts `sorry` in raw content including comments — verified via re-parse that code-only sorry=0.) Note: `audit_proven.py` has a minor bug where `sorry_count` is computed before stripping comments; this should be fixed separately.

**Honest status.** **`disproven`** — the original conjecture statement is **false** (m=4643 counterexample), Aristotle proved the disproof, no advance on the open E203 because this was a calibration probe, not the open conjecture. Closure label correctly says `CS=formalization_only / HM=calibration_only / real_closure_candidate=false`.

**Math content score.** 3/10. Calibration probe; the counterexample search is mechanical (Python pool + CRT-style residue cover). Useful as a pipeline smoke test, not as new mathematics. The closure JSON already flags this as calibration.

**Resubmission?** No — the conjecture as stated is *false*; resubmitting won't help. The interesting open question is the 2-D grid (slot 743).

---

## slot 743 — E203 12×12 grid B=1000

UUID: `8d9e29b3-c099-4fea-beb2-aab7ed76fb99`
Sketch: `submissions/sketches/erdos203_grid_12x12_B1000.txt`
Closure label: `CS=bounded_version_closure / CM=witness_table_chunked / CR=clean_decidable / HM=journal_partial` (real_closure_candidate=false, hedge=true)
Result file: `submissions/nu4_final/slot743_extracted/cdf8c4de-78a9-4297-9a63-9230440720df_aristotle/RequestProject/Main.lean`

**What Aristotle produced.** A 475-line proof with explicit witness `M = 625942982474437835576448580641867239959237377760067219877585649` (63-digit number constructed via greedy set cover + CRT over 34 index-1 primes ∈ {5,7,11,13,17,19,29,31,37,41,43,53,59,61,67,79,83,89,101,103,107,109,113,127,131,157,163,179,211,227,229,269,691,971}). 178 native_decide calls across 213 lemmas: 34 `index1_p` (primitive-root density), 34 `prime_p` (primality), 144 `dvd_k_l` (one per grid cell). Main theorem `erdos203_grid_12x12_B1000_exists` is proven via 144-way `interval_cases` matching each grid cell to its covering prime. sorry=0, axiom=0.

**F-mode failures.** F3 (HIGH) — 213 proven lemmas, no name match for `problem_id_hint='Main'`. **False positive**: the detector extracted "Main" from the filename `Main.lean` rather than the actual theorem id; the target `erdos203_grid_12x12_B1000_exists` IS present and IS proven. F9 (HIGH) — bounded native_decide. Correct flag on the bounded shape but the closure JSON already marks this as `bounded_version_closure` (real_closure_candidate=false).

**Honest status.** `compiled_no_advance` of the unbounded E203, **`compiled_advance` of the bounded sub-claim**. The 8×8 result from slot 740 DID extend to 12×12 at B=1000; the Monte-Carlo hedge in the sketch was disproven (it predicted unsatisfiability; Aristotle found a witness). Per CLAUDE.md gate: stays `compiled_no_advance` unless contribution_statement set manually.

**Math content score.** 7/10. Genuine bounded result that extends prior work. Witness construction is non-trivial (set cover + CRT) and the formalization is sound. Closure JSON wrongly predicted unsatisfiability; this is an actual sub-claim advance.

**Resubmission?** No — the bounded result is settled. The open lift problem (whether finite covers imply the unbounded conjecture) is documented in `analysis/erdos203_quotient_lift_may30.md` and requires structural mathematics, not larger grids.

---

## slot 744 — FT q=1583 alternate-witness diagnostic

UUID: `22dafcc6-0afa-4769-b293-c368b97ade0b`
Sketch: `submissions/sketches/FT_p3_q1583_alternate.txt`
Closure label: `CS=sub_claim_closure / CM=structural_finite_reduction / CR=clean_decidable / HM=journal_subclaim` (real_closure_candidate=true)
Result file: `submissions/nu4_final/slot744_extracted/b2236ca3-82b4-4cde-b608-4caf694579c7_aristotle/RequestProject/Main.lean`

**What Aristotle produced.** A 17-line proof. Single theorem `feit_thompson_p3_q1583 : ¬ (1583 ^ 3 - 1) / (1583 - 1) ∣ (3 ^ 1583 - 1) / 2 := by native_decide`. sorry=0, axiom=0, single native_decide on the direct modular exponentiation (3^1583 mod 2,507,473 = 1,702,700 ≠ 1).

**F-mode failures.** None.

**Honest status.** **`compiled_no_advance`** of the FT family. Settles one prime q=1583 — a structurally significant case because A(1583)=2,507,473 is itself prime, blocking the slot720/slot736 Fermat-reduction mechanism. Per CLAUDE.md gate, this is a sub-claim, not a family-level closure.

**Math content score.** 5/10. Honest single-prime case clearance via direct computation. The structural significance (A(q) is itself prime, blocking the family-reduction mechanism) makes this worth recording but it's mechanical at the individual prime.

**Resubmission with full prior context? STRONGLY RECOMMENDED.** Per S4 audit, **9 prior FT artifacts** would now be auto-attached by `gather_context` (which was fixed 2026-05-30 per `docs/infrastructure_changes_may30/I1_gather_context_fix.md`). Pre-fix `gather_context` returned 0 rows because it filtered on `status IN ('compiled_clean', 'near_miss', 'completed')` — all retired status names. The 9 artifacts that the *new* `gather_context` would attach for `problem_id LIKE '%feit_thompson%'`:

1. `slot720_iter2_ft_family_result.lean` (compiled_advance, 2026-05-28) — the family p3q71 close
2. `slot613_ft_p3_wieferich_kA2_result.lean` (compiled_no_advance, 2026-02-12)
3. `slot612_ft_p3_quartic_residue_result.lean` (compiled_no_advance, 2026-02-12)
4. `slot611_ft_p3_cubic_character_contradiction_result.lean` (compiled_no_advance, 2026-02-12)
5. `slot610_ft_p3_mod8_3_qr_contradiction_result.lean` (compiled_no_advance, 2026-02-12)
6. `slot608_ft_p3_mod9_2_contradiction_result.lean` (compiled_no_advance, 2026-02-11)
7. `slot603_ft_p3_higher_congruence_result.lean` (compiled_no_advance, 2026-02-11)
8. `slot602_ft_p3_mod9_additive_result.lean` (compiled_no_advance, 2026-02-11)
9. `slot601_ft_p3_cubic_supplement_result.lean` (compiled_no_advance, 2026-02-11)

Without these the current slot744 proof is the trivial 1-line native_decide. A resubmit with all 9 priors might trigger Aristotle to instantiate `not_dvd_via_fermat_factor` from slot720 (rather than bypass via native_decide on the full 3^1583 mod 2507473 computation) — that would be **structurally** stronger because it would reduce q=1583 to the same proof shape as the family-cleared primes. **Recommendation:** resubmit slot744 once with `--verbose-context` to confirm all 9 artifacts attach.

---

## slot 745 — Brocard [1001, 2000] iter4

UUID: `8e353fc6-c165-4df2-9577-088dea34eb52`
Sketch: `submissions/sketches/brocard_nrange_1001_2000.txt`
Closure label: `CS=bounded_version_closure / CM=witness_table_chunked / CR=clean_decidable / HM=journal_partial` (real_closure_candidate=false)
Result file: `submissions/nu4_final/slot745_extracted/9cb693c2-bf0b-4277-bc83-28c5f559d17d_aristotle/RequestProject/Main.lean` (+ `BrocardData.lean`)

**What Aristotle produced.** A 209-line `Main.lean` + ~70KB `BrocardData.lean` with explicit witness table (`getWitness` maps each n ∈ [1001, 2000] to a 6-tuple `(pₙ, pₙ₊₁, q₁, q₂, q₃, q₄)`). Proof structure: 2 helper lemmas (`nth_prime_eq`, `four_primes_in_Ioo`), decidable `BrocardCheck`, 20 chunked `native_decide` lemmas (50 entries each), top-level `brocard_check_all` routing via `le_or_gt` cascade, main theorem `brocard_conjecture_extended_1001_2000` assembling `brocard_of_check`. sorry=0, axiom=0.

**F-mode failures.** F3 (HIGH) — 26 proven lemmas, no name match for `problem_id_hint='Main'`. **False positive** (same as slot 743): the target `brocard_conjecture_extended_1001_2000` IS proven; the detector misread the filename as the problem id. F9 is *not* flagged because the theorem statement uses `1001 ≤ n → n ≤ 2000` outside of `Finset.Icc/.range`, so the F9 numeric-ceiling regex doesn't fire (the bound is in the hypothesis, not the conclusion).

**Honest status.** `compiled_no_advance` of unbounded Brocard, **`compiled_advance` of the bounded range [1001, 2000]**. Extends prior range bumps (slot 722 for [2, 50] and earlier slots for [501, 1000]) to [1001, 2000]. Sieving range reached p_2001² ≈ 3.03 × 10^8. Per CLAUDE.md gate: `compiled_no_advance` until manual promotion.

**Math content score.** 6/10. Range bump. Solid formalization, real verification work (witness primes pre-computed), but ultimately a calibrated extension of the same chunked-native_decide template that slot 738 used. Publishable as a research note; not the open conjecture.

**Resubmission?** No — the range is settled. To advance, the next iter must escape the witness-table paradigm (try a Bertrand-style structural argument for unbounded n).

---

## slot 746 — Odd multiperfect σ₀=11 sub-case closure ⭐ (GATE VALIDATION CASE)

UUID: `65da8d8c-4059-4454-b3b4-ea2e3b87ede7`
Sketch: `submissions/sketches/odd_multiperfect_sigma0_11.txt`
Closure label: `CS=sub_claim_closure / CM=structural_finite_reduction / CR=clean_decidable / HM=journal_subclaim` (real_closure_candidate=true) — **first submission through the new closure-axis gate (mathematical_content_score=4 pre-set by S4).**
Result file: `submissions/nu4_final/slot746_extracted/4dab36cf-5ed8-4df9-ac5f-cfd93a2c3e71_aristotle/RequestProject/OddMultiperfect.lean`

**What Aristotle produced.** A 72-line structural proof in **three helper lemmas + main theorem**:

1. `card_divisors_eq_prime_of_eleven` — if σ₀(n) = 11 (prime) and n > 1, then n = p^10 for some prime p (via `Nat.card_divisors` and the multiplicativity of σ₀). This is the structural reduction.
2. `sigma_prime_pow_mod` — σ(p^10) ≡ 1 (mod p) (geometric series telescoping).
3. `prime_dvd_of_pow_dvd` — transitivity utility.
4. Main theorem `odd_multiperfect_sigma0_11_impossible : ¬ ∃ n : ℕ, Odd n ∧ n > 1 ∧ (Nat.divisors n).card = 11 ∧ ∃ k : ℕ, k ≥ 2 ∧ ((Nat.divisors n).sum id) = k * n` — combines via `nlinarith` after instantiating n = p^10, σ(p^10) = k·p^10.

sorry=0, axiom=0, no native_decide. Pure structural/algebraic argument. Standard axioms only.

**F-mode failures.** None. No bounded ceilings, no Iff.rfl trap, no side-lemma proliferation (5 proven decls), no exact?/apply? trails, no native_decide leakage.

**Honest status.** **`compiled_advance`** sub-claim candidate. The σ₀=11 single-shape impossibility IS the open gap the sketch targeted, and Aristotle resolved it cleanly via a 1-line p-adic argument (after the multiplicativity reduction). Per CLAUDE.md gate, this requires `target_resolved=1 + axiomatizes_prior_work=0 + contribution_statement NOT NULL`; ready for manual promotion if a contribution_statement is added.

**Math content score.** 8/10. Real structural mathematics — single-shape reduction via prime σ₀, p-adic contradiction. The proof matches the closure JSON's rationale exactly ("1-line p-adic; n=p^10 cannot satisfy σ(n)=kn"). Verifies the slot737 σ₀ DNA precedent. This is a sub-claim of odd perfect / multiperfect that has NOT (to my best knowledge) been previously formalized in Lean/Mathlib for σ₀=11 specifically.

**Gate validation verdict.** ✅ **The closure-axis gate worked correctly on its first real test.** The sketch had `real_closure_candidate=true` with concrete structural rationale; Aristotle produced a clean structural proof matching the stated mechanism; the result has zero F-mode failures and meets all `compiled_advance` criteria. The new gate is fit for purpose.

**Resubmission?** No — the σ₀=11 sub-case is closed. Next targets: σ₀=13 (also prime), σ₀=17, σ₀=19 — same template should apply.

---

## DB update plan

5 of 6 slots (741, 742, 743, 744, 745) have **no row** in `submissions`. I will INSERT minimal rows with the audit verdicts. Slot 746 will be UPDATED.

For each row I will write:
- `uuid`, `filename` (the result file), `problem_id`, `output_file`
- `status` (per honest assignment above), `sorry_count=0`, `axiom_count=0`, `axiomatizes_prior_work=0`
- `mathematical_content_score`, `verified=1`
- `closure_axis_json` (copied from the `.closure.json` companion)
- `notes` summarizing F-mode detections and audit

**Compiled_advance count post-audit:** ZERO of these 6 are auto-promoted (the gate is opt-in, requires manual `contribution_statement`). slot 746 is the strongest candidate but is left as `compiled_no_advance` per gate-discipline; promotion is a separate manual decision.

## Detector quality notes (for S7 followup)

1. **F3 problem_id_hint extraction is buggy** when the file is named `Main.lean` — the regex strips `_extracted/<uuid>_aristotle/RequestProject/Main` to `Main`, losing the slot/problem info. Should walk up to the slot number from the tarball directory. Affects slots 743 and 745 with **false-positive HIGH F3**.
2. **`sorry_count` is computed against raw content** including comments, double-counting commented-out theorem statements. Affects slot 742 (1 sorry in a comment was counted). Fix: strip comments before the `sorry` regex.
3. F9 correctly fires on slots 741 and 743 but the closure-axis label already declares them bounded — the audit should cross-check F9 against `CS=bounded_version_closure` before flagging.
