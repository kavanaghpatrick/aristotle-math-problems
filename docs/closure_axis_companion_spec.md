# Closure-Axis Companion File Spec (v1.0)

**Authority**: Operationalizes the 4-axis closure taxonomy from `docs/closure_taxonomy_may30.md` at submission time.
**Status**: ACTIVE as of 2026-05-30. Enforced (with WARN-only transition) by `check_closure_axis()` in `scripts/safe_aristotle_submit.py`.
**Owner**: Closure-execution team, Agent #2 of 5.

---

## Why

The 4-axis taxonomy (CS / CM / CR / HM) lives on paper in `docs/closure_taxonomy_may30.md`. Until the May 30 contract, nothing checked it at submission time, so `bounded_version_closure` and `formalization_only` outcomes were silently counted as `compiled_advance` successes. This file specifies the on-disk artifact that fixes that gap.

Per MEMORY.md directive #4 ("Stop saying PROVEN for infrastructure that doesn't advance anything"), every submission that targets the real closure lane must carry an honest classification in a machine-readable form. The submission gate reads that file and either passes, warns, or rejects.

---

## File location and naming

For every sketch at `submissions/sketches/<name>.txt`, the companion file lives at:

```
submissions/sketches/<name>.closure.json
```

Examples:
- `submissions/sketches/erdos389_bounded_n50.txt` -> `submissions/sketches/erdos389_bounded_n50.closure.json`
- `submissions/sketches/slot737.txt`              -> `submissions/sketches/slot737.closure.json`

The naming rule: take the sketch path, strip the `.txt` suffix, append `.closure.json`. The gate computes this path by `input_file.with_suffix('.closure.json')`. No nesting, no separate directory — the companion lives next to its sketch.

---

## File format

Strict JSON. Six required top-level fields, no extra fields permitted.

```json
{
  "CS": "<closure-scope-enum>",
  "CM": "<closure-mechanism-enum>",
  "CR": "<closure-risk-enum>",
  "HM": "<honesty-marker-enum>",
  "real_closure_candidate": <bool>,
  "rationale": "<one-sentence English justification>"
}
```

### Enum values (verbatim, must match the taxonomy doc)

**CS — Closure Scope:**
- `full_closure`
- `direction_closure`
- `disproof_closure`
- `bounded_version_closure`
- `sub_claim_closure`
- `formalization_only`

**CM — Closure Mechanism:**
- `explicit_witness`
- `bounded_to_infinite_lift`
- `structural_finite_reduction`
- `disproof_construction`
- `witness_table_chunked`
- `density_sieve_closure`
- `induction_template`
- `none_known`

**CR — Closure Risk (primary risk only; secondaries go in the rationale):**
- `clean_decidable`
- `partial_result_only`
- `iff_rfl_trap`
- `witness_search_explosion`
- `definition_mismatch`
- `em_tautology`
- `infrastructure_overgrowth`
- `recursive_falsification`

**HM — Honesty Marker:**
- `journal_clean`
- `journal_partial`
- `journal_subclaim`
- `infrastructure_only`

**real_closure_candidate:** boolean. `true` iff (CS in {full_closure, direction_closure, disproof_closure}) AND (CM != none_known) AND (CR in {clean_decidable, witness_search_explosion}) AND (HM == journal_clean). The agent populates this; the gate does NOT re-derive it (it trusts the agent's honesty here and audits separately).

**rationale:** one English sentence, < 280 chars. Names the prior result this builds on, or the falsified pattern this avoids, or the reason the agent is willing to be on the hook for `real_closure_candidate`. This field is read by audit agents — not just the gate.

---

## Gate behavior (`check_closure_axis`)

`scripts/safe_aristotle_submit.py` implements the gate with the following decision table:

| Companion file | `real_closure_candidate` | `--rubric-points` flag | Outcome |
|---|---|---|---|
| missing | n/a | n/a | WARN + log `MISSING_CLOSURE_AXIS`; **allow** (transition period) |
| present, invalid JSON | n/a | n/a | REJECT with parse error |
| present, schema-invalid (missing field or bad enum) | n/a | n/a | REJECT with schema error |
| present, valid | `true` | n/a | PASS |
| present, valid | `false` | absent | REJECT — "not in the real-closure lane; pass `--rubric-points` to override" |
| present, valid | `false` | present | PASS (logged as `RUBRIC_POINTS_OVERRIDE`) |

The `--rubric-points` flag is the documented escape hatch for engineering submissions (mechanical extensions, formalization-only ports) that we are explicitly OK with not counting as gap closure. The override is logged so audit can spot abuse.

---

## DB integration

When a submission succeeds, `safe_submit()` records the closure axis on the DB row in column `submissions.closure_axis_json` (TEXT, JSON-serialized). Per the schema migration (`scripts/migrate_add_closure_axis.py`), rows submitted before this gate landed keep `closure_axis_json = NULL`. Backfills are out of scope for v1.0 of this spec — if a backfill is wanted, it should run as a separate, audited migration.

Query examples:

```sql
-- Real closure candidates only
SELECT id, filename, status, closure_axis_json
  FROM submissions
 WHERE closure_axis_json IS NOT NULL
   AND json_extract(closure_axis_json, '$.real_closure_candidate') = 1;

-- Bounded-version submissions misclassified as advances
SELECT id, filename, status
  FROM submissions
 WHERE status LIKE 'compiled_advance%'
   AND json_extract(closure_axis_json, '$.CS') = 'bounded_version_closure';

-- Formalization-only submissions (should never be in the closure lane)
SELECT id, filename
  FROM submissions
 WHERE json_extract(closure_axis_json, '$.CS') = 'formalization_only';
```

---

## How to populate a `.closure.json`

1. Read `docs/closure_taxonomy_may30.md` end-to-end the first time. Re-read the four tables (CS, CM, CR, HM) every time you classify.
2. Apply the decision rules in the taxonomy doc, one axis at a time.
3. Run the combined REAL-closure rule. If it yields `true`, set `real_closure_candidate: true` in the companion file. Otherwise `false`.
4. Write the rationale in ONE sentence. Name the parent slot (if mechanical extension) or the falsified-approach key you avoid (if structural) or the bound bump you are owning honestly (if bounded extension).
5. Validate with `python3 -c "import json; json.load(open('<path>.closure.json'))"` before invoking submit.

A sketch with no companion file is still submittable during the transition period — the gate prints a warning and logs `MISSING_CLOSURE_AXIS` so audit can catch it later. New sketches drafted after 2026-05-30 should ship the companion file unconditionally.

---

## Minimal valid example

`submissions/sketches/brocard_n500_to_1000.closure.json`:

```json
{
  "CS": "bounded_version_closure",
  "CM": "witness_table_chunked",
  "CR": "clean_decidable",
  "HM": "journal_partial",
  "real_closure_candidate": false,
  "rationale": "Extends slot722 (Brocard n in [2,500]) to [501,1000] via 10x50 chunked native_decide; Brocard unbounded remains open."
}
```

This submission requires `--rubric-points` to pass the gate. That is the correct outcome: bounded extension of Brocard is publishable as a research note, not as Brocard closure.

---

## F-mode mapping (S7, 2026-05-30)

The closure-axis enums are tied directly to the F1-F10 failure modes catalogued in `analysis/failure_dna_may30.md`. The gate now enforces internal coherence between axes — combinations that the taxonomy declares structurally impossible are REJECTED, not warned about. See `docs/failure_mode_prevention.md` for the master mapping.

| Axis enum | F-mode caught | Coherence rule enforced by gate |
|---|---|---|
| `CR=iff_rfl_trap` | F1, F8 | If `real_closure_candidate=true`, REJECT (F1-coherence) |
| `CR=em_tautology` | F2 | If `real_closure_candidate=true`, REJECT (F2-coherence) |
| `CR=infrastructure_overgrowth` | F3 | If `real_closure_candidate=true`, REJECT (F3-coherence) |
| `CR=recursive_falsification` | F5 | If `real_closure_candidate=true`, REJECT (F5-coherence) |
| `CR=definition_mismatch` | F10 | If `real_closure_candidate=true`, REJECT (F10-coherence) |
| `CR=witness_search_explosion` | F9 | (allowed when mitigated by chunking) |
| `CS=bounded_version_closure` | F7 | If `real_closure_candidate=true`, REJECT (F7-coherence) |
| `CS=formalization_only` | F10 (definitional drift), F1 (vacuous) | If `real_closure_candidate=true`, REJECT |
| `HM=infrastructure_only` | catch-all for F-mode-only outputs | If `real_closure_candidate=true`, REJECT |

These checks live in `_check_closure_axis_consistency()` and run *after* the basic schema validation in `check_closure_axis()`.

The taxonomy was designed so that an honest classification of an F-mode-tainted attempt cannot claim closure. If the gate rejects on coherence grounds, the author should re-read `docs/closure_taxonomy_may30.md` and pick CS/CR/HM values that match the F-mode they are actually producing.

---

## Versioning

- v1.0 (2026-05-30, this spec) — Initial. Six fields, single primary CR.
- v1.0.1 (2026-05-30, S7) — Added `_check_closure_axis_consistency()` enforcing the F-mode coherence rules above. Schema unchanged.
- Future v1.1: optional `closure_risk_secondary: [str]` array, optional `parent_slots: [str]` array. Backward-compatible.
- Future v2.0: if the closure taxonomy adds a 5th axis, the gate must be updated in lock-step.
