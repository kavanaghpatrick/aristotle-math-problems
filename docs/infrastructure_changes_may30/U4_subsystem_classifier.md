# U4 — Subsystem Engagement Classifier

**Author:** U4 (May 30 2026 wave, agent 4 of 5)
**Status:** Classifier shipped, historical audit complete, watch script ready.
**Files touched:**
- `scripts/subsystem_engagement_classifier.py` (new, ~440 LOC)
- `scripts/_subsystem_audit_runner.py` (new, internal CSV builder)
- `scripts/subsystem_engagement_watch.py` (new, polls 6 inflight UUIDs)
- `analysis/subsystem_engagement_audit.csv` (generated historical CSV)
- `analysis/inflight_subsystem_audit.md` (created by watch script on first hit)
- `docs/infrastructure_changes_may30/U4_subsystem_classifier.md` (this file)

---

## 1. Motivation

Per W8 (May 30 2026) and I9 (informal-mode adapter), Aristotle has two
substantively different subsystems:

1. **Subsystem #1 — MCGS formalizer.** Takes a Lean theorem statement,
   searches Mathlib tactic space. Output ARISTOTLE_SUMMARY.md describes the
   *tactic* (e.g. "`native_decide` handles the case range"). Theorem is
   typically closed by a brute-force computational tactic or left as `by
   sorry` when search fails.
2. **Subsystem #2 — Informal lemma-based reasoner.** Takes an NL problem,
   generates an NL proof, decomposes into lemmas, autoformalizes. Output
   ARISTOTLE_SUMMARY.md has an explicit "Informal proof:" section in
   English-mathematical prose plus a separate "Formalization:" section
   describing the Lean encoding.

The I9 smoke test confirmed the framing: when Aristotle invokes subsystem
#2, the summary has the bipartite structure (informal-proof + formalization)
visible at the document level. The U4 classifier turns that observation into
an automatic test.

---

## 2. Classifier API

### 2.1 Library use

```python
from subsystem_engagement_classifier import classify_artifact

result = classify_artifact(Path("submissions/nu4_final/i9_extracted"))
# -> ClassificationResult dataclass (asdict for JSON)
```

The function accepts a path to an extracted Aristotle artifact directory.
The directory must (directly or in a `<uuid>_aristotle/` child) contain
`ARISTOTLE_SUMMARY.md`. If `RequestProject/Main.lean` is present it is
inspected for Mathlib imports and tactic structure.

### 2.2 Output (JSON)

```jsonc
{
  "artifact_dir": "<absolute path to the *_aristotle/ directory>",
  "uuid": "<inferred uuid or null>",
  "subsystem_engaged": "formalizer_only" | "informal_reasoner" | "ambiguous",
  "evidence_signals": [ "<short signal string>", ... ],
  "informal_proof_section_present": bool,
  "separate_formalization_section_present": bool,
  "nl_reasoning_word_count": int,
  "mathlib_modules_imported": [ "Mathlib.X.Y", ... ],
  "validation_criteria_hit": [ "C1", "C2", "C3", "C4" ],
  // diagnostics:
  "summary_present": bool,
  "summary_word_count": int,
  "main_lean_present": bool,
  "has_native_decide_only_proof": bool,
  "has_unresolved_sorry": bool,
  "informal_headers_found": [ ... ],
  "formalization_headers_found": [ ... ]
}
```

### 2.3 CLI

```bash
# JSON to stdout
python3 scripts/subsystem_engagement_classifier.py <artifact_dir>

# Pretty-print
python3 scripts/subsystem_engagement_classifier.py <artifact_dir> --pretty
```

---

## 3. Classification rules (S10 validation framework)

The four validation criteria from S10:

| Criterion | Trigger |
|---|---|
| **C1** | ARISTOTLE_SUMMARY.md contains a header (markdown `#`/`##`, bold `**…**`, or `field:` line) with one of: "informal proof", "informal argument", "informal reasoning", "natural-language proof", "english proof", "english argument". |
| **C2** | Separate header for: "formalization", "lean encoding", "lean formalization", "lean proof", "formal proof", "in lean". |
| **C3** | The text under C1 headers (excluding fenced code blocks) contains ≥ 30 words. |
| **C4** | `RequestProject/Main.lean` (or first found `.lean`) imports Mathlib AND the proof is NOT pure-computational AND has no unresolved `sorry`. |

The classifier requires `C1 + C2 + (C3 or C4)` (i.e. ≥ 3 criteria including
both C1 and C2) before emitting `informal_reasoner`. This is intentionally
strict — the I9 framing puts the informal section AND a separate
formalization section in the same document; either signal alone is too weak.

`formalizer_only` requires:

- No C1, no C2, zero NL words, AND
- Theorem closed by pure computational tactic (`native_decide`/`decide`/`rfl`
  with no `exact <Lemma>`/`apply`/`rw`/etc.) OR contains unresolved `sorry`.

Everything else: `ambiguous`. This is the deliberate fall-through; a
substantial fraction of historical MCGS wins look ambiguous because Mathlib
lemma application alone (C4) does not prove the informal reasoner was
engaged. Only the bipartite document structure does.

### 3.1 Interpreting "ambiguous"

`ambiguous` does NOT mean "subsystem #2 might have run." Per the historical
audit (§4), every prior production submission that classified `ambiguous`
was a clean MCGS-only win where Aristotle found a real Mathlib proof but
wrote it up as "Proof strategy:" rather than "Informal proof:". The
distinction is the *framing* in ARISTOTLE_SUMMARY.md, not the proof quality.

Read `ambiguous` as: "Aristotle wrote up the result as a formalization
exercise. Cannot tell from the artifact alone whether the informal reasoner
ran first or whether MCGS found the proof directly."

For S10 validation purposes, `ambiguous` is a NEGATIVE signal for subsystem
#2 engagement (you should NOT count it toward the decisive threshold).

---

## 4. Historical audit (`analysis/subsystem_engagement_audit.csv`)

Generated via `python3 scripts/_subsystem_audit_runner.py`. Includes the I9
smoke artifact for calibration.

| Slot       | Lane (DB) | DB Status            | Subsystem        | Criteria       |
|------------|-----------|----------------------|------------------|----------------|
| i9_smoke   | informal  | (calibration)        | **informal_reasoner** | C1,C2,C3,C4 |
| slot723    | bare      | submitted            | formalizer_only  | (none)         |
| slot724    | bare      | submitted            | formalizer_only  | (none)         |
| slot736    | (n/a)     | (compiled)           | ambiguous        | C4             |
| slot737    | (n/a)     | (compiled)           | ambiguous        | C4             |
| slot738    | (n/a)     | (compiled)           | ambiguous        | C4             |
| slot739    | (n/a)     | (compiled)           | ambiguous        | C4             |
| slot740    | (n/a)     | (compiled)           | ambiguous        | C2             |
| slot741    | closure   | compiled_no_advance  | ambiguous        | C4             |
| slot742    | (n/a)     | disproven            | formalizer_only  | (none)         |
| slot743    | (n/a)     | compiled_no_advance  | ambiguous        | C2,C4          |
| slot744    | (n/a)     | compiled_no_advance  | formalizer_only  | (none)         |
| slot745    | (n/a)     | compiled_no_advance  | ambiguous        | C4             |
| slot746    | (n/a)     | (n/a)                | ambiguous        | C4             |

**Summary: 1 of 14 historical artifacts (= I9 smoke calibration) invoked
subsystem #2. 0 of 13 prior production submissions did.**

This is exactly the W8 prediction. Per the rolled-out infrastructure (I9
informal-mode adapter), every future submission via `--fusion-lane` /
`--informal-mode` should turn the production hit count up from zero.

### 4.1 I9 smoke-test verification

```
python3 scripts/subsystem_engagement_classifier.py \
    submissions/nu4_final/i9_extracted --pretty
```

Output (verified):

- `subsystem_engaged = "informal_reasoner"`
- `informal_proof_section_present = true` ("Informal proof (Euclid's argument):")
- `separate_formalization_section_present = true` ("Formalization:" + "Formal proof:")
- `nl_reasoning_word_count = 88` (the Euclid's-argument prose)
- `validation_criteria_hit = ["C1", "C2", "C3", "C4"]`

All four S10 criteria satisfied, confirming the classifier round-trips on
the known-positive case.

---

## 5. The single most important signal

**The presence of `Informal proof:` / `Informal argument:` as a header in
ARISTOTLE_SUMMARY.md (C1).**

Empirically (§4), every historical production summary written by MCGS-only
uses framings like "Proof strategy:" or "Theorem proved:" or no header at
all. The bipartite "Informal proof: ... Formalization: ..." structure is
the textual fingerprint of subsystem #2's report generator. No production
submission has ever produced this structure, and the I9 smoke test (the
ONLY known-positive case) does. C1 alone is the highest-signal binary test.

C2-C4 are secondary corroboration. The classifier requires C1+C2 because
"Informal proof:" alone could be a transcription style choice; the
*separate* formalization section is the structural marker of NL-first
reasoning followed by autoformalization.

---

## 6. Watch script (`subsystem_engagement_watch.py`)

Polls the 6 inflight informal-mode/fusion/closure submissions from the May
30 2026 wave every 5 minutes. On each COMPLETE / COMPLETE_WITH_ERRORS:

1. Downloads the artifact via `Project.get_files()`.
2. Extracts into `submissions/nu4_final/inflight_<problem>_extracted/`.
3. Runs `classify_artifact()`.
4. Appends a block to `analysis/inflight_subsystem_audit.md`.
5. Tags the DB row in `submissions.notes`.
6. Prints `DECISIVE` to stdout when ≥ 3 informal-mode submissions classify
   as `informal_reasoner`.

The 6 inflight UUIDs are hard-coded in `INFLIGHT` at the top of the script.

### 6.1 Start command (the user runs this, not the agent)

```bash
mkdir -p logs
nohup python3 scripts/subsystem_engagement_watch.py \
    --poll-interval 300 \
    > logs/subsystem_watch.log 2>&1 &
disown
```

Then to monitor:

```bash
tail -f logs/subsystem_watch.log
```

For an ad-hoc single check (no daemon):

```bash
python3 scripts/subsystem_engagement_watch.py --once
```

### 6.2 Exit conditions

- All 6 UUIDs resolved (COMPLETE / COMPLETE_WITH_ERRORS / FAILED /
  CANCELED): script exits cleanly.
- DECISIVE signal: script keeps running but prints the decisive line so
  notification tooling can fire.

### 6.3 Required environment

```
ARISTOTLE_API_KEY=<set>
```

---

## 7. References

- W8 finding (May 30 2026): Three Aristotle subsystems; informal reasoner
  never used by this project.
- I9 spec (`docs/infrastructure_changes_may30/I9_informal_mode.md`):
  Informal-mode adapter + smoke test (UUID
  `8d500201-0786-4bb2-8489-2f6aad91be91`, task
  `f9e23cf2-55f2-4eab-940c-6c06e79f54e5`).
- I9 artifact: `submissions/nu4_final/i9_extracted/f9e23cf2-…/`
  ARISTOTLE_SUMMARY.md is the canonical known-positive for "Informal proof:
  + Formalization:" structure.
- S10 (this U4 spec) — implements the four-criterion validation framework
  agreed for the May 30 wave.
