# I2 — Schema Unification (May 30 2026)

Agent I2 of 10 in the May 30 2026 infrastructure series.

This change extends `submissions/tracking.db` with five new audit columns to
support the post-bare-gap lanes (closure, fusion, informal) and F1's
"mathematical content vs brute force" axis, and exposes a unified
`submissions_audit` view.

Builds on X2's `migrate_add_closure_axis.py` (which added `closure_axis_json`).
Both migrations are idempotent and additive — no existing data is touched
beyond the documented backfills.

---

## 1. Schema diff

### Before (post-X2)

42 columns. The last column added by prior work was X2's:

```
41 | closure_axis_json | TEXT
```

### After (post-I2)

47 columns. Five new columns appended:

```
42 | lane                       | TEXT
43 | mathematical_content_score | INTEGER
44 | fusion_json                | TEXT
45 | informal_mode_used         | INTEGER
46 | paired_llm                 | TEXT
```

### Column semantics

| Column | Type | Values | Purpose |
|---|---|---|---|
| `lane` | TEXT | `bare` \| `closure` \| `fusion` \| `informal` | Which submission lane was used. Default for prior rows: `bare`. |
| `mathematical_content_score` | INTEGER | 0–10 | F1's axis. 0=pure brute force, 10=deep structural insight. Left NULL when not yet audited. |
| `fusion_json` | TEXT | JSON or NULL | Research-fusion dossier metadata (sources, hypotheses, etc.). |
| `informal_mode_used` | INTEGER | 0 \| 1 | Was Aristotle's informal reasoner invoked? Default 0. |
| `paired_llm` | TEXT | model name or `none` | What LLM produced the strategy: `gpt-5.2-pro`, `codex`, `none`, etc. |

### Lane resolution precedence (in `safe_aristotle_submit.safe_submit`)

1. `--informal-mode` flag set → `lane='informal'` and `informal_mode_used=1`
2. else `--fusion-lane` flag set → `lane='fusion'`
3. else closure-axis companion has `real_closure_candidate=true` → `lane='closure'`
4. else → `lane='bare'` (the historical default)

---

## 2. Migration verification

Migration script: `/Users/patrickkavanagh/math/scripts/migrate_add_lane_columns_may30.py`

### First run (additive)

```
$ python3 scripts/migrate_add_lane_columns_may30.py
OK  added 5 column(s): lane, mathematical_content_score, fusion_json, informal_mode_used, paired_llm
    backfill: lane='bare' on 1166 rows
    backfill: informal_mode_used=0 on 1166 rows
    backfill: paired_llm='none' on 1166 rows
    F1 verdict backfill:
      slot720 score=5  rows=1  [OK]
      slot722 score=3  rows=1  [OK]
      slot736 score=1  rows=0  [MISS (slot not in DB)]
      slot737 score=8  rows=0  [MISS (slot not in DB)]
      slot738 score=3  rows=0  [MISS (slot not in DB)]
      slot739 score=7  rows=0  [MISS (slot not in DB)]
    total rows: 1166
    lane distribution: {'bare': 1166}
    mathematical_content_score set on: 2 rows
OK  view submissions_audit (re)created
```

### Second run (idempotency)

```
$ python3 scripts/migrate_add_lane_columns_may30.py
OK  already-present (idempotent): lane, mathematical_content_score, fusion_json, informal_mode_used, paired_llm
    backfill: lane='bare' on 0 rows
    backfill: informal_mode_used=0 on 0 rows
    backfill: paired_llm='none' on 0 rows
    ...
    F1 verdict backfill:
      slot720 score=5  rows=0  [MISS (slot not in DB)]
      ...
OK  view submissions_audit (re)created
```

Second run: zero rows updated, no schema change. Idempotent confirmed.

The F1 backfill uses `WHERE filename LIKE 'slot{N}_%' AND mathematical_content_score IS NULL`, so re-runs are also a no-op for already-scored rows.

The view uses `DROP VIEW IF EXISTS submissions_audit; CREATE VIEW ...` so it stays in sync if column lists evolve.

---

## 3. Backfill audit results

### Default backfill (pre-lane era)

| Column | Value | Rows updated |
|---|---|---|
| `lane` | `'bare'` | 1166 / 1166 |
| `informal_mode_used` | `0` | 1166 / 1166 |
| `paired_llm` | `'none'` | 1166 / 1166 |
| `mathematical_content_score` | (left NULL) | 0 (deferred to I3) |
| `fusion_json` | (left NULL) | 0 (no fusion before May 30) |

Rationale: every submission before this migration was bare-gap mode by hard rule (see `CLAUDE.md` §"Sketch Format"). Backfilling `lane='bare'` is factually correct, not a guess.

### F1 verdict backfill

| Slot | F1 score | Verdict label | DB rows updated |
|---|---|---|---|
| 720 | 5 | structural mild | 1 |
| 722 | 3 | compute+glue | 1 |
| 736 | 1 | pure compute, regression | 0 (slot not in DB) |
| 737 | 8 | genuine structural | 0 (slot not in DB) |
| 738 | 3 | compute+glue | 0 (slot not in DB) |
| 739 | 7 | real algebra | 0 (slot not in DB) |

**Slots 736–739 are not yet present in `submissions/tracking.db`.** The migration intentionally tolerates this: the `UPDATE ... WHERE filename LIKE 'slot{N}_%'` will be a no-op when the slot doesn't exist, and the script reports `MISS (slot not in DB)` for each. When those slots are added by a future submission or fetch, re-running the migration will safely backfill their scores (the `AND mathematical_content_score IS NULL` clause keeps the operation idempotent — it will not overwrite scores already set).

Post-backfill rows with `mathematical_content_score` set: **2** (slot720, slot722).

---

## 4. SQL view: `submissions_audit`

A unified read-only view exposing every audit axis on `submissions` in a stable column order. Created by the migration as `CREATE VIEW IF NOT EXISTS submissions_audit ...`.

### View columns

```
id, uuid, filename, problem_id,
status, status_legacy, submitted_at, completed_at,
lane, informal_mode_used, paired_llm,
mathematical_content_score, fusion_json, closure_axis_json,
target_resolved, axiomatizes_prior_work, axiom_count,
contribution_statement, novelty_level, experiment_arm,
sketch_model_primary, sketch_model_secondary,
cost_usd
```

### Example queries

**Q1. F1 score distribution across compiled advances:**

```sql
SELECT id, filename, status, mathematical_content_score AS mcs
FROM submissions_audit
WHERE status = 'compiled_advance'
ORDER BY mcs DESC NULLS LAST;
```

Output (current state):

```
id    filename                           status            mcs
----  ---------------------------------  ----------------  ---
1255  slot720_feit_thompson_p3q71_close  compiled_advance  5
1254  slot722_brocard_bounded_n2_50      compiled_advance  3
```

**Q2. Lane breakdown:**

```sql
SELECT lane, COUNT(*) AS n FROM submissions_audit GROUP BY lane ORDER BY n DESC;
```

**Q3. Pair-LLM productivity (which strategy LLMs produce real-math advances?):**

```sql
SELECT paired_llm,
       COUNT(*) AS total,
       AVG(mathematical_content_score) AS avg_mcs,
       SUM(CASE WHEN target_resolved = 1 THEN 1 ELSE 0 END) AS resolutions
FROM submissions_audit
GROUP BY paired_llm
ORDER BY avg_mcs DESC NULLS LAST;
```

**Q4. Closure-lane real-math rate:**

```sql
SELECT lane,
       COUNT(*) AS n,
       AVG(mathematical_content_score) AS avg_mcs
FROM submissions_audit
WHERE mathematical_content_score IS NOT NULL
GROUP BY lane;
```

**Q5. Find advances that are pure brute force (regression candidates):**

```sql
SELECT id, filename, paired_llm, mathematical_content_score
FROM submissions_audit
WHERE status = 'compiled_advance'
  AND mathematical_content_score IS NOT NULL
  AND mathematical_content_score <= 2
ORDER BY submitted_at DESC;
```

---

## 5. Submission-time write path

`scripts/safe_aristotle_submit.py` was updated to persist the new columns on every successful submission.

New CLI flags:

```
--fusion-lane        Tag this submission as research-fusion lane (DB.lane='fusion').
--informal-mode      Tag as Aristotle informal-reasoner lane (DB.lane='informal',
                     DB.informal_mode_used=1).
--paired-llm <name>  Record the strategy LLM (e.g. 'gpt-5.2-pro', 'codex').
                     Stored on DB.paired_llm. Defaults to 'none'.
```

Implementation:

- `safe_submit()` accepts `fusion_lane: bool`, `informal_mode: bool`, `paired_llm: str | None`.
- After the existing `_record_closure_axis()` upsert, a new `_record_lane_metadata()` helper writes `lane`, `informal_mode_used`, `paired_llm`, and `fusion_json` to the submissions row keyed by `uuid`.
- Both upserts silently no-op if the migration has not been applied (column-existence check via `PRAGMA table_info`).
- DB write failures are caught and logged via `log_transaction("LANE_METADATA_DB_WRITE_FAILED", ...)`; they never block the submission record itself.

---

## 6. Rollback procedure

SQLite does not support `DROP COLUMN` before 3.35.0, and not all of our deployed SQLite versions are guaranteed to support it. The safe rollback is the standard "rebuild table" pattern:

```bash
# 0. Backup
cp submissions/tracking.db submissions/tracking.db.bak.$(date +%Y%m%d_%H%M%S)

# 1. Drop the view (safe at any version)
sqlite3 submissions/tracking.db "DROP VIEW IF EXISTS submissions_audit;"

# 2a. If sqlite3 >= 3.35.0: native column drop
sqlite3 submissions/tracking.db <<'SQL'
ALTER TABLE submissions DROP COLUMN lane;
ALTER TABLE submissions DROP COLUMN mathematical_content_score;
ALTER TABLE submissions DROP COLUMN fusion_json;
ALTER TABLE submissions DROP COLUMN informal_mode_used;
ALTER TABLE submissions DROP COLUMN paired_llm;
SQL

# 2b. Otherwise: classic rebuild
# (see https://www.sqlite.org/lang_altertable.html section 7)
#   - CREATE TABLE submissions_new (...pre-I2 columns...);
#   - INSERT INTO submissions_new SELECT <pre-I2 cols> FROM submissions;
#   - DROP TABLE submissions; ALTER TABLE submissions_new RENAME TO submissions;
#   - Re-create indexes.
```

**Note.** Rollback is only needed if downstream consumers are demonstrably broken by the new columns. The columns are nullable / additive and existing readers should be unaffected; in particular, `gather_context()`'s `PRAGMA table_info` based feature-detection (already used for `verified`) is the recommended pattern for consumers that need to handle both pre- and post-migration schemas.

To rollback only the write path (without touching the schema):

```bash
git revert <I2 commit hash>
```

The data backfilled (lane='bare', etc.) is factually correct for the pre-lane era and is safe to leave in place even after a code rollback.

---

## 7. Files changed

- **New.** `/Users/patrickkavanagh/math/scripts/migrate_add_lane_columns_may30.py`
- **Modified.** `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py`
  - Added `_record_lane_metadata()` helper
  - Extended `safe_submit()` and `submit_with_retry()` signatures with `fusion_lane`, `informal_mode`, `paired_llm`
  - Added `--fusion-lane`, `--informal-mode`, `--paired-llm <name>` CLI flags
  - Lane resolution precedence implemented inline in `safe_submit()`
- **New.** `/Users/patrickkavanagh/math/docs/infrastructure_changes_may30/I2_schema_unification.md` (this file)
- **DB.** `submissions/tracking.db`: 5 columns added, 1166 rows backfilled with defaults, 2 rows backfilled with F1 scores, view `submissions_audit` created.
