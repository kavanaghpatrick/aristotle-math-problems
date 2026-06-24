# I1: Silently-broken auto-context query — root cause and fix

**Date:** 2026-05-30
**Agent:** I1 (of 10)
**Source audit:** F2 (smoking gun)
**File:** `scripts/safe_aristotle_submit.py`
**Function:** `gather_context()`

---

## The bug

`gather_context()` is the function responsible for finding prior Aristotle
result files for a given `problem_id` so they can be auto-attached as
context to a new submission. The pre-fix implementation (lines 526-534)
ran this SQL:

```sql
SELECT output_file FROM submissions
WHERE (problem_id LIKE ? OR filename LIKE ?)
  AND output_file IS NOT NULL
  AND status IN ('compiled_clean', 'near_miss', 'completed')
ORDER BY submitted_at DESC
```

**None of those three status values exist in the current schema.**

Current `DISTINCT status` values in `submissions/tracking.db`:

```
compile_failed
compiled_no_advance
compiled_partial
submitted
disproven
compiled_advance
```

The intersection of `{compiled_clean, near_miss, completed}` with the
actual enum is the empty set. The query returned **0 rows on every call,
for every problem_id, regardless of how many prior `_result.lean` files
existed.**

### Blast radius

Out of 1166 submissions in the DB:

| Filter | Rows |
|---|---|
| Pre-fix filter (`compiled_clean / near_miss / completed`) | **0** |
| New filter (`output_file IS NOT NULL AND status != compile_failed AND verified != 0`) | **123** |
| Rows with any `output_file` populated | 326 |

Submissions made AFTER >=1 prior artifact existed but received empty
auto-context: **407 out of 410**. Every one of these submissions saw
`Auto-context: 0 prior result(s)` regardless of what had been completed
earlier.

---

## The fix

### Diff summary

The patch replaces the brittle status-enum filter with an artifact-based
filter, adds a canary warning when 0 artifacts are attached despite >0
prior submissions existing, and threads a `--verbose-context` flag from
the CLI down to the function for diagnostic output.

Key changes (full diff in git):

1. **Query rewrite** (lines 555-575). The query now gates on
   `output_file IS NOT NULL AND output_file != ''` and excludes only
   `compile_failed` (which by definition has no artifact). When the
   `verified` column exists, rows with `verified=0` (audit-marked
   invalid) are excluded; rows with `verified=NULL` (pending audit)
   and `verified=1` (audit-clean) are kept.

2. **Canary warning** (lines 577-597). If the query returns 0 rows but
   the DB contains >0 rows matching the problem_id by any status, a
   warning is printed to stdout: `0 artifacts attached for '<pid>'
   despite N prior submission(s)`. This catches future schema drift
   the way the pre-fix bug should have been caught.

3. **Missing-file warning** (lines 619-631). Rows whose `output_file`
   path no longer exists on disk (common because old paths point to
   `~/Downloads/`) are skipped with a counted warning instead of being
   silently dropped.

4. **`verbose` parameter** added to `gather_context()`; when True,
   per-row attach/skip diagnostics print to stdout including row id,
   status, verified flag, and resolved path.

5. **`--verbose-context` CLI flag** added to `safe_aristotle_submit.py`
   (threaded through `safe_submit()` and `submit_with_retry()` and
   into the auto-context block at line 678).

### Why "artifact present" beats "status enum"

The status enum has changed at least twice already (the
`compiled_clean -> compiled_advance` rename and the `near_miss` ->
`compiled_partial` rename appear to be the lost migrations behind the
F2 finding). Future renames or additions will break a hard-coded
filter the same way. `output_file IS NOT NULL` is a behavior-level
signal — if there's an artifact, there's something to attach — and
it doesn't shift when the audit taxonomy is renamed.

---

## Tests

Location: `/Users/patrickkavanagh/math/tests/test_gather_context.py`

10 tests, all passing (`pytest tests/test_gather_context.py -v` —
0.05s):

1. `test_problem_with_three_prior_advances_returns_three_files` —
   the happy path requested by the spec; three mixed-status (advance,
   partial, disproven) rows all attach, ordered most-recent-first.
2. `test_problem_with_no_prior_returns_empty` — empty DB.
3. `test_problem_with_only_partial_advances` — the core regression
   test; `compiled_partial`-only rows must attach (pre-fix bug
   dropped them).
4. `test_compile_failed_rows_excluded` — `compile_failed` rows never
   attach even if `output_file` happens to be set.
5. `test_verified_zero_excluded` — audit-rejected rows (`verified=0`)
   excluded; NULL/1 kept.
6. `test_missing_files_on_disk_skipped` — DB rows whose paths no
   longer exist on disk are dropped with a warning.
7. `test_warning_when_zero_artifacts_but_prior_submissions_exist` —
   the canary fires when prior submissions exist but none are
   attachable.
8. `test_missing_db_returns_empty` — no tracking.db -> empty list,
   no exception.
9. `test_filename_match_works` — match fires on `filename LIKE`
   when `problem_id` is NULL.
10. `test_verbose_prints_per_row_diagnostics` — verbose=True
    produces per-row `+attach`/`-skip` lines.

Test isolation: each test gets a synthetic `tracking.db` under
`tmp_path` and monkey-patches `MATH_DIR` on the imported module.
The fake `aristotlelib` from `conftest.py::mock_aristotlelib_module`
lets the script import without the real SDK.

---

## Backfill audit

Run by the patched function against the live `submissions/tracking.db`
on 2026-05-30:

| problem_id | Files attached now | Total prior submissions | Subs that lost context (post-first-artifact) |
|---|---:|---:|---:|
| `erdos_647` | 0* | 12 | 0 |
| `erdos_672` | 0 | 0 | 0 |
| `erdos672` (alt spelling) | 2 | 4 | 3 |
| `brocard` | 2 | 2 | 1 |
| `feit_thompson` | **9** | 14 | **11** |
| `leinster` | 0** | 15 | 10 |
| `tuza_nu4` | **4** | 353 | **69** |

\* `erdos_647`'s single artifact path points to `~/Downloads/...`
which is gone from disk. New code reports
`2 prior result file(s) referenced in DB but missing on disk` and
attaches 0.

\*\* `leinster` has 9 rows with `output_file` populated but ALL nine
were audited `verified=0` — the new filter correctly drops them.
Canary fires: `0 artifacts attached for 'leinster' despite 15 prior
submission(s)`.

**Total submissions that silently lost context: 94 across these 7
problems alone.** The 11 feit_thompson submissions post-first-artifact
would have benefitted most — those slots span the slot559..slot720
sequence and include the eventual `slot720_iter2_ft_family_result.lean`
(status `compiled_advance, verified=1`), so each of the 10
post-slot720 submissions targeting feit_thompson got no signal that
an `advance` already existed. tuza_nu4 lost 69 submissions' worth of
context, though the cycle-attack family of priors that should have
been attached lives under `submissions/nu4_final/` and is largely
intact on disk; about 30 older paths point to deleted `~/Downloads`
files which the warning now surfaces.

### Top problems by attachable-artifact count (post-fix)

```
tuza_nu4         : 29 priors
feit_thompson    :  9 priors
(problem_id NULL):  8 priors
sierpinski_5n    :  7 priors
erdos850         :  7 priors
```

These are the problems whose next submission will see the biggest
boost from the fix.

---

## Rollback procedure

If the new filter is too liberal (e.g., starts attaching huge tar
bundles that exceed the Aristotle prompt budget):

1. `cd /Users/patrickkavanagh/math`
2. `git log scripts/safe_aristotle_submit.py` — find the I1 commit.
3. `git revert <commit-sha>` — produces a clean revert commit.
4. The tests in `tests/test_gather_context.py` will fail on the
   reverted code; either delete them or mark them xfail with a
   comment pointing back to this doc.

Quick guard if you only want to dial back without a full revert:
in `gather_context()` re-add a status whitelist as an additional
clause AFTER the `output_file IS NOT NULL` gate, e.g.

```python
" AND status IN ('compiled_advance','compiled_partial','disproven') "
```

— but be aware that this restores the schema-drift fragility that
caused the original bug. If you do this, update the canary warning
threshold so the regression surfaces immediately.

---

## File index

- **Patched script:** `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py`
- **Tests:** `/Users/patrickkavanagh/math/tests/test_gather_context.py`
- **This doc:** `/Users/patrickkavanagh/math/docs/infrastructure_changes_may30/I1_gather_context_fix.md`
