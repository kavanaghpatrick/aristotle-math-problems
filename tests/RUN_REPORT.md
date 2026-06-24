# Test Sweep Report — aristotlelib 2.0 Upgrade

**Date:** 2026-05-27
**Runner:** integration-runner (team `aristotle-upgrade-tests`)
**Working dir:** `/Users/patrickkavanagh/math/`
**Python:** 3.11.14 / pytest 9.0.1 / asyncio mode AUTO
**aristotlelib:** 2.0.0 (verified via `aristotle --version`)

---

## TL;DR

**92 / 92 tests passing. Zero failures, zero flakes. Suite revealed no bugs in the patched scripts.**

| Suite | Command | Result |
|---|---|---|
| Unit + integration scaffold (non-live) | `pytest tests/ -v --tb=short -m 'not live'` | **85 passed**, 7 deselected, 0.26s |
| Live API + CLI | `pytest tests/ -v --tb=short -m live` | **7 passed**, 85 deselected, 3.34s |

---

## Per-file breakdown

| File | Tests run | Passed | Failed |
|---|---:|---:|---:|
| `tests/test_aristotle_fetch.py` | 33 | 33 | 0 |
| `tests/test_aristotle_queue_monitor.py` | 38 | 38 | 0 |
| `tests/test_submit_capacity.py` | 14 | 14 | 0 |
| `tests/test_live_api.py` | 7 | 7 | 0 |
| **Total** | **92** | **92** | **0** |

The default `addopts = "-m 'not live'"` in `pyproject.toml` deselects the 7 live tests on a normal `pytest` run — they only execute under `-m live` and skip cleanly when `ARISTOTLE_API_KEY` is unset (verified by re-running with the env var cleared: 7 skipped, 0 failed).

---

## Failures

**None.**

---

## Flaky behavior

**None observed.** The non-live suite is purely mock-driven and deterministic. The live suite ran cleanly on the first attempt — no retry was needed.

The two CLI subprocess tests (`test_cli_version_is_2_0_0`, `test_cli_list_runs`) have generous timeouts (30s and 60s respectively) and a network-touching test sequence (`list_projects` → `from_id` → `get_tasks`) completed in under 4 seconds total. No transient errors.

---

## Bugs revealed in patched scripts

**None.**

The 85 non-live tests exercise the patched call sites in `scripts/aristotle_fetch.py`, `scripts/aristotle_queue.py`, `scripts/aristotle_monitor.py`, `scripts/safe_aristotle_submit.py`, and `scripts/submit_parker_batch.py` — covering the call shapes the 2.0 SDK requires (tuple-unpacking from `list_projects` / `get_tasks`, `ProjectStatus.RUNNING` server-side filter, `TaskStatus`-based completion bucketing, `get_files(destination=...)` keyword arg, `Project.create(prompt=...)` for submissions, capacity-check arithmetic, 429/rate-limit branches). All call-site assumptions hold on the live SDK as well — the 7 live tests confirm enum members, the 2-tuple return shape, the status filter, the `from_id` → `get_tasks` round-trip, and the CLI surface that the scripts shell out to.

If any patched script had a real-world regression (wrong attribute name, missed enum rename, broken positional/keyword arg), one of these tests would have caught it. They didn't.

---

## Live test note

`test_project_from_id_and_get_tasks` calls `Project.from_id(projects[0].project_id)` on the first project returned by an unfiltered `list_projects(limit=1)`. This worked cleanly with the current `ARISTOTLE_API_KEY` (the key's account has visibility into the project it tried). The previously-observed 403 issue (key can list projects but `from_id` 403s on older slot UUIDs created by a prior key) does NOT trip this test because the test only round-trips a project ID that `list_projects` just returned — which is by definition a project the current key can see. No fixture or test change needed.

---

## Reproduce

```bash
cd /Users/patrickkavanagh/math/
pytest tests/ -v --tb=short -m 'not live'   # 85 passed
pytest tests/ -v --tb=short -m live         # 7 passed (with ARISTOTLE_API_KEY)
```

Default `pytest tests/ -v` runs 85 non-live tests and deselects 7 live ones; useful for CI without API access.
