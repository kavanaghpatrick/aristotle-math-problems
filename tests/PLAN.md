# tests/PLAN.md — aristotlelib 2.0 upgrade test plan

## Context
Upgraded `aristotlelib` 0.7.0 → 2.0.0. Tests verify the patched scripts work with the new SDK without hitting the live API.

**Real 2.0 enum values (verified by import):**
- `ProjectStatus`: `UNKNOWN, RUNNING, IDLE`
- `TaskStatus`: `UNKNOWN, QUEUED, IN_PROGRESS, COMPLETE, COMPLETE_WITH_ERRORS, OUT_OF_BUDGET, FAILED, CANCELED`

**Patched scripts under test:**
- `scripts/aristotle_fetch.py`
- `scripts/aristotle_queue.py`
- `scripts/aristotle_monitor.py`
- `scripts/safe_aristotle_submit.py`
- `scripts/submit_parker_batch.py`

**Test isolation:** every unit test injects a fake `aristotlelib` module into `sys.modules` via the `mock_aristotlelib_module` fixture BEFORE the script is imported, since scripts do `from aristotlelib import Project, TaskStatus`. Use `importlib.import_module` / `importlib.reload` to ensure fresh import per test.

---

## tests/test_aristotle_fetch.py (owner: unit-fetch)

Target: `scripts/aristotle_fetch.py`. Focus on the new SDK consumption: `Project.from_id`, `Project.get_tasks(limit=1)`, `Project.get_files(destination=...)`, `Project.ask(prompt)`.

### `check_status(uuid)` — coroutine
- `test_check_status_returns_task_status_when_task_exists` — make a fake project whose `get_tasks(limit=1)` returns `[task(COMPLETE, percent=100, file_name="foo.lean")]`; assert returned dict has `status="COMPLETE"`, `percent=100`, `file_name="foo.lean"`, `error is None`.
- `test_check_status_returns_UNKNOWN_when_no_tasks` — `get_tasks` returns `([], None)`; assert `status == "UNKNOWN"`, `percent is None`, `file_name == "unknown"`.
- `test_check_status_returns_ERROR_on_exception` — `Project.from_id` raises `RuntimeError("boom")`; assert `status == "ERROR"`, `error == "boom"`.
- `test_check_status_uses_get_tasks_limit_1` — record kwargs passed to `get_tasks` and assert `limit=1`.
- `test_check_status_returns_in_progress_with_percent` — task with `IN_PROGRESS, percent=42`; assert `status="IN_PROGRESS"`, `percent==42`.
- `test_check_status_handles_complete_with_errors` — task with `COMPLETE_WITH_ERRORS`; assert that exact name returned.

### `fetch_result(uuid, output_path)` — coroutine
- `test_fetch_result_downloads_on_COMPLETE` — task COMPLETE; assert `get_files(destination=str(output_path))` called, returns Path.
- `test_fetch_result_downloads_on_COMPLETE_WITH_ERRORS` — same but task COMPLETE_WITH_ERRORS; assert download still happens.
- `test_fetch_result_returns_None_when_not_complete` — task IN_PROGRESS; assert `get_files` NOT called and return is `None`.
- `test_fetch_result_returns_None_on_no_tasks` — empty task list; assert `None`, no download.
- `test_fetch_result_returns_None_on_QUEUED` — task QUEUED; assert `None`.
- `test_fetch_result_returns_None_on_FAILED` — task FAILED; assert `None`.
- `test_fetch_result_returns_None_on_OUT_OF_BUDGET` — assert `None`.
- `test_fetch_result_returns_None_on_exception` — `from_id` raises; assert `None`.
- `test_fetch_result_uses_destination_kwarg` — assert `get_files` called with `destination=` keyword (not positional).
- `test_fetch_result_returns_path_from_get_files` — `get_files` returns `"/tmp/x.lean"`; assert return is `Path("/tmp/x.lean")`.
- `test_fetch_result_falls_back_to_output_path` — `get_files` returns falsy; assert return is `output_path`.

### `cmd_ask(target, prompt)` — coroutine (new in 2.0)
- `test_cmd_ask_resolves_uuid_directly` — target is a UUID-like string (contains `-`); assert `Project.from_id` called with that uuid, `project.ask(prompt)` called.
- `test_cmd_ask_resolves_slot_via_id_files` — monkeypatch `load_slot_ids` to return `{692: {"uuid": "abc-uuid"}}`; target `"692"`; assert `from_id("abc-uuid")` called.
- `test_cmd_ask_handles_missing_slot` — monkeypatch `load_slot_ids` to `{}`; target `"999"`; assert returns early (no `from_id` call), prints "not found".
- `test_cmd_ask_rejects_non_uuid_non_int` — target `"banana"`; asserts prints error and returns without calling `from_id`.
- `test_cmd_ask_appends_to_slot_id_file` — target `"692"`; existing ID file in tmp dir; after call, file contains `# Follow-up task <id>` line.
- `test_cmd_ask_returned_task_status_and_id_printed` — `ask` returns task with `agent_task_id="t1"`, `status=COMPLETE`; assert both surfaced (capsys).

### Other (non-API)
- `test_audit_file_compiled_clean` — text with no `sorry`/axiom/negation → verdict `"compiled_clean"`.
- `test_audit_file_near_miss_one_sorry` — text with single `sorry` → verdict `"near_miss"`, `sorry==1`.
- `test_audit_file_disproven_on_negation` — text contains "The following was negated by Aristotle" → verdict `"disproven"`.
- `test_audit_file_failed_on_load_error_with_sorry` — text contains "Aristotle failed to load" and a `sorry` → verdict `"failed"`.
- `test_audit_file_ignores_sorry_in_comments` — `-- sorry` and `/- sorry -/` not counted.
- `test_load_slot_ids_parses_id_files` — write a fake `slot42_ID.txt` in tmp dir; monkeypatch `RESULTS_DIR`; assert returned dict has `uuid`, `task`, `submitted`.

---

## tests/test_aristotle_queue_monitor.py (owner: unit-queue)

Targets: `scripts/aristotle_queue.py` and `scripts/aristotle_monitor.py`.

### aristotle_queue: `get_queued_files()` — coroutine
- `test_get_queued_files_uses_RUNNING_server_filter` — mock `Project.list_projects`; assert called with `status=ProjectStatus.RUNNING` and `limit=20`.
- `test_get_queued_files_collects_basenames_from_tasks` — two RUNNING projects, each with one task whose `file_name="dir/foo.lean"` and `bar.lean`; assert return `{"foo.lean", "bar.lean"}`.
- `test_get_queued_files_skips_projects_with_no_tasks` — project with empty task list; assert not included.
- `test_get_queued_files_skips_tasks_with_no_file_name` — task `file_name=None`; assert not included.
- `test_get_queued_files_returns_empty_set_on_exception` — `list_projects` raises; assert `set()` returned (with warning log).
- `test_get_queued_files_per_project_get_tasks_limit_1` — assert `get_tasks(limit=1)` called once per project.

### aristotle_queue: `get_queue_status()` — coroutine
- `test_get_queue_status_buckets_by_task_status` — projects: one with task `IN_PROGRESS`, one with task `COMPLETE`, one with no tasks (project status `IDLE`); assert dict keys are `{"IN_PROGRESS", "COMPLETE", "IDLE"}`.
- `test_get_queue_status_includes_id_file_desc_created` — each project entry has `id`, `file`, `desc`, `created`.
- `test_get_queue_status_falls_back_to_project_desc` — task has `description=None`; assert entry's `desc` falls back to `project.description`.
- `test_get_queue_status_returns_error_dict_on_exception` — `list_projects` raises; assert `{"ERROR": [{"desc": ...}]}`.
- `test_get_queue_status_does_not_filter_projects` — confirm called WITHOUT `status=` filter (`limit=20`).

### aristotle_queue: `submit_file(filepath)` — sync function calling `asyncio.run(Project.create(...))`
- `test_submit_file_calls_Project_create_with_prompt` — write a temp `foo.txt` with content `"hello"`; set `ARISTOTLE_API_KEY` env; mock `Project.create` returning a project with `project_id="pid1"`; assert `(True, "Submitted! Project ID: pid1", "pid1")` and that `Project.create` was awaited with `prompt="hello"`.
- `test_submit_file_no_api_key_returns_false` — unset env; assert `(False, "ARISTOTLE_API_KEY not set", None)`.
- `test_submit_file_429_returns_queue_full` — `Project.create` raises with "429"; assert `(False, "Queue full (5/5)", None)`.
- `test_submit_file_too_many_requests_returns_queue_full` — exception message contains "Too Many Requests".
- `test_submit_file_already_have_5_returns_queue_full` — exception contains "already have 5 projects".
- `test_submit_file_other_exception_returns_failure_message` — generic exception; assert message starts with `"Exception:"`.
- `test_submit_file_no_longer_uses_subprocess` — patch `subprocess.run` to raise if called; ensure it isn't.

### aristotle_monitor: `get_all_projects()` — coroutine
- `test_get_all_projects_unpacks_tuple` — `list_projects` returns `([p1, p2], "pkey")`; assert function returns `[p1, p2]` (list, not the tuple, not including the pagination key).
- `test_get_all_projects_returns_empty_list_on_exception` — `list_projects` raises; assert `[]`.
- `test_get_all_projects_calls_list_projects_with_limit_50` — assert called with `limit=50`.

### aristotle_monitor: `download_output(project_id)` — coroutine
- `test_download_output_uses_get_files_with_destination` — mock project; assert `project.get_files(destination=expected_path)` called; ensure returned path matches.
- `test_download_output_returns_None_when_file_missing` — `get_files` invoked, but file doesn't exist on disk; assert `None`.
- `test_download_output_returns_path_when_exists` — touch the destination path so `Path.exists()` is True; assert returned string equals output path.
- `test_download_output_returns_None_on_exception` — `from_id` raises; assert `None`.
- `test_download_output_creates_output_dir` — output_dir is a non-existent path; after call assert it exists (tmp_path).

### aristotle_monitor: `check_completions()` — coroutine
- `test_check_completions_uses_task_status_not_project_status` — give one project with task `COMPLETE`; project's own status is `IDLE`; ensure it's treated as completed (download triggered).
- `test_check_completions_accepts_COMPLETE_WITH_ERRORS` — task `COMPLETE_WITH_ERRORS`; assert it's processed.
- `test_check_completions_accepts_FAILED_OUT_OF_BUDGET_CANCELED` — parametrize over those three; assert each triggers download + analysis.
- `test_check_completions_skips_IN_PROGRESS` — task IN_PROGRESS; assert no download.
- `test_check_completions_skips_QUEUED` — task QUEUED; assert no download.
- `test_check_completions_skips_already_analyzed` — pid already in `analysis_log`; assert no second download.
- `test_check_completions_handles_project_with_no_tasks_as_UNKNOWN` — empty task list; status string "UNKNOWN"; not in the completion-trigger set; assert skipped.
- `test_check_completions_persists_analysis_and_submissions` — verify both JSON logs written via `save_json` mock.

---

## tests/test_submit_capacity.py (owner: unit-submit)

Targets: `scripts/safe_aristotle_submit.py` and `scripts/submit_parker_batch.py`.

### safe_aristotle_submit: `check_rate_limit_and_capacity()` — coroutine
- `test_capacity_uses_RUNNING_server_filter` — assert `list_projects` called with `status=ProjectStatus.RUNNING, limit=20` for the first call.
- `test_capacity_in_progress_counts_filtered_projects` — RUNNING list returns 3 projects; assert `in_progress == 3`.
- `test_capacity_slots_available_is_5_minus_in_progress` — in_progress=2; assert `slots_available == 3`, `has_capacity is True`.
- `test_capacity_no_capacity_when_in_progress_geq_5` — in_progress=5; assert `has_capacity is False`, `slots_available == 0`.
- `test_capacity_no_capacity_when_in_progress_exceeds_5` — in_progress=6 (sanity); `slots_available == 0`, `has_capacity is False`.
- `test_capacity_recent_count_uses_unfiltered_call` — second `list_projects` call (no status filter) returns mix; recent_count reflects time window cutoff.
- `test_capacity_recent_count_excludes_old` — projects with `created_at` >11 minutes ago not counted.
- `test_capacity_recent_count_handles_Z_timezone_suffix` — `created_at` strings end with `Z`; assert parser doesn't crash and counts correctly.

### safe_aristotle_submit: `check_gap_targeting(input_file)` — sync
- `test_gap_targeting_rejects_lean_suffix` — `foo.lean`; raises `GapTargetingError` mentioning "INFORMAL (.txt)".
- `test_gap_targeting_rejects_empty_file` — empty `.txt`; raises with "empty".
- `test_gap_targeting_rejects_over_30_lines` — 31 non-blank lines; raises with line count.
- `test_gap_targeting_rejects_proof_strategy_keyword` — contains `"## Proof Strategy"`; raises with "proof guidance".
- `test_gap_targeting_rejects_approach_n_keyword` — contains `"APPROACH 1"`; raises.
- `test_gap_targeting_rejects_too_many_lean_lines` — 6 lines containing `theorem `; raises with "Lean code".
- `test_gap_targeting_passes_minimal_sketch` — valid 5-line OPEN GAP sketch; returns `{"pass": True, "submission_type": "gap_targeting", ...}`.
- `test_gap_targeting_falsification_skips_strategy_check` — contains "falsify" + "## Proof Strategy" (would normally fail strategy); returns `submission_type == "falsification"`.
- `test_gap_targeting_extracts_first_nonblank_as_gap_statement` — first meaningful line surfaced.

### safe_aristotle_submit: `safe_submit(...)` — coroutine (high-level, mock-heavy)
- `test_safe_submit_uses_Project_create_not_subprocess` — mock `Project.create` returning project; assert it's awaited and that no `subprocess.run` is invoked.
- `test_safe_submit_passes_tar_when_context_files_present` — supply a context file; assert `Project.create` called with `tar_file_path` set to a `Path`; assert tar is cleaned up after.
- `test_safe_submit_passes_None_tar_when_no_context` — no context files; assert `tar_file_path=None`.
- `test_safe_submit_writes_project_id_file_immediately` — assert ID file written with `project_id`, hash, timestamp.
- `test_safe_submit_logs_transaction_pre_and_post` — assert `pre_submit` + `submitted` entries appended.
- `test_safe_submit_releases_lock_on_failure` — `Project.create` raises; assert lockfile removed.
- `test_safe_submit_force_skips_gap_gate_and_lock` — `force=True` with a .lean file; assert no `GapTargetingError`, no lock acquired.
- `test_safe_submit_batch_skips_capacity_check` — `batch=True`; assert `check_rate_limit_and_capacity` NOT called.

### submit_parker_batch: `check_queue()` — coroutine
- `test_parker_check_queue_uses_RUNNING_filter` — assert `list_projects` called with `status=ProjectStatus.RUNNING, limit=20`.
- `test_parker_check_queue_returns_count_and_available` — 2 RUNNING projects; assert `(2, 3)`.
- `test_parker_check_queue_returns_zero_available_when_full` — 5 RUNNING; assert `(5, 0)`.

### submit_parker_batch: `submit_file(info)` — coroutine
- `test_parker_submit_uses_Project_create_with_prompt` — mock `Project.create`; assert called with `prompt=<file contents>`.
- `test_parker_submit_returns_project_id_on_success` — returns `project_id` string.
- `test_parker_submit_returns_None_on_exception` — `create` raises; returns `None`.
- (DB write side-effect tests are out of scope unless cheap; the integration tests catch this end-to-end.)

---

## tests/test_live_api.py (owner: integration-runner)

Skipped unless `ARISTOTLE_API_KEY` is in env. Marked `@pytest.mark.live`. Goal: smoke-test that the 2.0 SDK calls actually work against the real service in a non-destructive way.

- `test_live_list_projects_returns_tuple` — calls `Project.list_projects(limit=1)`; asserts shape `(list, pagination_key_or_None)`.
- `test_live_list_projects_RUNNING_filter_works` — `Project.list_projects(limit=5, status=ProjectStatus.RUNNING)` does not error.
- `test_live_check_status_known_uuid` — read `submissions/nu4_final/slot*_ID.txt`, grab first uuid; call `check_status` (from aristotle_fetch); assert returned dict has expected keys.
- `test_live_get_tasks_on_real_project` — for first known uuid, call `Project.from_id` then `get_tasks(limit=1)`; assert task has `.status` attribute of type `TaskStatus`.

All live tests use `pytestmark = pytest.mark.live` at file top + a session-scoped skip-if-no-key fixture in conftest. Default `pytest` invocation should NOT run them. Run with `pytest -m live` to opt in.

---

## File ownership summary

| File | Owner | Tests |
|---|---|---|
| tests/conftest.py | planner | pytest fixtures + module-injection |
| tests/fixtures.py | planner | importable helpers: `MockTaskStatus`, `MockProjectStatus`, `make_mock_project`, `make_mock_task` |
| tests/PLAN.md | planner | this file |
| tests/test_aristotle_fetch.py | unit-fetch | ~30 tests |
| tests/test_aristotle_queue_monitor.py | unit-queue | ~25 tests |
| tests/test_submit_capacity.py | unit-submit | ~25 tests |
| tests/test_live_api.py | integration-runner | 4 tests, skipped by default |
| pyproject.toml | planner | pytest config + markers |

## Conventions

**Standard test setup pattern (use in every unit test):**
```python
from tests.fixtures import MockTaskStatus, make_mock_project, make_mock_task

async def test_foo(import_patched_script, mock_aristotlelib_module):
    task = make_mock_task(status=MockTaskStatus.COMPLETE, file_name="x.lean")
    project = make_mock_project(tasks=[task])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.check_status("any-uuid")
    assert result["status"] == "COMPLETE"
```

- All async tests run via `asyncio_mode = "auto"` — no `@pytest.mark.asyncio` decorator needed.
- The `mock_aristotlelib_module` fixture installs a fake `aristotlelib` in `sys.modules` AND evicts any previously-imported patched script so the `from aristotlelib import ...` binding refreshes.
- The `import_patched_script` fixture wraps `importlib.import_module` / `importlib.reload` — always import patched scripts through it, never with a bare `import aristotle_fetch` at module top.
- Conftest already adds `<repo>/scripts` to `sys.path`. Writers should not need additional sys.path setup.
- The autouse `_scrub_api_key_unless_live` fixture deletes `ARISTOTLE_API_KEY` for non-live tests. If a unit test needs the env var set (e.g. `submit_file` checks for it), `monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")` inside the test.
- Do NOT depend on the real `submissions/tracking.db` or real `submissions/nu4_final/` slot files; tests must redirect via `monkeypatch.setattr` on module-level constants (e.g. `monkeypatch.setattr(af, "RESULTS_DIR", tmp_path)`).
- `Project.list_projects` on the fake is an `AsyncMock` with default `return_value=([], None)`. Override via `mock_aristotlelib_module.Project.list_projects.return_value = ([project1, project2], None)`.
- `Project.create` and `Project.from_id` are `AsyncMock`s — set `.return_value = ...` or `.side_effect = ...` directly.
- To verify call kwargs use `Project.list_projects.assert_awaited_with(limit=20, status=mock_aristotlelib_module.ProjectStatus.RUNNING)`.
