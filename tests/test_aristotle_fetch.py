"""Unit tests for scripts/aristotle_fetch.py against the aristotlelib 2.0 SDK.

All tests run with a fake `aristotlelib` injected into sys.modules via
`mock_aristotlelib_module` from conftest. The patched script is imported via
`import_patched_script("aristotle_fetch")` so its `from aristotlelib import ...`
binds to the fakes.
"""

from __future__ import annotations

from pathlib import Path
from unittest.mock import AsyncMock

import pytest

from tests.fixtures import (
    MockTaskStatus,
    build_fake_aristotlelib_module,
    make_mock_project,
    make_mock_task,
)


# ===========================================================================
# check_status(uuid)
# ===========================================================================

async def test_check_status_returns_task_status_when_task_exists(
    import_patched_script, mock_aristotlelib_module
):
    task = make_mock_task(
        status=MockTaskStatus.COMPLETE,
        percent_complete=100,
        file_name="foo.lean",
    )
    project = make_mock_project(tasks=[task])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.check_status("any-uuid")

    assert result["status"] == "COMPLETE"
    assert result["percent"] == 100
    assert result["file_name"] == "foo.lean"
    assert result["error"] is None


async def test_check_status_returns_UNKNOWN_when_no_tasks(
    import_patched_script, mock_aristotlelib_module
):
    project = make_mock_project(tasks=[])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.check_status("any-uuid")

    assert result["status"] == "UNKNOWN"
    assert result["percent"] is None
    assert result["file_name"] == "unknown"
    assert result["error"] is None


async def test_check_status_returns_ERROR_on_exception(
    import_patched_script, mock_aristotlelib_module
):
    mock_aristotlelib_module.Project.from_id.side_effect = RuntimeError("boom")

    af = import_patched_script("aristotle_fetch")
    result = await af.check_status("any-uuid")

    assert result["status"] == "ERROR"
    assert result["percent"] is None
    assert result["file_name"] == "unknown"
    assert result["error"] == "boom"


async def test_check_status_uses_get_tasks_limit_1(
    import_patched_script, mock_aristotlelib_module
):
    project = make_mock_project(tasks=[make_mock_task()])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    await af.check_status("any-uuid")

    project.get_tasks.assert_awaited_with(limit=1)


async def test_check_status_returns_in_progress_with_percent(
    import_patched_script, mock_aristotlelib_module
):
    task = make_mock_task(
        status=MockTaskStatus.IN_PROGRESS,
        percent_complete=42,
        file_name="bar.lean",
    )
    project = make_mock_project(tasks=[task])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.check_status("uuid")

    assert result["status"] == "IN_PROGRESS"
    assert result["percent"] == 42


async def test_check_status_handles_complete_with_errors(
    import_patched_script, mock_aristotlelib_module
):
    task = make_mock_task(status=MockTaskStatus.COMPLETE_WITH_ERRORS)
    project = make_mock_project(tasks=[task])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.check_status("uuid")

    assert result["status"] == "COMPLETE_WITH_ERRORS"


# ===========================================================================
# fetch_result(uuid, output_path)
# ===========================================================================

async def test_fetch_result_downloads_on_COMPLETE(
    import_patched_script, mock_aristotlelib_module, tmp_path
):
    out = tmp_path / "result.lean"
    task = make_mock_task(status=MockTaskStatus.COMPLETE)
    project = make_mock_project(tasks=[task])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.fetch_result("uuid", out)

    project.get_files.assert_awaited_with(destination=str(out))
    assert result == Path(str(out))


async def test_fetch_result_downloads_on_COMPLETE_WITH_ERRORS(
    import_patched_script, mock_aristotlelib_module, tmp_path
):
    out = tmp_path / "result.lean"
    task = make_mock_task(status=MockTaskStatus.COMPLETE_WITH_ERRORS)
    project = make_mock_project(tasks=[task])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.fetch_result("uuid", out)

    project.get_files.assert_awaited_with(destination=str(out))
    assert result == Path(str(out))


async def test_fetch_result_returns_None_when_in_progress(
    import_patched_script, mock_aristotlelib_module, tmp_path
):
    out = tmp_path / "result.lean"
    task = make_mock_task(status=MockTaskStatus.IN_PROGRESS)
    project = make_mock_project(tasks=[task])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.fetch_result("uuid", out)

    assert result is None
    project.get_files.assert_not_awaited()


async def test_fetch_result_returns_None_on_no_tasks(
    import_patched_script, mock_aristotlelib_module, tmp_path
):
    out = tmp_path / "result.lean"
    project = make_mock_project(tasks=[])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.fetch_result("uuid", out)

    assert result is None
    project.get_files.assert_not_awaited()


@pytest.mark.parametrize(
    "status",
    [
        MockTaskStatus.QUEUED,
        MockTaskStatus.FAILED,
        MockTaskStatus.OUT_OF_BUDGET,
        MockTaskStatus.CANCELED,
        MockTaskStatus.UNKNOWN,
    ],
)
async def test_fetch_result_returns_None_on_non_complete_states(
    import_patched_script, mock_aristotlelib_module, tmp_path, status
):
    out = tmp_path / "result.lean"
    task = make_mock_task(status=status)
    project = make_mock_project(tasks=[task])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.fetch_result("uuid", out)

    assert result is None
    project.get_files.assert_not_awaited()


async def test_fetch_result_returns_None_on_exception(
    import_patched_script, mock_aristotlelib_module, tmp_path
):
    mock_aristotlelib_module.Project.from_id.side_effect = RuntimeError("network down")

    af = import_patched_script("aristotle_fetch")
    result = await af.fetch_result("uuid", tmp_path / "x.lean")

    assert result is None


async def test_fetch_result_uses_destination_kwarg(
    import_patched_script, mock_aristotlelib_module, tmp_path
):
    out = tmp_path / "deep" / "nested" / "result.lean"
    task = make_mock_task(status=MockTaskStatus.COMPLETE)
    project = make_mock_project(tasks=[task])
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    await af.fetch_result("uuid", out)

    # Must be a keyword call with `destination=`, not positional.
    call_kwargs = project.get_files.await_args.kwargs
    call_args = project.get_files.await_args.args
    assert call_args == ()
    assert call_kwargs == {"destination": str(out)}


async def test_fetch_result_returns_path_from_get_files(
    import_patched_script, mock_aristotlelib_module, tmp_path
):
    out = tmp_path / "result.lean"
    task = make_mock_task(status=MockTaskStatus.COMPLETE)
    project = make_mock_project(tasks=[task])
    project.get_files = AsyncMock(return_value="/tmp/x.lean")
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.fetch_result("uuid", out)

    assert result == Path("/tmp/x.lean")


async def test_fetch_result_falls_back_to_output_path(
    import_patched_script, mock_aristotlelib_module, tmp_path
):
    out = tmp_path / "result.lean"
    task = make_mock_task(status=MockTaskStatus.COMPLETE)
    project = make_mock_project(tasks=[task])
    project.get_files = AsyncMock(return_value=None)
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    result = await af.fetch_result("uuid", out)

    assert result == out


# ===========================================================================
# cmd_ask(target, prompt)
# ===========================================================================

async def test_cmd_ask_resolves_uuid_directly(
    import_patched_script, mock_aristotlelib_module, monkeypatch, capsys
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    project = make_mock_project()
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    await af.cmd_ask("abc-uuid-with-dash", "try harder")

    mock_aristotlelib_module.Project.from_id.assert_awaited_with("abc-uuid-with-dash")
    project.ask.assert_awaited_with("try harder")


async def test_cmd_ask_resolves_slot_via_id_files(
    import_patched_script, mock_aristotlelib_module, monkeypatch, tmp_path
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    project = make_mock_project()
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    # Redirect RESULTS_DIR so the auto-append doesn't touch real files.
    monkeypatch.setattr(af, "RESULTS_DIR", tmp_path)
    monkeypatch.setattr(af, "load_slot_ids", lambda: {692: {"uuid": "abc-uuid"}})

    await af.cmd_ask("692", "retry decomposition")

    mock_aristotlelib_module.Project.from_id.assert_awaited_with("abc-uuid")
    project.ask.assert_awaited_with("retry decomposition")


async def test_cmd_ask_handles_missing_slot(
    import_patched_script, mock_aristotlelib_module, monkeypatch, capsys
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")

    af = import_patched_script("aristotle_fetch")
    monkeypatch.setattr(af, "load_slot_ids", lambda: {})

    await af.cmd_ask("999", "anything")

    mock_aristotlelib_module.Project.from_id.assert_not_awaited()
    out = capsys.readouterr().out
    assert "999" in out and "not found" in out.lower()


async def test_cmd_ask_rejects_non_uuid_non_int(
    import_patched_script, mock_aristotlelib_module, monkeypatch, capsys
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")

    af = import_patched_script("aristotle_fetch")
    await af.cmd_ask("banana", "anything")

    mock_aristotlelib_module.Project.from_id.assert_not_awaited()
    out = capsys.readouterr().out
    assert "banana" in out


async def test_cmd_ask_appends_to_slot_id_file(
    import_patched_script, mock_aristotlelib_module, monkeypatch, tmp_path
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    follow_up_task = make_mock_task(
        status=MockTaskStatus.QUEUED,
        agent_task_id="followup-t1",
        description="retry",
        file_name=None,
    )
    project = make_mock_project()
    project.ask = AsyncMock(return_value=follow_up_task)
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    monkeypatch.setattr(af, "RESULTS_DIR", tmp_path)
    monkeypatch.setattr(af, "load_slot_ids", lambda: {692: {"uuid": "abc-uuid"}})

    # Pre-create the slot ID file so the append step has a target.
    id_file = tmp_path / "slot692_ID.txt"
    id_file.write_text("abc-uuid\n# Task: original task\n# Submitted: 2026-05-27T10:00:00\n")

    await af.cmd_ask("692", "another decomposition please")

    content = id_file.read_text()
    assert "followup-t1" in content
    assert "# Follow-up task" in content
    assert "another decomposition please" in content


async def test_cmd_ask_returned_task_status_and_id_printed(
    import_patched_script, mock_aristotlelib_module, monkeypatch, capsys
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    follow_up_task = make_mock_task(
        status=MockTaskStatus.COMPLETE,
        agent_task_id="t1",
        description="follow-up desc",
        file_name=None,
    )
    project = make_mock_project()
    project.ask = AsyncMock(return_value=follow_up_task)
    mock_aristotlelib_module.Project.from_id.return_value = project

    af = import_patched_script("aristotle_fetch")
    await af.cmd_ask("abc-uuid-with-dash", "retry")

    out = capsys.readouterr().out
    assert "t1" in out
    assert "COMPLETE" in out


# ===========================================================================
# audit_file(path)
# ===========================================================================

def test_audit_file_compiled_clean(import_patched_script, tmp_path):
    # Canonical status enum (2026-05-28): a sorry-free, axiom-free,
    # non-negated compile lands in 'compiled_no_advance'. Promotion to
    # 'compiled_advance' is OPT-IN (requires manual gap-resolution confirm).
    af = import_patched_script("aristotle_fetch")
    f = tmp_path / "clean.lean"
    f.write_text("theorem foo : 1 = 1 := rfl\nlemma bar : 2 = 2 := rfl\n")

    result = af.audit_file(f)

    assert result["verdict"] == "compiled_no_advance"
    assert result["sorry"] == 0
    assert result["axioms"] == 0
    assert result["declarations"] == 2


def test_audit_file_near_miss_one_sorry(import_patched_script, tmp_path):
    # Canonical status enum (2026-05-28): 1 sorry => 'compiled_partial'.
    # The historical 'near_miss' bucket collapsed into compiled_partial.
    af = import_patched_script("aristotle_fetch")
    f = tmp_path / "near.lean"
    f.write_text("theorem foo : True := by sorry\n")

    result = af.audit_file(f)

    assert result["verdict"] == "compiled_partial"
    assert result["sorry"] == 1


def test_audit_file_completed_multiple_sorries(import_patched_script, tmp_path):
    # Canonical status enum (2026-05-28): 2+ sorry => 'compiled_partial'.
    # The historical 'completed' bucket (multi-sorry) collapsed into compiled_partial.
    af = import_patched_script("aristotle_fetch")
    f = tmp_path / "two.lean"
    f.write_text(
        "theorem a : True := by sorry\n"
        "theorem b : True := by sorry\n"
        "theorem c : True := by sorry\n"
    )

    result = af.audit_file(f)

    assert result["verdict"] == "compiled_partial"
    assert result["sorry"] == 3


def test_audit_file_disproven_on_negation(import_patched_script, tmp_path):
    af = import_patched_script("aristotle_fetch")
    f = tmp_path / "neg.lean"
    f.write_text(
        "-- The following was negated by Aristotle\n"
        "theorem foo : False := by sorry\n"
    )

    result = af.audit_file(f)

    assert result["verdict"] == "disproven"
    assert result["negation"] is True


def test_audit_file_failed_on_load_error_with_sorry(import_patched_script, tmp_path):
    # Canonical status enum (2026-05-28): Aristotle load error => 'compile_failed'.
    af = import_patched_script("aristotle_fetch")
    f = tmp_path / "fail.lean"
    f.write_text("-- Aristotle failed to load the project\ntheorem foo := by sorry\n")

    result = af.audit_file(f)

    assert result["verdict"] == "compile_failed"
    assert result["load_error"] is True


def test_audit_file_ignores_sorry_in_comments(import_patched_script, tmp_path):
    af = import_patched_script("aristotle_fetch")
    f = tmp_path / "comments.lean"
    f.write_text(
        "-- sorry should not count\n"
        "/- sorry -/\n"
        "theorem foo : 1 = 1 := rfl\n"
    )

    result = af.audit_file(f)

    assert result["sorry"] == 0
    assert result["verdict"] == "compiled_no_advance"


def test_audit_file_counts_axioms(import_patched_script, tmp_path):
    af = import_patched_script("aristotle_fetch")
    f = tmp_path / "ax.lean"
    f.write_text("axiom magic : True\ntheorem foo : True := magic\n")

    result = af.audit_file(f)

    assert result["axioms"] == 1
    # Axiom present without sorry/negation: not compiled_no_advance (audit
    # treats axioms as a non-clean signal — should fall to compiled_partial).
    assert result["verdict"] != "compiled_no_advance"
    assert result["verdict"] != "compiled_advance"


# ===========================================================================
# load_slot_ids
# ===========================================================================

def test_load_slot_ids_parses_id_files(
    import_patched_script, monkeypatch, tmp_path
):
    af = import_patched_script("aristotle_fetch")
    monkeypatch.setattr(af, "RESULTS_DIR", tmp_path)

    (tmp_path / "slot42_ID.txt").write_text(
        "some-uuid-xyz\n"
        "# Task: erdos42 conjecture\n"
        "# Submitted: 2026-05-27T09:00:00\n"
    )

    slots = af.load_slot_ids()

    assert 42 in slots
    assert slots[42]["uuid"] == "some-uuid-xyz"
    assert slots[42]["task"] == "erdos42 conjecture"
    assert slots[42]["submitted"] == "2026-05-27T09:00:00"
