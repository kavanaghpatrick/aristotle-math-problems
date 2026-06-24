"""Unit tests for scripts/aristotle_queue.py and scripts/aristotle_monitor.py.

Verifies the aristotlelib 0.7.0 -> 2.0.0 upgrade — specifically:
- get_queued_files uses ProjectStatus.RUNNING server-side filter
- get_queue_status buckets by AgentTask.status (falls back to Project.status)
- submit_file calls Project.create(prompt=...) instead of the dead
  `aristotle prove-from-file` subprocess
- get_all_projects unpacks the (list, pagination_key) tuple
- download_output uses Project.get_files(destination=...)
- check_completions reads task.status (not project.status) and triggers
  on COMPLETE / COMPLETE_WITH_ERRORS / FAILED / OUT_OF_BUDGET / CANCELED
"""

from __future__ import annotations

from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from tests.fixtures import (
    MockProjectStatus,
    MockTaskStatus,
    make_mock_project,
    make_mock_task,
)


# ===========================================================================
# aristotle_queue.get_queued_files
# ===========================================================================


async def test_get_queued_files_uses_RUNNING_server_filter(
    import_patched_script, mock_aristotlelib_module
):
    mock_aristotlelib_module.Project.list_projects.return_value = ([], None)
    aq = import_patched_script("aristotle_queue")

    await aq.get_queued_files()

    mock_aristotlelib_module.Project.list_projects.assert_awaited_with(
        limit=20, status=mock_aristotlelib_module.ProjectStatus.RUNNING
    )


async def test_get_queued_files_collects_basenames_from_tasks(
    import_patched_script, mock_aristotlelib_module
):
    t1 = make_mock_task(file_name="submissions/dir/foo.lean")
    t2 = make_mock_task(file_name="bar.lean")
    p1 = make_mock_project(project_id="p1", tasks=[t1])
    p2 = make_mock_project(project_id="p2", tasks=[t2])
    mock_aristotlelib_module.Project.list_projects.return_value = ([p1, p2], None)

    aq = import_patched_script("aristotle_queue")
    result = await aq.get_queued_files()

    assert result == {"foo.lean", "bar.lean"}


async def test_get_queued_files_skips_projects_with_no_tasks(
    import_patched_script, mock_aristotlelib_module
):
    p_empty = make_mock_project(project_id="p-empty", tasks=[])
    p_full = make_mock_project(
        project_id="p-full",
        tasks=[make_mock_task(file_name="x.lean")],
    )
    mock_aristotlelib_module.Project.list_projects.return_value = (
        [p_empty, p_full],
        None,
    )

    aq = import_patched_script("aristotle_queue")
    result = await aq.get_queued_files()

    assert result == {"x.lean"}


async def test_get_queued_files_skips_tasks_with_no_file_name(
    import_patched_script, mock_aristotlelib_module
):
    t_no_name = make_mock_task(file_name=None)
    p = make_mock_project(tasks=[t_no_name])
    mock_aristotlelib_module.Project.list_projects.return_value = ([p], None)

    aq = import_patched_script("aristotle_queue")
    result = await aq.get_queued_files()

    assert result == set()


async def test_get_queued_files_returns_empty_set_on_exception(
    import_patched_script, mock_aristotlelib_module
):
    mock_aristotlelib_module.Project.list_projects.side_effect = RuntimeError("boom")

    aq = import_patched_script("aristotle_queue")
    result = await aq.get_queued_files()

    assert result == set()


async def test_get_queued_files_per_project_get_tasks_limit_1(
    import_patched_script, mock_aristotlelib_module
):
    p = make_mock_project(tasks=[make_mock_task(file_name="x.lean")])
    mock_aristotlelib_module.Project.list_projects.return_value = ([p], None)

    aq = import_patched_script("aristotle_queue")
    await aq.get_queued_files()

    p.get_tasks.assert_awaited_with(limit=1)


# ===========================================================================
# aristotle_queue.get_queue_status
# ===========================================================================


async def test_get_queue_status_buckets_by_task_status(
    import_patched_script, mock_aristotlelib_module
):
    p1 = make_mock_project(
        project_id="p1",
        tasks=[make_mock_task(status=MockTaskStatus.IN_PROGRESS)],
    )
    p2 = make_mock_project(
        project_id="p2",
        tasks=[make_mock_task(status=MockTaskStatus.COMPLETE)],
    )
    p3 = make_mock_project(
        project_id="p3", tasks=[], status=MockProjectStatus.IDLE
    )
    mock_aristotlelib_module.Project.list_projects.return_value = (
        [p1, p2, p3],
        None,
    )

    aq = import_patched_script("aristotle_queue")
    status = await aq.get_queue_status()

    assert set(status.keys()) == {"IN_PROGRESS", "COMPLETE", "IDLE"}
    assert len(status["IN_PROGRESS"]) == 1
    assert len(status["COMPLETE"]) == 1
    assert len(status["IDLE"]) == 1


async def test_get_queue_status_includes_id_file_desc_created(
    import_patched_script, mock_aristotlelib_module
):
    t = make_mock_task(file_name="foo.lean", description="task-desc")
    p = make_mock_project(
        project_id="p1", tasks=[t], created_at="2026-05-01T00:00:00Z"
    )
    mock_aristotlelib_module.Project.list_projects.return_value = ([p], None)

    aq = import_patched_script("aristotle_queue")
    status = await aq.get_queue_status()

    entry = status["IN_PROGRESS"][0]
    assert entry["id"] == "p1"
    assert entry["file"] == "foo.lean"
    assert entry["desc"] == "task-desc"
    assert entry["created"] == "2026-05-01T00:00:00Z"


async def test_get_queue_status_falls_back_to_project_desc(
    import_patched_script, mock_aristotlelib_module
):
    t = make_mock_task(description=None, file_name="x.lean")
    p = make_mock_project(tasks=[t], description="project-fallback-desc")
    mock_aristotlelib_module.Project.list_projects.return_value = ([p], None)

    aq = import_patched_script("aristotle_queue")
    status = await aq.get_queue_status()

    entry = status["IN_PROGRESS"][0]
    assert entry["desc"] == "project-fallback-desc"


async def test_get_queue_status_returns_error_dict_on_exception(
    import_patched_script, mock_aristotlelib_module
):
    mock_aristotlelib_module.Project.list_projects.side_effect = RuntimeError(
        "kaboom"
    )

    aq = import_patched_script("aristotle_queue")
    status = await aq.get_queue_status()

    assert "ERROR" in status
    assert status["ERROR"][0]["desc"] == "kaboom"


async def test_get_queue_status_does_not_filter_projects(
    import_patched_script, mock_aristotlelib_module
):
    """Status view shows all states, unlike get_queued_files which filters RUNNING."""
    mock_aristotlelib_module.Project.list_projects.return_value = ([], None)

    aq = import_patched_script("aristotle_queue")
    await aq.get_queue_status()

    # Should be called WITHOUT the status= filter
    call = mock_aristotlelib_module.Project.list_projects.await_args
    assert call.kwargs == {"limit": 20}


# ===========================================================================
# aristotle_queue.submit_file
# ===========================================================================


def test_submit_file_calls_Project_create_with_prompt(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    src = tmp_path / "foo.txt"
    src.write_text("hello")

    fake_project = MagicMock()
    fake_project.project_id = "pid1"
    mock_aristotlelib_module.Project.create.return_value = fake_project

    aq = import_patched_script("aristotle_queue")
    ok, msg, pid = aq.submit_file(str(src))

    assert ok is True
    assert pid == "pid1"
    assert "pid1" in msg
    mock_aristotlelib_module.Project.create.assert_awaited_with(prompt="hello")


def test_submit_file_no_api_key_returns_false(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    monkeypatch.delenv("ARISTOTLE_API_KEY", raising=False)
    src = tmp_path / "foo.txt"
    src.write_text("hello")

    aq = import_patched_script("aristotle_queue")
    ok, msg, pid = aq.submit_file(str(src))

    assert ok is False
    assert pid is None
    assert "ARISTOTLE_API_KEY" in msg
    mock_aristotlelib_module.Project.create.assert_not_awaited()


def test_submit_file_429_returns_queue_full(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    src = tmp_path / "foo.txt"
    src.write_text("hi")
    mock_aristotlelib_module.Project.create.side_effect = RuntimeError(
        "HTTP 429 rate limited"
    )

    aq = import_patched_script("aristotle_queue")
    ok, msg, pid = aq.submit_file(str(src))

    assert ok is False
    assert msg == "Queue full (5/5)"
    assert pid is None


def test_submit_file_too_many_requests_returns_queue_full(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    src = tmp_path / "foo.txt"
    src.write_text("hi")
    mock_aristotlelib_module.Project.create.side_effect = RuntimeError(
        "Too Many Requests"
    )

    aq = import_patched_script("aristotle_queue")
    ok, msg, pid = aq.submit_file(str(src))

    assert ok is False
    assert msg == "Queue full (5/5)"


def test_submit_file_already_have_5_returns_queue_full(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    src = tmp_path / "foo.txt"
    src.write_text("hi")
    mock_aristotlelib_module.Project.create.side_effect = RuntimeError(
        "User already have 5 projects running"
    )

    aq = import_patched_script("aristotle_queue")
    ok, msg, pid = aq.submit_file(str(src))

    assert ok is False
    assert msg == "Queue full (5/5)"


def test_submit_file_other_exception_returns_failure_message(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    src = tmp_path / "foo.txt"
    src.write_text("hi")
    mock_aristotlelib_module.Project.create.side_effect = RuntimeError(
        "weird network error"
    )

    aq = import_patched_script("aristotle_queue")
    ok, msg, pid = aq.submit_file(str(src))

    assert ok is False
    assert msg.startswith("Exception:")
    assert "weird network error" in msg


def test_submit_file_no_longer_uses_subprocess(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    """Dead `aristotle prove-from-file` subprocess path must not be invoked."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    src = tmp_path / "foo.txt"
    src.write_text("hi")

    fake_project = MagicMock()
    fake_project.project_id = "pid42"
    mock_aristotlelib_module.Project.create.return_value = fake_project

    aq = import_patched_script("aristotle_queue")

    with patch.object(aq.subprocess, "run") as mock_run:
        ok, msg, pid = aq.submit_file(str(src))

    assert ok is True
    assert pid == "pid42"
    mock_run.assert_not_called()


# ===========================================================================
# aristotle_monitor.get_all_projects
# ===========================================================================


async def test_get_all_projects_unpacks_tuple(
    import_patched_script, mock_aristotlelib_module
):
    p1 = make_mock_project(project_id="p1")
    p2 = make_mock_project(project_id="p2")
    mock_aristotlelib_module.Project.list_projects.return_value = (
        [p1, p2],
        "page-key",
    )

    am = import_patched_script("aristotle_monitor")
    result = await am.get_all_projects()

    assert result == [p1, p2]
    assert "page-key" not in result


async def test_get_all_projects_returns_empty_list_on_exception(
    import_patched_script, mock_aristotlelib_module
):
    mock_aristotlelib_module.Project.list_projects.side_effect = RuntimeError(
        "boom"
    )

    am = import_patched_script("aristotle_monitor")
    result = await am.get_all_projects()

    assert result == []


async def test_get_all_projects_calls_list_projects_with_limit_50(
    import_patched_script, mock_aristotlelib_module
):
    mock_aristotlelib_module.Project.list_projects.return_value = ([], None)

    am = import_patched_script("aristotle_monitor")
    await am.get_all_projects()

    mock_aristotlelib_module.Project.list_projects.assert_awaited_with(limit=50)


# ===========================================================================
# aristotle_monitor.download_output
# ===========================================================================


async def test_download_output_uses_get_files_with_destination(
    tmp_path, import_patched_script, mock_aristotlelib_module
):
    expected = tmp_path / "pid-output.tar.gz"
    expected.write_text("payload")

    project = make_mock_project(project_id="pid")
    mock_aristotlelib_module.Project.from_id.return_value = project

    am = import_patched_script("aristotle_monitor")
    result = await am.download_output("pid", output_dir=str(tmp_path))

    # Verify call shape: destination kwarg, expected path
    project.get_files.assert_awaited_with(destination=str(expected))
    assert result == str(expected)


async def test_download_output_returns_None_when_file_missing(
    tmp_path, import_patched_script, mock_aristotlelib_module
):
    project = make_mock_project(project_id="pid")
    # get_files completes but never writes the file
    project.get_files = AsyncMock(return_value=None)
    mock_aristotlelib_module.Project.from_id.return_value = project

    am = import_patched_script("aristotle_monitor")
    result = await am.download_output("pid", output_dir=str(tmp_path))

    assert result is None


async def test_download_output_returns_path_when_exists(
    tmp_path, import_patched_script, mock_aristotlelib_module
):
    expected = tmp_path / "pid-output.tar.gz"

    async def _touch(destination=None):
        Path(destination).write_text("data")
        return destination

    project = make_mock_project(project_id="pid")
    project.get_files = AsyncMock(side_effect=_touch)
    mock_aristotlelib_module.Project.from_id.return_value = project

    am = import_patched_script("aristotle_monitor")
    result = await am.download_output("pid", output_dir=str(tmp_path))

    assert result == str(expected)
    assert Path(result).exists()


async def test_download_output_returns_None_on_exception(
    tmp_path, import_patched_script, mock_aristotlelib_module
):
    mock_aristotlelib_module.Project.from_id.side_effect = RuntimeError(
        "from_id failed"
    )

    am = import_patched_script("aristotle_monitor")
    result = await am.download_output("pid", output_dir=str(tmp_path))

    assert result is None


async def test_download_output_creates_output_dir(
    tmp_path, import_patched_script, mock_aristotlelib_module
):
    nested = tmp_path / "deep" / "nested" / "dir"
    assert not nested.exists()

    async def _touch(destination=None):
        Path(destination).write_text("data")
        return destination

    project = make_mock_project(project_id="pid")
    project.get_files = AsyncMock(side_effect=_touch)
    mock_aristotlelib_module.Project.from_id.return_value = project

    am = import_patched_script("aristotle_monitor")
    await am.download_output("pid", output_dir=str(nested))

    assert nested.exists()


# ===========================================================================
# aristotle_monitor.check_completions
# ===========================================================================


async def test_check_completions_uses_task_status_not_project_status(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    """Project status IDLE but task COMPLETE -> still processed as completed."""
    am = import_patched_script("aristotle_monitor")

    # Redirect logs to tmp_path so we don't touch the real ones
    submissions_path = tmp_path / "submissions.json"
    analysis_path = tmp_path / "analysis.json"
    monkeypatch.setattr(am, "SUBMISSIONS_LOG", str(submissions_path))
    monkeypatch.setattr(am, "ANALYSIS_LOG", str(analysis_path))

    src_file = tmp_path / "mysubmission.lean"
    src_file.write_text("theorem foo : True := trivial\n")
    submissions_path.write_text(
        '{"' + str(src_file) + '": {"project_id": "pid1", "status": "submitted"}}'
    )

    t = make_mock_task(status=MockTaskStatus.COMPLETE, file_name=str(src_file))
    project = make_mock_project(
        project_id="pid1",
        tasks=[t],
        status=MockProjectStatus.IDLE,  # project status irrelevant
    )
    mock_aristotlelib_module.Project.list_projects.return_value = ([project], None)

    # Mock download_output to return a file we control
    output_file = tmp_path / "pid1.tar.gz"
    output_file.write_text("theorem foo : True := trivial\n")
    monkeypatch.setattr(
        am, "download_output", AsyncMock(return_value=str(output_file))
    )

    completed = await am.check_completions()

    assert len(completed) == 1
    assert completed[0]["project_id"] == "pid1"
    assert completed[0]["completion_status"] == "COMPLETE"


async def test_check_completions_accepts_COMPLETE_WITH_ERRORS(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    am = import_patched_script("aristotle_monitor")
    submissions_path = tmp_path / "submissions.json"
    analysis_path = tmp_path / "analysis.json"
    monkeypatch.setattr(am, "SUBMISSIONS_LOG", str(submissions_path))
    monkeypatch.setattr(am, "ANALYSIS_LOG", str(analysis_path))

    src_file = tmp_path / "sub.lean"
    src_file.write_text("theorem ok : True := trivial\n")
    submissions_path.write_text(
        '{"' + str(src_file) + '": {"project_id": "pid2"}}'
    )

    t = make_mock_task(status=MockTaskStatus.COMPLETE_WITH_ERRORS, file_name=str(src_file))
    project = make_mock_project(project_id="pid2", tasks=[t])
    mock_aristotlelib_module.Project.list_projects.return_value = ([project], None)

    output_file = tmp_path / "pid2.tar.gz"
    output_file.write_text("theorem ok : True := trivial\n")
    monkeypatch.setattr(
        am, "download_output", AsyncMock(return_value=str(output_file))
    )

    completed = await am.check_completions()
    assert len(completed) == 1
    assert completed[0]["completion_status"] == "COMPLETE_WITH_ERRORS"


@pytest.mark.parametrize(
    "task_status",
    [MockTaskStatus.FAILED, MockTaskStatus.OUT_OF_BUDGET, MockTaskStatus.CANCELED],
)
async def test_check_completions_accepts_FAILED_OUT_OF_BUDGET_CANCELED(
    task_status,
    tmp_path,
    monkeypatch,
    import_patched_script,
    mock_aristotlelib_module,
):
    am = import_patched_script("aristotle_monitor")
    submissions_path = tmp_path / "submissions.json"
    analysis_path = tmp_path / "analysis.json"
    monkeypatch.setattr(am, "SUBMISSIONS_LOG", str(submissions_path))
    monkeypatch.setattr(am, "ANALYSIS_LOG", str(analysis_path))

    src_file = tmp_path / "sub.lean"
    src_file.write_text("theorem ok : True := trivial\n")
    submissions_path.write_text(
        '{"' + str(src_file) + '": {"project_id": "pid3"}}'
    )

    t = make_mock_task(status=task_status, file_name=str(src_file))
    project = make_mock_project(project_id="pid3", tasks=[t])
    mock_aristotlelib_module.Project.list_projects.return_value = ([project], None)

    output_file = tmp_path / "pid3.tar.gz"
    output_file.write_text("theorem ok : True := trivial\n")
    download_mock = AsyncMock(return_value=str(output_file))
    monkeypatch.setattr(am, "download_output", download_mock)

    completed = await am.check_completions()

    download_mock.assert_awaited_once()
    assert len(completed) == 1
    assert completed[0]["completion_status"] == task_status.name


async def test_check_completions_skips_IN_PROGRESS(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    am = import_patched_script("aristotle_monitor")
    submissions_path = tmp_path / "submissions.json"
    analysis_path = tmp_path / "analysis.json"
    monkeypatch.setattr(am, "SUBMISSIONS_LOG", str(submissions_path))
    monkeypatch.setattr(am, "ANALYSIS_LOG", str(analysis_path))

    src_file = tmp_path / "sub.lean"
    src_file.write_text("theorem ok : True := trivial\n")
    submissions_path.write_text(
        '{"' + str(src_file) + '": {"project_id": "pid4"}}'
    )

    t = make_mock_task(status=MockTaskStatus.IN_PROGRESS, file_name=str(src_file))
    project = make_mock_project(project_id="pid4", tasks=[t])
    mock_aristotlelib_module.Project.list_projects.return_value = ([project], None)

    download_mock = AsyncMock()
    monkeypatch.setattr(am, "download_output", download_mock)

    completed = await am.check_completions()

    download_mock.assert_not_awaited()
    assert completed == []


async def test_check_completions_skips_QUEUED(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    am = import_patched_script("aristotle_monitor")
    submissions_path = tmp_path / "submissions.json"
    analysis_path = tmp_path / "analysis.json"
    monkeypatch.setattr(am, "SUBMISSIONS_LOG", str(submissions_path))
    monkeypatch.setattr(am, "ANALYSIS_LOG", str(analysis_path))

    src_file = tmp_path / "sub.lean"
    src_file.write_text("theorem ok : True := trivial\n")
    submissions_path.write_text(
        '{"' + str(src_file) + '": {"project_id": "pid5"}}'
    )

    t = make_mock_task(status=MockTaskStatus.QUEUED, file_name=str(src_file))
    project = make_mock_project(project_id="pid5", tasks=[t])
    mock_aristotlelib_module.Project.list_projects.return_value = ([project], None)

    download_mock = AsyncMock()
    monkeypatch.setattr(am, "download_output", download_mock)

    completed = await am.check_completions()

    download_mock.assert_not_awaited()
    assert completed == []


async def test_check_completions_skips_already_analyzed(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    am = import_patched_script("aristotle_monitor")
    submissions_path = tmp_path / "submissions.json"
    analysis_path = tmp_path / "analysis.json"
    monkeypatch.setattr(am, "SUBMISSIONS_LOG", str(submissions_path))
    monkeypatch.setattr(am, "ANALYSIS_LOG", str(analysis_path))

    src_file = tmp_path / "sub.lean"
    src_file.write_text("theorem ok : True := trivial\n")
    submissions_path.write_text(
        '{"' + str(src_file) + '": {"project_id": "pid-done"}}'
    )
    # Pre-existing analysis entry for this project
    analysis_path.write_text('{"pid-done": {"status": "success"}}')

    t = make_mock_task(status=MockTaskStatus.COMPLETE, file_name=str(src_file))
    project = make_mock_project(project_id="pid-done", tasks=[t])
    mock_aristotlelib_module.Project.list_projects.return_value = ([project], None)

    download_mock = AsyncMock()
    monkeypatch.setattr(am, "download_output", download_mock)

    completed = await am.check_completions()

    download_mock.assert_not_awaited()
    assert completed == []


async def test_check_completions_handles_project_with_no_tasks_as_UNKNOWN(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    am = import_patched_script("aristotle_monitor")
    submissions_path = tmp_path / "submissions.json"
    analysis_path = tmp_path / "analysis.json"
    monkeypatch.setattr(am, "SUBMISSIONS_LOG", str(submissions_path))
    monkeypatch.setattr(am, "ANALYSIS_LOG", str(analysis_path))

    src_file = tmp_path / "sub.lean"
    src_file.write_text("theorem ok : True := trivial\n")
    submissions_path.write_text(
        '{"' + str(src_file) + '": {"project_id": "pid6"}}'
    )

    project = make_mock_project(project_id="pid6", tasks=[])
    mock_aristotlelib_module.Project.list_projects.return_value = ([project], None)

    download_mock = AsyncMock()
    monkeypatch.setattr(am, "download_output", download_mock)

    completed = await am.check_completions()

    download_mock.assert_not_awaited()
    assert completed == []


async def test_check_completions_persists_analysis_and_submissions(
    tmp_path, monkeypatch, import_patched_script, mock_aristotlelib_module
):
    am = import_patched_script("aristotle_monitor")
    submissions_path = tmp_path / "submissions.json"
    analysis_path = tmp_path / "analysis.json"
    monkeypatch.setattr(am, "SUBMISSIONS_LOG", str(submissions_path))
    monkeypatch.setattr(am, "ANALYSIS_LOG", str(analysis_path))

    src_file = tmp_path / "sub.lean"
    src_file.write_text("theorem ok : True := trivial\n")
    submissions_path.write_text(
        '{"' + str(src_file) + '": {"project_id": "pid7", "status": "submitted"}}'
    )

    t = make_mock_task(status=MockTaskStatus.COMPLETE, file_name=str(src_file))
    project = make_mock_project(project_id="pid7", tasks=[t])
    mock_aristotlelib_module.Project.list_projects.return_value = ([project], None)

    output_file = tmp_path / "pid7.tar.gz"
    output_file.write_text("theorem ok : True := trivial\n")
    monkeypatch.setattr(
        am, "download_output", AsyncMock(return_value=str(output_file))
    )

    save_calls = []
    orig_save = am.save_json

    def _spy(path, data):
        save_calls.append(path)
        orig_save(path, data)

    monkeypatch.setattr(am, "save_json", _spy)

    completed = await am.check_completions()

    assert len(completed) == 1
    # Both JSONs were persisted via save_json
    assert str(analysis_path) in save_calls
    assert str(submissions_path) in save_calls

    # And the on-disk state reflects the update
    import json
    submissions = json.loads(submissions_path.read_text())
    assert submissions[str(src_file)]["status"] == "complete"
    assert submissions[str(src_file)]["analyzed"] is True

    analysis = json.loads(analysis_path.read_text())
    assert "pid7" in analysis


# ===========================================================================
# aristotle_monitor.analyze_output (synthetic-file checks)
# ===========================================================================


def test_analyze_output_classifies_proven_and_sorry_lemmas(
    tmp_path, import_patched_script, mock_aristotlelib_module
):
    am = import_patched_script("aristotle_monitor")

    src = tmp_path / "out.lean"
    src.write_text(
        "theorem proven_one : True := by trivial\n"
        "lemma failing_one : False := by sorry\n"
        "theorem proven_two : 1 + 1 = 2 := by rfl\n"
    )

    result = am.analyze_output(str(src))

    assert "proven_one" in result["proven_lemmas"]
    assert "proven_two" in result["proven_lemmas"]
    assert "failing_one" in result["failed_lemmas"]
    assert result["sorries"] == 1
    assert result["status"] in {"partial", "success", "incomplete"}


def test_analyze_output_returns_error_on_missing_file(
    tmp_path, import_patched_script, mock_aristotlelib_module
):
    am = import_patched_script("aristotle_monitor")

    result = am.analyze_output(str(tmp_path / "does_not_exist.lean"))

    assert result["status"] == "error"
