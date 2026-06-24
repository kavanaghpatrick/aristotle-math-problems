"""Integration tests against the real Aristotle API.

These tests verify that the live `aristotlelib` 2.0 SDK and the `aristotle`
CLI behave as the patched scripts assume. They are gated on the `live` marker
and require `ARISTOTLE_API_KEY` to be set; otherwise each test is skipped.

Run with:
    pytest tests/test_live_api.py -v -m live
"""

from __future__ import annotations

import os
import re
import subprocess

import pytest

from aristotlelib import Project, ProjectStatus, TaskStatus, set_api_key


pytestmark = pytest.mark.live


# Names every patched script expects to find on TaskStatus / ProjectStatus.
REQUIRED_TASK_STATUS_NAMES = {
    "UNKNOWN",
    "QUEUED",
    "IN_PROGRESS",
    "COMPLETE",
    "COMPLETE_WITH_ERRORS",
    "OUT_OF_BUDGET",
    "FAILED",
    "CANCELED",
}

REQUIRED_PROJECT_STATUS_NAMES = {"UNKNOWN", "RUNNING", "IDLE"}


def _install_key(live_api_key: str) -> None:
    """The SDK module-level client requires set_api_key() to have been called
    before any async call. The fixture supplies the key string."""
    set_api_key(live_api_key)


# ---------------------------------------------------------------------------
# Enum shape — pure-Python, no network. Skipped if no key so the suite stays
# fully gated on `-m live`.
# ---------------------------------------------------------------------------

def test_taskstatus_enum_values(live_api_key):
    names = set(TaskStatus.__members__.keys())
    missing = REQUIRED_TASK_STATUS_NAMES - names
    assert not missing, (
        f"TaskStatus is missing required members: {missing}. Present: {names}"
    )


def test_projectstatus_enum_values(live_api_key):
    names = set(ProjectStatus.__members__.keys())
    missing = REQUIRED_PROJECT_STATUS_NAMES - names
    assert not missing, (
        f"ProjectStatus is missing required members: {missing}. Present: {names}"
    )


# ---------------------------------------------------------------------------
# Live API calls.
# ---------------------------------------------------------------------------

async def test_list_projects_returns_tuple(live_api_key):
    _install_key(live_api_key)
    result = await Project.list_projects(limit=2)

    assert isinstance(result, tuple), f"expected tuple, got {type(result).__name__}"
    assert len(result) == 2, f"expected 2-tuple, got len={len(result)}"
    projects, pagination_key = result
    assert isinstance(projects, list), f"first element should be list, got {type(projects).__name__}"
    assert len(projects) <= 2, f"limit=2 should cap list at 2, got {len(projects)}"
    assert pagination_key is None or isinstance(pagination_key, str), (
        f"pagination_key should be None or str, got {type(pagination_key).__name__}"
    )


async def test_list_projects_with_status_filter(live_api_key):
    _install_key(live_api_key)
    projects, _ = await Project.list_projects(limit=5, status=ProjectStatus.RUNNING)
    assert isinstance(projects, list)
    # ProjectStatus is an IntEnum; the returned `.status` may be the raw int
    # or the enum. Compare on .value so either works.
    for p in projects:
        assert int(p.status) == ProjectStatus.RUNNING.value, (
            f"project {p.project_id} returned by RUNNING filter has status "
            f"{p.status} (expected RUNNING={ProjectStatus.RUNNING.value})"
        )


async def test_project_from_id_and_get_tasks(live_api_key):
    _install_key(live_api_key)
    projects, _ = await Project.list_projects(limit=1)
    if not projects:
        pytest.skip("no projects available on this account to exercise from_id")
    pid = projects[0].project_id

    project = await Project.from_id(pid)
    assert project is not None
    assert hasattr(project, "project_id"), "Project.from_id result missing project_id"

    tasks, _tkey = await project.get_tasks(limit=1)
    assert isinstance(tasks, list)
    assert len(tasks) <= 1
    for t in tasks:
        assert hasattr(t, "status"), "AgentTask missing .status"
        assert isinstance(t.status, TaskStatus), (
            f"AgentTask.status should be TaskStatus instance, got {type(t.status).__name__}"
        )


# ---------------------------------------------------------------------------
# CLI end-to-end.
# ---------------------------------------------------------------------------

def test_cli_version_is_2_0_0(live_api_key):
    proc = subprocess.run(
        ["aristotle", "--version"],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert proc.returncode == 0, (
        f"`aristotle --version` exited {proc.returncode}. "
        f"stdout={proc.stdout!r} stderr={proc.stderr!r}"
    )
    output = (proc.stdout or "") + (proc.stderr or "")
    match = re.search(r"aristotlelib\s+(\d+)\.(\d+)\.(\d+)", output)
    assert match, f"could not parse `aristotlelib X.Y.Z` from output: {output!r}"
    major = int(match.group(1))
    assert major == 2, f"expected aristotlelib major version 2, got {major} (full: {match.group(0)})"


def test_cli_list_runs(live_api_key):
    proc = subprocess.run(
        ["aristotle", "list", "--limit", "1"],
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert proc.returncode == 0, (
        f"`aristotle list --limit 1` exited {proc.returncode}. "
        f"stdout={proc.stdout!r} stderr={proc.stderr!r}"
    )
