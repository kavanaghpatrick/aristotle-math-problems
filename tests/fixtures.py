"""Test helpers shared across all aristotlelib 2.0 upgrade tests.

Importable as `from tests.fixtures import ...` from any test module.

Lives outside conftest.py because pytest loads conftest.py as a plugin
(not via the import system), so `from conftest import ...` doesn't work
reliably across the test tree. Keep this file plain Python.
"""

from __future__ import annotations

import enum
from typing import Any
from unittest.mock import AsyncMock, MagicMock


# ---------------------------------------------------------------------------
# Enum mocks — must mirror real aristotlelib 2.0 names exactly.
# ---------------------------------------------------------------------------

class MockTaskStatus(enum.Enum):
    UNKNOWN = "UNKNOWN"
    QUEUED = "QUEUED"
    IN_PROGRESS = "IN_PROGRESS"
    COMPLETE = "COMPLETE"
    COMPLETE_WITH_ERRORS = "COMPLETE_WITH_ERRORS"
    OUT_OF_BUDGET = "OUT_OF_BUDGET"
    FAILED = "FAILED"
    CANCELED = "CANCELED"


class MockProjectStatus(enum.Enum):
    UNKNOWN = "UNKNOWN"
    RUNNING = "RUNNING"
    IDLE = "IDLE"


# ---------------------------------------------------------------------------
# Factories — build the kind of objects the scripts read off the SDK.
# ---------------------------------------------------------------------------

def make_mock_task(
    status: MockTaskStatus = MockTaskStatus.IN_PROGRESS,
    file_name: str | None = "submissions/example.lean",
    percent_complete: int | None = 0,
    agent_task_id: str = "task-id-default",
    description: str | None = "a task",
) -> MagicMock:
    """Build a mock AgentTask with the attributes scripts actually read."""
    t = MagicMock(name=f"AgentTask({status.name})")
    t.status = status
    t.file_name = file_name
    t.percent_complete = percent_complete
    t.agent_task_id = agent_task_id
    t.description = description
    return t


def make_mock_project(
    project_id: str = "proj-id-default",
    status: MockProjectStatus = MockProjectStatus.RUNNING,
    tasks: list[Any] | None = None,
    description: str | None = "a project",
    created_at: str | None = "2026-05-27T12:00:00Z",
) -> MagicMock:
    """Build a mock Project. `get_tasks(limit=N)` returns (tasks[:N], None).

    `get_files(destination=...)` echoes the destination back as the path.
    `ask(prompt)` returns a QUEUED follow-up task.

    Tests can override any of these by reassigning, e.g.:
        project.get_files = AsyncMock(return_value=None)
    """
    p = MagicMock(name=f"Project({project_id})")
    p.project_id = project_id
    p.status = status
    p.description = description
    p.created_at = created_at

    task_list = list(tasks) if tasks is not None else []

    async def _get_tasks(limit: int = 10):
        return list(task_list[:limit]), None

    async def _get_files(destination: str | None = None):
        return destination

    async def _ask(prompt: str):
        return make_mock_task(
            status=MockTaskStatus.QUEUED,
            agent_task_id="ask-task-1",
            description="follow-up",
            file_name=None,
        )

    p.get_tasks = AsyncMock(side_effect=_get_tasks)
    p.get_files = AsyncMock(side_effect=_get_files)
    p.ask = AsyncMock(side_effect=_ask)
    return p


def build_fake_aristotlelib_module():
    """Construct a fresh fake `aristotlelib` module.

    Exposes the names patched scripts import:
        Project, TaskStatus, ProjectStatus, set_api_key
    Project is a MagicMock; its async classmethods (from_id, create,
    list_projects) are AsyncMocks the tests can stub.

    `mock_aristotlelib_module` (in conftest.py) calls this and injects the
    result into sys.modules — tests should not normally call this directly.
    """
    import types

    mod = types.ModuleType("aristotlelib")

    Project = MagicMock(name="Project")
    Project.from_id = AsyncMock(name="Project.from_id")
    Project.create = AsyncMock(name="Project.create")
    Project.list_projects = AsyncMock(
        name="Project.list_projects", return_value=([], None)
    )

    mod.Project = Project
    mod.TaskStatus = MockTaskStatus
    mod.ProjectStatus = MockProjectStatus
    mod.set_api_key = MagicMock(name="set_api_key")
    return mod
