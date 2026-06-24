"""Tests for capacity-probe functions in submission scripts.

Covers:
- scripts/safe_aristotle_submit.py :: check_rate_limit_and_capacity
- scripts/submit_parker_batch.py   :: check_queue

Both functions consume aristotlelib 2.0's server-side
`Project.list_projects(status=ProjectStatus.RUNNING)` filter; the old
0.7 enum values (QUEUED/IN_PROGRESS at project level) no longer exist.
"""

from __future__ import annotations

from datetime import datetime, timedelta

from tests.fixtures import make_mock_project


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _iso_z(dt: datetime) -> str:
    """Format a naive datetime as the `...Z` string the SDK returns."""
    return dt.strftime("%Y-%m-%dT%H:%M:%SZ")


def _set_two_call_side_effect(mock_module, running, recent):
    """Configure `list_projects` to return `(running, None)` then `(recent, None)`.

    `check_rate_limit_and_capacity` calls list_projects twice: first filtered
    by status=RUNNING, then unfiltered for the recent-window count.
    """
    mock_module.Project.list_projects.side_effect = [
        (running, None),
        (recent, None),
    ]


# ---------------------------------------------------------------------------
# safe_aristotle_submit.check_rate_limit_and_capacity
# ---------------------------------------------------------------------------

async def test_capacity_uses_RUNNING_server_filter(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    _set_two_call_side_effect(mock_aristotlelib_module, running=[], recent=[])

    sas = import_patched_script("safe_aristotle_submit")
    await sas.check_rate_limit_and_capacity(window_minutes=10)

    calls = mock_aristotlelib_module.Project.list_projects.await_args_list
    assert len(calls) == 2
    # First call: filtered by RUNNING
    first_kwargs = calls[0].kwargs
    assert first_kwargs.get("status") is mock_aristotlelib_module.ProjectStatus.RUNNING
    assert first_kwargs.get("limit") == 20
    # Second call: unfiltered (no status kwarg)
    second_kwargs = calls[1].kwargs
    assert "status" not in second_kwargs
    assert second_kwargs.get("limit") == 20


async def test_capacity_in_progress_counts_filtered_projects(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    running = [make_mock_project(project_id=f"p{i}") for i in range(3)]
    _set_two_call_side_effect(mock_aristotlelib_module, running=running, recent=[])

    sas = import_patched_script("safe_aristotle_submit")
    result = await sas.check_rate_limit_and_capacity(window_minutes=10)

    assert result["in_progress"] == 3
    assert result["slots_available"] == 2
    assert result["has_capacity"] is True


async def test_capacity_slots_available_is_5_minus_in_progress(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    running = [make_mock_project(project_id=f"p{i}") for i in range(2)]
    _set_two_call_side_effect(mock_aristotlelib_module, running=running, recent=[])

    sas = import_patched_script("safe_aristotle_submit")
    result = await sas.check_rate_limit_and_capacity(window_minutes=10)

    assert result["in_progress"] == 2
    assert result["slots_available"] == 3
    assert result["has_capacity"] is True


async def test_capacity_no_capacity_when_in_progress_equals_5(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    running = [make_mock_project(project_id=f"p{i}") for i in range(5)]
    _set_two_call_side_effect(mock_aristotlelib_module, running=running, recent=[])

    sas = import_patched_script("safe_aristotle_submit")
    result = await sas.check_rate_limit_and_capacity(window_minutes=10)

    assert result["in_progress"] == 5
    assert result["has_capacity"] is False
    assert result["slots_available"] == 0


async def test_capacity_slots_available_clamped_to_zero_when_over_5(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """Sanity check: if in_progress somehow exceeds 5, slots is max(0, ...)."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    running = [make_mock_project(project_id=f"p{i}") for i in range(6)]
    _set_two_call_side_effect(mock_aristotlelib_module, running=running, recent=[])

    sas = import_patched_script("safe_aristotle_submit")
    result = await sas.check_rate_limit_and_capacity(window_minutes=10)

    assert result["in_progress"] == 6
    assert result["slots_available"] == 0
    assert result["has_capacity"] is False


async def test_capacity_recent_count_uses_unfiltered_call(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """recent_count is computed from the SECOND (unfiltered) list_projects call."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    now = datetime.now()
    # 3 are within 10-min window, 2 are well outside.
    recent = [
        make_mock_project(project_id="r0", created_at=_iso_z(now - timedelta(minutes=1))),
        make_mock_project(project_id="r1", created_at=_iso_z(now - timedelta(minutes=5))),
        make_mock_project(project_id="r2", created_at=_iso_z(now - timedelta(minutes=9))),
        make_mock_project(project_id="r3", created_at=_iso_z(now - timedelta(minutes=30))),
        make_mock_project(project_id="r4", created_at=_iso_z(now - timedelta(hours=2))),
    ]
    _set_two_call_side_effect(mock_aristotlelib_module, running=[], recent=recent)

    sas = import_patched_script("safe_aristotle_submit")
    result = await sas.check_rate_limit_and_capacity(window_minutes=10)

    # in_progress reflects RUNNING list (empty); recent_count from unfiltered list
    assert result["in_progress"] == 0
    assert result["recent_count"] == 3


async def test_capacity_recent_count_excludes_old(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """Projects with created_at older than window_minutes are not counted."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    now = datetime.now()
    recent = [
        make_mock_project(project_id="old1", created_at=_iso_z(now - timedelta(minutes=11))),
        make_mock_project(project_id="old2", created_at=_iso_z(now - timedelta(minutes=60))),
    ]
    _set_two_call_side_effect(mock_aristotlelib_module, running=[], recent=recent)

    sas = import_patched_script("safe_aristotle_submit")
    result = await sas.check_rate_limit_and_capacity(window_minutes=10)

    assert result["recent_count"] == 0


async def test_capacity_recent_count_handles_Z_timezone_suffix(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """The `...Z` UTC suffix should be parsed without crashing."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    now = datetime.now()
    recent = [
        make_mock_project(project_id="z1", created_at=_iso_z(now - timedelta(minutes=2))),
    ]
    _set_two_call_side_effect(mock_aristotlelib_module, running=[], recent=recent)

    sas = import_patched_script("safe_aristotle_submit")
    result = await sas.check_rate_limit_and_capacity(window_minutes=10)

    assert result["recent_count"] == 1


async def test_capacity_returns_all_four_keys(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """Contract test: result has exactly the documented keys."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    _set_two_call_side_effect(mock_aristotlelib_module, running=[], recent=[])

    sas = import_patched_script("safe_aristotle_submit")
    result = await sas.check_rate_limit_and_capacity(window_minutes=10)

    assert set(result.keys()) == {
        "recent_count", "in_progress", "has_capacity", "slots_available",
    }


# ---------------------------------------------------------------------------
# submit_parker_batch.check_queue
# ---------------------------------------------------------------------------

async def test_parker_check_queue_uses_RUNNING_filter(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """check_queue must call list_projects with keyword status=ProjectStatus.RUNNING."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    mock_aristotlelib_module.Project.list_projects.return_value = ([], None)

    spb = import_patched_script("submit_parker_batch")
    await spb.check_queue()

    mock_aristotlelib_module.Project.list_projects.assert_awaited_once_with(
        limit=20, status=mock_aristotlelib_module.ProjectStatus.RUNNING
    )


async def test_parker_check_queue_returns_count_and_available(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """2 RUNNING projects -> (2, 3)."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    running = [make_mock_project(project_id=f"p{i}") for i in range(2)]
    mock_aristotlelib_module.Project.list_projects.return_value = (running, None)

    spb = import_patched_script("submit_parker_batch")
    active, available = await spb.check_queue()

    assert (active, available) == (2, 3)


async def test_parker_check_queue_returns_zero_active_when_empty(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """Empty queue -> (0, 5)."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    mock_aristotlelib_module.Project.list_projects.return_value = ([], None)

    spb = import_patched_script("submit_parker_batch")
    active, available = await spb.check_queue()

    assert (active, available) == (0, 5)


async def test_parker_check_queue_returns_zero_available_when_full(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """5 RUNNING -> (5, 0)."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    running = [make_mock_project(project_id=f"p{i}") for i in range(5)]
    mock_aristotlelib_module.Project.list_projects.return_value = (running, None)

    spb = import_patched_script("submit_parker_batch")
    active, available = await spb.check_queue()

    assert (active, available) == (5, 0)


async def test_parker_check_queue_does_not_use_old_string_status_check(
    monkeypatch, mock_aristotlelib_module, import_patched_script
):
    """Regression guard: must use enum keyword, not the old 0.7 string check."""
    monkeypatch.setenv("ARISTOTLE_API_KEY", "fake-key")
    # If the script were still doing `str(p.status) in ['ProjectStatus.QUEUED', ...]`,
    # a RUNNING-status project would slip past and break the count semantics.
    running = [make_mock_project(
        project_id="p1", status=mock_aristotlelib_module.ProjectStatus.RUNNING
    )]
    mock_aristotlelib_module.Project.list_projects.return_value = (running, None)

    spb = import_patched_script("submit_parker_batch")
    await spb.check_queue()

    call = mock_aristotlelib_module.Project.list_projects.await_args
    # Status must be passed as keyword arg, value must be the new enum.
    assert "status" in call.kwargs
    assert call.kwargs["status"] is mock_aristotlelib_module.ProjectStatus.RUNNING
