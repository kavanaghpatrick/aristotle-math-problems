"""Shared pytest fixtures for aristotlelib 2.0 upgrade tests.

The big idea: every patched script does
    from aristotlelib import Project, TaskStatus     (or ProjectStatus, set_api_key)
at import time. To test without the real SDK / network, we inject a fake
`aristotlelib` module into `sys.modules` BEFORE the script under test is
imported, and then `importlib.import_module(...)` (or reload) the script so
its `from aristotlelib import ...` binds to our fakes.

Enum mocks and object factories live in `tests/fixtures.py` so test modules
can import them directly: `from tests.fixtures import make_mock_project, ...`
"""

from __future__ import annotations

import importlib
import os
import sys
from pathlib import Path

import pytest

from tests.fixtures import build_fake_aristotlelib_module


REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"

# Make `import aristotle_fetch`, `import aristotle_queue`, etc. work from tests.
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))


# ---------------------------------------------------------------------------
# Fake aristotlelib module injection.
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_aristotlelib_module(monkeypatch):
    """Inject a fake `aristotlelib` into sys.modules and return the module.

    Use this fixture FIRST, then `import_patched_script("aristotle_fetch")`
    to bind the patched script's `from aristotlelib import ...` to the fakes.

    Yields the fake module so tests can stub e.g.
        mock_aristotlelib_module.Project.from_id.return_value = make_mock_project(...)

    Also evicts every previously-imported patched script so the next import
    picks up the fresh fakes (the `from aristotlelib import X` bindings are
    cached on the script module object).
    """
    fake = build_fake_aristotlelib_module()
    monkeypatch.setitem(sys.modules, "aristotlelib", fake)

    for name in (
        "aristotle_fetch",
        "aristotle_queue",
        "aristotle_monitor",
        "safe_aristotle_submit",
        "submit_parker_batch",
    ):
        if name in sys.modules:
            monkeypatch.delitem(sys.modules, name, raising=False)

    yield fake


@pytest.fixture
def import_patched_script(mock_aristotlelib_module):
    """Returns a callable that imports a patched script after the fake
    aristotlelib has been installed.

    Usage:
        def test_something(import_patched_script):
            af = import_patched_script("aristotle_fetch")
            ...
    """
    def _do_import(name: str):
        if name in sys.modules:
            return importlib.reload(sys.modules[name])
        return importlib.import_module(name)

    return _do_import


# ---------------------------------------------------------------------------
# Environment cleanup so unit tests don't accidentally hit the real API.
# ---------------------------------------------------------------------------

@pytest.fixture(autouse=True)
def _scrub_api_key_unless_live(request, monkeypatch):
    """Remove ARISTOTLE_API_KEY for unit tests so accidental real calls fail
    fast. Tests marked `live` keep the env var.
    """
    if request.node.get_closest_marker("live") is not None:
        return
    monkeypatch.delenv("ARISTOTLE_API_KEY", raising=False)


# ---------------------------------------------------------------------------
# Live-test gating.
# ---------------------------------------------------------------------------

@pytest.fixture
def live_api_key():
    """Skip if no real ARISTOTLE_API_KEY. Used by `tests/test_live_api.py`."""
    key = os.environ.get("ARISTOTLE_API_KEY")
    if not key:
        pytest.skip("ARISTOTLE_API_KEY not set; skipping live test")
    return key
