"""Tests for safe_aristotle_submit.gather_context().

Covers the silently-broken-status-filter bug found in the May-30 F2 audit:
the pre-fix query filtered on status IN ('compiled_clean','near_miss',
'completed'), none of which exist in the current schema, so 0 rows came
back for every submission. See docs/infrastructure_changes_may30/
I1_gather_context_fix.md.

Test strategy
-------------
gather_context() opens MATH_DIR/submissions/tracking.db directly. We
monkey-patch MATH_DIR on the imported module to point at a tmp_path
containing a synthetic tracking.db and synthetic .lean result files.
The fake aristotlelib (from conftest.py) lets us import the script
without the SDK installed.
"""

from __future__ import annotations

import os
import sqlite3
from pathlib import Path

import pytest


# Schema mirrors submissions table at 2026-05-30 (column subset needed by
# gather_context — adding the full column list keeps the test honest if
# someone widens the query).
_SCHEMA_SQL = """
CREATE TABLE submissions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    uuid TEXT UNIQUE,
    filename TEXT NOT NULL,
    problem_id TEXT,
    submitted_at TEXT,
    status TEXT DEFAULT 'draft',
    output_file TEXT,
    verified INTEGER
);
"""


def _ensure_api_key():
    """safe_aristotle_submit imports raise without ARISTOTLE_API_KEY set.
    Set a dummy value before the script is imported. The fake aristotlelib
    from conftest's mock_aristotlelib_module is what actually receives any
    set_api_key() call."""
    os.environ.setdefault("ARISTOTLE_API_KEY", "test-dummy-key")


def _make_db(db_path: Path, rows: list[dict]) -> None:
    """Create tracking.db at db_path and insert the given rows."""
    db_path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(str(db_path))
    try:
        conn.executescript(_SCHEMA_SQL)
        for row in rows:
            conn.execute(
                "INSERT INTO submissions "
                "(uuid, filename, problem_id, submitted_at, status, output_file, verified) "
                "VALUES (?, ?, ?, ?, ?, ?, ?)",
                (
                    row.get("uuid"),
                    row.get("filename", "x.txt"),
                    row.get("problem_id"),
                    row.get("submitted_at"),
                    row.get("status", "submitted"),
                    row.get("output_file"),
                    row.get("verified"),
                ),
            )
        conn.commit()
    finally:
        conn.close()


def _make_result(dir_: Path, name: str) -> Path:
    dir_.mkdir(parents=True, exist_ok=True)
    p = dir_ / name
    p.write_text("-- dummy result\n")
    return p


@pytest.fixture
def patched_submit_module(tmp_path, monkeypatch, mock_aristotlelib_module, import_patched_script):
    """Import safe_aristotle_submit with MATH_DIR redirected to tmp_path.

    The script reads MATH_DIR at module-import time, so we must redirect
    AFTER import (via monkeypatch.setattr). Returns (module, tmp_path).
    """
    _ensure_api_key()
    sas = import_patched_script("safe_aristotle_submit")
    monkeypatch.setattr(sas, "MATH_DIR", tmp_path)
    return sas, tmp_path


def test_problem_with_three_prior_advances_returns_three_files(patched_submit_module):
    """Three rows with status=compiled_advance|compiled_partial|disproven and
    valid output_file paths should all be attached, ordered most-recent-first."""
    sas, root = patched_submit_module
    results_dir = root / "submissions" / "results"
    f1 = _make_result(results_dir, "slot100_result.lean")
    f2 = _make_result(results_dir, "slot101_result.lean")
    f3 = _make_result(results_dir, "slot102_result.lean")

    _make_db(
        root / "submissions" / "tracking.db",
        [
            {"problem_id": "fooprob", "submitted_at": "2026-05-01", "status": "compiled_advance",  "output_file": str(f1)},
            {"problem_id": "fooprob", "submitted_at": "2026-05-02", "status": "compiled_partial",  "output_file": str(f2)},
            {"problem_id": "fooprob", "submitted_at": "2026-05-03", "status": "disproven",         "output_file": str(f3)},
        ],
    )

    paths = sas.gather_context("fooprob")
    assert len(paths) == 3
    # most-recent-first
    assert paths == [f3, f2, f1]


def test_problem_with_no_prior_returns_empty(patched_submit_module, capsys):
    """Problem id not present in DB returns empty list and prints no
    warning (since total prior count is 0)."""
    sas, root = patched_submit_module
    _make_db(root / "submissions" / "tracking.db", [])  # empty DB

    paths = sas.gather_context("unseen_problem")
    assert paths == []
    out = capsys.readouterr().out
    assert "0 artifacts attached" not in out


def test_problem_with_only_partial_advances(patched_submit_module):
    """Only compiled_partial rows present — all should be attached.

    This is the core regression test for the bug: pre-fix code filtered on
    statuses that never existed, so compiled_partial rows were dropped.
    """
    sas, root = patched_submit_module
    results_dir = root / "submissions" / "results"
    fa = _make_result(results_dir, "slotA_result.lean")
    fb = _make_result(results_dir, "slotB_result.lean")

    _make_db(
        root / "submissions" / "tracking.db",
        [
            {"problem_id": "barprob", "submitted_at": "2026-05-10", "status": "compiled_partial", "output_file": str(fa)},
            {"problem_id": "barprob", "submitted_at": "2026-05-11", "status": "compiled_partial", "output_file": str(fb)},
        ],
    )

    paths = sas.gather_context("barprob")
    assert len(paths) == 2
    assert set(paths) == {fa, fb}


def test_compile_failed_rows_excluded(patched_submit_module):
    """compile_failed rows must NOT be attached even if output_file is set
    (failed builds have no useful artifact)."""
    sas, root = patched_submit_module
    results_dir = root / "submissions" / "results"
    good = _make_result(results_dir, "good_result.lean")
    bad = _make_result(results_dir, "bad_result.lean")

    _make_db(
        root / "submissions" / "tracking.db",
        [
            {"problem_id": "mixed", "submitted_at": "2026-05-01", "status": "compile_failed",   "output_file": str(bad)},
            {"problem_id": "mixed", "submitted_at": "2026-05-02", "status": "compiled_advance", "output_file": str(good)},
        ],
    )

    paths = sas.gather_context("mixed")
    assert paths == [good]


def test_verified_zero_excluded(patched_submit_module):
    """Rows with verified=0 (explicitly invalid) are dropped; verified
    NULL or 1 are kept."""
    sas, root = patched_submit_module
    results_dir = root / "submissions" / "results"
    fok = _make_result(results_dir, "ok.lean")
    fbad = _make_result(results_dir, "verified_bad.lean")
    fpending = _make_result(results_dir, "pending.lean")

    _make_db(
        root / "submissions" / "tracking.db",
        [
            {"problem_id": "vtest", "submitted_at": "2026-05-01", "status": "compiled_advance", "output_file": str(fok),      "verified": 1},
            {"problem_id": "vtest", "submitted_at": "2026-05-02", "status": "compiled_advance", "output_file": str(fbad),     "verified": 0},
            {"problem_id": "vtest", "submitted_at": "2026-05-03", "status": "compiled_advance", "output_file": str(fpending), "verified": None},
        ],
    )

    paths = sas.gather_context("vtest")
    assert fok in paths
    assert fpending in paths
    assert fbad not in paths


def test_missing_files_on_disk_skipped(patched_submit_module, capsys):
    """DB rows whose output_file does not exist on disk are dropped, and a
    warning is printed."""
    sas, root = patched_submit_module
    results_dir = root / "submissions" / "results"
    real = _make_result(results_dir, "real.lean")
    ghost = results_dir / "ghost.lean"  # never created

    _make_db(
        root / "submissions" / "tracking.db",
        [
            {"problem_id": "ghosty", "submitted_at": "2026-05-01", "status": "compiled_advance", "output_file": str(real)},
            {"problem_id": "ghosty", "submitted_at": "2026-05-02", "status": "compiled_advance", "output_file": str(ghost)},
        ],
    )

    paths = sas.gather_context("ghosty")
    assert paths == [real]
    err = capsys.readouterr().out
    assert "missing on disk" in err


def test_warning_when_zero_artifacts_but_prior_submissions_exist(patched_submit_module, capsys):
    """The canary warning: if there are 0 attachable artifacts but >0 prior
    submissions, the function must print a visible warning. This is the
    pattern that hid the pre-fix bug for 1166 submissions."""
    sas, root = patched_submit_module

    _make_db(
        root / "submissions" / "tracking.db",
        [
            # 3 prior submissions, all compile_failed -> no artifacts to attach
            {"problem_id": "canary", "submitted_at": "2026-05-01", "status": "compile_failed", "output_file": None},
            {"problem_id": "canary", "submitted_at": "2026-05-02", "status": "compile_failed", "output_file": None},
            {"problem_id": "canary", "submitted_at": "2026-05-03", "status": "compile_failed", "output_file": None},
        ],
    )

    paths = sas.gather_context("canary")
    assert paths == []
    out = capsys.readouterr().out
    assert "0 artifacts attached" in out
    assert "3 prior submission" in out


def test_missing_db_returns_empty(patched_submit_module):
    """No tracking.db -> empty list, no exception."""
    sas, _root = patched_submit_module
    # MATH_DIR is set to tmp_path but we never created the DB
    paths = sas.gather_context("whatever")
    assert paths == []


def test_filename_match_works(patched_submit_module):
    """problem_id LIKE OR filename LIKE — match should fire on filename even
    if problem_id is NULL."""
    sas, root = patched_submit_module
    results_dir = root / "submissions" / "results"
    f = _make_result(results_dir, "slot500_erdos999_result.lean")

    _make_db(
        root / "submissions" / "tracking.db",
        [
            {"problem_id": None, "filename": "slot500_erdos999.txt",
             "submitted_at": "2026-05-01", "status": "compiled_partial", "output_file": str(f)},
        ],
    )

    paths = sas.gather_context("erdos999")
    assert paths == [f]


def test_verbose_prints_per_row_diagnostics(patched_submit_module, capsys):
    """--verbose-context flag should produce per-row attach/skip lines."""
    sas, root = patched_submit_module
    results_dir = root / "submissions" / "results"
    f = _make_result(results_dir, "v.lean")

    _make_db(
        root / "submissions" / "tracking.db",
        [
            {"problem_id": "vp", "submitted_at": "2026-05-01", "status": "compiled_advance", "output_file": str(f)},
        ],
    )

    paths = sas.gather_context("vp", verbose=True)
    assert paths == [f]
    out = capsys.readouterr().out
    assert "+attach" in out
    assert "compiled_advance" in out
