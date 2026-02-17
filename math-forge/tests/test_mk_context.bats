#!/usr/bin/env bats

load test_helper

setup() {
    # Create a temp directory structure for tracking.db
    TMPDIR_PROJ=$(mktemp -d /tmp/mf_ctx_XXXXXX)
    mkdir -p "$TMPDIR_PROJ/submissions"
    TRACKING="$TMPDIR_PROJ/submissions/tracking.db"
    sqlite3 "$TRACKING" "
        CREATE TABLE submissions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            uuid TEXT, filename TEXT NOT NULL, problem_id TEXT,
            submitted_at TEXT, status TEXT DEFAULT 'draft',
            sorry_count INTEGER, proven_count INTEGER,
            output_file TEXT, target_resolved INTEGER DEFAULT 0,
            gap_statement TEXT, submission_type TEXT, notes TEXT
        );
    "
    export CLAUDE_PROJECT_DIR="$TMPDIR_PROJ"
}

teardown() {
    rm -rf "$TMPDIR_PROJ"
    unset CLAUDE_PROJECT_DIR
}

@test "context: no args shows usage" {
    run "$MK" context
    [ "$status" -eq 1 ]
    assert_output_contains "Usage"
}

@test "context: with problem_id produces output" {
    # Should work even if no results found
    run "$MK" context "nonexistent_problem_xyz"
    [ "$status" -eq 0 ]
    assert_output_contains "Context files"
}

@test "context: handles real problem query" {
    run "$MK" context "erdos"
    [ "$status" -eq 0 ]
    assert_output_contains "Context files"
}
