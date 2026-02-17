#!/usr/bin/env bats

load test_helper

setup() {
    # Create a temp directory structure for tracking.db
    TMPDIR_PROJ=$(mktemp -d /tmp/mf_gaps_XXXXXX)
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
        INSERT INTO submissions (filename, problem_id, status, submission_type, gap_statement, target_resolved, submitted_at)
        VALUES
        ('slot700_test.txt', 'test_prob', 'compiled_clean', 'gap_targeting', 'Test gap statement', 0, datetime('now')),
        ('slot701_test.txt', 'test_prob', 'near_miss', 'gap_targeting', 'Test gap statement', 0, datetime('now'));
    "
    export CLAUDE_PROJECT_DIR="$TMPDIR_PROJ"
}

teardown() {
    rm -rf "$TMPDIR_PROJ"
    unset CLAUDE_PROJECT_DIR
}

@test "gaps: shows header" {
    run "$MK" gaps
    [ "$status" -eq 0 ]
    assert_output_contains "Open Gaps"
}

@test "gaps: shows resolved count" {
    run "$MK" gaps
    [ "$status" -eq 0 ]
    assert_output_contains "Gaps resolved"
}
