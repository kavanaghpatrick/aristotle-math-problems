#!/usr/bin/env bats

load test_helper

setup() { setup_test_db; }
teardown() { teardown_test_db; }

@test "search: no args shows usage" {
    run "$MK" search
    [ "$status" -eq 1 ]
    assert_output_contains "Usage"
}

@test "search: finds theorem by keyword" {
    run "$MK" search "cubic"
    [ "$status" -eq 0 ]
    assert_output_contains "cubic"
}

@test "search: finds false lemma by keyword" {
    run "$MK" search "apex"
    [ "$status" -eq 0 ]
    assert_output_contains "FALSE"
}

@test "search: no results message" {
    run "$MK" search "nonexistent_xyzzy_12345"
    [ "$status" -eq 0 ]
    assert_output_contains "No findings"
}

@test "search: --limit flag works" {
    run "$MK" search "theorem" --limit 2
    [ "$status" -eq 0 ]
}

@test "search: --domain filter works" {
    run "$MK" search "residue" --domain nt
    [ "$status" -eq 0 ]
}
