#!/usr/bin/env bats

load test_helper

setup() { setup_test_db; }
teardown() { teardown_test_db; }

@test "stats: shows finding counts" {
    run "$MK" stats
    [ "$status" -eq 0 ]
    assert_output_contains "theorem"
}

@test "stats: shows domain distribution" {
    run "$MK" stats
    [ "$status" -eq 0 ]
    assert_output_contains "nt"
}

@test "stats: shows total count" {
    run "$MK" stats
    [ "$status" -eq 0 ]
    assert_output_contains "Total findings"
}
