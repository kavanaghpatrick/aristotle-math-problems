#!/usr/bin/env bats

load test_helper

@test "help: shows usage" {
    run "$MK" help
    [ "$status" -eq 0 ]
    assert_output_contains "search"
    assert_output_contains "find"
    assert_output_contains "stats"
    assert_output_contains "context"
    assert_output_contains "gaps"
}

@test "no args: shows help" {
    run "$MK"
    [ "$status" -eq 0 ]
    assert_output_contains "search"
}

@test "init: creates DB from schema" {
    local tmpdb=$(mktemp /tmp/mf_init_XXXXXX.db)
    rm -f "$tmpdb"
    MATH_FORGE_DB="$tmpdb" run "$MK" init
    [ "$status" -eq 0 ]
    [ -f "$tmpdb" ]
    rm -f "$tmpdb"
}
