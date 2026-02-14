#!/usr/bin/env bats

load test_helper

setup() { setup_test_db; }
teardown() { teardown_test_db; }

@test "find: no args shows usage" {
    run "$MK" find
    [ "$status" -eq 1 ]
    assert_output_contains "Usage"
}

@test "find: shows problem summary" {
    run "$MK" find "ft_p3"
    [ "$status" -eq 0 ]
    assert_output_contains "ft_p3"
}

@test "find: shows findings for problem" {
    run "$MK" find "ft_p3"
    [ "$status" -eq 0 ]
    assert_output_contains "Findings"
}

@test "find: handles non-existent problem" {
    run "$MK" find "nonexistent_problem_xyz"
    [ "$status" -eq 0 ]
    assert_output_contains "No problem record"
}
