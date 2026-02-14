#!/usr/bin/env bats

load test_helper

setup() { setup_test_db; }
teardown() { teardown_test_db; }

# Golden queries test FTS5 relevance — these must return expected results

@test "golden: 'cubic residue' finds FT p=3 theorem" {
    run "$MK" search "cubic residue"
    [ "$status" -eq 0 ]
    assert_output_contains "cubic"
}

@test "golden: 'Euler criterion' finds technique" {
    run "$MK" search "Euler criterion"
    [ "$status" -eq 0 ]
    assert_output_contains "Euler"
}

@test "golden: 'smooth consecutive' finds Erdos 370" {
    run "$MK" search "smooth consecutive"
    [ "$status" -eq 0 ]
    assert_output_contains "smooth"
}

@test "golden: 'apex' finds false lemma" {
    run "$MK" search "apex"
    [ "$status" -eq 0 ]
    assert_output_contains "FALSE"
}

@test "golden: 'quartic' finds mod 12 theorem" {
    run "$MK" search "quartic"
    [ "$status" -eq 0 ]
    assert_output_contains "12"
}

@test "golden: failed command finds failures" {
    run "$MK" failed "apex"
    [ "$status" -eq 0 ]
    assert_output_contains "apex"
}

@test "golden: strategies shows proven techniques" {
    run "$MK" strategies
    [ "$status" -eq 0 ]
    assert_output_contains "Euler criterion"
}

@test "golden: find shows problem dashboard" {
    run "$MK" find "tuza"
    [ "$status" -eq 0 ]
    assert_output_contains "tuza"
}
