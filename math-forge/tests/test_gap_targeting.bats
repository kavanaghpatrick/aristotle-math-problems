#!/usr/bin/env bats

load test_helper

HOOK="${BATS_TEST_DIRNAME}/../hooks/scripts/lean-validator.sh"

@test "lean-validator: warns on strategy keywords in sketch" {
    local tmpfile=$(mktemp /tmp/slot999_sketch_XXXXXX.txt)
    printf '## Proof Strategy\nApproach 1: by induction\nKey Lemma: foo\n' > "$tmpfile"
    run bash -c "echo '{\"tool_input\":{\"file_path\":\"$tmpfile\"},\"tool_name\":\"Write\"}' | bash $HOOK"
    [ "$status" -eq 0 ]
    assert_output_contains "WARNING"
    rm -f "$tmpfile"
}

@test "lean-validator: passes clean bare-gap sketch" {
    local tmpfile=$(mktemp /tmp/slot999_sketch_XXXXXX.txt)
    printf 'OPEN GAP: Test Problem\nEvery odd n > 1 is the sum of a squarefree and a power of 2.\nStatus: OPEN.\n' > "$tmpfile"
    run bash -c "echo '{\"tool_input\":{\"file_path\":\"$tmpfile\"},\"tool_name\":\"Write\"}' | bash $HOOK"
    [ "$status" -eq 0 ]
    # Should NOT contain warning for a clean sketch
    if [[ "$output" == *"WARNING"* ]]; then
        echo "Unexpected WARNING for clean sketch"
        return 1
    fi
    rm -f "$tmpfile"
}

@test "lean-validator: warns on >30 line sketch" {
    local tmpfile=$(mktemp /tmp/slot999_sketch_XXXXXX.txt)
    for i in $(seq 1 35); do
        echo "Line $i of the sketch content" >> "$tmpfile"
    done
    run bash -c "echo '{\"tool_input\":{\"file_path\":\"$tmpfile\"},\"tool_name\":\"Write\"}' | bash $HOOK"
    [ "$status" -eq 0 ]
    assert_output_contains "WARNING"
    assert_output_contains "lines"
    rm -f "$tmpfile"
}
