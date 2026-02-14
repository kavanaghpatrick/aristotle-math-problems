#!/usr/bin/env bats

load test_helper

HOOK="${PLUGIN_ROOT}/hooks/scripts/lean-validator.sh"

@test "lean-validator: non-lean file passes through" {
    run bash -c 'echo "{\"tool_input\":{\"file_path\":\"test.py\"}}" | bash '"$HOOK"
    [ "$status" -eq 0 ]
    [ -z "$output" ]
}

@test "lean-validator: lean file without sorry passes" {
    local tmpfile=$(mktemp /tmp/test_XXXXXX.lean)
    echo "theorem test : 1 = 1 := by rfl" > "$tmpfile"
    run bash -c 'echo "{\"tool_input\":{\"file_path\":\"'"$tmpfile"'\"},\"tool_name\":\"Write\"}" | bash '"$HOOK"
    [ "$status" -eq 0 ]
    rm -f "$tmpfile"
}

@test "lean-validator: blocks sorry replacement" {
    local tmpfile=$(mktemp /tmp/test_XXXXXX.lean)
    echo "theorem test : 1 + 1 = 2 := by omega" > "$tmpfile"
    run bash -c 'echo "{\"tool_input\":{\"file_path\":\"'"$tmpfile"'\",\"old_string\":\"by omega\",\"new_string\":\"by sorry\"},\"tool_name\":\"Edit\"}" | bash '"$HOOK"
    [ "$status" -eq 0 ]
    assert_output_contains "block"
    rm -f "$tmpfile"
}

@test "lean-validator: missing file exits cleanly" {
    run bash -c 'echo "{\"tool_input\":{\"file_path\":\"/nonexistent/path.lean\"}}" | bash '"$HOOK"
    [ "$status" -eq 0 ]
}
