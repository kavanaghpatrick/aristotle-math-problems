#!/usr/bin/env bats

load test_helper

HOOK="${PLUGIN_ROOT}/hooks/scripts/context-loader.sh"

@test "context-loader: outputs valid JSON" {
    run bash "$HOOK"
    [ "$status" -eq 0 ]
    echo "$output" | python3 -c "import json,sys; json.load(sys.stdin)"
}

@test "context-loader: has hookSpecificOutput" {
    run bash "$HOOK"
    [ "$status" -eq 0 ]
    echo "$output" | python3 -c "import json,sys; d=json.load(sys.stdin); assert 'hookSpecificOutput' in d"
}

@test "context-loader: has additionalContext" {
    run bash "$HOOK"
    [ "$status" -eq 0 ]
    echo "$output" | python3 -c "import json,sys; d=json.load(sys.stdin); assert 'additionalContext' in d['hookSpecificOutput']"
}

@test "context-loader: briefing contains math-forge header" {
    run bash "$HOOK"
    [ "$status" -eq 0 ]
    echo "$output" | python3 -c "import json,sys; d=json.load(sys.stdin); assert '[math-forge]' in d['hookSpecificOutput']['additionalContext']"
}
