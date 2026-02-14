#!/usr/bin/env bash
# Test helper for math-forge BATS tests

# Paths
export PLUGIN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export MK="$PLUGIN_ROOT/scripts/mk"
export SCHEMA="$PLUGIN_ROOT/data/schema.sql"
export TEST_DB=""
export FIXTURES="$PLUGIN_ROOT/tests/fixtures"

# Setup: create temp test DB with sample data
setup_test_db() {
    TEST_DB="$(mktemp /tmp/mf_test_XXXXXX.db)"
    export MATH_FORGE_DB="$TEST_DB"

    # Initialize from schema
    sqlite3 "$TEST_DB" < "$SCHEMA"

    # Insert sample findings
    sqlite3 "$TEST_DB" "
        INSERT INTO findings (finding_type, domain_id, title, description, problem_id, source_slot, theorem_name, theorem_statement, proof_technique, confidence, tags)
        VALUES
        ('theorem', 'nt', 'Euler criterion for cubic residues', 'Proven theorem about cubic residue characterization', 'ft_p3', 612, 'euler_cubic', 'a^((p-1)/3) ≡ 1 mod p', 'Euler criterion', 'verified', 'nt,cubic'),
        ('theorem', 'nt', 'Quartic residue A mod 12', 'A ≡ 1 mod 12 for FT p=3', 'ft_p3', 612, 'A_mod_12', 'A ≡ 1 (mod 12)', 'modular arithmetic', 'verified', 'nt,quartic'),
        ('failure', 'nt', 'FAILED: Kummer symbol approach', 'Circular: 3^(q+1)=3 iff 3^q=1', 'ft_p3_q71mod72', NULL, NULL, NULL, NULL, 'high', 'failure,circular'),
        ('false_lemma', 'combinatorics', 'FALSE: apex disjoint triangles', 'Counterexample on Fin 6', 'tuza_nu4', NULL, NULL, NULL, NULL, 'disproven', 'false_lemma'),
        ('technique', 'nt', 'Technique: native_decide for bounded', 'Used in slot596 for bounded verification', 'ft_p3', 596, NULL, NULL, 'finite computation (native_decide)', 'verified', 'technique'),
        ('theorem', 'combinatorics', 'Erdos 370 smooth consecutive', 'First-ever proof of smooth consecutive integers', 'erdos_370', 616, 'smooth_consecutive', 'exists smooth consecutive', 'pigeonhole', 'verified', 'combinatorics,erdos'),
        ('insight', 'nt', 'FT p=3 q≡71mod72 hardest case', 'All multiplicative characters trivially 1', 'ft_p3_q71mod72', NULL, NULL, NULL, NULL, 'high', 'insight'),
        ('theorem', 'algebra', 'Wolstenholme theorem', 'Binomial coefficient divisibility', 'wolstenholme', 594, 'wolstenholme_main', 'p^2 | C(2p,p)-2', 'modular arithmetic', 'verified', 'algebra,wolstenholme');
    "

    # Insert sample strategies
    sqlite3 "$TEST_DB" "
        INSERT INTO strategies (problem_id, problem_name, domain_id, approach_name, outcome, submission_slot, learned)
        VALUES
        ('ft_p3', 'Feit-Thompson p=3', 'nt', 'QR + Euler criterion', 'proven', 590, 'Works for q≡1mod4'),
        ('ft_p3', 'Feit-Thompson p=3', 'nt', 'Kummer symbol', 'failed', NULL, 'Circular argument'),
        ('tuza_nu4', 'Tuza nu=4', 'combinatorics', 'Apex-based coverage', 'failed', NULL, 'Negated by counterexample');
    "

    # Insert sample problems
    sqlite3 "$TEST_DB" "
        INSERT INTO problems (id, name, domain_id, status, submission_count, proven_count, failed_count)
        VALUES
        ('ft_p3', 'Feit-Thompson p=3', 'nt', 'partial', 20, 16, 3),
        ('tuza_nu4', 'Tuza conjecture nu=4', 'combinatorics', 'open', 50, 5, 12),
        ('erdos_370', 'Erdos 370', 'nt', 'proven', 2, 1, 0);
    "
}

# Teardown: clean up test DB
teardown_test_db() {
    [ -n "$TEST_DB" ] && rm -f "$TEST_DB"
    unset MATH_FORGE_DB
}

# Assertion helpers (in case bats-assert is not installed)
assert_output_contains() {
    local expected="$1"
    if ! echo "$output" | grep -q "$expected"; then
        echo "Expected output to contain: $expected"
        echo "Actual output: $output"
        return 1
    fi
}

assert_success() {
    if [ "$status" -ne 0 ]; then
        echo "Expected success (exit 0), got exit $status"
        echo "Output: $output"
        return 1
    fi
}

assert_failure() {
    if [ "$status" -eq 0 ]; then
        echo "Expected failure (exit != 0), got exit 0"
        echo "Output: $output"
        return 1
    fi
}
