#!/bin/bash
# Definition audit for common Lean formalization bugs
# Usage: ./scripts/audit_definitions.sh submissions/problem.lean

set -euo pipefail

FILE="$1"
ERRORS=0
WARNINGS=0

# Use grep for better compatibility (rg might be aliased in interactive shells)
# Note: Users should have grep available on all Unix systems

echo "=== Definition Audit ==="
echo "File: $FILE"
echo

# Check for sInf without edge restriction
echo "Checking for unrestricted sInf definitions..."
if grep -q "sInf.*Finset.*Sym2\|sInf.*Sym2.*Finset" "$FILE"; then
    # Check if it has proper restriction
    if ! grep -q "⊆ G\.edgeFinset\|G\.edgeFinset\.powerset" "$FILE"; then
        echo "❌ CRITICAL: sInf definition without edge restriction"
        echo "   Lines with sInf over Sym2:"
        grep -n "sInf.*Sym2" "$FILE" || true
        echo
        echo "   REQUIRED: Edges must be restricted to G.edgeFinset"
        echo "   Either add 'E ⊆ G.edgeFinset' to predicate,"
        echo "   or use 'G.edgeFinset.powerset.filter ...'"
        ERRORS=$((ERRORS + 1))
    else
        echo "✅ sInf definitions appear restricted to graph edges"
    fi
else
    echo "✅ No sInf definitions found (or not over Sym2)"
fi

# Check for Finset.sym2 usage
echo
echo "Checking for Finset.sym2 usage..."
if grep -q "\.sym2[^.]" "$FILE"; then
    echo "⚠️  WARNING: Uses Finset.sym2 (includes self-loops s(v,v))"
    echo "   Lines using .sym2:"
    grep -n "\.sym2" "$FILE" || true
    echo
    echo "   REMINDER: Finset.sym2 includes diagonal pairs"
    echo "   For triangle edges, use: t.offDiag.image (fun x => Sym2.mk (x.1, x.2))"
    echo "   If self-loops are intended, this is OK."
    WARNINGS=$((WARNINGS + 1))
else
    echo "✅ No Finset.sym2 usage found"
fi

# Check for Set V in decidability contexts
echo
echo "Checking for Set/Finset type issues..."
if grep -q "Set V.*induce\|induce.*Set V" "$FILE"; then
    if ! grep -q "DecidablePred" "$FILE"; then
        echo "⚠️  WARNING: Set V used with induce, no DecidablePred instance visible"
        echo "   Consider using Finset V instead for automatic decidability"
        WARNINGS=$((WARNINGS + 1))
    else
        echo "✅ DecidablePred instance found for Set V usage"
    fi
else
    echo "✅ No problematic Set V usage found"
fi

# Check for required instances in graph theorems
echo
echo "Checking for required instances..."
if grep -q "SimpleGraph V" "$FILE"; then
    MISSING=()
    if ! grep -q "\[DecidableRel G\.Adj\]" "$FILE"; then
        MISSING+=("DecidableRel G.Adj")
    fi

    if [[ ${#MISSING[@]} -gt 0 ]]; then
        echo "⚠️  WARNING: Graph operations may need: ${MISSING[*]}"
        WARNINGS=$((WARNINGS + 1))
    else
        echo "✅ DecidableRel instance found"
    fi
fi

# Check for axiom usage (should never be present in submissions)
echo
echo "Checking for forbidden constructs..."
if grep -q "^axiom \|^ *axiom " "$FILE"; then
    echo "❌ CRITICAL: File contains 'axiom' declarations"
    echo "   Axioms are forbidden in submissions"
    grep -n "axiom" "$FILE" || true
    ERRORS=$((ERRORS + 1))
else
    echo "✅ No axiom declarations"
fi

# Summary
echo
echo "=== Audit Summary ==="
echo "Critical errors: $ERRORS"
echo "Warnings: $WARNINGS"

if [[ $ERRORS -gt 0 ]]; then
    echo
    echo "❌ AUDIT FAILED: $ERRORS critical issue(s) found"
    echo "   DO NOT SUBMIT until fixed"
    exit 1
elif [[ $WARNINGS -gt 0 ]]; then
    echo
    echo "⚠️  AUDIT PASSED with warnings"
    echo "   Review warnings before submission"
    exit 0
else
    echo
    echo "✅ AUDIT PASSED: No issues found"
    exit 0
fi
