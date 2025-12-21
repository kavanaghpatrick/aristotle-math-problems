# Lean Theorem Proving Verification Workflow

**Version**: 1.1
**Date**: December 20, 2025
**Status**: Production

---

## Quick Start

```bash
# Unified CLI for all workflow commands
python3 scripts/workflow.py validate submissions/file.lean    # Pre-submission validation
python3 scripts/workflow.py audit submissions/file.lean       # Multi-agent audit (Grok + Gemini)
python3 scripts/workflow.py submit submissions/file.lean      # Full submission workflow
python3 scripts/workflow.py verify submissions/output/X.lean  # Verify Aristotle output
python3 scripts/workflow.py status                            # Show current submissions
python3 scripts/workflow.py history                           # Show submission history
```

---

## Overview

This workflow prevents formalization bugs, definition errors, and invalid proofs through rigorous multi-stage verification before and after Aristotle submission.

### Key Lessons from Discovered Bugs

| Bug | Impact | Files Affected |
|-----|--------|----------------|
| **Erdős #128 formalization** | Missing `+1` in threshold | 1 invalid counterexample claim |
| **sInf unrestricted edges** | Allows non-graph edges | 16 corrupted files |
| **Finset.sym2 self-loops** | Invalid self-loop covering | ν=2 "proven" invalidated |
| **Definition contamination** | Wrong definitions propagated | 16+ submissions |

**Cost**: ~40 Aristotle job slots wasted, weeks of incorrect work

---

## Phase 1: Pre-Submission Validation

### 1.1 Syntax and Type Checking

**Run BEFORE every Aristotle submission.**

```bash
# Single file validation
lake env lean submissions/problem.lean

# Batch validation script
./scripts/validate_submission.sh submissions/problem.lean
```

**Expected output**:
```
warning: declaration uses 'sorry'  ← OK (Aristotle fills these)
```

**Failure indicators** (DO NOT SUBMIT):
```
error: unexpected token...
error: unknown identifier...
error: type mismatch...
error: application type mismatch...
```

#### Validation Checklist

- [ ] File compiles without syntax errors
- [ ] All imports resolve
- [ ] No unknown identifiers
- [ ] No type mismatches
- [ ] Only `sorry` warnings present
- [ ] Required instances declared (`Fintype`, `DecidableEq`, `DecidableRel`)

### 1.2 Definition Audit (CRITICAL)

**Run for ANY file defining `coveringNumber`, `packingNumber`, or graph structures.**

#### Audit Checklist: Triangle Covering

```lean
-- WRONG: Allows arbitrary edge sets
def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ IsTriangleCover G E}

-- RIGHT: Restricted to graph edges
def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (IsTriangleCover G)
    |>.image Finset.card
    |>.min
    |>.getD G.edgeFinset.card
```

**Red flags**:
- `sInf {n : ℕ | ∃ E : Finset (Sym2 V), ...}` without `E ⊆ G.edgeFinset`
- Using `Finset.sym2` without filtering self-loops
- Existential definitions over arbitrary sets
- Missing edge restriction in covering predicates

#### Audit Checklist: Set vs Finset

```lean
-- WRONG: Set requires DecidablePred instance
def foo (G : SimpleGraph V) (S : Set V) :=
  (G.induce S).edgeFinset  -- Fails without DecidablePred

-- RIGHT: Use Finset for decidability
def foo (G : SimpleGraph V) (S : Finset V) :=
  (G.induce S).edgeFinset  -- Works with Fintype + DecidableEq
```

**Red flags**:
- `Set V` in contexts requiring decidability
- Missing `DecidablePred (· ∈ S)` instance
- `{x | P}` without providing decidability

#### Audit Checklist: Sym2 Self-Loops

```lean
-- Verification: Does sym2 include diagonals?
#eval ({1, 2, 3} : Finset ℕ).sym2
-- Output: {s(1,1), s(1,2), s(1,3), s(2,2), s(2,3), s(3,3)}
--         ^^^^^^         ^^^^^^         ^^^^^^ SELF-LOOPS!

-- WRONG: Includes self-loops
def triangleEdges (t : Finset V) : Finset (Sym2 V) := t.sym2

-- RIGHT: Only off-diagonal pairs
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))
```

**Red flags**:
- Using `Finset.sym2` directly for edge sets
- Not filtering `s(v, v)` self-loops
- Assuming `triangleEdges` excludes diagonals

### 1.3 Formalization Verification Against Source

**Run for ALL Erdős problems or published theorems.**

#### Comparison Protocol

1. **Locate original source**
   - Erdős problems: https://erdosproblems.com/
   - Papers: Original publication (arXiv, journal)
   - Formal Conjectures: https://github.com/google-deepmind/formal-conjectures

2. **Compare quantifiers and thresholds**

   | Original English | Correct Lean | Wrong Lean |
   |-----------------|--------------|------------|
   | "≥ n/2 vertices" | `2 * S.ncard + 1 ≥ n` | `2 * S.ncard ≥ n` |
   | "< k edges" | `E.card < k` | `E.card ≤ k` |
   | "at most m" | `x ≤ m` | `x < m + 1` |

3. **Test edge cases manually**
   ```python
   # For n=5, "≥ n/2 vertices"
   # WRONG: 2*|S| ≥ 5 → |S| ≥ 3
   # RIGHT: 2*|S|+1 ≥ 5 → |S| ≥ 2
   ```

4. **Check against Formal Conjectures**
   ```bash
   # Download FC formalization
   curl https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/128.lean

   # Compare side-by-side
   diff -u submissions/erdos128.lean FC_erdos128.lean
   ```

#### Formalization Checklist

- [ ] Original problem statement located
- [ ] All quantifiers match (∀, ∃, ≥, >, etc.)
- [ ] Thresholds match for small n (test n=3,4,5)
- [ ] Floor vs ceiling correct
- [ ] Strict vs non-strict inequalities correct
- [ ] If FC exists, our formalization matches or justification documented

### 1.4 Multi-Agent Pre-Review (Optional for $250+ problems)

**When to use**: High-value targets, complex formalizations, novel definitions

#### Grok-4 Review (Syntax & Definition Bugs)

```bash
# System prompt
SYSTEM="Lean 4 syntax checker. DO NOT solve math. ONLY check:
1. Syntax errors
2. Definition bugs (sInf unrestricted, sym2 self-loops, Set/Finset)
3. Missing instances (Fintype, DecidableEq, DecidableRel)
4. Type errors
Output ONLY errors found, or 'CLEAN' if none."

# Create request
python3 << 'EOF'
import json
code = open('submissions/problem.lean').read()
req = {
    "messages": [
        {"role": "system", "content": "$SYSTEM"},
        {"role": "user", "content": f"Check this Lean code:\n\n{code}"}
    ],
    "model": "grok-beta",
    "temperature": 0,
    "max_tokens": 1000
}
json.dump(req, open('/tmp/grok_syntax.json', 'w'))
EOF

curl -X POST https://api.x.ai/v1/chat/completions \
  -H "Authorization: Bearer $GROK_API_KEY" \
  -H "Content-Type: application/json" \
  -d @/tmp/grok_syntax.json \
  --max-time 180
```

**Grok checks**:
- Missing edge restriction in `sInf` definitions
- `Finset.sym2` used without filtering
- Set/Finset type mismatches
- Missing decidability instances

#### Gemini Review (Formalization Correctness)

```bash
gemini -p "Compare this Lean formalization to the original problem:

ORIGINAL: [paste erdosproblems.com statement]

LEAN: $(cat submissions/problem.lean)

Check:
1. Are quantifiers (∀, ∃, ≥) correct?
2. Are thresholds (⌊n/2⌋ vs ⌈n/2⌉) correct?
3. Test for n=3,4,5: do conditions match?
4. Any missing or extra hypotheses?"
```

**Gemini checks**:
- Mathematical correctness of formalization
- Threshold and boundary conditions
- Missing hypotheses from original problem

---

## Phase 2: Submission Tracking

### 2.1 Submission Database Schema

**Location**: `submissions/tracking.db` (SQLite)

```sql
CREATE TABLE submissions (
    uuid TEXT PRIMARY KEY,
    filename TEXT NOT NULL,
    submission_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    problem_id TEXT,  -- e.g., 'erdos128', 'tuza_nu4'
    status TEXT CHECK(status IN ('queued', 'running', 'completed', 'failed', 'timeout')),
    pattern TEXT,  -- 'boris_minimal', 'scaffolded', 'prescriptive'
    validation_passed BOOLEAN DEFAULT 0,
    definitions_audited BOOLEAN DEFAULT 0,
    formalization_verified BOOLEAN DEFAULT 0,
    runtime_seconds INTEGER,
    result_file TEXT,
    notes TEXT
);

CREATE TABLE definitions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    submission_uuid TEXT REFERENCES submissions(uuid),
    definition_name TEXT,  -- e.g., 'coveringNumber', 'triangleEdges'
    definition_type TEXT,  -- 'correct', 'sInf_unrestricted', 'sym2_selfloop', 'set_finset'
    line_number INTEGER,
    audit_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(submission_uuid, definition_name)
);

CREATE TABLE proof_claims (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    submission_uuid TEXT REFERENCES submissions(uuid),
    theorem_name TEXT,
    claim_status TEXT CHECK(claim_status IN ('proven', 'partial', 'sorry', 'contaminated')),
    verification_status TEXT CHECK(verification_status IN ('pending', 'verified', 'invalid')),
    sorry_count INTEGER DEFAULT 0,
    verification_date TIMESTAMP,
    invalidation_reason TEXT,
    UNIQUE(submission_uuid, theorem_name)
);

CREATE TABLE definition_contamination (
    source_uuid TEXT REFERENCES submissions(uuid),
    target_uuid TEXT REFERENCES submissions(uuid),
    contaminated_definition TEXT,
    discovered_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    PRIMARY KEY(source_uuid, target_uuid, contaminated_definition)
);

CREATE INDEX idx_status ON submissions(status);
CREATE INDEX idx_problem ON submissions(problem_id);
CREATE INDEX idx_verification ON proof_claims(verification_status);
```

### 2.2 Pre-Submission Recording

```bash
# Record submission (before aristotle call)
./scripts/track_submission.sh submissions/problem.lean "erdos128" "boris_minimal"

# Output:
# Validation: PASSED
# Definitions audited: YES (2 definitions, all correct)
# Formalization verified: YES (matches FC)
# UUID: abc123...
# Safe to submit.

# Then submit
aristotle prove-from-file submissions/problem.lean --no-wait
```

### 2.3 Status Monitoring

```bash
# Update status from Aristotle
./scripts/update_status.sh

# Check current portfolio
sqlite3 submissions/tracking.db << EOF
SELECT filename, status, pattern, runtime_seconds
FROM submissions
WHERE status IN ('queued', 'running')
ORDER BY submission_date DESC;
EOF
```

---

## Phase 3: Post-Submission Verification

### 3.1 Aristotle Output Retrieval

```bash
# Download output
aristotle status <UUID> > submissions/output/<UUID>.lean

# Record in database
./scripts/record_output.sh <UUID> submissions/output/<UUID>.lean
```

### 3.2 Sorry Detection (CRITICAL)

**All "proven" files MUST be scanned for buried sorry.**

```bash
# Scan for sorry statements
rg --count-matches "sorry" submissions/output/<UUID>.lean

# If count > 0:
rg -n "sorry" submissions/output/<UUID>.lean
```

**Classification**:

| Sorry Context | Status | Action |
|---------------|--------|--------|
| Main theorem only | Expected | Aristotle didn't solve |
| Helper lemmas only | Partial | Extract proven parts |
| No sorry at all | **VERIFY** | Deep verification required |
| Buried in proof | **CONTAMINATED** | Mark as invalid |

### 3.3 Deep Verification Protocol

**Run for ALL outputs claiming "no sorry".**

#### Step 1: Lean Compilation

```bash
# Copy to test directory
cp submissions/output/<UUID>.lean test/verify_<UUID>.lean

# Compile independently
lake env lean test/verify_<UUID>.lean

# Must show ZERO errors and ZERO warnings
```

#### Step 2: Definition Re-Audit

```bash
# Extract all definitions from output
rg "^def |^structure |^class " submissions/output/<UUID>.lean

# Run full Definition Audit (Section 1.2) on each
./scripts/audit_definitions.sh submissions/output/<UUID>.lean
```

**Red flags in Aristotle output**:
- New definitions using `sInf` without restriction
- Introduced `Finset.sym2` without filtering
- Changed existing definitions subtly

#### Step 3: Proof Structure Analysis

```bash
# Check proof uses only valid tactics
rg "axiom |admit |sorry" submissions/output/<UUID>.lean

# Verify no circular dependencies
./scripts/check_circular.sh submissions/output/<UUID>.lean
```

#### Step 4: Multi-Agent Verification (High-Value Only)

**Grok-4: Critical Issues**

```bash
SYSTEM="Lean proof verifier. Check for CRITICAL issues ONLY:
1. Uses 'axiom' (forbidden)
2. Uses 'sorry' (incomplete)
3. Circular reasoning
4. Self-loops in edge sets
5. Arbitrary edge sets not restricted to G.edgeFinset
Output ONLY critical issues or 'CLEAN'."

python3 << 'EOF'
import json
code = open('submissions/output/<UUID>.lean').read()
req = {
    "messages": [
        {"role": "system", "content": "$SYSTEM"},
        {"role": "user", "content": f"Verify:\n\n{code}"}
    ],
    "model": "grok-beta",
    "temperature": 0
}
json.dump(req, open('/tmp/grok_verify.json', 'w'))
EOF

curl -X POST https://api.x.ai/v1/chat/completions \
  -H "Authorization: Bearer $GROK_API_KEY" \
  -H "Content-Type: application/json" \
  -d @/tmp/grok_verify.json \
  --max-time 300
```

**Gemini: Proof Validity**

```bash
gemini -p "Analyze this Lean proof for mathematical validity:

$(cat submissions/output/<UUID>.lean)

Questions:
1. Does the proof actually establish the claimed theorem?
2. Are all helper lemmas used correctly?
3. Are there any hidden assumptions or axioms?
4. Does the proof match the original problem formulation?
5. For graph problems: Are edge sets restricted to G.edgeFinset?"
```

### 3.4 Contamination Tracing

**Run when a bug is discovered in a "proven" file.**

#### Backward Trace: Where Did This Come From?

```bash
# Find files with matching definitions
rg -l "def coveringNumber.*sInf" submissions/*.lean

# Check git history
git log --all --full-history -- submissions/*contaminated_def*.lean

# Record contamination
sqlite3 submissions/tracking.db << EOF
INSERT INTO definition_contamination (source_uuid, target_uuid, contaminated_definition)
VALUES ('source_uuid', 'affected_uuid', 'coveringNumber');
EOF
```

#### Forward Trace: What Did This Contaminate?

```bash
# Find all files copying this definition
./scripts/find_contaminated.sh "coveringNumber" "sInf.*Finset.*Sym2"

# Mark all as contaminated
./scripts/mark_contaminated.sh <list_of_uuids> "sInf unrestricted edges"
```

#### Quarantine Protocol

```bash
# Move contaminated files
mkdir -p submissions/CORRUPTED
mv submissions/<contaminated>.lean submissions/CORRUPTED/

# Update database
sqlite3 submissions/tracking.db << EOF
UPDATE proof_claims
SET claim_status = 'contaminated',
    verification_status = 'invalid',
    invalidation_reason = 'Definition bug: sInf unrestricted'
WHERE submission_uuid IN (SELECT uuid FROM submissions WHERE filename LIKE '%contaminated%');
EOF
```

---

## Phase 4: Proof Portfolio Verification

### 4.1 Cross-File Consistency Check

**Run when multiple files claim to prove related theorems.**

```bash
# Extract all theorem statements
./scripts/extract_theorems.sh submissions/tuza_*.lean > /tmp/tuza_theorems.txt

# Check for contradictions
./scripts/check_contradictions.sh /tmp/tuza_theorems.txt
```

**Red flags**:
- Same theorem proven differently with different results
- Lemma X proven in file A, but assumed axiom in file B
- Contradictory bounds (τ ≤ 6 vs τ ≤ 8)

### 4.2 Dependency Graph Analysis

```bash
# Build dependency graph
./scripts/build_dep_graph.sh submissions/*.lean > deps.dot
dot -Tpng deps.dot -o deps.png

# Check for cycles
./scripts/detect_cycles.sh deps.dot
```

**Valid dependency patterns**:
- Base cases → Inductive cases
- Proven lemmas → Main theorems
- Infrastructure → Specific problems

**Invalid patterns**:
- Circular: A depends on B depends on A
- Contaminated → Clean (must break dependency)
- Unverified assumptions in critical path

---

## Automated Workflow Scripts

### validate_submission.sh

```bash
#!/bin/bash
# Usage: ./scripts/validate_submission.sh submissions/problem.lean

FILE="$1"
if [[ ! -f "$FILE" ]]; then
    echo "Error: File not found: $FILE"
    exit 1
fi

echo "=== Pre-Submission Validation ==="
echo "File: $FILE"
echo

# 1. Syntax check
echo "1. Syntax and type checking..."
if lake env lean "$FILE" 2>&1 | grep -v "warning: declaration uses 'sorry'" | grep -q "error:"; then
    echo "❌ FAILED: Syntax/type errors found"
    lake env lean "$FILE" 2>&1 | grep "error:"
    exit 1
else
    echo "✅ PASSED: No syntax errors"
fi

# 2. Definition audit
echo
echo "2. Definition audit..."
AUDIT_RESULT=$(./scripts/audit_definitions.sh "$FILE")
if echo "$AUDIT_RESULT" | grep -q "CRITICAL"; then
    echo "❌ FAILED: Critical definition bugs found"
    echo "$AUDIT_RESULT"
    exit 1
else
    echo "✅ PASSED: Definitions clean"
fi

# 3. Sorry count
echo
echo "3. Sorry count..."
SORRY_COUNT=$(rg -c "sorry" "$FILE" || echo "0")
echo "Found $SORRY_COUNT sorry statements (expected for submission)"

echo
echo "=== SAFE TO SUBMIT ==="
exit 0
```

### audit_definitions.sh

```bash
#!/bin/bash
# Usage: ./scripts/audit_definitions.sh submissions/problem.lean

FILE="$1"
ERRORS=0

echo "=== Definition Audit ==="

# Check for sInf without edge restriction
if rg -q "sInf.*Finset.*Sym2" "$FILE" && ! rg -q "⊆ G.edgeFinset|G.edgeFinset.powerset" "$FILE"; then
    echo "❌ CRITICAL: sInf definition without edge restriction"
    rg -n "sInf.*Sym2" "$FILE"
    ERRORS=$((ERRORS + 1))
fi

# Check for Finset.sym2 usage
if rg -q "\.sym2[^.]" "$FILE"; then
    echo "⚠️  WARNING: Uses Finset.sym2 (includes self-loops)"
    rg -n "\.sym2" "$FILE"
    echo "Verify self-loops are filtered or intended."
fi

# Check for Set V in decidability contexts
if rg -q "Set V.*induce|induce.*Set V" "$FILE" && ! rg -q "DecidablePred" "$FILE"; then
    echo "❌ CRITICAL: Set V used without DecidablePred instance"
    rg -n "Set V" "$FILE"
    ERRORS=$((ERRORS + 1))
fi

# Check for required instances
for INST in "Fintype V" "DecidableEq V" "DecidableRel G.Adj"; do
    if ! rg -q "$INST" "$FILE"; then
        echo "⚠️  WARNING: Missing instance: $INST"
    fi
done

if [[ $ERRORS -gt 0 ]]; then
    echo
    echo "=== AUDIT FAILED: $ERRORS critical issues ==="
    exit 1
else
    echo
    echo "=== AUDIT PASSED ==="
    exit 0
fi
```

### track_submission.sh

```bash
#!/bin/bash
# Usage: ./scripts/track_submission.sh submissions/problem.lean "erdos128" "boris_minimal"

FILE="$1"
PROBLEM_ID="$2"
PATTERN="$3"

# Run validation
if ! ./scripts/validate_submission.sh "$FILE"; then
    echo "Validation failed. Fix errors before submitting."
    exit 1
fi

# Run definition audit
AUDIT_PASSED=0
if ./scripts/audit_definitions.sh "$FILE" > /dev/null 2>&1; then
    AUDIT_PASSED=1
fi

# Generate UUID placeholder (actual UUID from Aristotle)
UUID="pending_$(date +%s)"

# Record in database
sqlite3 submissions/tracking.db << EOF
INSERT INTO submissions (uuid, filename, problem_id, status, pattern, validation_passed, definitions_audited)
VALUES ('$UUID', '$FILE', '$PROBLEM_ID', 'pending', '$PATTERN', 1, $AUDIT_PASSED);
EOF

echo "Recorded submission: $UUID"
echo "File: $FILE"
echo "Problem: $PROBLEM_ID"
echo "Pattern: $PATTERN"
echo
echo "Run: aristotle prove-from-file $FILE --no-wait"
echo "Then update UUID in database."
```

### find_contaminated.sh

```bash
#!/bin/bash
# Usage: ./scripts/find_contaminated.sh "coveringNumber" "sInf.*Sym2"

DEF_NAME="$1"
BUG_PATTERN="$2"

echo "=== Searching for contaminated definitions ==="
echo "Definition: $DEF_NAME"
echo "Bug pattern: $BUG_PATTERN"
echo

# Find all files with this definition bug
rg -l "def $DEF_NAME.*$BUG_PATTERN" submissions/*.lean submissions/**/*.lean | while read -r FILE; do
    echo "CONTAMINATED: $FILE"

    # Show the buggy definition
    rg -A 2 "def $DEF_NAME" "$FILE"
    echo
done
```

---

## Quick Reference Checklists

### Pre-Submission Checklist

- [ ] `lake env lean file.lean` passes (only `sorry` warnings)
- [ ] No `sInf` definitions without edge restriction
- [ ] No `Finset.sym2` without self-loop filtering
- [ ] All instances declared (`Fintype`, `DecidableEq`, `DecidableRel`)
- [ ] Formalization matches original problem (if applicable)
- [ ] For Erdős: compared against Formal Conjectures
- [ ] Submission recorded in database

### Post-Output Checklist

- [ ] Output retrieved from Aristotle
- [ ] `rg sorry` scan performed
- [ ] If "proven": `lake env lean` compilation passes
- [ ] If "proven": Definition re-audit passes
- [ ] If "proven": Multi-agent verification (high-value problems)
- [ ] Result recorded in database
- [ ] If contaminated: backward/forward trace completed

### Definition Audit Checklist

- [ ] `sInf` definitions include `E ⊆ G.edgeFinset` or use `G.edgeFinset.powerset`
- [ ] `triangleEdges` uses `offDiag.image`, not `.sym2`
- [ ] No `Set V` without `DecidablePred`
- [ ] Edge restrictions explicit in predicates
- [ ] No arbitrary `Finset (Sym2 V)` without graph membership

---

## Appendix: Known Bugs Reference

### Bug: sInf Unrestricted Edges

**Symptom**: Definition allows edges not in the graph.

**Buggy code**:
```lean
def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ IsTriangleCover G E}
```

**Fix**:
```lean
def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (IsTriangleCover G)
    |>.image Finset.card
    |>.min
    |>.getD G.edgeFinset.card
```

**Detection**: `rg "sInf.*Sym2" file.lean`

---

### Bug: Finset.sym2 Self-Loops

**Symptom**: Triangle edge sets include diagonal pairs `s(v,v)`.

**Buggy code**:
```lean
def triangleEdges (t : Finset V) : Finset (Sym2 V) := t.sym2
-- Includes s(v,v) for all v ∈ t
```

**Fix**:
```lean
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))
```

**Detection**: `rg "\.sym2" file.lean`

---

### Bug: Set/Finset Decidability

**Symptom**: Type error when inducing subgraph on `Set V`.

**Buggy code**:
```lean
def foo (G : SimpleGraph V) (S : Set V) :=
  (G.induce S).edgeFinset  -- Needs DecidablePred (· ∈ S)
```

**Fix**:
```lean
def foo (G : SimpleGraph V) (S : Finset V) :=
  (G.induce S).edgeFinset  -- Works with Fintype + DecidableEq
```

**Detection**: `rg "Set V.*induce" file.lean`

---

### Bug: Formalization Threshold Mismatch

**Symptom**: Threshold condition differs from original problem for odd n.

**Example**: Erdős #128

**Buggy**: `2 * S.ncard ≥ n` (checks |S| ≥ ⌈n/2⌉)
**Correct**: `2 * S.ncard + 1 ≥ n` (checks |S| ≥ ⌊n/2⌋)

**Detection**: Compare to Formal Conjectures, test small n manually

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.1 | 2025-12-20 | Added unified CLI (workflow.py), multi-agent audit (Grok+Gemini), SQLite tracking |
| 1.0 | 2025-12-20 | Initial workflow based on discovered bugs |

---

## References

- Contamination Report: `docs/CONTAMINATION_REPORT.md`
- Erdős #128 Analysis: `docs/ERDOS128_ANALYSIS.md`
- Formal Conjectures: https://github.com/google-deepmind/formal-conjectures
