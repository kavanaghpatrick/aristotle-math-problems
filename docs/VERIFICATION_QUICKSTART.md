# Verification Workflow Quick Start

**Goal**: Prevent bugs like Erdős #128 formalization error, sInf unrestricted edges, and sym2 self-loops.

---

## Pre-Submission (MANDATORY)

### Step 1: Validate Syntax

```bash
./scripts/validate_submission.sh submissions/my_problem.lean
```

**Expected**: All checks pass, only `sorry` warnings allowed.

**If it fails**: Fix errors before proceeding.

### Step 2: Track Submission

```bash
./scripts/track_submission.sh submissions/my_problem.lean "erdos128" "boris_minimal"
```

**Expected**: Database entry created, validation confirmed.

### Step 3: Submit to Aristotle

```bash
# Copy the UUID from tracking output
aristotle prove-from-file submissions/my_problem.lean --no-wait

# Save the actual UUID returned by Aristotle
# Update in monitor_log.txt or database
```

---

## Post-Submission (When Results Arrive)

### Step 1: Retrieve Output

```bash
# Download output
aristotle status <UUID> > submissions/output/<UUID>.lean
```

### Step 2: Verify Output

```bash
./scripts/verify_output.sh submissions/output/<UUID>.lean
```

**Possible outcomes**:

1. **No sorry found**: Claimed PROVEN → proceed to deep verification
2. **One sorry in main theorem**: Aristotle couldn't solve → analyze partial progress
3. **Multiple sorry**: Partial proof → extract what worked

### Step 3: Deep Verification (If Claimed Proven)

```bash
# 1. Syntax check
lake env lean submissions/output/<UUID>.lean

# 2. Definition audit
./scripts/audit_definitions.sh submissions/output/<UUID>.lean

# 3. For high-value problems: Multi-agent review
#    (See VERIFICATION_WORKFLOW.md Section 3.4)
```

---

## Common Workflows

### Workflow A: New Erdős Problem

```bash
# 1. Compare to Formal Conjectures
curl https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/128.lean -o /tmp/FC_128.lean

# 2. Write your formalization
vim submissions/erdos128_v1.lean

# 3. Compare
diff -u /tmp/FC_128.lean submissions/erdos128_v1.lean

# 4. Validate and submit
./scripts/validate_submission.sh submissions/erdos128_v1.lean
./scripts/track_submission.sh submissions/erdos128_v1.lean "erdos128" "boris_minimal"
aristotle prove-from-file submissions/erdos128_v1.lean --no-wait
```

### Workflow B: Tuza Variant with New Definitions

```bash
# 1. Write definitions
vim submissions/tuza_nu5_v1.lean

# 2. CRITICAL: Audit definitions BEFORE submission
./scripts/audit_definitions.sh submissions/tuza_nu5_v1.lean

# If audit finds issues:
# - Fix sInf definitions (use G.edgeFinset.powerset)
# - Fix sym2 usage (use offDiag.image)
# - Fix Set/Finset issues

# 3. Validate and submit
./scripts/validate_submission.sh submissions/tuza_nu5_v1.lean
./scripts/track_submission.sh submissions/tuza_nu5_v1.lean "tuza_nu5" "boris_minimal"
aristotle prove-from-file submissions/tuza_nu5_v1.lean --no-wait
```

### Workflow C: Found a Bug in Existing File

```bash
# 1. Find all contaminated files
./scripts/find_contaminated.sh "coveringNumber" "sInf.*Sym2"

# 2. Quarantine
mkdir -p submissions/CORRUPTED
git mv submissions/contaminated_file.lean submissions/CORRUPTED/

# 3. Update database (manual SQL or script)
# Mark all affected submissions as contaminated

# 4. Re-formalize correctly
vim submissions/fixed_version.lean
# Use G.edgeFinset.powerset instead of sInf

# 5. Re-submit
./scripts/validate_submission.sh submissions/fixed_version.lean
aristotle prove-from-file submissions/fixed_version.lean --no-wait
```

---

## Red Flags Checklist

Before submitting, manually check for these patterns:

### Definition Red Flags

- [ ] `sInf {n : ℕ | ∃ E : Finset (Sym2 V), ...}` without `E ⊆ G.edgeFinset`
- [ ] `t.sym2` used for triangle edges (should be `t.offDiag.image ...`)
- [ ] `Set V` with `induce` but no `DecidablePred`
- [ ] Any `axiom` declarations

### Formalization Red Flags (Erdős Problems)

- [ ] Quantifier mismatch (≥ vs >, ∀ vs ∃)
- [ ] Threshold differs from original (test n=3,4,5 manually)
- [ ] Missing `+1` in inequality (e.g., `2*|S| ≥ n` vs `2*|S|+1 ≥ n`)
- [ ] Differs from Formal Conjectures without justification

### Aristotle Output Red Flags

- [ ] No `sorry` but file doesn't compile
- [ ] Uses `axiom` or `admit`
- [ ] New definitions introduced with sInf/sym2 bugs
- [ ] Claims proof but circular reasoning detected

---

## Database Queries

### Check Submission Status

```bash
sqlite3 submissions/tracking.db << EOF
SELECT filename, status, pattern, submission_date
FROM submissions
WHERE status IN ('queued', 'running')
ORDER BY submission_date DESC;
EOF
```

### Find All Validated Submissions

```bash
sqlite3 submissions/tracking.db << EOF
SELECT filename, problem_id, validation_passed, definitions_audited
FROM submissions
WHERE validation_passed = 1 AND definitions_audited = 1
ORDER BY submission_date DESC
LIMIT 10;
EOF
```

### Find Contaminated Proofs

```bash
sqlite3 submissions/tracking.db << EOF
SELECT s.filename, pc.theorem_name, pc.invalidation_reason
FROM submissions s
JOIN proof_claims pc ON s.uuid = pc.submission_uuid
WHERE pc.verification_status = 'invalid'
ORDER BY pc.verification_date DESC;
EOF
```

---

## Emergency: Found Major Bug

If you discover a widespread bug (like sInf or sym2):

### Step 1: Document the Bug

Create `docs/BUG_<name>_REPORT.md` with:
- Description of bug
- Why it's wrong
- How to detect it
- How to fix it
- Example files affected

### Step 2: Find All Affected Files

```bash
./scripts/find_contaminated.sh "<definition_name>" "<bug_pattern>"
```

### Step 3: Quarantine

```bash
# Move all contaminated files
mkdir -p submissions/CORRUPTED
for file in $(./scripts/find_contaminated.sh "def" "pattern" | grep "^submissions" | cut -d: -f1); do
    git mv "$file" submissions/CORRUPTED/
done
```

### Step 4: Update Audit Script

Add detection for this bug to `scripts/audit_definitions.sh`

### Step 5: Re-Validate Portfolio

```bash
# Run audit on all active submissions
for file in submissions/tuza_nu*.lean submissions/erdos*.lean; do
    echo "Checking: $file"
    ./scripts/audit_definitions.sh "$file" || echo "FAILED: $file"
done
```

---

## Example: Complete Submission Workflow

```bash
# Write new submission
vim submissions/tuza_nu4_v8_optimized.lean

# Validate
./scripts/validate_submission.sh submissions/tuza_nu4_v8_optimized.lean
# Output:
# ✅ PASSED: No syntax errors
# ✅ PASSED: Definitions clean
# Found 1 sorry statements (expected for submission)
# ✅ SAFE TO SUBMIT

# Track
./scripts/track_submission.sh submissions/tuza_nu4_v8_optimized.lean "tuza_nu4" "optimized"
# Output:
# UUID: pending_tuza_nu4_v8_optimized_1734723456

# Submit
aristotle prove-from-file submissions/tuza_nu4_v8_optimized.lean --no-wait
# Output:
# Job submitted with UUID: abc123-def456-...

# Wait 6-24 hours...

# Retrieve
aristotle status abc123-def456-... > submissions/output/abc123.lean

# Verify
./scripts/verify_output.sh submissions/output/abc123.lean
# Output:
# ✅ No sorry found - claimed PROVEN
# ✅ No axioms found
# ✅ Compilation successful
# ✅ Definitions clean
# ✅ Output claims to be proven and passes basic verification

# For $250+ problem: Multi-agent review
# (Run Grok-4 and Gemini checks from VERIFICATION_WORKFLOW.md)

# If all checks pass: Mark as verified
sqlite3 submissions/tracking.db << EOF
UPDATE proof_claims
SET verification_status = 'verified',
    verification_date = datetime('now')
WHERE submission_uuid = 'abc123-def456-...';
EOF
```

---

## Tools Reference

| Tool | Purpose | When to Use |
|------|---------|-------------|
| `validate_submission.sh` | Syntax + definition check | Before EVERY submission |
| `audit_definitions.sh` | Check for known bugs | Any file with definitions |
| `track_submission.sh` | Database tracking | Record submission metadata |
| `verify_output.sh` | Check Aristotle output | When results arrive |
| `find_contaminated.sh` | Find buggy definitions | After discovering new bug |

---

## Next Steps

For full details, see:
- Complete workflow: `docs/VERIFICATION_WORKFLOW.md`
- Known bugs: `docs/CONTAMINATION_REPORT.md`
- Database schema: `docs/VERIFICATION_WORKFLOW.md` Section 2.1

For questions or issues with the workflow, check recent submissions in the tracking database.
