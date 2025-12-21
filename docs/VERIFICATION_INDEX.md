# Verification System Documentation Index

**Navigation guide for the verification workflow system**

---

## Quick Access

| Need | Document | Location |
|------|----------|----------|
| **Daily use** | Reference Card | `VERIFICATION_REFERENCE_CARD.md` |
| **Getting started** | Quick Start | `VERIFICATION_QUICKSTART.md` |
| **Understanding flow** | Visual Guide | `VERIFICATION_VISUAL.md` |
| **Complete details** | Full Workflow | `VERIFICATION_WORKFLOW.md` |
| **System overview** | Summary | `VERIFICATION_SUMMARY.md` |

---

## By User Role

### I'm Submitting to Aristotle

**Read first**: `VERIFICATION_QUICKSTART.md`
**Keep handy**: `VERIFICATION_REFERENCE_CARD.md` (print it!)
**Before submission**: Run `validate_submission.sh`
**After results**: Run `verify_output.sh`

### I'm Reviewing Proofs

**Read first**: `VERIFICATION_WORKFLOW.md` Section 3 (Post-Submission)
**Use tools**: `verify_output.sh`, `audit_definitions.sh`
**Check**: Database for verification status
**For high-value**: Multi-agent review protocol (Section 3.4)

### I'm Managing the Project

**Read first**: `VERIFICATION_SUMMARY.md`
**Monitor**: Database queries (Section in QUICKSTART)
**Track**: Contamination (use `find_contaminated.sh`)
**Maintain**: Weekly/monthly tasks (Section in SUMMARY)

### I'm Debugging a Bug

**Document it**: Create `docs/BUG_<name>_REPORT.md` (see CONTAMINATION_REPORT.md as template)
**Find affected**: Run `find_contaminated.sh`
**Quarantine**: Move to `submissions/CORRUPTED/`
**Prevent**: Add detection to `audit_definitions.sh`

---

## By Task

### Task: Validate a Submission Before Sending

1. Run `./scripts/validate_submission.sh submissions/file.lean`
2. If errors: Fix and re-run
3. If warnings: Review (may be OK)
4. If clean: Proceed to tracking

**Docs**: `VERIFICATION_QUICKSTART.md` - Workflow A/B

### Task: Track a Submission

1. Run `./scripts/track_submission.sh submissions/file.lean "problem_id" "pattern"`
2. Copy UUID from output
3. Submit to Aristotle
4. Update database with actual Aristotle UUID

**Docs**: `VERIFICATION_WORKFLOW.md` - Section 2.2

### Task: Verify Aristotle Output

1. Retrieve: `aristotle status <UUID> > submissions/output/<UUID>.lean`
2. Run `./scripts/verify_output.sh submissions/output/<UUID>.lean`
3. Review output (proven, partial, failed)
4. If proven: Deep verification (Section 3.3)

**Docs**: `VERIFICATION_WORKFLOW.md` - Section 3

### Task: Check for Definition Bugs

1. Run `./scripts/audit_definitions.sh submissions/file.lean`
2. Check for CRITICAL errors (sInf, sym2, axioms)
3. Check for WARNINGS (may be OK depending on context)
4. Fix any critical issues before submitting

**Docs**: `VERIFICATION_WORKFLOW.md` - Section 1.2

### Task: Compare to Formal Conjectures (Erdős)

1. Download FC formalization:
   ```bash
   curl https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/<NUM>.lean -o /tmp/FC_<NUM>.lean
   ```
2. Compare side-by-side with your formalization
3. Check quantifiers, thresholds, hypotheses
4. Test edge cases (n=3,4,5)

**Docs**: `VERIFICATION_WORKFLOW.md` - Section 1.3

### Task: Find Files Contaminated by a Bug

1. Run `./scripts/find_contaminated.sh "definition_name" "bug_pattern"`
2. Review list of affected files
3. Quarantine: `git mv file.lean submissions/CORRUPTED/`
4. Update database with contamination records

**Docs**: `VERIFICATION_WORKFLOW.md` - Section 3.4

### Task: Multi-Agent Review (High-Value Proofs)

1. Prepare: Proven output with no sorry, compiles
2. Run Grok-4 review (critical issues)
3. Run Gemini review (math validity)
4. Synthesize results
5. Mark as verified or suspicious

**Docs**: `VERIFICATION_WORKFLOW.md` - Section 3.4

### Task: Query Database for Status

**Active submissions**:
```bash
sqlite3 submissions/tracking.db "SELECT filename, status FROM submissions WHERE status IN ('queued', 'running');"
```

**Verified proofs**:
```bash
sqlite3 submissions/tracking.db "SELECT s.filename, pc.theorem_name FROM submissions s JOIN proof_claims pc ON s.uuid=pc.submission_uuid WHERE pc.verification_status='verified';"
```

**Contaminated files**:
```bash
sqlite3 submissions/tracking.db "SELECT filename FROM submissions s JOIN proof_claims pc ON s.uuid=pc.submission_uuid WHERE pc.verification_status='invalid';"
```

**Docs**: `VERIFICATION_QUICKSTART.md` - Database Queries section

---

## By Document Type

### Tutorials & Guides

| Document | Purpose | Length | Audience |
|----------|---------|--------|----------|
| `VERIFICATION_QUICKSTART.md` | Hands-on workflows with examples | ~8KB | All users |
| `VERIFICATION_VISUAL.md` | Diagrams and flowcharts | ~10KB | Visual learners |

### Reference Materials

| Document | Purpose | Length | Audience |
|----------|---------|--------|----------|
| `VERIFICATION_REFERENCE_CARD.md` | One-page cheat sheet | ~4KB | Daily users (print!) |
| `VERIFICATION_WORKFLOW.md` | Complete technical specification | ~15KB | All users |

### Overviews & Context

| Document | Purpose | Length | Audience |
|----------|---------|--------|----------|
| `VERIFICATION_SUMMARY.md` | System overview and rationale | ~12KB | Project leads |
| `VERIFICATION_INDEX.md` | This document | ~5KB | Navigation |

### Bug Reports & Case Studies

| Document | Purpose | Lessons |
|----------|---------|---------|
| `CONTAMINATION_REPORT.md` | sInf and sym2 bugs | Use G.edgeFinset restriction |
| `ERDOS128_ANALYSIS.md` | Formalization threshold bug | Always compare to FC |
| `TAU_TE_SKEPTICAL_ANALYSIS.md` | Why to doubt "obvious" lemmas | Test with Pessimist |

---

## Tools Reference

### Scripts

| Script | Input | Output | When |
|--------|-------|--------|------|
| `validate_submission.sh` | .lean file | Pass/fail + errors | Before EVERY submission |
| `audit_definitions.sh` | .lean file | Bug detection report | Any file with definitions |
| `track_submission.sh` | .lean file + metadata | DB entry + UUID | Before submission |
| `verify_output.sh` | Aristotle output | Verification report | After results arrive |
| `find_contaminated.sh` | Definition + pattern | List of affected files | After bug discovery |

### Database

**Location**: `submissions/tracking.db`
**Format**: SQLite 3
**Schema**: See `VERIFICATION_WORKFLOW.md` Section 2.1

**Tables**:
- `submissions` - Core tracking
- `definitions` - Definition audit results
- `proof_claims` - Theorem verification
- `definition_contamination` - Bug propagation

### Multi-Agent Tools

**Grok-4**: Critical code review
**Gemini**: Mathematical validity
**Protocol**: See `VERIFICATION_WORKFLOW.md` Section 3.4

---

## Workflow Sequences

### Complete Submission Lifecycle

```
1. Write → 2. Validate → 3. Audit → 4. Track → 5. Submit
                ↓
           [Wait 6-24h]
                ↓
6. Retrieve → 7. Scan Sorry → 8. Verify → 9. Review (if proven) → 10. Record
```

**Docs**: `VERIFICATION_VISUAL.md` - Overview Diagram

### Bug Discovery & Remediation

```
1. Discover Bug → 2. Document → 3. Find Contaminated → 4. Quarantine
                                                            ↓
                                5. Update Audit ← 6. Update Database
```

**Docs**: `VERIFICATION_VISUAL.md` - Contamination Tracing

### Definition Audit Decision Tree

```
Check sInf → Check sym2 → Check Set/Finset → Check Axioms → Result
```

**Docs**: `VERIFICATION_VISUAL.md` - Definition Audit Decision Tree

---

## Learning Path

### Level 1: Basic User (Week 1)

1. Read `VERIFICATION_QUICKSTART.md`
2. Print `VERIFICATION_REFERENCE_CARD.md`
3. Submit 1-2 files with validation
4. Review verified output

**Goal**: Can validate and submit independently

### Level 2: Proficient User (Week 2-3)

1. Read `VERIFICATION_WORKFLOW.md` Sections 1-3
2. Practice definition auditing
3. Perform deep verification on claimed proof
4. Query database for portfolio status

**Goal**: Can verify proofs and catch definition bugs

### Level 3: Power User (Month 1+)

1. Read `VERIFICATION_SUMMARY.md`
2. Study `VERIFICATION_VISUAL.md` flowcharts
3. Perform multi-agent review
4. Trace contamination when bug discovered
5. Update audit scripts with new patterns

**Goal**: Can maintain verification system and extend it

---

## Common Patterns

### Pattern: Daily Submission

```bash
vim submissions/new.lean
./scripts/validate_submission.sh submissions/new.lean
./scripts/track_submission.sh submissions/new.lean "problem" "pattern"
aristotle prove-from-file submissions/new.lean --no-wait
```

### Pattern: Batch Validation

```bash
for f in submissions/tuza_nu5_*.lean; do
    echo "Validating: $f"
    ./scripts/validate_submission.sh "$f"
done
```

### Pattern: Portfolio Status Check

```bash
sqlite3 submissions/tracking.db << EOF
SELECT
    problem_id,
    COUNT(*) as total,
    SUM(CASE WHEN status='completed' THEN 1 ELSE 0 END) as completed,
    SUM(CASE WHEN validation_passed=1 THEN 1 ELSE 0 END) as validated
FROM submissions
GROUP BY problem_id;
EOF
```

---

## Troubleshooting

### Validation Fails with Syntax Error

**Check**: Line number in error message
**Fix**: Correct syntax in Lean file
**Re-run**: `validate_submission.sh`
**If persists**: Check imports, instances

### Audit Finds sInf Unrestricted

**Problem**: Definition allows non-graph edges
**Fix**: Replace with `G.edgeFinset.powerset.filter ...`
**See**: `CONTAMINATION_REPORT.md` - Bug 1

### Database Entry Missing

**Problem**: Submission not tracked
**Fix**: Run `track_submission.sh`
**Check**: `sqlite3 submissions/tracking.db "SELECT * FROM submissions WHERE filename='...';"`

### Output Has Buried Sorry

**Problem**: Claimed proven but has sorry in helpers
**Status**: Partial proof, not fully proven
**Action**: Extract proven lemmas, mark as partial

### Multi-Agent Review Contradicts

**Grok says CLEAN, Gemini finds issue**:
- Manual review required
- Lean compilation is ground truth
- Mark as suspicious, investigate

---

## File Locations

### Documentation
```
docs/
├── VERIFICATION_WORKFLOW.md       (Complete specification)
├── VERIFICATION_QUICKSTART.md     (Practical guide)
├── VERIFICATION_VISUAL.md         (Diagrams)
├── VERIFICATION_REFERENCE_CARD.md (Cheat sheet)
├── VERIFICATION_SUMMARY.md        (Overview)
├── VERIFICATION_INDEX.md          (This file)
├── CONTAMINATION_REPORT.md        (Bug case study)
└── ERDOS128_ANALYSIS.md           (Formalization bug)
```

### Scripts
```
scripts/
├── validate_submission.sh   (Pre-submission check)
├── audit_definitions.sh     (Definition bug detection)
├── track_submission.sh      (Database recording)
├── verify_output.sh         (Output verification)
└── find_contaminated.sh     (Bug propagation finder)
```

### Database
```
submissions/
├── tracking.db              (SQLite database)
├── *.lean                   (Active submissions)
├── output/                  (Aristotle outputs)
│   └── *.lean
└── CORRUPTED/               (Quarantined files)
    └── *.lean
```

---

## Version Information

**System Version**: 1.0
**Created**: December 20, 2025
**Last Updated**: December 20, 2025

**Changelog**:
- 1.0: Initial verification system based on Dec 2024-2025 bug lessons

---

## Next Steps

After reading this index:

1. **If new user**: Start with `VERIFICATION_QUICKSTART.md`
2. **If experienced**: Print `VERIFICATION_REFERENCE_CARD.md`
3. **If debugging**: Find relevant bug report
4. **If maintaining**: Read `VERIFICATION_SUMMARY.md`

**Questions?** Check the relevant document above, or search for keywords in the full workflow.
