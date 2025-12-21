# Verification Workflow Reference Card

**Quick reference for daily use. Print this.**

---

## Before Every Submission

```bash
# 1. Validate
./scripts/validate_submission.sh submissions/file.lean

# 2. Track
./scripts/track_submission.sh submissions/file.lean "problem_id" "pattern"

# 3. Submit
aristotle prove-from-file submissions/file.lean --no-wait
```

---

## After Results Arrive

```bash
# 1. Retrieve
aristotle status <UUID> > submissions/output/<UUID>.lean

# 2. Verify
./scripts/verify_output.sh submissions/output/<UUID>.lean
```

---

## Definition Bugs to Watch For

| Bug | Bad Code | Good Code |
|-----|----------|-----------|
| **sInf unrestricted** | `sInf {n │ ∃ E : Finset (Sym2 V), ...}` | `G.edgeFinset.powerset.filter ...` |
| **sym2 self-loops** | `t.sym2` | `t.offDiag.image (fun x => Sym2.mk ...)` |
| **Set/Finset** | `(S : Set V)` with `induce` | `(S : Finset V)` |
| **Axioms** | `axiom foo : ...` | **NEVER** use axioms |

---

## Red Flags Checklist

Pre-submission:
- [ ] File compiles (`lake env lean`)
- [ ] No `sInf` without edge restriction
- [ ] No `Finset.sym2` for triangle edges
- [ ] No `axiom` declarations
- [ ] Formalization matches original (if Erdős)

Post-submission:
- [ ] No `sorry` (if claiming proven)
- [ ] Compiles independently
- [ ] Definitions re-audited
- [ ] No circular reasoning
- [ ] High-value: multi-agent verified

---

## Formalization Verification (Erdős)

1. **Find Formal Conjectures version**:
   ```bash
   curl https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/<NUM>.lean
   ```

2. **Compare quantifiers**: ∀, ∃, ≥, >, ≤, <

3. **Test small n**: For n=3,4,5, do conditions match?

4. **Common mistakes**:
   - `2*|S| ≥ n` vs `2*|S|+1 ≥ n` (off by one for odd n)
   - `<` vs `≤`
   - Missing hypotheses

---

## Emergency: Found a Bug

```bash
# 1. Find contaminated files
./scripts/find_contaminated.sh "definition_name" "bug_pattern"

# 2. Quarantine
mkdir -p submissions/CORRUPTED
git mv submissions/bad_file.lean submissions/CORRUPTED/

# 3. Document
vim docs/BUG_<name>_REPORT.md

# 4. Update audit script
vim scripts/audit_definitions.sh
```

---

## Database Quick Queries

**Active submissions**:
```bash
sqlite3 submissions/tracking.db "SELECT filename, status FROM submissions WHERE status IN ('queued', 'running');"
```

**Recent validated**:
```bash
sqlite3 submissions/tracking.db "SELECT filename, problem_id FROM submissions WHERE validation_passed=1 ORDER BY submission_date DESC LIMIT 5;"
```

**Contaminated proofs**:
```bash
sqlite3 submissions/tracking.db "SELECT filename FROM submissions s JOIN proof_claims pc ON s.uuid=pc.submission_uuid WHERE pc.verification_status='invalid';"
```

---

## Multi-Agent Review (High-Value Only)

**When**: $250+ problems OR genuinely open problems

**Grok-4** (Critical issues):
```bash
# Check: axioms, self-loops, edge restrictions, circular deps
# Max time: 180s
```

**Gemini** (Math validity):
```bash
# Check: proof logic, assumptions, completeness, formalization correctness
# Use for deep analysis
```

Both CLEAN → Mark VERIFIED
Any issues → Manual review

---

## File Naming Convention

| Type | Pattern | Example |
|------|---------|---------|
| Submission | `<problem>_<variant>.lean` | `tuza_nu4_v1_boris_prime.lean` |
| Output | `output/<UUID>.lean` | `output/abc123.lean` |
| Corrupted | `CORRUPTED/<original>.lean` | `CORRUPTED/tuza_nu3_bad.lean` |
| Proven | `aristotle_<problem>_proven.lean` | `aristotle_parker_proven.lean` |

---

## Status Codes

| Code | Meaning | Action |
|------|---------|--------|
| `pending` | Recorded, not submitted | Submit to Aristotle |
| `queued` | Waiting to run | Wait |
| `running` | Aristotle working | Wait (6-24h normal) |
| `completed` | Finished | Retrieve and verify |
| `failed` | Error | Check logs |
| `timeout` | Exceeded time limit | Re-submit or simplify |

---

## Proof Claim Status

| Status | Meaning |
|--------|---------|
| `proven` | No sorry, compiles |
| `partial` | Some lemmas proven, main theorem has sorry |
| `sorry` | Main theorem unsolved |
| `contaminated` | Invalid due to definition bug |

| Verification | Meaning |
|-------------|---------|
| `pending` | Not verified yet |
| `verified` | Checked and valid |
| `invalid` | Bug found, do not use |

---

## Definition Type Codes

| Type | Meaning | Severity |
|------|---------|----------|
| `correct` | No issues | ✅ |
| `sInf_unrestricted` | Allows non-graph edges | ❌ Critical |
| `sym2_selfloop` | Includes self-loops | ❌ Critical |
| `set_finset` | Decidability issue | ⚠️ Warning |

---

## Common Lean Instances Required

```lean
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
```

Missing these → type errors in graph operations.

---

## Script Exit Codes

| Exit Code | Meaning |
|-----------|---------|
| `0` | Success |
| `1` | Validation failed, fix before submitting |

---

## Quick Decision Tree

**Before submitting**:
- Does it compile? NO → Fix syntax
- Definitions clean? NO → Fix definitions
- Matches original? NO → Fix formalization
- All YES → SUBMIT

**After receiving output**:
- Has sorry? YES → Partial, extract lemmas
- Has sorry? NO → Claimed proven, verify
- Compiles? NO → Invalid proof
- Audit clean? NO → Contaminated
- High value? YES → Multi-agent review
- All checks pass? → Mark VERIFIED

---

## Contact / Issues

- Workflow docs: `docs/VERIFICATION_WORKFLOW.md`
- Quick start: `docs/VERIFICATION_QUICKSTART.md`
- Visual guide: `docs/VERIFICATION_VISUAL.md`
- Bug reports: `docs/CONTAMINATION_REPORT.md`

---

**Version**: 1.0
**Last Updated**: 2025-12-20
