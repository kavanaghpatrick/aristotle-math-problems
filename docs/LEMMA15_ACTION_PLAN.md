# Lemma 15 - Action Plan

**Decision Date**: January 3, 2026
**Lemma**: `tau_le_8_cycle4` (Lemma 15 of 15)
**Status**: BLOCKED - Do not attempt submission

---

## Summary

Lemma 15 has a **sound proof architecture** but is **impossible to complete** because it depends on a **mathematically false assumption** (Pattern 6: "2 edges cover triangles at each shared vertex").

This assumption was rigorously proven false by AI agents (Gemini + Codex) on Dec 29, 2025.

---

## Why This Matters

The cycle_4 case is the "hardest remaining case" for ν=4. However:

- **The τ ≤ 8 bound for cycle_4 is NOT proven**, and
- **The 4×2=8 approach is mathematically impossible** due to Pattern 6

This doesn't mean τ ≤ 8 is false—just that this proof strategy won't work.

---

## What You Should Do

### Option 1: Accept τ ≤ 12 (Recommended)

**Status**: PROVEN COMPLETE in slot139

```bash
Query for details:
sqlite3 /Users/patrickkavanagh/math/submissions/tracking.db << 'EOF'
SELECT * FROM submissions WHERE filename LIKE '%slot139%';
EOF
```

**Advantage**: Complete proof exists
**Disadvantage**: τ ≤ 12 > τ ≤ 8 (Tuza's bound)

### Option 2: Find Alternative Approach to τ ≤ 8

Before coding, research:

```bash
# See what's been tried before
sqlite3 /Users/patrickkavanagh/math/submissions/tracking.db << 'EOF'
SELECT approach_name, why_failed, avoid_pattern
FROM failed_approaches
WHERE frontier_id='nu_4' AND pattern LIKE '%cycle4%'
ORDER BY attempt_number DESC;
EOF

# See what other configurations achieved τ ≤ 8
SELECT case_name, status, key_insight
FROM nu4_cases
WHERE status='proven' AND key_insight LIKE '%8%';
```

**Candidate approaches**:
- Edge-centric decomposition (vs. vertex-centric)
- Fractional packing + rounding
- König-Egerváry for specific structures
- Constraint satisfaction approach

### Option 3: Prove Pattern 6 True (Unlikely)

Pattern 6 states: "At shared vertex v, 2 edges cover all triangles"

This has been verified false by:
- Grok-4 (code analysis)
- Gemini (mathematical analysis)
- Codex (counterexample construction)

**Effort required**: Would need to find error in all three analyses
**Probability of success**: < 5%

---

## Database Queries for Next Steps

### Check all false lemmas related to cycle_4:

```sql
SELECT pattern_number, lemma_name, false_statement_english, evidence_level, impact
FROM false_lemmas
WHERE lemma_name LIKE '%cycle4%' OR lemma_name LIKE '%sunflower%' OR lemma_name LIKE '%external%'
ORDER BY evidence_level DESC;
```

### Check what approaches have been exhausted:

```sql
SELECT approach_name, why_failed, related_slots
FROM failed_approaches
WHERE frontier_id='nu_4'
ORDER BY id DESC
LIMIT 20;
```

### See all ν=4 case status:

```sql
SELECT case_name, status, proven_lemmas, next_action
FROM nu4_cases
ORDER BY status, case_name;
```

### Check literature on Tuza's conjecture for τ ≤ 8:

```sql
SELECT author, title, year, relevant_result
FROM literature_lemmas
WHERE problem LIKE '%Tuza%' AND relevant_result LIKE '%8%'
ORDER BY year DESC;
```

---

## If You Must Attempt τ ≤ 8

Follow this checklist BEFORE coding:

### Pre-Coding Checklist

- [ ] Query false_lemmas table for all patterns that affect cycle_4
- [ ] Query failed_approaches for cycle_4-specific prior attempts
- [ ] Document your approach's UNIQUE insight (vs. why slot130 failed)
- [ ] Find or construct counterexample to Pattern 6 if using vertex-centric approach
- [ ] Get Grok-4 code review BEFORE submitting to Aristotle
- [ ] Get Gemini mathematical review of approach BEFORE coding

### Pre-Submission Checklist

- [ ] Run `./scripts/dashboard.sh` to see current state
- [ ] Verify no sorry/axiom in final proof
- [ ] Check against false_lemmas table one more time
- [ ] Estimate Aristotle runtime (if > 6 hours, reconsider)
- [ ] Prepare fallback to τ ≤ 12 if it fails

### During Aristotle Run

- [ ] Monitor for `counterexample` output (Aristotle found false assumption)
- [ ] Monitor for `timeout` (approach too complex)
- [ ] Be ready to pivot to alternative if after 4 hours no progress

---

## Files to Consult

| File | Purpose | Status |
|------|---------|--------|
| `/Users/patrickkavanagh/math/docs/FALSE_LEMMAS.md` | All patterns 1-16 with evidence | Current |
| `/Users/patrickkavanagh/math/docs/LEMMA15_REVIEW.md` | Full architectural review | Current |
| `/Users/patrickkavanagh/math/submissions/tracking.db` | All historical data | Current |
| `/Users/patrickkavanagh/math/proven/tuza/nu4/slot139_tau_le_12_PROVEN.lean` | Proven τ ≤ 12 | Reference |
| `/Users/patrickkavanagh/math/submissions/nu4_final/slot130_tau_le_8_assembly.lean` | Lemma 15 (blocked) | Don't submit |

---

## Key Takeaways

1. **Lemma 15 assembly is well-designed** but depends on a false core assumption
2. **Pattern 6 is definitively proven false** (AI-verified with counterexample)
3. **The 4×2=8 approach is impossible** - maximum bound is 4×3=12
4. **Alternative: τ ≤ 12 is already proven** (slot139)
5. **If pursuing τ ≤ 8**: Need completely different approach, not just different proofs of same structure

---

## Risk Assessment

| Action | Risk | Effort | Expected Outcome |
|--------|------|--------|------------------|
| Submit Lemma 15 as-is | CRITICAL | 0 | Aristotle rejects due to false lemma |
| Complete missing proofs in Lemma 15 | CRITICAL | 10 hrs | Even if complete, false assumption prevents proof |
| Find alternative τ ≤ 8 approach | MEDIUM | 20-40 hrs | Possible but no guarantees |
| Accept τ ≤ 12 | LOW | 0 | Immediate: proves conjecture for ν≤4 |

---

## Decision Framework

**Use this decision tree:**

```
Do you have a FUNDAMENTALLY NEW approach to τ ≤ 8?
  │
  ├─ NO (or "I'll modify Lemma 15")
  │  └─> Accept τ ≤ 12 [slot139] + STOP
  │
  └─ YES (completely different structure)
     │
     ├─ Have you checked false_lemmas?
     │  └─ NO  -> Do that first
     │  └─ YES -> Continue
     │
     ├─ Have you documented why it avoids Pattern 6?
     │  └─ NO  -> Do that first
     │  └─ YES -> Continue
     │
     └─ Get Grok-4 + Gemini review BEFORE coding
        └─ If either finds showstoppers -> Reconsider
        └─ If both approve -> Proceed with full confidence

```

---

**Last Updated**: January 3, 2026
**Next Review**: When new approach is identified or after 1 week
