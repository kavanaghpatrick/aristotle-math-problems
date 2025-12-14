# CLAUDE.md - Math Project

> Extends `~/.claude/CLAUDE.md` (global). Project-specific rules and context.

---

## 🚨 CRITICAL LESSONS FROM 12 FAILED SUBMISSIONS (Dec 2025)

**Result**: 0/12 complete proofs of open Erdős problems

**Root Cause**: We submitted ENGLISH descriptions. Boris submitted PRE-FORMALIZED LEAN.

| What Boris Did (SUCCESS) | What We Did (FAILURE) |
|--------------------------|----------------------|
| Pre-formalized Lean statement | English description |
| Theorem signature LOCKED | AI chose easiest interpretation |
| Zero intervention (went to bed) | Kept refining prompts |
| AI fills proof only | AI redefines + proves trivial version |

---

## 🎯 THE NEW APPROACH: Immutable Formal Statements

### The Boris Pattern (ACTUALLY WORKS)

```lean
-- From Formal Conjectures project - EXISTING formalization
@[category research open, AMS 11]
theorem erdos_124 : (formal_statement_already_exists) := by
  sorry
```

**That's it.** Submit → Go to bed → Wake up → SOLVED.

### Our Old Pattern (FAILED 12 TIMES)

```
"Prove Erdős #64: Every graph with minimum degree ≥3 has a 2^k cycle"
```

**Result**: AI proved trivial cases, explored examples, or redefined the problem.

---

## The Three-Agent Protocol (MANDATORY)

**NEVER let the proving agent write the theorem statement.**

### Step 1: Architect Agent
- Translates English → Lean theorem statement
- Creates the formal specification with explicit quantifiers

### Step 2: Critic Agent
- Verifies the Lean matches the original problem
- Checks: quantifiers (∀ vs ∃), hypotheses, conclusion
- Rejects trivial/vacuous formulations

### Step 3: Prover Agent
- Receives LOCKED theorem statement (immutable)
- Can ONLY fill the proof body (`:= by ...`)
- Cannot modify theorem signature

```lean
-- LOCKED (from Architect + Critic) - DO NOT MODIFY
theorem tuza_conjecture (G : SimpleGraph V) [Fintype V] [DecidableEq V] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  -- Prover fills ONLY this part
  sorry
```

---

## Failure Modes We Discovered

### 1. Exploration Drift (3ab73560, 87a1f043)
**Symptom**: AI "completes" (0 sorries) but never proves the main theorem
**Example**: Defined `ErdosProblem64Statement` as `Prop`, explored Petersen graphs, never proved it
**Fix**: Lock the theorem; AI can only fill proof body

### 2. Quantifier Trap (erdos153 multiple attempts)
**Symptom**: AI proves ∃ version instead of ∀ version
**Example**: "There exists a Sidon family where gaps → ∞" instead of "For ALL Sidon sets"
**Fix**: Explicit Lean quantifiers in locked theorem

### 3. Hypothesis Restriction (erdos149 attempts)
**Symptom**: AI adds `(h : G.maxDegree ≤ 2)` to make theorem trivial
**Fix**: Locked theorem signature prevents additions

### 4. The `exact?` Killer (Tuza, #593, #152)
**Symptom**: 502 lines built, then stuck on 2 `exact?` holes
**Fix**: Iterate! Resubmit with explicit hole-filling request

---

## Iteration Strategy (NEW - CRITICAL)

**OLD**: Submit 12 different problems → 0 successes
**NEW**: Iterate on near-wins until complete

### Near-Successes to Iterate On

| Submission | Problem | Lines | Holes | Priority |
|------------|---------|-------|-------|----------|
| **047671c7** | Tuza's Conjecture | 502 | 2 | HIGHEST |
| **14271720** | Erdős #593 | 229 | 1 | HIGH |
| **de15bdcb** | Erdős #152 | 265 | 2 | MEDIUM |

### Iteration Protocol

```
Iteration 1: Initial submission → Get partial result with holes
Iteration 2: Resubmit with: "Complete this proof. Fill holes at lines X, Y"
Iteration 3: If still stuck, decompose hole into sub-lemma
Iteration 4: Manually fill trivial holes if needed
```

**Target**: 50%+ completion rate on near-successes with 2-3 iterations

---

## Source of Truth: Formal Conjectures

**USE THIS**: https://github.com/google-deepmind/formal-conjectures

This project has PRE-FORMALIZED Erdős problems in Lean. Use these exact statements.

### Workflow

1. Find problem in Formal Conjectures with existing Lean statement
2. Copy the EXACT theorem statement (do not paraphrase)
3. Submit to Aristotle with `sorry` for proof body
4. Go to bed
5. Wake up → Check result

### If Problem Not in Formal Conjectures

1. **Architect**: Write explicit Lean theorem with locked quantifiers
2. **Critic**: Verify via Grok/Gemini that it matches original
3. **Prover**: Submit locked statement to Aristotle

---

## Quantifier Reference

| Natural Language | WRONG (AI chooses) | RIGHT (explicit) |
|-----------------|--------------------|--------------------|
| "X → ∞ as n → ∞" | ∀n, ∃X, X > n | **∀M, ∃N, ∀n>N, X(n) > M** |
| "For large n, P holds" | ∃n, P(n) | **∃N, ∀n>N, P(n)** |
| "Every X has P" | ∃X, P(X) | **∀X, P(X)** |

**ALWAYS write explicit Lean with locked quantifier order.**

---

## Post-Submission Verification (MANDATORY)

After ANY Aristotle "success" (0 sorries + compiles):

```
□ Extract main theorem statement from output
□ Compare QUANTIFIER-BY-QUANTIFIER with original problem
□ Check: Did AI add restrictive hypotheses?
□ Check: Did AI prove ∃ instead of ∀?
□ Check: Is the proven theorem actually the target?
□ If any mismatch → Resubmit with locked formal statement
```

**Success Metric**:
```
OLD: 0 sorries + compiles = solved
NEW: 0 sorries + compiles + EXACT MATCH = solved
```

---

## Aristotle API Quick Reference

```bash
# Submit with pre-formalized Lean
aristotle prove-from-file problem.lean

# Submit informal (AVOID - causes interpretation drift)
aristotle prove-from-file --informal problem.txt

# Check status
aristotle  # TUI option 4 for history
```

### Python API

```python
from aristotlelib import Project, ProjectInputType, set_api_key
import asyncio, os

async def submit():
    set_api_key(os.environ["ARISTOTLE_API_KEY"])
    project = await Project.prove_from_file(
        input_file_path="problem.lean",
        project_input_type=ProjectInputType.FORMAL_LEAN,
        wait_for_completion=True
    )
    print(f"Result: {project.status}")

asyncio.run(submit())
```

---

## Problem Selection Criteria

### Good Candidates
- ✅ In Formal Conjectures (pre-formalized)
- ✅ Bounded complexity (search space < 2^20)
- ✅ Clear discrete structure
- ✅ Recent partial progress (2023-2025)

### Bad Candidates
- ❌ Requires formalization from English
- ❌ Asymptotic/continuous problems
- ❌ Massive search spaces (R(5,5), quantum collision)
- ❌ No existing Mathlib infrastructure

---

## Grok API for Verification

```bash
python3 << 'EOF'
import json
prompt = """
Original problem: [paste original]
Aristotle's theorem: [paste from output]

Does Aristotle's theorem EXACTLY match the original?
Check: quantifiers, hypotheses, conclusion.
If mismatch, explain precisely what differs.
"""
req = {"messages": [{"role": "user", "content": prompt}], "model": "grok-4", "temperature": 0}
json.dump(req, open('/tmp/req.json', 'w'))
EOF

curl -s -X POST https://api.x.ai/v1/chat/completions \
  -H "Authorization: Bearer $GROK_API_KEY" \
  -H "Content-Type: application/json" \
  -d @/tmp/req.json | python3 -c "import sys,json; print(json.load(sys.stdin)['choices'][0]['message']['content'])"
```

---

## The Bottom Line

### What Failed (0/12)
- Submitting English descriptions
- Letting AI formalize AND prove
- Not iterating on near-wins
- No verification of output theorems

### What Works (Boris 90%)
- Pre-formalized Lean statements
- Locked theorem signatures
- AI fills proof only
- Zero intervention

### Action Items
1. **Find problems in Formal Conjectures** (pre-formalized)
2. **Lock theorem statements** (three-agent protocol)
3. **Iterate on Tuza** (047671c7 has only 2 holes)
4. **Verify every output** (quantifier-by-quantifier check)

---

## Reference Documents

- `ARISTOTLE_12_SUBMISSIONS_ANALYSIS.md` - Full audit of 12 failures
- `docs/BORIS_VS_OUR_APPROACH.md` - Why Boris succeeded
- `docs/ERDOS_REAL_PATTERNS_DEC_2025.md` - What actually works
- https://github.com/google-deepmind/formal-conjectures - Pre-formalized problems
