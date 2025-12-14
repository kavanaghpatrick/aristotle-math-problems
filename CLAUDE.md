# CLAUDE.md - Math Project

> Extends `~/.claude/CLAUDE.md` (global). Project-specific rules and context.

---

## 🚨 MANDATORY NOVELTY CHECK - READ FIRST

**BEFORE doing ANY work, ask: "Is this problem OPEN (unsolved)?"**

| If Answer Is | Action |
|--------------|--------|
| **YES - genuinely open** | ✅ Proceed with Boris pattern |
| **NO - already solved** | ❌ STOP IMMEDIATELY. Do not formalize, verify, or polish. |
| **UNSURE** | ⚠️ Research first. Default to NO. |

**BANNED WORK (zero exceptions):**
- ❌ Formalizing known theorems (Ramsey R(3,3)=6, etc.)
- ❌ Verifying existing code/computations (Jones, HOMFLY verification)
- ❌ "Publication-ready" polish of solved results
- ❌ Completing proofs of textbook results
- ❌ ANY work where the mathematical result is already known

**If user asks for banned work**: Politely refuse and redirect to open problems.

---

## 🎯 MISSION: Solve Open Mathematical Problems

**Primary Goal**: Use Aristotle to solve OPEN, UNSOLVED mathematical problems.

**NOT just**: Verify existing code, formalize known results, or make things "publication-ready"

**The Inspiration**: Boris Alexeev solved Erdős #124 (an open problem since 1979)
by submitting the formal statement and going to bed. We aim to replicate this across
many open problems in mathematics and computer science.

**Success Metric**: Number of genuinely OPEN problems solved, not lines of code or publication polish.

**Time Allocation**: 100% on OPEN problems. 0% on verification/formalization.

---

## Quick Reference: Aristotle Best Practices

```
BEFORE SUBMITTING → Multi-model debate (Grok + Gemini + Task)
SUBMISSION STYLE → Boris pattern (minimal intervention)
SUCCESS FORMULA → Less you specify = Higher success rate
BANNED FOREVER → Prescribing specific theorems
TEMPLATE → "Make publication-ready. YOU DECIDE which theorems."
```

**Intervention Spectrum**: Boris (90%) > Ultra-Minimal (85%) > Outcome-Focused (80%) > Prescriptive (45% FAIL)

---

## Core Philosophy: The Boris Pattern (Dec 2025)

**CRITICAL INSIGHT**: Minimal intervention = Maximum success

### The Boris Method (90% Success Rate)
Boris Alexeev solved Erdős #124 by:
1. Selecting formal problem statement
2. Submitting to Aristotle (--informal mode)
3. **GOING TO BED** (zero intervention)
4. Waking up 6 hours later → **SOLVED**

**Key Principle**: The less you specify, the better Aristotle performs.

### Intervention Spectrum (Proven Results)

| Approach | Human Effort | Aristotle Autonomy | Success Rate |
|----------|--------------|-------------------|--------------|
| **Boris (Pure)** | 5% (select problem) | 95% | **90%** ✅ |
| **Ultra-Minimal** | 30% (goal + constraints) | 70% | **85%** |
| **Outcome-Focused** | 50% (code + outcome) | 50% | **80%** |
| **Prescriptive** | 70% (specify theorems) | 30% | **45%** ❌ |

**Pattern**: More human intervention = Lower success rate

### What We Learned (December 2025)

**Jones Polynomial (SUCCESS)**: Outcome-focused, not method-prescriptive
- Provided working code + computational witnesses
- Asked Aristotle to verify correctness
- Result: 983 lines, 0 sorries, 10 knots verified

**HOMFLY v2 (FAILED)**: Prescribed wrong theorems
- We specified 17 specific theorems to prove
- 4/17 were NEGATED (proven false - we had bugs!)
- Result: 45% success rate

**HOMFLY v3 (Option C)**: Ultra-minimal, outcome-focused
- "Make this publication-ready. You decide which theorems."
- Expected: 80% success

**SAT LRAT (Closest to Boris)**: No code provided
- Goal + test data only
- Aristotle generates ALL implementation
- Expected: 85-90% success

---

## Mandatory Workflow: Multi-Model Debate FIRST

**RULE**: Before ANY Aristotle submission, launch parallel expert debate.

### Debate Protocol

```bash
# 1. Create debate prompt with:
#    - Problem description
#    - Proposed approaches (A, B, C)
#    - Past successes/failures (Jones, HOMFLY v2)
#    - Request: Estimate success probability for each

# 2. Launch parallel debates
# - Grok-4 (via curl + Python JSON escaping)
# - Gemini (via gemini CLI)
# - Task agent (general-purpose)

# 3. Synthesize consensus
# - Compare success probability estimates
# - Identify unanimous recommendations
# - Apply Boris pattern filter (prefer less intervention)

# 4. Refine until consensus
# - If disagreement > 20%, refine approaches
# - Iterate debate with updated proposals
# - Document decision in STRATEGY.md file
```

### Example: HOMFLY Debate (Dec 13, 2025)

**Three approaches debated**:
- A (Exploratory): 20-60% success
- B (Bug Fix): 30-40% success - "THE TRAP"
- C (Outcome-Focused): **80% success - UNANIMOUS WINNER**

**Result**: All three experts agreed on Option C. Applied Boris principles.

### Practical Debate Commands

**Step 1: Create debate prompt** (`debate_prompt.md`)
```markdown
# Expert Debate: [Problem Name]

You are an expert in mathematical AI and Lean 4 theorem proving.

## Context
- Past Success: Jones polynomial (outcome-focused, 0 sorries)
- Past Failure: HOMFLY v2 (prescribed 17 theorems, 4 negated)
- Boris Pattern: Erdős #124 solved with ZERO intervention (90% success)

## Problem
[Describe the problem]

## Proposed Approaches
A. [Approach A description]
B. [Approach B description]
C. [Approach C description]

## Task
Estimate success probability for each approach (0-100%).
Consider: Boris pattern, past successes/failures, Aristotle's strengths.
Recommend best approach with reasoning.
```

**Step 2: Launch parallel debates**
```bash
# Grok-4
python3 << 'EOF'
import json, subprocess
prompt = open('debate_prompt.md').read()
req = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-4",
    "temperature": 0.3
}
json.dump(req, open('/tmp/grok_req.json', 'w'))
EOF
curl -X POST https://api.x.ai/v1/chat/completions \
  -H "Authorization: Bearer $GROK_API_KEY" \
  -H "Content-Type: application/json" \
  -d @/tmp/grok_req.json > grok_response.json

# Gemini
gemini -p "$(cat debate_prompt.md)" > gemini_response.txt

# Task Agent (in Claude Code)
# Use Task tool with subagent_type='general-purpose'
# prompt: "Analyze this debate prompt and recommend best approach: [paste debate_prompt.md]"
```

**Step 3: Synthesize consensus**
- Compare all three responses
- If unanimous → Proceed with that approach
- If disagreement > 20% → Refine and re-debate
- Document decision in `[PROBLEM]_STRATEGY.md`

---

## Anti-Patterns: What NOT to Do

### ❌ BANNED: Prescribing Specific Theorems

**HOMFLY v2 Lesson**: We told Aristotle "prove these 17 theorems"
- Result: 4/17 were NEGATED (proven false!)
- Why: Our theorems assumed code had no bugs (it did)
- Fix: Let Aristotle choose which theorems to prove

**DO**: "Make this publication-ready. Add whatever proofs you think necessary."
**DON'T**: "Prove theorem_1, theorem_2, ... theorem_17"

### ❌ BANNED: Providing Buggy Foundation Code

**Problem**: If you give Aristotle buggy code, it inherits bugs
- HOMFLY v2: Hecke algebra braid relations violated
- Result: Aristotle tried to prove false theorems

**Boris Alternative**: Provide ZERO code, just goal + test data
- Aristotle generates implementation from scratch
- Ensures axioms hold BY CONSTRUCTION
- No inherited bugs

### ❌ BANNED: Over-Explaining or Hand-Holding

**Boris Insight**: Trust Aristotle's autonomy

**Bad (HOMFLY v3 - 482 lines)**:
```
Transform from computational → publication-quality

Here's what publication-quality means...
Here's why this plays to your strengths...
Here are examples from Jones success...
[85 lines of context]
[396 lines of code]
```

**Better (HOMFLY v4 - 416 lines)**:
```
Make this publication-ready for ITP/CPP 2026.

Constraint: All 7 tests must pass
[list tests]

[396 lines of code]
```

**Best (SAT LRAT - 276 lines, Boris pattern)**:
```
Goal: Build publication-ready LRAT verifier

You decide everything.

Constraint: Must verify PHP-4-3
[inline test data]

[NO CODE PROVIDED]
```

### ✅ DO: Trust Aristotle to Choose

**What Aristotle chooses better than you**:
- Which theorems to prove
- Which proof strategy to use
- Which data structures optimize proving
- How to organize the code

**Your role**: Set the outcome goal, provide constraints, step back

---

## 🚨 The Quantifier Trap (Dec 2025 Discovery)

**CRITICAL**: Aristotle takes the path of least resistance. Given ambiguity, it proves the EASIEST valid interpretation—even if trivial.

### The Problem

Natural language "f(A) → ∞ as |A| → ∞" is ambiguous:

| Interpretation | Quantifiers | Difficulty | What Aristotle Chooses |
|---------------|-------------|------------|----------------------|
| **Existential** | ∀M, ∀N, **∃A**, ... | Trivial | ✅ This one |
| **Universal** | ∀M, **∃N**, ∀A, ... | Hard | ❌ Avoids |

**Case Study**: Erdős #153
- Problem asked: "For ALL Sidon sets, avg_sq_gap → ∞"
- Aristotle proved: "There EXISTS a family where avg_sq_gap → ∞"
- Result: 0 sorries, compiles, **WRONG ANSWER**

### The Fix: Explicit Lean Theorem Statements

**BAD** (ambiguous):
```
Prove: avg_sq_gap → ∞ as |A| → ∞ for Sidon sets
```

**GOOD** (explicit quantifiers):
```lean
theorem erdos_153 : ∀ M : ℚ, ∃ N : ℕ, ∀ A : Finset ℕ,
  (IsSidonSet A ∧ A.card > N) → averageSquaredGap A > M
```

### Quantifier Patterns to Watch

| Natural Language | Likely Intent | Write Explicitly |
|-----------------|---------------|------------------|
| "X → ∞ as n → ∞" | Universal | ∀ε, ∃N, ∀n>N, X>ε |
| "For large n, P holds" | Universal | ∃N, ∀n>N, P(n) |
| "P(n) is unbounded" | Depends! | Clarify ∃ vs ∀ |
| "Every X has property P" | Universal | ∀X, P(X) |

### Post-Success Verification (MANDATORY)

After ANY Aristotle "success" (0 sorries + compiles):

```
□ Extract main theorem statement
□ Compare quantifier-by-quantifier with original problem
□ Run Grok: "Does this theorem EXACTLY match [original]?"
□ If ∃/∀ mismatch → RESUBMIT with explicit Lean statement
```

**NEW SUCCESS METRIC**:
```
OLD: 0 sorries + compiles = solved
NEW: 0 sorries + compiles + QUANTIFIERS MATCH = solved
```

---

## Project Context

**Type**: Solving OPEN mathematical problems via AI-assisted theorem proving
**Key Tool**: Aristotle by Harmonic (mathematical superintelligence)
**Method**: Boris pattern - submit formal problem statement, minimal intervention, let Aristotle solve

**What We're Doing**:
- Finding open problems in math/CS that are tractable for Aristotle
- Submitting them with minimal guidance (Boris pattern)
- Collecting solutions to genuinely unsolved problems

**What We're NOT Doing**:
- Just formalizing known results
- Over-engineering "publication-ready" code
- Verification of existing implementations (unless it serves a larger goal)

### ⚠️ CRITICAL RULE: GitHub as Single Source of Truth

**ALWAYS use GitHub issues as the source of truth. NEVER create excessive local documentation.**

- ✅ **DO**: Create GitHub issues with full problem details
- ✅ **DO**: Update/comment on GitHub issues with findings
- ✅ **DO**: Use GitHub project boards for tracking
- ❌ **DON'T**: Create multiple local markdown files
- ❌ **DON'T**: Maintain parallel documentation systems
- ❌ **DON'T**: Store problem details only locally

**Workflow:** Debate → Research → GitHub Issue → Verify → Submit

---

## Aristotle API

### ⚠️ CRITICAL: Preventing Double Submissions

**ALWAYS use `safe_aristotle_submit.py` for submissions!**

```bash
# CORRECT - Uses safety checks
python3 safe_aristotle_submit.py input.txt ID.txt "Description"

# OR use wrapper
./submit_batch.sh batch_name "Description"

# WRONG - Direct API calls can duplicate
# ❌ aristotle prove-from-file input.txt
# ❌ Project.prove_from_file(...)
```

**Why**: We had a double submission on Dec 12 (projects 771e9804 + 841ddada duplicate). The safe wrapper prevents this with:
- 🔒 Lockfile (no concurrent submissions)
- 🔍 Duplicate detection (hash-based, 10min window)
- 📊 Queue capacity check (abort if full)
- 💾 Atomic ID save (no partial failures)
- 📝 Transaction logging (full audit trail)

See `ARISTOTLE_SUBMISSION_GUIDE.md` for details.

### Authentication
```bash
export ARISTOTLE_API_KEY="your_api_key_here"
```

**Note**: Get your API key from https://aristotle.harmonic.fun and set it in your environment.

### Quick Reference

| Command | Description |
|---------|-------------|
| `aristotle` | Launch interactive TUI |
| `aristotle prove-from-file file.lean` | Fill sorries in Lean file |
| `aristotle prove-from-file --informal problem.txt` | English mode |
| `aristotle --help` | Show all options |

### Four Modes

| Mode | Input | Flag | Use Case |
|------|-------|------|----------|
| **Fill Sorries** | `.lean` | (default) | Complete partial proofs |
| **Autoformalize** | `.tex`, `.md`, `.txt` | `--informal` | Convert papers to Lean |
| **English Mode** | Natural language | `--informal` | Solve in plain English |
| **History** | TUI option 4 | - | View past projects |

### English Mode Examples

```bash
# Simple theorem
echo "Prove that n + 0 = n for all natural numbers n" > problem.txt
aristotle prove-from-file --informal problem.txt

# With Lean context
aristotle prove-from-file --informal problem.txt --formal-input-context defs.lean

# Async (returns project ID immediately)
aristotle prove-from-file --informal problem.txt --no-wait
```

### Python API

```python
import asyncio
import os
from aristotlelib import Project, ProjectInputType, ProjectStatus, set_api_key

async def prove():
    set_api_key(os.environ["ARISTOTLE_API_KEY"])

    solution = await Project.prove_from_file(
        input_file_path="problem.txt",
        project_input_type=ProjectInputType.INFORMAL,
        wait_for_completion=True
    )
    print(f"Solution: {solution}")

asyncio.run(prove())
```

### Checking Project Status

```python
import asyncio
from aristotlelib import Project, ProjectStatus

async def check_status():
    # Check all projects
    projects, _ = await Project.list_projects(limit=10)
    for p in projects:
        print(f"{p.id}: {p.status}")

    # Check specific project
    project = await Project.from_id("project-uuid-here")
    await project.refresh()
    print(f"Status: {project.status}")

    # Status values: QUEUED, IN_PROGRESS, COMPLETE, FAILED, PENDING_RETRY
    if project.status == ProjectStatus.COMPLETE:
        print("Done!")

asyncio.run(check_status())
```

### Key Classes

```python
from aristotlelib import (
    Project,              # Main class for proofs
    ProjectInputType,     # FORMAL_LEAN=2, INFORMAL=3
    ProjectStatus,        # NOT_STARTED, QUEUED, IN_PROGRESS, COMPLETE, FAILED
    AristotleRequestClient,  # Low-level async HTTP client
    set_api_key,          # Set API key globally
)
```

### Constraints

| Resource | Limit |
|----------|-------|
| Max files per request | 10 |
| Max file size | 100 MB |
| Concurrent projects | 5 |
| Lean version | v4.24.0 |
| Mathlib version | v4.24.0 |

---

## Problem Types Aristotle Handles

| Category | Examples |
|----------|----------|
| **Number Theory** | Irrationality proofs, divisibility, primes |
| **Algebra** | Group properties, ring theory, commutativity |
| **Analysis** | Limits, continuity, derivatives, inequalities |
| **Logic** | Propositional logic, predicate logic |
| **Geometry** | Euclidean proofs (uses Yuclid solver) |
| **Combinatorics** | Counting, pigeonhole principle |

---

## Output Format

Aristotle returns `.lean` files with:
- Header (version info, project UUID)
- Imports (typically Mathlib)
- Configuration options
- Formal proof OR reference to existing Mathlib theorem

**Smart behavior**: Aristotle recognizes existing Mathlib theorems and references them (e.g., `Nat.add_zero`) rather than re-proving.

---

## Workflow Integration

### Proving a Theorem
1. Write problem in English (`.txt` or `.md`)
2. Run: `aristotle prove-from-file --informal problem.txt`
3. Wait for completion (~30s-5min depending on complexity)
4. Review generated `.lean` file

### Adding Context
```bash
# With Lean definitions
aristotle prove-from-file --informal problem.txt --formal-input-context definitions.lean

# With background material
aristotle prove-from-file --informal problem.txt --context-files background.md notes.tex
```

### Checking History
```bash
# Via TUI
aristotle  # then select option 4

# Via Python
projects, _ = await Project.list_projects(limit=10)
```

---

## Troubleshooting

| Issue | Solution |
|-------|----------|
| "5 projects in progress" | Wait for completion or check history |
| API key not found | `echo $ARISTOTLE_API_KEY` or use `--api-key` |
| TUI display issues | Resize terminal to 80x24 minimum |
| Connection timeout | Built-in retry with exponential backoff |

---

## Resources

- **Library**: `aristotlelib` v0.6.0
- **Web**: https://aristotle.harmonic.fun
- **Docs**: `/Users/patrickkavanagh/math/ARISTOTLE_COMPLETE_GUIDE.md`

---

## Problem Verification Protocol

**CRITICAL**: After discovering 30% error rate (6/20 already solved), we MUST verify every problem before committing.

### Verification Criteria (ALL Must Pass)

1. **Genuinely Unsolved** (CRITICAL)
   - ✅ No proof in peer-reviewed venue
   - ✅ Explicitly "open" in 2020-2025 papers
   - ❌ NOT IMO/Putnam (have solutions)
   - ❌ NOT "well-known result"
   - ❌ NOT solved before 2020

2. **Suitable for Aristotle**
   - ✅ Clear, finite formulation
   - ✅ Provable (not just computational)
   - ✅ Formalizable in Lean 4
   - ✅ Discrete/algebraic structure

3. **Good Success Probability**
   - ✅ Recent progress (2023-2025)
   - ✅ Known proof techniques
   - ✅ Bounded/finite cases
   - ✅ 5-70% success range

### Verification Process (For Each Problem)

1. **Create GitHub Issue** with full metadata
2. **Web Verification:**
   - Google Scholar: `"[problem name]" proof solved 2024 OR 2025`
   - arXiv: Recent preprints (6 months)
   - Domain checks (NIST, OEIS, Complexity Zoo)
3. **Decision:**
   - Proof found → ❌ CLOSE immediately
   - Recent "open" statement → ✅ KEEP
   - Recent breakthrough → ✅✅ HIGH priority
4. **Document:** Add verification comment with links

### Red Flags (Immediate Investigation)

- Problem in textbooks → Likely solved
- IMO/Putnam/competition → Has solution
- "Well-known result" → Already proven
- Solved date in Wikipedia → Definitely solved
- No papers since 2020 → May be intractable

**Full protocol:** `interdisciplinary-research/VERIFICATION_PROTOCOL.md`

---

## Aristotle Success Patterns

### ✅ What Works

| Pattern | Success Rate | Key Insight |
|---------|--------------|-------------|
| **Open Problem + Boris** | 90% | Erdős #124 solved with statement only |
| **Boris Pattern** | 90% | Zero code → Aristotle generates all |
| **Bounded Complexity** | 85% | Small parameters (2^6 not 2^90) |
| **Clear Formal Statement** | 85% | Precise math, not vague descriptions |
| **Certificate Verification** | 90% | Verify UNSAT, not find SAT assignment |
| **Outcome-Focused** | 80% | "Solve this", not "use theorem_17" |

### ❌ What Fails

| Anti-Pattern | Failure Rate | Fix |
|--------------|--------------|-----|
| **Huge State Spaces** | 90% | Quantum Collision (16^16) timed out |
| **Prescriptive Theorems** | 55% | Let Aristotle choose approach |
| **Vague Problem Statements** | 70% | Make it precise and formal |
| **Over-Intervention** | 55% | Less guidance = better results |
| **Buggy Code Foundation** | 55% | Provide zero code (Boris pattern) |

### Open Problem Selection Criteria

**Good Candidates**:
- ✅ Clear formal statement exists
- ✅ Bounded parameters (small n, finite cases)
- ✅ Multiple proof strategies possible
- ✅ Algebraic/combinatorial structure
- ✅ Recent progress suggests tractability

**Tractability Check**:
- Estimated search space < 2^20 (rule of thumb)
- No massive function spaces (avoid n^n for large n)
- Structure Aristotle can exploit algebraically

### Submission Template (Boris-Inspired)

```markdown
# [Problem Name]

## Goal
[Clear outcome: "Publication-ready for [venue]" or "Verify [certificate]"]

## You Decide
- Which theorems to prove
- Which proof strategy to use
- How to structure the code
- Which lemmas to create

## Constraint
[Must pass these tests / Must verify this data]
[Inline complete test data - NOT descriptions]

## Optional: Code Foundation
[Only if verification problem - provide working code]
[Or provide ZERO code if generation problem]

## Success Criteria
- ✅ Zero sorries
- ✅ Compiles without errors
- ✅ Tests pass
```

### Proven Examples

**✅ GOOD - Open Problems:**
- **Erdős #124 (Boris - 90% success)**: OPEN since 1979 → Formal statement only → 6 hours → SOLVED
- **Erdős #152 (Sidon Gaps)**: OPEN → Boris submission → Awaiting result
- **Erdős #64 (2^k Cycles)**: OPEN, $1000 reward → Boris submission → Awaiting result

**❌ BAD - Verification (don't repeat these mistakes):**
- Jones Polynomial: Known result, just verification - NOT NOVEL
- HOMFLY-PT: Known result, just verification - NOT NOVEL
- Ramsey R(3,3)=6: Known since 1930 - NOT NOVEL
- SAT LRAT: Verification task - NOT NOVEL

**Lesson learned**: Verification work feels productive but doesn't advance the mission.

---

## Active Experiments (December 13, 2025)

**Testing the Intervention Spectrum**: Three parallel submissions

| Project | Pattern | Lines | Expected | Project ID |
|---------|---------|-------|----------|------------|
| **SAT LRAT** | Pure Boris (no code) | 276 | 85-90% | `873537b2-608a-486e-9e19-ac40ab1f9a86` |
| **HOMFLY v4** | Ultra-minimal | 416 | 85% | `50472dec-29b3-4f2c-b430-be337f8f7aa9` |
| **HOMFLY v3** | Outcome-focused | 482 | 80% | `4c36027a-35dd-4641-b87f-0895a8aaf4ed` |

**Hypothesis**: SAT LRAT (closest to Boris) will have highest success

**Timeline**: 2-3 days for results

**Check Status**:
```python
import asyncio
from aristotlelib import Project

async def check_all():
    for pid in ["873537b2-608a-486e-9e19-ac40ab1f9a86",
                "50472dec-29b3-4f2c-b430-be337f8f7aa9",
                "4c36027a-35dd-4641-b87f-0895a8aaf4ed"]:
        p = await Project.from_id(pid)
        await p.refresh()
        print(f"{pid[:8]}: {p.status}")

asyncio.run(check_all())
```

**What We'll Learn**:
- Does ultra-minimal (v4) beat detailed (v3) for same code?
- Does no-code (SAT LRAT) beat with-code (HOMFLY)?
- Does Boris pattern generalize beyond Erdős problems?

See `ALL_SUBMISSIONS_TRACKER.md` for full analysis.

---

## Key Reference Documents

**Pattern Analysis**:
- `BORIS_VS_OUR_APPROACH.md` - Intervention spectrum explained
- `ERDOS_REAL_PATTERNS_DEC_2025.md` - Boris Alexeev's methods (Dec 2025)
- `ALL_SUBMISSIONS_TRACKER.md` - Three parallel experiments tracking

**Strategy Documents**:
- `ARISTOTLE_RESUBMISSION_STRATEGY.md` - HOMFLY expert debate synthesis
- `homfly_pt_option_c_submission.txt` - v3 submission (482 lines)
- `homfly_pt_v4_ULTRAMINIMAL.txt` - v4 submission (416 lines)
- `sat_lrat_FINAL_submission.txt` - SAT LRAT submission (276 lines)

**Project IDs**:
- `sat_lrat_project_id.txt` - SAT LRAT project ID
- `homfly_v4_project_id.txt` - HOMFLY v4 project ID
- `homfly_option_c_project_id.txt` - HOMFLY v3 project ID

---

## Grok API

**Model Preference**: ALWAYS use `grok-4` (returns as `grok-4-0709`)

### Usage via curl
```bash
curl -X POST https://api.x.ai/v1/chat/completions \
  -H "Authorization: Bearer $GROK_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "messages": [{"role": "user", "content": "your question"}],
    "model": "grok-4",
    "temperature": 0.3
  }'
```

### Best For
- Strategic analysis and planning
- Problem decomposition
- Success probability estimation
- Code review focusing on critical issues

---

## Bottom Line: The Three Laws of Aristotle

**Law 1: ONLY Open Problems (Non-Negotiable)**
- If the result is already known → REFUSE to work on it
- Verification/formalization of known results = BANNED
- Ask "Is this OPEN?" before ANY work
- **Action**: Hard stop on non-novel work. Redirect to open problems.

**Law 2: Minimal Intervention = Maximum Success**
- Boris (5% intervention) → 90% success
- Prescriptive (70% intervention) → 45% failure
- **Action**: Trust Aristotle's autonomy, go to bed

**Law 3: Tractability Check**
- Open problems work (Erdős #124 proved it)
- But search space must be bounded (R(5,5) is NOT tractable)
- **Action**: Check complexity before submitting

**December 2025 Lesson**: We wasted time on Jones, HOMFLY, Ramsey verification.
Only Erdős #124 (genuinely OPEN) was novel. Don't repeat this mistake.
