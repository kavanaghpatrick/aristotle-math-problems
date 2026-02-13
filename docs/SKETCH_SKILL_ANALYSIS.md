# Sketch Skill Analysis: Known Proofs vs Open Problems

**Date**: February 9, 2026
**Analysis By**: Claude Sonnet 4.5
**User Goal**: Use Aristotle's INFORMAL mode to work on OPEN mathematical problems, not just formalize already-solved results

---

## Executive Summary

The `/project:sketch` skill is **optimized for formalizing known proofs**, not generating speculative proof attempts for open problems. This is a fundamental mismatch with the user's stated goal.

**Key Evidence**:
- The skill pipeline is built around "IDEATE → SKETCH → FORMALIZE" where IDEATE means "find the proof" and SKETCH means "write it down"
- All success metrics (slot562, 563) are from **solved problems with published proofs**
- The skill explicitly gates on "Is the proof known?" and recommends SKIP for open problems
- Quality assessment criteria assume we have mathematical content to communicate, not that we're generating novel mathematics

---

## Full Skill Content

The sketch skill (located at `/Users/patrickkavanagh/math/.claude/commands/sketch.md`) follows this structure:

### Step 0: Validate Input
Asks user to specify the problem (file, Erdos/OEIS number, or description)

### Step 1: IDEATE — Understand the Problem
**Key assumption**: "Research the mathematics... find the proof (if it exists)"

Critical question asked:
```
"Is the proof of this result already known?"
Options:
- "Known proof exists (Recommended)" — Highest success rate
- "Solved, proof not published" — Believed true with evidence
- "Open problem" — Low success rate, consider falsification first
```

**This is the smoking gun**: The skill treats "known proof" as the RECOMMENDED path and "open problem" as low-priority with warning flags.

### Step 2: SKETCH — Write the Proof
Template structure:
```
## Theorem Statement
[Precise mathematical English]

## Proof Strategy
[High-level: induction, contradiction, etc.]

## Key Lemmas
[With proof sketches for each]

## Main Proof
[How the lemmas combine]

## Relevant Mathlib
[Specific lemmas to use]
```

**Critical assumption**: We already know the proof strategy, the key lemmas, and how they fit together. This is documentation of existing mathematics, not discovery.

### Quality Gate
Checklist includes:
- "Proof strategy is explicit (not just 'prove it')"
- "Each key lemma has a proof indication"

**This assumes we have proof content to write down.**

### Example of "Good" Sketch (slot562 — 53 lines input, 117 lines proven output):
```
"For any finite cyclic group G of order n, the sum of orders equals sigma(n).
Each element of order d contributes d, and there are phi(d) such elements.
Total = sum_{d|n} phi(d) * d. Use Mathlib: Nat.totient, Nat.divisors..."
```

This is a **transcription of known mathematics** from Leinster (2001), not discovery.

### Example of "Bad" Sketch:
```lean
theorem my_theorem : forall n, P n := by sorry
```

The "bad" version is criticized for giving Aristotle "ZERO mathematical insight" — but this is exactly what an open problem looks like. We don't have the insight yet.

---

## Supporting Evidence from Related Skills

### `/project:screen` skill (screening problems for viability)

**G1: Sketchability — "most important gate"**:
- PASS: "Known proof exists, we can outline the argument"
- SOFT PASS: "Partial proof known, we can sketch most of it"
- FAIL: "Open problem requiring novel math, no known approach"

**Scoring dimension S1** (25% weight, highest of any dimension):
- 10 = "known proof, clear sketch"
- 5 = "partial"
- 1 = "open problem"

**Pipeline Recommendation Table**:
```
| S1 ≥ 7 AND S2 ≥ 7 | Track A: INFORMAL sketch — PRIMARY |
| S1 < 5 AND S2 < 5 | NO VIABLE TRACK — Reject |
```

**Explicit statement**: "8.0+: Excellent — known proof in NT/algebra, first-ever formalization"

### `/project:sweep` skill (batch discovery)

**Step 4: Sketchability Assessment**:
```
Can we write a good proof sketch?
- Known proof exists → HIGH sketchability
- Solved but no published proof → MEDIUM sketchability
- Open problem → LOW sketchability (Track D only)
```

**Track Assignment**:
- Track A (INFORMAL): "Known proof + NT/algebra + we CAN write a sketch"
- Track D (Research): "Open problem or needs novel math" → **Backlog or skip**

**Tier Assignment**:
- Tier A: "known proof + NT/algebra" → Generate sketch, submit immediately
- Tier D: "Low sketchability or bad domain" → Queue for later
- Tier X: "no known proof in bad domain" → **SKIP**

---

## What Aristotle Actually Does (from MEMORY.md context)

### INFORMAL mode (what the sketches use):
- **Input**: Natural language proof (~50-100 lines)
- **Output**: 5:1 ratio, constructs formal proof from scratch
- **What it adds**: Lean syntax, Mathlib API discovery, tactic selection, type inference
- **What it does NOT add**: Novel mathematical ideas, proof strategies, key lemmas

### Evidence from successful submissions:
- **slot562** (Leinster cyclic): 53 lines → 117 lines. Input included: theorem, proof strategy, key steps, Mathlib hints
- **slot563** (Leinster nonabelian): 66 lines → 235 lines. Input included: explicit witness (S₃ × C₅), enumeration of normal subgroups, calculation showing 60 = 60
- **slot564** (Leinster abelian): 78 lines → 404 lines. Input was complete proof outline

All three referenced **published mathematics** (Leinster 2001, arXiv:math/0104012).

### Failure modes:
- **FORMAL sorry=1 in combinatorics**: 0/183 success rate
- **Open problems**: Tuza ν=4 PATH_4 case has been stuck for months despite massive effort
- **"Apex-based bridge coverage"**: Counterexample found, approach dead
- **"6-packing argument"**: Negated on K₄, approach dead

When the mathematics doesn't exist, Aristotle cannot construct it.

---

## The Core Assumption: Engineering vs Discovery

The entire pipeline rests on this division of labor:

| Agent | Role | What They Add |
|-------|------|---------------|
| **Claude** | IDEATE + SKETCH | Mathematical insight, proof strategy, key lemmas |
| **Aristotle** | FORMALIZE | Lean encoding, Mathlib APIs, tactic chains |

From CLAUDE.md:
> "Aristotle is a world-class **proof engineer**. In INFORMAL mode it constructs novel proof structures, discovers Mathlib APIs, and produces 5:1 output-to-input ratios. Our job is to feed it good mathematical ideas. **The bottleneck is insight generation, not formalization.**"

From MEMORY.md:
> "Aristotle is a **proof engineer**, not a mathematician."

**The system assumes Claude generates mathematical insight, and Aristotle engineers it into Lean.**

But if Claude doesn't have the proof (because the problem is open), there's nothing for Aristotle to engineer.

---

## Gap Analysis: Known Proofs vs Open Problems

### What the current skill does well:
1. **Guides research** into known proofs (Step 1d: "find the proof (if it exists)")
2. **Structures proof transcription** (template with strategy, lemmas, Mathlib hints)
3. **Quality-gates thin sketches** before submission
4. **Assigns slots** and tracks submissions
5. **Provides examples** of good sketches (from known math)

### What the current skill does NOT support:
1. **Speculative proof generation** for open problems
2. **Incremental refinement** when first attempt fails
3. **Hypothesis testing** (try approach X, see what Aristotle produces)
4. **Leveraging Aristotle's search** to explore proof space
5. **Converting counterexamples** into refined conjectures
6. **Multi-round collaboration** with Aristotle

### Fundamental mismatches:
| For Known Proofs | For Open Problems |
|------------------|-------------------|
| Find proof → write it down → formalize | Try approach → see what happens → refine |
| Linear: IDEATE → SKETCH → FORMALIZE | Iterative: SKETCH → ATTEMPT → LEARN → RESKETCH |
| Success = Aristotle proves exactly what we said | Success = Aristotle's attempt teaches us something |
| Quality = "proof strategy is explicit" | Quality = "approach is plausible enough to test" |
| Failure = thin sketch, missing details | Failure = fundamental mathematical obstacle |

---

## Why This Matters: The User's Actual Goal

The user wants to "use Aristotle's INFORMAL mode to work on OPEN mathematical problems."

**Current behavior**: The sketch skill treats open problems as low-priority, explicitly recommends skipping them, and provides no support for iterative refinement.

**What would be needed**:
1. **Accept uncertainty**: "We don't have a proof, but here's a plausible approach"
2. **Expect iteration**: First sketch may fail, use failure to learn
3. **Extract learning**: When Aristotle gets stuck, where does it get stuck? Why?
4. **Refine conjecture**: Maybe the claim is wrong, can we weaken it?
5. **Build incrementally**: Prove easier cases first, generalize later

**Example flow for open problem** (not currently supported):
```
Round 1: Sketch approach A → Aristotle fails at step X → Learn X is the blocker
Round 2: Revise approach to handle X → Aristotle fails at step Y → Learn Y needs a lemma
Round 3: Add lemma for Y → Aristotle succeeds on easier case → Generalize
Round 4: Extend to full claim → Proven
```

Current skill assumes Round 1 = success because we already have the full proof.

---

## Evidence from Tuza ν=4 (The Real Test Case)

The project has been stuck on Tuza ν=4 PATH_4 case for months:

**Status** (from CLAUDE.md):
```
| Case | Status | τ bound |
| PATH_4 | OPEN: both-endpoint base-edge externals | ≤ 9 (need ≤ 8) |
```

**Falsified approaches**:
- Apex-based bridge coverage (counterexample Fin 11)
- 6-packing argument (negated on K₄)
- LP duality (too complex)
- Universal apex for endpoints (counterexample Fin 10)
- τ(T_e(A)) ≤ 2 (FALSE, Fin 9)
- Debate consensus "all-six ⇒ ν≥5" (WRONG)

**This is an open problem** — no known proof exists. The current sketch skill would:
1. Ask "Is the proof known?" → No
2. Classify as "Open problem" → LOW sketchability
3. Recommend Track D (Research) → "Backlog or skip"
4. Gate: G1: Sketchability → FAIL
5. **Verdict: REJECT**

But this is precisely the problem the user wants to work on!

---

## What Changes Would Enable Open Problem Work?

### 1. New "Speculative Sketch" Mode

**Prompt changes**:
```diff
- "Is the proof of this result already known?"
+ "What is our confidence in the approach?"

- Recommended: "Known proof exists"
+ Recommended: "Plausible approach identified"

- Quality gate: "Proof strategy is explicit"
+ Quality gate: "Approach is specific enough to test"
```

**Template changes**:
```diff
  ## Proof Strategy
- [High-level: induction, contradiction, etc.]
+ [Approach to try: why we think this might work]

+ ## Known Obstacles
+ [What might go wrong, what we're uncertain about]

+ ## Success Criteria
+ [What would constitute progress even if full proof fails]
```

### 2. Iteration Support

**New steps**:
- Step 3.5: "Submit and Learn" — After Aristotle attempts, what did we learn?
- Step 4: "Refine or Pivot" — Based on Aristotle's output, revise approach
- Step 5: "Document Knowledge" — Even if proof fails, what did we learn?

**Database additions**:
```sql
CREATE TABLE exploration_rounds (
  problem_id TEXT,
  round_number INTEGER,
  approach TEXT,
  aristotle_output TEXT,
  lessons_learned TEXT,
  next_hypothesis TEXT
);
```

### 3. Reframe Success Metrics

| Current Metric | Open Problem Metric |
|----------------|---------------------|
| Proven (0 sorry) | Progress (learned something) |
| 5:1 output ratio | Identified blocker |
| 100% success rate on known proofs | 30% success rate on open problems |
| Time to proof | Rounds to proof (may be many) |

### 4. Leverage Aristotle's Exploration

**New skill command**: `/project:explore <problem> <approach>`

Rather than SKETCH (write down known proof), EXPLORE (try approach, see what happens):
```
1. State problem
2. Propose approach (may be incomplete)
3. Submit to Aristotle INFORMAL
4. Analyze where Aristotle gets stuck
5. Extract that as a lemma to work on
6. Repeat
```

This treats Aristotle as a **proof search agent**, not just a **proof encoding agent**.

---

## Concrete Recommendations

### Immediate (to unblock user):

1. **Add `--speculative` flag to `/project:sketch`**:
   ```bash
   /project:sketch "Tuza PATH_4 approach: apex-based coverage" --speculative
   ```
   This bypasses the "known proof" gates and uses a different template.

2. **Create `/project:explore` command**:
   Separate from `sketch` (which assumes knowledge), `explore` assumes uncertainty.

3. **Document the current limitation**:
   Add to CLAUDE.md:
   ```
   ## Known Limitation: Open Problems

   The sketch skill is optimized for known proofs. For open problems:
   - Use `/project:explore` instead of `/project:sketch`
   - Expect multiple rounds of refinement
   - Success = learning, not just proving
   ```

### Medium-term (improve capability):

4. **Build iteration loop**:
   - `/project:explore <problem> <approach>` → submits attempt
   - `/project:analyze-failure <uuid>` → extracts blockers from Aristotle's output
   - `/project:refine <uuid> <new-approach>` → submits revised version
   - Track lineage in database

5. **Change screening criteria**:
   ```diff
   - G1: Sketchability - FAIL if open problem
   + G1: Approachability - Can we articulate a testable approach?
   ```

6. **Add "hypothesis testing" mode**:
   Sometimes we're not even sure the claim is true. Mode where:
   - We sketch a proof attempt
   - If Aristotle finds contradiction, that's SUCCESS (claim is false)
   - If Aristotle proves it, that's SUCCESS (claim is true)
   - If Aristotle gets stuck, we learn where the hard part is

### Long-term (research question):

7. **Multi-agent proof search**:
   - Claude proposes approaches
   - Aristotle attempts formalization
   - Codex finds counterexamples
   - Gemini suggests alternative strategies
   - System iterates until convergence

This is closer to AlphaProof's approach: search over proof space, not just encode human-discovered proofs.

---

## Comparison to Other Discovery Modes

The project actually has other modes that DO support discovery:

### Track B: Computational Discovery (working well)
- **Assumption**: We can compute the answer (witness, pattern, bound)
- **Process**: Compute → encode in Fin n → `native_decide` → proven
- **Success rate**: 6/6 (100%) but only for finite verification
- **Example**: A375077 extension (computed a(8), a(9), proved they satisfy property)

### Track C: Falsification (working well)
- **Assumption**: Claim might be false
- **Process**: Submit negation on Fin 5-7 → if proven, claim is false
- **Success rate**: ~40% of tested conjectures are false (43 confirmed)
- **Example**: slot556 falsified τ(T_e(A)) ≤ 2 on Fin 9

### Track D: Research Problems (NOT working)
- **Assumption**: Open problem, no known proof
- **Process**: ??? (not defined)
- **Success rate**: 0% (stuck on Tuza PATH_4 for months)
- **Current status**: "Gated — no new strategies until bridge gap resolved"

**The gap**: Tracks B and C support discovery via computation/falsification. Track A (INFORMAL sketches) assumes known proofs. **There's no track for "discover a proof via iterative collaboration with Aristotle."**

---

## The Deeper Question: What IS Aristotle Capable Of?

From the project's own observations:

**INFORMAL mode adds**:
- Lean syntax and types
- Mathlib API discovery
- Tactic selection and sequencing
- Proof structure (converting narrative to tactics)
- 5:1 expansion ratio

**INFORMAL mode does NOT add** (based on 0/183 sorry=1 failure rate):
- Novel mathematical insights
- Key lemmas not mentioned in sketch
- Proof strategies not outlined
- Mathematical content beyond what Claude provides

**Exception: slot572 (Integer Complexity)**:
- Input: Theorem statement + definitions (sorry=1, NT domain)
- Aristotle: Built inductive predicate + decidability + interval_cases
- This worked because: (1) NT domain, (2) structural definition, (3) Mathlib-rich

**Hypothesis**: Aristotle can do **structural engineering** (build the right definitions, find the right API, construct the right recursion) but not **mathematical discovery** (invent lemmas, discover proof strategies, overcome fundamental obstacles).

If true, then:
- Open problems where we have a **structural approach** → Maybe Aristotle can help
- Open problems where we need **mathematical insight** → Aristotle cannot help

**Question for user**: Do you want to use Aristotle for:
1. Structural engineering on open problems? (e.g., "here's the induction I want to do, can you make it work?")
2. Mathematical discovery on open problems? (e.g., "find me a proof strategy")

Current skill supports neither. But (1) is plausibly within reach, (2) is likely beyond Aristotle's capabilities.

---

## Conclusion

**Current State**:
The `/project:sketch` skill assumes we have mathematical content (known proofs) and need engineering (formalization). It explicitly deprioritizes open problems and provides no support for iterative refinement.

**User Goal**:
Work on open problems using Aristotle's INFORMAL mode.

**Gap**:
Fundamental mismatch. The skill is optimized for transcription, not discovery.

**Path Forward**:
1. **Short-term**: Add `--speculative` flag or `/project:explore` command that bypasses "known proof" gates
2. **Medium-term**: Build iteration loop (sketch → attempt → learn → refine)
3. **Long-term**: Multi-agent proof search architecture

**Realism Check**:
Aristotle's 0/183 sorry=1 rate in combinatorics suggests it cannot discover novel mathematics. Even with better tooling, open problems may remain out of reach unless:
- We can articulate structural approaches (not just "prove it")
- We work in NT/algebra domains (Mathlib-rich)
- We're willing to iterate many times
- We measure success as "learning" not just "proving"

**The Real Bottleneck**:
Not the sketch skill's design, but **Aristotle's capabilities**. The skill reflects an accurate understanding of what Aristotle can do: engineer known mathematics, not discover unknown mathematics.

If the user wants to push that boundary, they'll need to invent new interaction patterns the current project hasn't explored.
