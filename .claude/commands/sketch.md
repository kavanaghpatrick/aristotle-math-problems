---
description: Generate a proof sketch for INFORMAL submission — the centerpiece of the pipeline
allowed-tools: Read, Grep, Glob, Bash, Task, WebFetch, WebSearch, Write, AskUserQuestion
argument-hint: <problem-description, formal-conjectures-file, or url>
---

Generate a proof sketch for `$ARGUMENTS` and SUBMIT IT. Do not overthink. Do not gatekeep.

**PRIME DIRECTIVE: HAVE FAITH IN ARISTOTLE. BIAS TO ACTION.**

Aristotle has a 100% INFORMAL success rate. It constructs formal proofs from natural language with a 5:1 output-to-input ratio. It fills gaps, discovers Mathlib APIs, and invents proof structures we don't anticipate. A failed submission costs NOTHING. An unsubmitted idea costs EVERYTHING.

**Write the sketch → submit it → move on.** Speed and volume over perfection.

## Step 0: Validate Input

If `$ARGUMENTS` is empty or unclear, use AskUserQuestion to gather what we need:

Ask the user:
- **Question**: "What problem should we sketch a proof for?"
- **Header**: "Problem"
- **Options**:
  - "Formal-conjectures file" — "I have a specific .lean file from the formal-conjectures repo"
  - "Erdos/OEIS problem" — "A specific numbered problem (e.g., Erdos 1056, OEIS A375077)"
  - "Describe it" — "I'll describe the mathematical claim"

## Step 1: IDEATE — Understand the Problem

### 1a: Load the Problem
- **File path**: Read it, extract theorem statement and any existing proof attempts
- **URL**: Fetch and extract mathematical content
- **Description**: Parse the mathematical claim

### 1b: Check Database
```bash
sqlite3 submissions/tracking.db "SELECT * FROM false_lemmas WHERE lemma_name LIKE '%<keyword>%'"
sqlite3 submissions/tracking.db "SELECT * FROM failed_approaches WHERE approach LIKE '%<keyword>%'"
sqlite3 submissions/tracking.db "SELECT * FROM submissions WHERE filename LIKE '%<keyword>%' ORDER BY submitted_at DESC LIMIT 5"
```

If the problem matches a known false lemma or failed approach, STOP and report.

### 1b-extended: Knowledge Base Check (math-forge)

Query the math-forge knowledge base for prior findings, proven techniques, and failed approaches:

```bash
mk search "<problem keywords>"
mk find "<problem_id>"
mk failed "<problem keywords>"
```

Use results to populate a "## Prior Knowledge (auto-populated by math-forge)" section in the sketch. This prevents repeating failed approaches and leverages proven techniques from related problems.

### 1c: Classify

Determine:
- **Domain**: Number theory, algebra, analysis, combinatorics, etc.
- **Problem status**: Open problem, solved-not-formalized, or unknown
- **Partial progress**: Any known reductions, bounded cases, related results?

For OPEN problems (primary target):
- Research what's known — literature, partial results, computational evidence
- Identify tractable sub-goals — bounded cases, structural lemmas, special cases
- Develop a proof strategy — even speculative

For known results (Track D):
- Find the published proof
- Extract key lemmas and techniques

### 1d: Research the Mathematics

Use web search and literature to find:
1. **For open problems**: Partial results, related techniques, why prior approaches failed, computational patterns
2. **For known results**: The proof itself — published papers, textbooks
3. Key Mathlib types and lemmas
4. Witness values if computational

### 1e: Computational Exploration (if applicable)

For problems involving specific values, sequences, or witnesses:
- Write quick Python3 to compute/verify claims
- For heavy computation: Rust (see `scripts/erdos396_rust/` for template)
- Record patterns and witnesses — these inform the proof strategy

### 1f: Falsification Check

If truth is uncertain, ask:

- **Question**: "Should we test if this claim is actually true before sketching?"
- **Header**: "Falsify?"
- **Options**:
  - "Yes, test negation on Fin 5-7 first" — "~40% of conjectures are false. Quick check saves hours."
  - "No, proceed with sketch" — "I'm confident the claim is true."

## Step 2: SKETCH — Write the Proof Attempt

### 2a: Generate the Sketch

Write a .txt file. The structure depends on whether it's open or known:

**For OPEN problems:**
```
# [Problem Name] — Proof Attempt
# Domain: [Number Theory / Algebra / Analysis]
# Source: [formal-conjectures file, Erdos number, etc.]
# Status: OPEN PROBLEM

## Theorem Statement
[Precise mathematical English statement]

## What's Known
[Partial results, reductions, bounded cases, computational evidence]

## Proposed Proof Strategy
[High-level approach: why this might work]

## Key Lemmas to Establish

### Lemma 1: [Name]
[Statement]
Proposed proof: [Your idea — "by induction on p using Wilson's theorem", etc.]

### Lemma 2: [Name]
[Statement]
Proposed proof: [Your idea]

## Main Proof Assembly
[How the lemmas combine. Be explicit about the logical flow.]

## Tractable Sub-Goals
[If the full proof is too ambitious, list bounded cases or structural results
 that would still be valuable contributions]

## Computational Evidence
[Patterns observed, witnesses found, exhaustive checks]

## Relevant Mathlib
[Specific types and lemmas: Nat.Prime, ZMod, Fintype, etc.]
```

**For KNOWN results (Track D):**
```
# [Problem Name] — Proof Sketch
# Domain: [Number Theory / Algebra]
# Source: [formal-conjectures file, paper reference]
# Status: KNOWN — [reference]

## Theorem Statement
[Precise statement]

## Proof Strategy
[Outline the known proof]

## Key Lemmas
### Lemma 1: ...
Proof sketch: [Brief indication]

## Main Proof
[How lemmas combine]

## Relevant Mathlib
[Specific lemmas]
```

### 2b: Quick Sanity Check

Only verify:
- [ ] Theorem statement is present
- [ ] SOME proof strategy or approach is mentioned (even speculative)
- [ ] 20+ lines (Aristotle needs minimal input to work with)

**DO NOT block on missing Mathlib references, thin sketches, or low confidence.** Aristotle fills gaps. Submit it.

### 2c: Assign Slot and Save

```bash
sqlite3 submissions/tracking.db "SELECT COALESCE(MAX(CAST(SUBSTR(filename, 5, INSTR(SUBSTR(filename,5),'_')-1) AS INTEGER)), 577) + 1 FROM submissions WHERE filename LIKE 'slot%'"
```

Save to `submissions/nu4_final/slot<NNN>_<name>.txt`

## Step 3: Report and Next Steps

```
╔══════════════════════════════════════════════════════╗
║  SKETCH: <problem name>                             ║
╠══════════════════════════════════════════════════════╣
║ Domain: NT / Algebra           │  Lines: NN         ║
║ Status: OPEN / KNOWN           │  Track: A / D      ║
║ Approach: [brief]              │  Confidence: H/M/L ║
╠══════════════════════════════════════════════════════╣
║ File: submissions/nu4_final/slot<NNN>_<name>.txt    ║
╠══════════════════════════════════════════════════════╣
║ Quality: READY — submit it                          ║
╠══════════════════════════════════════════════════════╣
║ Next: /project:submit <file>                        ║
╚══════════════════════════════════════════════════════╝
```

## What Makes a Good Sketch

**Good open-problem sketch** (slot577 — Kurepa, in flight):
> "Kurepa's conjecture (1971): !p ≢ 0 (mod p) for odd primes p.
> Known: Reduction to primes (proven). First cases verified for p < 100.
> Strategy: Use Wilson's theorem — (p-1)! ≡ -1 (mod p). The left factorial
> !p = Σ_{k=0}^{p-1} k!. Modular analysis of this sum using factorial residues..."

**Good known-result sketch** (slot562 — Leinster cyclic, PROVEN):
> "For any finite cyclic group G of order n, the sum of orders equals sigma(n).
> Each element of order d contributes d, and there are phi(d) such elements.
> Total = sum_{d|n} phi(d) * d. Use Mathlib: Nat.totient, Nat.divisors..."

**Bad** (typical sorry=1 — 0/183 success):
> `theorem my_theorem : forall n, P n := by sorry`

The bad version gives Aristotle ZERO mathematical insight. Even for open problems, propose a strategy.
