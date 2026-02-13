---
name: open-problems
description: "Open problem attack workflow with KB-informed sketch writing. Use when targeting unsolved conjectures. Queries prior knowledge, checks failed approaches, generates Prior Knowledge section for sketches."
---

# Open Problem Attack (KB-Informed)

**PRIME DIRECTIVE: We ONLY target OPEN/UNSOLVED problems. Known-result formalizations have ZERO value.**

## Workflow

### Step 1: Check KB for Prior Knowledge
```bash
mk search "<problem name or keywords>"
mk find "<problem_id>"
mk failed "<problem keywords>"
```

### Step 2: Build Prior Knowledge Section
From the KB results, build this section for the sketch:

```
## Prior Knowledge (auto-populated by math-forge)
- [PROVEN] <related theorem> via <technique> (slot N)
- [FAILED] <approach> — <why it failed> (slot M)
- [FALSE] <disproven claim> — <counterexample>
- Related technique: <technique> (used in <related problem>)
```

### Step 3: Write Sketch
- Include the Prior Knowledge section
- Reference proven sub-results by slot number
- Explicitly avoid approaches listed in [FAILED]
- Propose a NEW approach informed by what we know

### Step 4: Submit
```bash
/project:submit <sketch.txt>
```

## Rules
- NEVER repeat a [FAILED] approach without a fundamentally new angle
- NEVER use a [FALSE] lemma in the proof strategy
- ALWAYS check `mk failed` before writing a sketch
- Speculative sketches are FINE — Aristotle fills gaps
- HAVE FAITH IN ARISTOTLE. SUBMIT AGGRESSIVELY.
