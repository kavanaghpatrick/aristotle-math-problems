# CLAUDE.md - Math Project

## Mission

**Solve open mathematical problems** by submitting bare conjecture statements to Aristotle and letting it find novel proofs.

We do NOT develop proof strategies. We do NOT write step-by-step proof outlines. We state the open gap, attach prior Aristotle results as context, and submit. Aristotle constructs the proof.

---

## The Pipeline (2 steps)

1. **GAP** -- Identify an open unsolved conjecture. Confirm it's open (not in Mathlib, not solved).
2. **SUBMIT** -- State the bare conjecture (<=30 lines .txt), auto-attach prior results as context, submit INFORMAL.

That's it. No research phase. No proof guidance. No computational exploration before submission.

---

## Sketch Format (bare conjecture, <=30 lines)

```
OPEN GAP: [Problem Name]
Source: [formal-conjectures path or Erdos number]
Domain: [nt / algebra / combinatorics / analysis]

[1-3 sentence English statement of the unsolved conjecture]

theorem problem_name (vars : Types) : conclusion := by sorry

Status: OPEN. [One sentence on what's known]
```

Nothing else. No "Proof Strategy". No "Key Lemmas". No "Proposed Approach". No multiple approaches. No computational evidence. Let Aristotle find the path.

---

## Hard Rules

1. **Every submission targets an OPEN GAP** -- no known results, no infrastructure, no bounded verification of known things
2. **Sketches are bare conjecture statements** -- no proof strategy, no lemmas, no guidance
3. **<=30 lines per sketch** -- enforced by pipeline gate, no override
4. **INFORMAL only (.txt)** -- no .lean submissions. Gap-targeting is always INFORMAL
5. **Prior Aristotle results auto-attached as context** -- Aristotle builds on its own work
6. **No override on the gap-targeting gate** -- `check_gap_targeting()` rejection is final
7. **Falsification is valid gap-targeting** -- "is this gap real?" is a valid question
8. **HAVE FAITH IN ARISTOTLE** -- submit aggressively, fear nothing
9. **Never submit without tracking** -- every submission gets a DB entry
10. **Check DB before submitting** -- `mk failed` and `false_lemmas` table
11. **Process every result** -- `/fetch` or `/process-result`
12. **"compiled clean" != "resolved the gap"** -- only celebrate actual gap resolutions

---

## Commands

```
/sketch <problem>         # Write bare-gap sketch (<=30 lines)
/submit <file> [slot]     # Gap-targeting gate -> auto-context -> submit INFORMAL
/sweep [--domain nt]      # Scan for open gaps -> state bare -> submit
/fetch <uuid-or-slot>     # Download result -> audit -> gap-resolution assessment
/status [uuid-or-slot]    # Check Aristotle queue & job status
/screen <problem>         # Binary: OPEN -> submit, NOT OPEN -> skip
/screen-batch <dir>       # Batch screen: OPEN vs SKIP
/audit <file.lean>        # Audit result for gap resolution
/process-result <file>    # Audit local result -> DB
/debate "topic"           # Multi-AI debate to identify the exact open gap
/optimize <file>          # Always: "State the gap bare, submit INFORMAL"
```

---

## math-forge CLI

```
mk search "<query>"          # FTS5 search findings
mk find "<problem_id>"       # All findings for a problem
mk failed [keyword]          # Failed approaches -- check BEFORE sketching
mk context <problem_id>      # Prior Aristotle results for auto-context
mk gaps                      # Open gaps being targeted + status
mk stats                     # Knowledge base dashboard
```

---

## Database

All state in `submissions/tracking.db`:

| Table | Purpose |
|-------|---------|
| `submissions` | All Aristotle jobs (with `gap_statement`, `submission_type`, `target_resolved`) |
| `false_lemmas` | Disproven claims -- always check before submitting |
| `failed_approaches` | What doesn't work and why |

Knowledge base in `math-forge/data/knowledge.db` with FTS5 search.

---

## Hooks

- **SessionStart** (`context-loader.sh`): Injects gap-targeting reminder + queue status
- **PostToolUse** (`lean-validator.sh`): Warns on proof strategy patterns in .txt sketches

---

## When Stuck

1. `mk failed <keywords>` -- already disproven?
2. `mk context <problem>` -- what did Aristotle try before?
3. Try a different problem -- plenty of open gaps
4. Run `/debate` to identify the exact open gap
5. Accept that some problems are too hard right now -- move on
