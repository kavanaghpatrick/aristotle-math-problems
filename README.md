# math-forge

An automated research harness for solving open mathematical problems. We identify unsolved conjectures, state them as bare targets, and submit them to [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) for autonomous proof construction — then feed results back as context for the next attempt.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4-purple)](https://lean-lang.org/)

---

## The Idea

We don't write proofs. We don't develop proof strategies. We state the open gap and let Aristotle find the path.

The critical insight is **compounding context**: when Aristotle works on a problem and produces partial results (structural lemmas, bounds, reductions), those results are automatically attached as context on the next submission. Submission N+1 builds on everything Aristotle proved in submission N. Over repeated iterations, the prover accumulates a growing body of verified results to draw on.

---

## Workflow

```
SCREEN  →  SKETCH  →  SUBMIT  →  FETCH  →  ITERATE
  │           │          │          │          │
  │           │          │          │          └─ Prior results become
  │           │          │          │             context for next run
  │           │          │          │
  │           │          │          └─ Download .lean result,
  │           │          │             audit for gap resolution
  │           │          │
  │           │          └─ Gap-targeting gate enforced,
  │           │             auto-context attached, submit INFORMAL
  │           │
  │           └─ State the conjecture in ≤30 lines,
  │              bare theorem statement + sorry
  │
  └─ Is this problem genuinely open?
     Check DB for prior attempts and false lemmas
```

### Screening

Before sketching, we check whether the problem is genuinely open and whether we've already tried (and failed) approaches against it:

```bash
mk failed <keywords>     # Dead ends — what's been disproven
mk context <problem_id>  # What Aristotle has already produced
```

The `false_lemmas` and `failed_approaches` tables prevent us from re-submitting against known dead ends.

### Sketching

A sketch is a minimal informal statement of an open conjecture — nothing more:

```
OPEN GAP: [Problem Name]
Source: [reference]
Domain: [nt / algebra / combinatorics / analysis]

[1-3 sentence English statement of the unsolved conjecture]

theorem problem_name (vars : Types) : conclusion := by sorry

Status: OPEN. [One sentence on what's known]
```

No proof strategy. No key lemmas. No suggested approaches. The sketch states *what* to prove, never *how*.

### The Gap-Targeting Gate

Every submission passes a hard gate before reaching Aristotle. No exceptions, no override:

- **.txt only** — no .lean files (INFORMAL mode)
- **≤30 non-blank lines** — enforced, not advisory
- **No strategy keywords** — "Proof Strategy", "Key Lemma", "Approach" etc. are rejected
- **No empty files**

This forces discipline. The temptation to "help" the prover with hints is strong, but the gate exists because bare submissions with good context outperform guided ones.

### Auto-Context

When submitting, the pipeline queries the tracking database for prior Aristotle results on the same problem. Any compiled-clean `.lean` files are attached as `context_file_paths`. This is how compounding works — Aristotle sees its own prior theorems and can `import` or build on them.

### Submission

```bash
python3 scripts/safe_aristotle_submit.py <sketch.txt> <slot> --informal [--context <file.lean>]
```

The submission script handles:
- Gap-targeting gate enforcement
- Lockfile to prevent concurrent submissions
- Dedup check against recent submissions (by content hash)
- Queue capacity check (5 concurrent slots)
- Transaction logging to the tracking database
- UUID tracking for result fetching

### Fetching and Auditing

Results come back as `.lean` files. Auditing checks whether the result actually resolves the open gap vs. just building supporting infrastructure. A file that "compiled clean" (0 sorry) is not necessarily a win — it might have proved helper lemmas without touching the core conjecture.

---

## Tooling

### Claude Code Skills

The harness is orchestrated through Claude Code with project-specific skills:

| Skill | Purpose |
|-------|---------|
| `/project:screen` | Binary decision: is this problem open? |
| `/project:sketch` | Write a bare-gap sketch |
| `/project:submit` | Gate check → auto-context → submit INFORMAL |
| `/project:sweep` | Batch: scan for open gaps, sketch, submit |
| `/project:fetch` | Download result → audit → update DB |
| `/project:status` | Queue and job status |
| `/project:audit` | Deep audit of a result file |
| `/project:process-result` | Audit + DB update in one step |
| `/project:debate` | Multi-AI debate to identify the exact open gap |

### math-forge CLI

```bash
mk search "<query>"      # FTS5 full-text search across knowledge base
mk find "<problem_id>"   # All findings for a specific problem
mk failed [keyword]      # Failed approaches — check BEFORE sketching
mk context <problem_id>  # Prior Aristotle results for auto-context
mk gaps                  # All open gaps currently being targeted
mk stats                 # Dashboard: submissions, clean rate, queue
```

### Multi-Agent Support

When stuck on problem identification or gap analysis, the harness can invoke multiple AI models in parallel:

- **Grok** — web search, X/Twitter search for recent results
- **Gemini** — deep analysis with large context window
- **Codex** — autonomous task delegation
- **Claude** — synthesis, orchestration, sketch writing

These are used for *screening and gap identification*, never for proof guidance.

---

## Database

All state lives in `submissions/tracking.db` (SQLite):

| Table | Purpose |
|-------|---------|
| `submissions` | Every Aristotle job — UUID, status, gap statement, resolution flag |
| `false_lemmas` | Mathematical claims that seemed plausible but are provably wrong |
| `failed_approaches` | Approaches that were tried and failed, with reasons |

A separate knowledge base (`math-forge/data/knowledge.db`) provides FTS5 search across accumulated mathematical findings.

### Key Fields on `submissions`

- `gap_statement` — what open gap this targets
- `submission_type` — `gap_targeting` or `falsification`
- `status` — `compiled_clean`, `near_miss`, `error`, etc.
- `target_resolved` — did this actually close the gap?
- `output_file` — path to the `.lean` result (used for auto-context)

---

## Repository Structure

```
math/
├── submissions/
│   ├── sketches/                  # Bare-gap .txt files for submission
│   ├── nu4_final/                 # Aristotle result files (.lean)
│   └── tracking.db                # Submission state and knowledge DB
├── scripts/
│   ├── safe_aristotle_submit.py   # Safe submission with all checks
│   ├── aristotle_fetch.py         # Result fetching and tracking
│   └── math_forge.py              # Knowledge base CLI (mk commands)
├── math-forge/data/               # FTS5 knowledge base
├── skills/                        # Claude Code skill definitions
├── hooks/                         # Session and validation hooks
└── CLAUDE.md                      # Pipeline rules and methodology
```

---

## Design Principles

**Have faith in the prover.** Submit aggressively. Most submissions won't resolve the gap — that's fine. The ones that produce partial results feed the next attempt.

**Bare conjecture only.** No proof hints, no lemma suggestions, no strategy. State what needs to be proved and get out of the way.

**Context compounds.** The value of the system grows with each submission. Even "failed" attempts that compile clean add to the context pool.

**Falsification is valid.** "Is this gap actually real?" is a legitimate submission. Disproving a conjecture is progress.

**Track everything.** Every submission, every false lemma, every dead end goes in the database. The system's memory prevents repeating mistakes.

**Move on when stuck.** There are plenty of open problems in mathematics. Don't grind on one when the prover isn't making progress — sweep for new targets.

**"Compiled clean" is not "solved".** A result that builds helper infrastructure without touching the core conjecture is not a resolution. Only celebrate when `target_resolved = true`.

---

## License

MIT
