# math-forge

An automated research harness for solving open mathematical problems. We identify unsolved conjectures, state them as bare targets, and submit them to [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) for autonomous proof construction — then feed results back as context for the next attempt.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4-purple)](https://lean-lang.org/)

**1,160 submissions | 96 open problems | 205 compiled clean | 568 knowledge base entries | 15 months of operation**

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

## Autonomous Proof Loop

Beyond the manual workflow, the harness includes an autonomous Codex-to-Aristotle proof loop that automates multi-attempt proof campaigns.

### Codex Proof Engine

[Codex](https://openai.com/index/codex/) (OpenAI's `codex` CLI) writes complete Lean 4 proofs, iterating against `lake build` in an isolated temp project with symlinked Mathlib cache. Build errors feed back to Codex for iterative fixing. Results are tracked in the `codex_proofs` table.

```bash
# One-shot proof attempt
/codex-prove <problem>
```

### Proof Orchestrator

The orchestrator (`scripts/proof_orchestrator.py`) is a persistent background process that drives a Codex → Aristotle cycle via a state machine:

```
QUEUED → CODEX_RUNNING → CODEX_DONE
                              │
                    ┌─────────┴──────────┐
                    │                    │
              0 sorry = RESOLVED    has sorries
                                         │
                                    auto-sketch
                                         │
                              ARISTOTLE_SUBMITTED
                                         │
                              ARISTOTLE_COMPLETE
                                         │
                              ┌──────────┴──────────┐
                              │                     │
                        fewer sorries          no progress
                              │                     │
                     feed back as context      STALLED
                     re-enter QUEUED
```

Features: parallel Codex workers (up to 4 concurrent), reasoning effort escalation, crash recovery, sorry-count tracking, sub-problem decomposition for partial proofs.

```bash
python3 scripts/proof_orchestrator.py enqueue "<problem>" --problem-id <id>
python3 scripts/proof_orchestrator.py run [--single-pass]
python3 scripts/proof_orchestrator.py status
python3 scripts/proof_orchestrator.py cancel <id>
python3 scripts/proof_orchestrator.py retry <id>
```

---

## Tooling

### Claude Code Skills

The harness is orchestrated through Claude Code with project-specific skills:

| Skill | Purpose |
|-------|---------|
| `/screen` | Binary decision: is this problem open? |
| `/sketch` | Write a bare-gap sketch |
| `/submit` | Gate check → auto-context → submit INFORMAL |
| `/sweep` | Batch: scan for open gaps, sketch, submit |
| `/fetch` | Download result → audit → update DB |
| `/status` | Queue and job status |
| `/audit` | Deep audit of a result file |
| `/process-result` | Audit + DB update in one step |
| `/codex-prove` | Codex proof loop: write Lean 4, iterate against lake build |
| `/debate` | Multi-AI debate to identify the exact open gap |
| `/optimize` | Recommend optimal submission path |
| `/screen-batch` | Batch screen: OPEN vs SKIP |

### math-forge CLI

```bash
mk search "<query>"          # FTS5 full-text search across knowledge base
mk find "<problem_id>"       # All findings for a specific problem
mk failed [keyword]          # Failed approaches — check BEFORE sketching
mk context <problem_id>      # Prior Aristotle results for auto-context
mk gaps                      # All open gaps currently being targeted
mk stats                     # Dashboard: submissions, clean rate, queue
mk codex [problem_id]        # Codex proof loop history
mk codex-best <problem_id>   # Best compiled Codex proof file path
mk strategies [domain]       # Proven techniques by frequency/domain
mk partials                  # Near-miss submissions (sorry=1)
mk resubmittable             # Resubmission candidates (1-3 sorries)
mk query "<sql>"             # Read-only SQL against tracking.db
mk submit <file>             # Submit sketch to Aristotle
mk status [uuid-or-slot]     # Aristotle queue status
```

### Multi-Agent Support

When stuck on problem identification or gap analysis, the harness can invoke multiple AI models in parallel:

- **Grok** — web search, X/Twitter search for recent results
- **Gemini** — deep analysis with large context window
- **Codex** — Lean 4 proof generation via iterative compile-fix loop
- **Claude** — synthesis, orchestration, sketch writing

These are used for *screening, gap identification, and proof generation*, never for proof guidance to Aristotle.

---

## Database

All state lives in `submissions/tracking.db` (SQLite):

| Table | Purpose |
|-------|---------|
| `submissions` | Every Aristotle job — UUID, status, gap statement, resolution flag |
| `codex_proofs` | Codex proof loop results — problem_id, sorry count, compiled status, lean file |
| `proof_queue` | Autonomous orchestrator queue — state machine, Codex↔Aristotle loop |
| `false_lemmas` | Mathematical claims that seemed plausible but are provably wrong |
| `failed_approaches` | Approaches that were tried and failed, with reasons |

A separate knowledge base (`math-forge/data/knowledge.db`) provides FTS5 search across 568+ accumulated mathematical findings.

### Key Fields on `submissions`

- `gap_statement` — what open gap this targets
- `submission_type` — `gap_targeting` or `falsification`
- `status` — `compiled_clean`, `near_miss`, `error`, etc.
- `target_resolved` — did this actually close the gap?
- `output_file` — path to the `.lean` result (used for auto-context)

---

## Hooks and Guardrails

Two layers of automation enforce the gap-targeting methodology:

**Project-level** (`.claude/settings.json`):
- **SessionStart** — injects orchestrator queue status and gap-targeting reminder

**Plugin-level** (`math-forge/hooks/`):
- **SessionStart** — generates session briefing from tracking.db and knowledge.db
- **PostToolUse** — validates `.txt` sketches for proof-strategy keywords and line count; blocks sorry-replacing edits in `.lean` files; warns on false lemma references

---

## Repository Structure

```
math/
├── submissions/
│   ├── sketches/                  # Bare-gap .txt files (253 sketches)
│   ├── nu4_final/                 # Aristotle result files (.lean)
│   ├── results/                   # Additional result directories
│   └── tracking.db                # Submission state and knowledge DB
├── scripts/
│   ├── safe_aristotle_submit.py   # Safe submission with all gate checks
│   ├── aristotle_fetch.py         # Result fetching and tracking
│   ├── proof_orchestrator.py      # Autonomous Codex→Aristotle loop
│   ├── codex_proof_loop.py        # Codex Lean 4 proof iteration engine
│   ├── debate.py                  # Multi-AI debate orchestrator
│   ├── workflow.py                # Unified submission CLI
│   ├── a375071_rust/              # Rust: OEIS A375071 computation (Erdos 389)
│   └── erdos396_rust/             # Rust: Erdos 396 search
├── math-forge/
│   ├── data/knowledge.db          # FTS5 knowledge base
│   ├── hooks/                     # Plugin hooks (gap-targeting enforcement)
│   └── scripts/mk                 # math-forge CLI wrapper
├── results_v07/                   # Aristotle result tarballs
├── codex_proofs/                  # Codex proof loop outputs
├── Math/                          # Lean 4 source directory
├── lakefile.toml                  # Lean 4 build configuration
├── lean-toolchain                 # Lean 4 toolchain version
├── .claude/
│   ├── commands/                  # Claude Code skill definitions
│   └── settings.json              # Hooks and session config
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
