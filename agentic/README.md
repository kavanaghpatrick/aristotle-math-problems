# Agentic Theorem Proving System

## Overview

This system maintains 15 parallel Aristotle slots for autonomous theorem proving on Tuza's conjecture (nu=4 case). It uses a multi-tier architecture with specialized agents for generation, validation, counterexample hunting, and learning.

## Architecture

```
                                    ┌─────────────────────────────────────┐
                                    │         ORCHESTRATOR DAEMON         │
                                    │   (orchestrator.py - runs 24/7)     │
                                    │                                     │
                                    │  - Maintains 15 active Aristotle    │
                                    │  - Prioritizes from submission_queue│
                                    │  - Triggers learning on completion  │
                                    │  - Spawns generators when queue low │
                                    └───────────────┬─────────────────────┘
                                                    │
                    ┌───────────────────────────────┼───────────────────────────────┐
                    │                               │                               │
                    ▼                               ▼                               ▼
    ┌───────────────────────────┐   ┌───────────────────────────┐   ┌───────────────────────────┐
    │     GENERATOR AGENTS      │   │    VALIDATOR PIPELINE     │   │    MONITOR SERVICE        │
    │                           │   │                           │   │                           │
    │  1. Proof Generator       │   │  Stage 1: Syntax Check    │   │  - Real-time dashboard    │
    │     (Codex worktrees)     │   │  Stage 2: False Lemma     │   │  - Slot status tracker    │
    │                           │   │  Stage 3: Grok Review     │   │  - Metrics collection     │
    │  2. Gap Filler            │   │  Stage 4: Counterexample  │   │  - Alert system           │
    │     (Near-miss completion)│   │                           │   │                           │
    │                           │   │  Only passes Stage 4 go   │   │  Writes to:               │
    │  3. Variant Explorer      │   │  to submission_queue      │   │  - status.json            │
    │     (Strategy mutations)  │   │                           │   │  - metrics.db             │
    └───────────────┬───────────┘   └───────────────┬───────────┘   └───────────────────────────┘
                    │                               │
                    │      ┌────────────────────────┘
                    │      │
                    ▼      ▼
    ┌─────────────────────────────────────────────────────────────────────────────────────────┐
    │                              SUBMISSION QUEUE (SQLite)                                   │
    │                                                                                          │
    │  id | file_path | priority | case_name | approach | validation_stage | created_at       │
    │  ---+----------+----------+-----------+----------+------------------+---------------     │
    │  1  | slot160  | 100      | cycle_4   | LP_dual  | PASSED           | 2026-01-01 10:00  │
    │  2  | slot161  | 90       | path_4    | gap_fill | PASSED           | 2026-01-01 10:05  │
    │  ...                                                                                     │
    └─────────────────────────────────────────────────────────────────────────────────────────┘
                    │
                    ▼
    ┌─────────────────────────────────────────────────────────────────────────────────────────┐
    │                            ARISTOTLE SLOTS (15 parallel)                                 │
    │                                                                                          │
    │  [01: cycle_4_LP]  [02: path_4_gap]   [03: matching_v3]   [04: two_two_v2]  [05: ...]   │
    │  [06: ...]         [07: ...]          [08: ...]           [09: ...]         [10: ...]   │
    │  [11: ...]         [12: ...]          [13: ...]           [14: ...]         [15: ...]   │
    │                                                                                          │
    └─────────────────────────────────────────────────────────────────────────────────────────┘
                    │
                    ▼
    ┌─────────────────────────────────────────────────────────────────────────────────────────┐
    │                              LEARNING PIPELINE                                           │
    │                                                                                          │
    │  On Completion:                                                                          │
    │  1. Download output from Aristotle                                                       │
    │  2. Parse proven/sorry/negated lemmas                                                    │
    │  3. If negated: extract counterexample → add to false_lemmas                            │
    │  4. If proven: extract proofs → add to scaffolding                                       │
    │  5. Update nu4_cases with new knowledge                                                  │
    │  6. Trigger variant generation for near-misses                                           │
    │                                                                                          │
    └─────────────────────────────────────────────────────────────────────────────────────────┘
```

## Components

### 1. Orchestrator Daemon (`orchestrator.py`)
Main control loop that runs 24/7:
- Polls Aristotle for slot availability every 30 seconds
- Submits highest-priority validated items from queue
- Triggers learning pipeline on completions
- Spawns generator agents when queue depth < 30

### 2. Generator Agents

#### 2a. Proof Generator (`generators/proof_generator.py`)
- Uses Codex CLI in worktrees for parallel proof generation
- Generates proofs for each nu4 case using known scaffolding
- Applies mutation strategies (different proof tactics, orderings)

#### 2b. Gap Filler (`generators/gap_filler.py`)
- Focuses on near-misses (1-2 sorry in otherwise complete proofs)
- Uses Grok to analyze gaps and suggest completions
- Highest priority for queue entry

#### 2c. Variant Explorer (`generators/variant_explorer.py`)
- Takes proven approaches and creates variants
- Tries different decompositions of the same problem
- Generates "what if" proofs based on counterexamples

### 3. Validator Pipeline (`validators/pipeline.py`)

Four-stage validation before any Aristotle submission:

| Stage | Tool | Check | Failure Action |
|-------|------|-------|----------------|
| 1 | Lake/Lean | Syntax valid | Fix syntax, retry |
| 2 | SQLite | No false lemmas used | Flag which false lemma, block |
| 3 | Grok | Mathematical plausibility | Log concerns, may proceed |
| 4 | Counterexample Hunter | Actively try to disprove | If disproven, add to false_lemmas |

### 4. Counterexample Hunter (`validators/counterexample_hunter.py`)
- Before proving a lemma, actively tries to find counterexamples
- Uses Grok-4 to construct potential counterexamples
- Runs Z3/SMT for decidable fragments
- Only lemmas surviving hunting go to Aristotle

### 5. Monitor Service (`monitor/dashboard.py`)
- Real-time web dashboard (localhost:8080)
- Shows: slots, queue depth, success rate, learnings
- Alerts on: all slots idle, high failure rate, counterexamples found

### 6. Learning Pipeline (`learning/extractor.py`)
Automatic knowledge extraction from every Aristotle result:
- Parse proven theorems → add to scaffolding table
- Parse negations → add to false_lemmas table
- Update nu4_cases with new insights
- Generate follow-up proof attempts

## Database Schema Extensions

```sql
-- Submission queue for validated items ready to submit
CREATE TABLE IF NOT EXISTS submission_queue (
    id INTEGER PRIMARY KEY,
    file_path TEXT NOT NULL,
    priority INTEGER DEFAULT 50,  -- 0-100, higher = more important
    case_name TEXT,               -- which nu4 case
    approach TEXT,                -- proof approach
    validation_stage TEXT DEFAULT 'pending',
    validator_notes TEXT,         -- JSON notes from validators
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    submitted_at TEXT,            -- NULL until submitted
    aristotle_uuid TEXT           -- filled on submission
);

-- Generator task tracking
CREATE TABLE IF NOT EXISTS generator_tasks (
    id INTEGER PRIMARY KEY,
    generator_type TEXT NOT NULL,  -- proof, gap_filler, variant
    target_case TEXT,              -- nu4 case
    base_file TEXT,                -- source file if any
    status TEXT DEFAULT 'pending', -- pending, running, completed, failed
    output_file TEXT,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    completed_at TEXT
);

-- Metrics for dashboard
CREATE TABLE IF NOT EXISTS metrics (
    id INTEGER PRIMARY KEY,
    timestamp TEXT DEFAULT CURRENT_TIMESTAMP,
    metric_name TEXT NOT NULL,
    metric_value REAL NOT NULL
);
```

## Coordination Protocol

### Agent Communication
All agents communicate through SQLite database:
- No direct inter-agent communication
- Database is single source of truth
- Agents poll their relevant tables

### Priority Calculation
```python
def calculate_priority(file_info: dict) -> int:
    """Higher = more important"""
    priority = 50  # base

    # Near-misses get highest priority
    if file_info.get('sorry_count', 99) <= 2:
        priority += 40

    # Blocked cases (cycle_4) get boost
    if file_info.get('case_name') == 'cycle_4':
        priority += 20

    # New approaches get slight boost
    if file_info.get('approach') not in known_approaches:
        priority += 10

    # Penalize repeated failures
    priority -= file_info.get('failure_count', 0) * 5

    return max(0, min(100, priority))
```

### Slot Allocation Strategy
```
Slot 1-5:   Reserved for cycle_4 (hardest case, needs most attempts)
Slot 6-8:   Reserved for near-misses (highest success probability)
Slot 9-12:  General queue (FIFO by priority)
Slot 13-15: Exploratory (new approaches, low-probability high-reward)
```

## Bootstrap Procedure

### Step 1: Initialize Database
```bash
python3 agentic/setup.py --init-db
```

### Step 2: Populate Initial Queue
```bash
# Generate initial proof attempts for all cases
python3 agentic/generators/proof_generator.py --all-cases

# Validate and add to queue
python3 agentic/validators/pipeline.py --process-pending
```

### Step 3: Start Services (use tmux/screen)
```bash
# Terminal 1: Orchestrator
python3 agentic/orchestrator.py

# Terminal 2: Monitor Dashboard
python3 agentic/monitor/dashboard.py

# Terminal 3: Generator Pool (spawns subprocesses)
python3 agentic/generators/pool.py

# Terminal 4: Validator Pipeline (continuous)
python3 agentic/validators/pipeline.py --watch
```

### Step 4: Verify System Health
```bash
# Check all components
python3 agentic/health_check.py
```

## Configuration

All configuration in `agentic/config.py`:

```python
# Aristotle settings
MAX_PARALLEL_SLOTS = 15
POLL_INTERVAL_SECONDS = 30
MAX_WAIT_FOR_SLOT = 3600

# Queue management
MIN_QUEUE_DEPTH = 30  # Spawn generators when below this
MAX_RETRIES_PER_APPROACH = 3

# Validation thresholds
GROK_PLAUSIBILITY_THRESHOLD = 0.7
COUNTEREXAMPLE_TIMEOUT_SECONDS = 120

# Generator settings
CODEX_WORKTREES = 5  # Number of parallel Codex instances
VARIANT_MUTATIONS_PER_PROOF = 3
```

## Metrics & Monitoring

The system tracks:
- **Discovery Velocity**: proven theorems / day
- **Slot Utilization**: % time slots are occupied
- **Validation Pass Rate**: % of generated proofs passing validation
- **Counterexample Catch Rate**: % of false lemmas caught before Aristotle
- **Near-Miss Conversion**: % of 1-2 sorry proofs completed

## Failure Modes & Recovery

| Failure | Detection | Recovery |
|---------|-----------|----------|
| Aristotle API down | Repeated 5xx errors | Pause submissions, alert, retry every 5m |
| All validators busy | Queue growing, no submissions | Auto-scale validators or pause generators |
| Same lemma keeps failing | 3+ failures for same approach | Mark approach as failed, stop generating variants |
| Counterexample found | Hunter returns counterexample | Add to false_lemmas, regenerate proofs avoiding it |
| Codex worktree conflict | Git lock errors | Kill stale worktrees, recreate |

## Directory Structure

```
agentic/
├── README.md              # This file
├── config.py              # Configuration
├── setup.py               # Database init and bootstrap
├── orchestrator.py        # Main daemon
├── health_check.py        # System health verification
│
├── generators/
│   ├── __init__.py
│   ├── pool.py            # Generator pool manager
│   ├── proof_generator.py # Main proof generation
│   ├── gap_filler.py      # Near-miss completion
│   └── variant_explorer.py # Mutation strategies
│
├── validators/
│   ├── __init__.py
│   ├── pipeline.py        # Main validation pipeline
│   ├── syntax_checker.py  # Stage 1: Lean syntax
│   ├── false_lemma_detector.py  # Stage 2: Known false lemmas
│   ├── grok_reviewer.py   # Stage 3: AI plausibility
│   └── counterexample_hunter.py  # Stage 4: Active disproving
│
├── learning/
│   ├── __init__.py
│   ├── extractor.py       # Parse Aristotle outputs
│   ├── scaffolding.py     # Update proven theorems
│   └── false_lemma_recorder.py  # Record counterexamples
│
└── monitor/
    ├── __init__.py
    ├── dashboard.py       # Web dashboard
    └── metrics.py         # Metrics collection
```
