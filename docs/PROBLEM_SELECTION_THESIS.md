# Problem Selection Thesis: What Works With Aristotle

## Evidence Base
- 978 Aristotle submissions, 127 proven, 43 false lemmas, 56 failed approaches (46 days)
- 30+ research agents investigating AI theorem proving landscape (Feb 9 2026)
- 4-round multi-AI debate on problem selection (Grok, Gemini, Codex)
- 4-agent deep dive on Boris Alexeev's methodology
- External benchmarks: MiniF2F 90%, IMO 5/6 gold, CombiBench 7/100, Polya-Szego 100%

---

## Core Thesis

**Attack problems where we have a STRUCTURAL ADVANTAGE, not domain expertise.**

Our structural advantages are:
1. **Finite verification** via `native_decide` on `Fin n` (77% success at sorry=0)
2. **Falsification** via negation on `Fin 5-7` (~40% of conjectures are false)
3. **Boris workflow** via INFORMAL mode (LLM generates proof → Aristotle formalizes)

Our structural DISadvantages are:
1. Combinatorics domain (7-50% AI success vs 85-100% algebra)
2. Novel mathematical insight generation (0/56 failed approaches succeeded)
3. Infinite domain quantification (native_decide is useless)
4. Large search spaces without symmetry breaking

---

## What AI Has Actually Solved (Feb 2026)

### With Aristotle specifically:
| Problem | Domain | Workflow | Key Feature |
|---------|--------|----------|-------------|
| Erdos #728 | NT | A (GPT idea → Aristotle) | LLM generated the proof |
| Erdos #729 | NT | A | Adapted from #728 |
| Erdos #205 | NT | A (ChatGPT 5.2) | Disproof (counterexample) |
| Erdos #397 | NT | A | Disproof (infinite family) |
| Erdos #124 (weak) | Combinatorics | Boris INFORMAL | ~6 hrs, 100% autonomous |
| Erdos #1026 | Combinatorics | Collaborative | Multiple tools + humans |
| IMO 2025 (5/6) | Mixed | Full system | NOT our API version |

### With other AI systems:
| Problem | Domain | System | Key Feature |
|---------|--------|--------|-------------|
| Erdos #1051 | NT (irrationality) | Aletheia | Continued fractions |
| Erdos #75 | Graph theory | Aletheia | Solved |
| 12 Erdos problems | Mixed | Aletheia | 5 novel, 7 literature |
| Fel's Conjecture | Commutative algebra | AxiomProver | Open 10+ years |
| Chen-Gendron | Algebraic geometry | AxiomProver | Open 5 years |
| Putnam 2025 (12/12) | Mixed | AxiomProver | Competition math |

### Pattern Analysis:
- **NT dominates**: ~70% of AI-solved problems are number theory
- **Disproofs are common**: ~40% of AI contributions are counterexamples
- **Workflow A dominates for hard problems**: LLM generates idea → prover formalizes
- **Finite verification is underexploited**: Most teams use informal reasoning, not native_decide
- **Combinatorics is rare**: Only #124 (weak variant), #1026 (collaborative), #75 (Aletheia)

---

## The Three Workflows

### Track 1: Finite Verification (native_decide)
- **What**: Complete sorry=0 proof with scaffold tower, closed by native_decide on Fin n
- **Success rate**: 77% (127/165 at sorry=0)
- **Best for**: Claims about finite structures (graphs, sets, modular arithmetic on bounded domain)
- **Limits**: Fin ≤ 15 typically; search space must be < ~10^9
- **Our edge**: 3,229 uses, deeply practiced. Most other teams don't use this approach.

### Track 2: Boris Workflow (INFORMAL mode)
- **What**: Claude/GPT generates complete proof idea → submit via INFORMAL mode → Aristotle auto-formalizes
- **Success rate**: ~45% (Boris's data) vs our 0% (we never tried properly)
- **Best for**: NT/algebra problems where LLMs can generate proof sketches
- **Limits**: Requires LLM to "know" the proof technique; fails on truly novel math
- **Our edge**: Untested — must calibrate on known-provable problems first

### Track 3: Falsification Sweep
- **What**: Submit negation of conjecture on Fin 5-7, let native_decide find counterexample
- **Success rate**: ~40% of conjectures tested are false
- **Best for**: Open conjectures where truth value is uncertain; pre-formalized statements
- **Limits**: Only disproves, doesn't prove; may miss counterexamples needing larger n
- **Our edge**: Proven pipeline, database-as-memory prevents repeats

---

## Strict Screening Criteria

### HARD GATES (any fail = instant reject)

| Gate | Question | Kill Signal |
|------|----------|-------------|
| G1: Finite Reducibility | Can any part be checked on Fin n (n ≤ 15)? | Pure infinite domain with no finite reduction |
| G2: Domain Viability | Is domain algebra, NT, or finite combinatorics? | General combinatorics (CombiBench 7%), geometry, analysis |
| G3: Novel Insight Required? | Does solving require a new mathematical idea nobody has? | "Resisted decades of effort," "requires new techniques" |
| G4: Search Space | Is the search space < 10^12? | > 10^12 without symmetry breaking (e.g., Seymour n=8: 2^56) |
| G5: Mathlib Infrastructure | Does Mathlib have the relevant types/lemmas? | Requires building custom theory from scratch |
| G6: Proof Length | Estimated proof < 500 lines? | Known to require >2000 lines (Tutte: 5,757) |

### SCORING DIMENSIONS (1-10 each)

| Dimension | Weight | What It Measures |
|-----------|--------|-----------------|
| S1: Domain AI Success Rate | 20% | Algebra 9, NT 8, Analysis 5, Geometry 3, Combinatorics 2 |
| S2: Finite Structure | 20% | Can native_decide close it? (10 = pure Fin n, 1 = pure infinite) |
| S3: Pre-formalized | 15% | Lean 4 statement exists? (10 = compilable, 5 = partial, 1 = nothing) |
| S4: LLM Proof Amenability | 15% | Can GPT/Claude generate a proof sketch? (standard techniques = high) |
| S5: Falsifiability | 10% | Can we test negation on small instances? |
| S6: Independent Publishability | 10% | Is resolving this ONE result worth reporting? |
| S7: Existing Progress | 10% | Has anyone (AI or human) made partial progress? |

### COMPOSITE SCORE
`score = 0.20*S1 + 0.20*S2 + 0.15*S3 + 0.15*S4 + 0.10*S5 + 0.10*S6 + 0.10*S7`

### WORKFLOW RECOMMENDATION

| Condition | Recommended Track |
|-----------|------------------|
| S2 ≥ 7 AND S1 ≥ 6 | Track 1: native_decide finite verification |
| S4 ≥ 7 AND S1 ≥ 7 | Track 2: Boris INFORMAL workflow |
| S5 ≥ 7 AND truth value uncertain | Track 3: Falsification sweep |
| S2 ≥ 7 AND S5 ≥ 7 | Track 1 + Track 3 (falsify first, then prove) |
| S2 < 5 AND S4 < 5 | REJECT — no viable workflow |

---

## Calibration: Known Results

| Problem | Gates | Score | Workflow | Actual Outcome |
|---------|-------|-------|----------|----------------|
| Tuza nu=4 (our flagship) | FAIL G2 (combinatorics), FAIL G3 (novel insight) | 3.7 | None viable | 6/7 cases, stuck on last |
| Erdos #728 (NT, solved by AI) | All PASS | ~8.0 | Track 2 | Solved by GPT+Aristotle |
| Erdos #124 weak (solved by Boris) | All PASS | ~7.5 | Track 2 | Solved by Boris INFORMAL |
| Seymour n=8 | FAIL G4 (2^56 search space) | 6.5 | REJECT | Already proven (Kaneko-Locke) |
| Erdos-Straus r=1 | FAIL G1 (infinite), FAIL G3 (decades resist) | 8.0 nominal, but gates fail | REJECT | Open, no progress |
| Formal Conjectures sweep | All PASS for subset | 8.4 | Track 1 + Track 3 | Not yet attempted |

The calibration shows the gates correctly reject Tuza-like problems and Erdos-Straus while accepting the Formal Conjectures sweep and NT problems that have actually been solved.

---

## Action Priority (Debate Consensus + Boris Findings)

1. **75% — Formal Conjectures Sweep** (Track 1 + Track 3)
   - Clone repo, filter for finite/NT/algebra, falsify then prove
2. **25% — Gated Tuza** (Track 2 experimental)
   - INFORMAL mode only for 50 slots, formalize only if sketch emerges
3. **0% — Erdos-Straus, Seymour, Brocard**
   - Gates fail: infinite domain, search space, or decades of resistance
