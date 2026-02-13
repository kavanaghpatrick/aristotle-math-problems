# Operating Model: Solving Tuza's Conjecture for ν=4 with Aristotle

## Context

978 submissions, 127 proven, 43 false lemmas, 56 failed approaches, 46 days.
6/7 cases proven. PATH_4 both-endpoints remains open.

---

## Core Thesis (Revised After Pressure Test)

Aristotle is a **verifier first, gap-filler second** — but it CAN fill gaps on
competition-level problems (90% MiniF2F, 100% Polya-Szego). Our sorry=1 failures
are domain-specific: research-level combinatorics is the hardest domain for all
AI provers (CombiBench: 7/100). The math is still the bottleneck, but we should
experiment with hints and INFORMAL mode for the remaining gap.

### Evidence FOR sorry=0 strategy (our data)
- 127/127 proven submissions had sorry=0 on input
- 0/183 sorry=1 submissions achieved proven status
- 0/630 sorry≥2 submissions achieved proven status
- 53 sorry=1 attempts at τ≤8 → 0 successes
- 84% of failed approaches were "wrong direction" (math wrong, not code)

### Evidence AGAINST sorry=0 exclusivity (external data)
- Polya-Szego: 80/80 (100%) WITH sorry in files
- IMO 2025: 5/6 gold medal
- MiniF2F: 90% state of the art
- PROVIDED SOLUTION hints: documented feature we never tried
- CombiBench 7/100 explains the discrepancy (domain difficulty, not tool misuse)

---

## The 5 Core Skills

### 1. Falsify Before Proving
- ~40% of conjectures tested were false
- Submit negation on Fin 6-7 BEFORE investing in proof
- Aristotle's native_decide on counterexample > unanimous AI consensus
- Check false_lemmas DB (43 entries) before ANY new conjecture
- Each falsification prevents 2-10 wasted submission slots

### 2. sorry=0 as Primary Strategy (with Experimental sorry=1 Track)
- 77% success at sorry=0, 0% at sorry≥1 (in our domain)
- Write the complete proof yourself using helpers
- Aristotle verifies reliably; gap-filling fails on research-level combinatorics
- **NEW**: Experiment with sorry=1 + PROVIDED SOLUTION hints on sub-lemmas
- **NEW**: Use `admit` on everything except the ONE target gap
- **NEW**: One sorry per file, individual sub-lemma files for full MCTS budget

### 3. native_decide on Fin n
- 3,229 uses across 840 files — the dominant proof-closing tactic
- Fin 9-12 for proofs, Fin 5-7 for falsification
- Scaffold tower: 10-80 helpers, each closed by native_decide
- rcases ... with rfl | rfl | rfl | rfl → native_decide per case
- Explicit witnesses for existentials, never search tactics

### 4. Multi-Agent Debate for Stress-Testing
- 4-round format, full context accumulation
- Round 2 is where insights emerge
- Best at finding FALSE claims, not generating proofs
- Christmas Day false lemma → 3 cases fell in one day
- 3 falsified claims had prior multi-agent endorsement — always verify on Fin n

### 5. Database-as-Institutional-Memory
- false_lemmas: 43 entries — query before every submission
- failed_approaches: 56 entries — 84% were "wrong direction"
- v_actionable_near_misses: auto-filters blocked near-misses
- approach_hash UNIQUE constraint prevents duplicate failed approaches

---

## The Scaffold Tower Architecture

Every successful file follows this structure:

```
1. Header block: case description, proof sketch
2. set_option maxHeartbeats 400000-800000
3. abbrev V := Fin n
4. Definitions: A, B, C, D as Finset V; M as Finset (Finset V)
5. Graph: named adjacency predicate + inferInstanceAs
6. Scaffolding: 10-80 helper lemmas (cardinality, intersection, membership)
7. Triangle enumeration: trianglesInG = M ∪ externals (native_decide)
8. Cover construction: explicit Finset of edges
9. Coverage verification: per-triangle lemmas
10. Main theorem: assembly via rcases + exact
```

### Key Encoding Rules
- Edges as Finset V of card 2, NEVER Sym2 V (self-loop pitfall)
- Named adjacency predicate + `inferInstanceAs (DecidableRel starAdj)`
- `import Mathlib` (full, not selective — ensures all instances available)
- Own namespace per file to prevent name collisions
- 200-400 lines sweet spot

---

## What NEVER Works

| Anti-Pattern | Evidence |
|---|---|
| sorry≥1 expecting gap closure | 0/813 success rate |
| Bridge coverage assumptions | 14 falsified variants |
| LP / duality formalization | 0/19 proven, load failures |
| Assembly files | 0/8, too complex to load |
| Custom structures (Path4Config) | Aristotle can't synthesize instances |
| Resubmitting without rewrite | 0% on mode-change-only resubmissions |
| Assuming shared structure | #1 error pattern, 15 false lemmas |
| Finset.sym2 for edge encoding | 12+ invalidated proofs |

---

## The Remaining Mathematical Gap

### PATH_4 Both-Endpoints: τ(T_e(A))=3 when base-edge externals exist

When BOTH endpoints have base-edge externals:
- τ(T_e(A)) can be 3 (slot556 verified on Fin 9)
- Naive bound: 3 + 6 = 9 > 8

### Most Promising Strategy: Compensating Decomposition

The slot556 counterexample reveals WHY it should still work:

1. τ(T_e(A))=3 forces w1,w2 ∈ B (5-packing argument)
2. Cover T_e(A) ∪ T_e(B) jointly with 4 edges: E(B) ∪ {a1,a2}
3. Remaining has ν≤2 → τ≤4
4. Total: 4 + 4 = 8

### Execution Plan

```
Step 1: Falsify compensation pieces on Fin 9 (use slot556 graph)
Step 2: Prove w1,w2 ∈ B when τ(T_e(A))=3 (sorry=0 on Fin 9-12)
Step 3: Prove 4-edge cover of T_e(A) ∪ T_e(B) (sorry=0)
Step 4: Prove ν(remaining) ≤ 2 (sorry=0)
Step 5: Assembly at sorry=0 → submit to Aristotle
```

---

## Kill List (Do NOT Retry)

- Apex-based bridge coverage (slot543 counterexample, Fin 11)
- 6-packing argument (slot530 K4 counterexample)
- LP duality (too complex for Aristotle)
- Universal apex for endpoints (Fin 10 K4 counterexample)
- τ(T_e(A)) ≤ 2 (slot556, Fin 9, Aristotle-verified FALSE)
- T_e(A)+T_e(D)+remaining (2+2+4=8) — broken because first term can be 3
- "all-six ⇒ ν≥5" debate consensus — WRONG when w1,w2 ∈ B

---

## Pressure Test Results (10-Agent Research, Feb 9 2026)

### Questions Answered

**Q1: Are we using Aristotle correctly?**
Partially. Aristotle IS designed to fill sorry gaps — it's a core feature, not secondary.
Polya-Szego benchmark: 80/80 (100%) with sorry-containing files. IMO 2025: 5/6 gold.
Our 0/183 sorry=1 failure rate is anomalous. Two explanations:
- CombiBench: only 7/100 for combinatorics — our domain is genuinely harder
- We never used PROVIDED SOLUTION hints (documented feature for guiding MCTS search)

**Q2: Is the sorry=0 cliff domain-specific?**
YES. MiniF2F: 90%, VERINA: 96.8%, Polya-Szego: 100%. These are competition/textbook
problems. CombiBench (combinatorics): 7/100. The cliff is real FOR US because our sorry
gaps are research-level combinatorics, not competition-level algebra/analysis.

**Q3: Are there usage patterns we're missing?**
YES — three:
1. **PROVIDED SOLUTION**: Natural language proof hints in header comments guide MCTS
2. **Strategic admit**: Use `admit` for everything except the ONE gap → focuses budget
3. **INFORMAL discovery**: Submit problem in natural language, let autoformalizer decompose

**Q4: Has anyone used Aristotle on open conjectures?**
Boris (Harmonic employee) has ~10 successful solves with minimal intervention. The
Formal Conjectures Project (Bloom, Gowers, et al.) targets open problems but no
published success yet. No one has published a methodology for open conjectures.

**Q5: Is native_decide optimal?**
For finite graph combinatorics, yes. Alternatives to explore:
- `omega` for linear arithmetic over naturals
- `aesop` for term rewriting
- `lean-auto + Z3/CVC5` for SMT-backed reasoning on larger types
- `Decidable` instances + `decide` for propositional logic

**Q6: Better graph encodings?**
LeanCamCombi library has graph theory infrastructure for Lean 4. Worth checking for
relevant lemmas. Our Finset-of-card-2 encoding is sound; the key is avoiding Sym2.

**Q7: State of Tuza research 2025-2026?**
- Parker published ν≤3 → τ≤6 in EJC May 2025 (arXiv:2406.06501)
- ν=4 remains genuinely open — no published proof
- Our formalization is the FIRST-EVER attempt to formally verify any case of Tuza
- Haxell's ν=6 → τ≤12 (2-approximation) remains best general bound

### Key External Benchmarks

| System | Benchmark | Score | Domain |
|--------|-----------|-------|--------|
| Aristotle | MiniF2F | 90% | Competition math |
| Aristotle | IMO 2025 | 5/6 gold | Olympiad |
| Aristotle | Polya-Szego | 80/80 (100%) | Textbook analysis |
| HILBERT (Apple) | MiniF2F | 99.2% | Competition math |
| DeepSeek-Prover-V2 | MiniF2F | 88.9% | Competition math |
| Numina-Lean-Agent | Putnam 2025 | 12/12 | Competition math |
| All systems | CombiBench | 7/100 | **Combinatorics** |

The competition-to-research gap is enormous. No AI system reliably solves open research
problems. CombiBench confirms combinatorics is the hardest domain for current provers.

### Boris Alexeev Methodology Findings (4-Agent Research, Feb 9 2026)

Boris (Harmonic employee, ~10 successful Erdos solves) uses a FUNDAMENTALLY different
workflow from ours:

| Dimension | Boris (successful) | Us (978 submissions) |
|-----------|-------------------|---------------------|
| Sorry strategy | Submits WITH sorry, ~45% fill rate | sorry=0 only, 0/210 fill rate |
| Mode | INFORMAL mode extensively | FORMAL_LEAN exclusively |
| Idea generation | ChatGPT explains solution first | We write the Lean ourselves |
| Pipeline | GPT idea → Aristotle formalizes | Human scaffolding → Aristotle verifies |
| native_decide | Rarely used | 3,229 uses (our dominant tactic) |

**Three Breakthrough Workflows Identified:**
1. **Workflow A (hard problems):** LLM generates proof idea → Aristotle auto-formalizes → verify
   - How Erdos #728 and IMO 2025 were solved
   - Boris's primary method
2. **Workflow B (easier problems):** Submit formal Lean statement → Aristotle works autonomously
   - What the Formal Conjectures sweep would use
   - Works for competition-level, NOT research-level
3. **Workflow C (batch discovery):** Multiple LLMs generate attempts → human filters → submit best

**Key revelation:** The Aristotle API we use is a "dramatically reduced version" of the full
system that solved IMO 2025. The full system has informal reasoning + autoformalization
pipelines we don't access.

**Implication:** Our 0/210 sorry=1 rate may be self-imposed — Boris gets ~45% because he
provides proof context via INFORMAL mode. We provide bare sorry gaps without context.

### Revised Strategy: Triple-Track Approach

**Track 1 — Finite Verification (50% effort): sorry=0 scaffolded proofs**
- Proven: 77% success rate, 127 proven files.
- Apply to: Formal Conjectures falsification sweep, Tuza lemmas.
- Skill: native_decide on Fin n, falsification-first, scaffold tower.

**Track 2 — Boris Workflow (30% effort): INFORMAL + proof sketches**
- NEW: Adopt Boris's pipeline for harder problems.
- Claude/GPT generates complete proof idea in natural language.
- Submit via INFORMAL mode (.txt) — let Aristotle auto-formalize.
- Use PROVIDED SOLUTION hints in header comments for FORMAL_LEAN files.
- Test on KNOWN provable lemmas first to calibrate success rate.
- Apply to: Tuza PATH_4, Erdos NT problems, harder Formal Conjectures.

**Track 3 — Portfolio Diversification (20% effort): New problem frontiers**
- Formal Conjectures falsification sweep (high volume, our skills transfer directly).
- Cherry-pick NT/algebra problems with high AI-amenability scores.
- Each solved problem is independently publishable.

### Alternative Tools to Explore

| Tool | Use Case | Status |
|------|----------|--------|
| DeepSeek-Prover-V2 | Generate proof sketches (open source, 671B) | Available |
| Lean Copilot | IDE tactic suggestions, 74.2% automation | Available |
| Pantograph | Programmatic proof search API for Lean 4 | Available |
| lean-auto + Z3 | SMT-backed reasoning for larger types | Available |
| LeanCamCombi | Graph theory library for Lean 4 | Check relevance |

---

## Kill List (Do NOT Retry — Updated)

### Mathematical Dead Ends
- Apex-based bridge coverage (slot543 counterexample, Fin 11)
- 6-packing argument (slot530 K4 counterexample)
- Universal apex for endpoints (Fin 10 K4 counterexample)
- τ(T_e(A)) ≤ 2 (slot556, Fin 9, Aristotle-verified FALSE)
- T_e(A)+T_e(D)+remaining (2+2+4=8) — broken because first term can be 3
- "all-six ⇒ ν≥5" debate consensus — WRONG when w1,w2 ∈ B

### Technical Dead Ends
- LP duality formalization (too complex for Aristotle, 0/19)
- Assembly files (too complex to load, 0/8)
- Custom structures like Path4Config (Aristotle can't synthesize instances)
- Finset.sym2 for edge encoding (self-loop pitfall, 12+ invalidated)
- Mode-change-only resubmissions (0% success rate)

---

## Problem Selection: AI-Amenability Landscape (10-Agent Research, Feb 9 2026)

### Domain Success Rates (best AI systems)

| Domain | AI Success Rate | Our Evidence |
|--------|----------------|-------------|
| Algebra | 85-100% | MiniF2F, Polya-Szego |
| Number Theory | 75-97% | Erdos #728, #1026 solved by AI |
| Analysis | 25-100% | Level-dependent |
| Geometry | 0-83% | Dedicated solver required |
| **Combinatorics** | **7-50%** | **CombiBench; our 13% over 978 submissions** |

### Tuza nu=4 AI-Amenability Score: 3.7/10

| Dimension | Score | Notes |
|-----------|-------|-------|
| Domain | 4/10 | Extremal graph theory — hardest AI domain |
| Proof Structure | 2/10 | Multi-step with interacting cases |
| Mathlib Readiness | 2/10 | No packing/covering infrastructure |
| Finite Reducibility | 6/10 | Individual cases verify, assembly doesn't |
| Proof Length | 4/10 | 3000+ lines across files |
| Formalization Precedent | 2/10 | First-ever Tuza formalization |
| Community Interest | 7/10 | Named conjecture, active research |

### Higher-Scoring Alternative Targets

| Problem | Score | Domain | Finite? |
|---------|-------|--------|---------|
| Erdos NT problems (long tail) | 7-8.5 | Number theory | Yes |
| Erdos-Straus residue classes | ~8.0 | Algebra | Yes |
| Seymour 2nd Neighborhood (n=7-8) | ~6.5 | Graph theory | Yes |
| Formal Conjectures sweep | varies | Mixed | Mostly |
| Brocard nonexistence (ranges) | ~7.0 | Number theory | Yes |
| Frankl (graph form, small n) | ~5.5 | Combinatorics | Yes |

### Why Combinatorics Is the Hardest Domain for AI

1. Largest formalization gap (every problem is its own micro-theory)
2. Ad hoc constructions vs algebraic rewrite rules (branching factor explosion)
3. Thinnest Mathlib coverage (algebra 9/10, graph theory 4/10, packing 2/10)
4. Proof length explosion (Tutte: 5,757 lines vs algebraic results: 10-50 lines)
5. "Simple counting arguments" in informal math = 100 lines in Lean

### What Open Problems Has AI Actually Solved? (as of Feb 2026)

- Erdos #728 (NT) — GPT-5.2 + Aristotle. Tao verified.
- Erdos #1026 (combinatorics) — Aristotle autonomous. Tao verified.
- Erdos #1051 (combinatorics) — Aletheia (DeepMind).
- Fel's Conjecture (commutative algebra) — AxiomProver.
- Chen-Gendron (algebraic geometry) — AxiomProver.
- 15 Erdos problems shifted from open to solved since Christmas 2025, 11 crediting AI.
- Tao's assessment: "lowest hanging fruit" — ~1-2% of open Erdos problems tractable for AI.
