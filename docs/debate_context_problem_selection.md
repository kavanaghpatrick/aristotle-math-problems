# Debate Context: Which Open Problems Should We Tackle Next?

## Who We Are

A team using Aristotle (Harmonic's AI theorem prover) + Claude Code + multi-agent strategy to formally verify open mathematical conjectures in Lean 4. 46 days in, 978 Aristotle submissions.

## Our Track Record

### Tuza's Conjecture for nu=4 (our flagship)
- **Goal**: Prove tau(G) <= 8 whenever nu(G) = 4 (triangle packing/covering)
- **Status**: 6/7 cases proven. PATH_4 both-endpoints remains open.
- **Stats**: 978 submissions, 127 proven lemmas, 43 false lemmas discovered, 56 failed approaches
- **Blockers**: 6 falsified strategies on the remaining case. The PATH_4 both-endpoints case requires a novel combinatorial argument about how bridge edges interact with endpoint-sharing base-edge externals. tau(T_e(A)) can be 3 (slot556 verified), making naive bound 9 > 8.
- **AI-amenability score**: 3.7/10 — "Very hard" category
- **Significance**: First-ever formal verification attempt for any case of Tuza's conjecture. Publishable regardless of whether we finish.

### Our Proven Core Skills
1. **sorry=0 cliff**: 77% success at sorry=0, 0% at sorry>=1 (in combinatorics). For NT/algebra, Aristotle fills sorry gaps at 90%+ rates.
2. **Falsification-first**: ~40% of conjectures tested were false. Submit negation on Fin 5-7 BEFORE investing. Each falsification prevents 2-10 wasted slots.
3. **native_decide on Fin n**: 3,229 uses. Fin 9-12 for proofs, Fin 5-7 for falsification. THE dominant proof-closing tactic.
4. **Scaffold tower architecture**: 200-400 lines, 10-80 helpers, explicit witnesses. Every proven file follows this structure.
5. **Multi-agent debate**: 4-round format. Best at finding FALSE claims. Round 2 is the insight round.
6. **Database-as-memory**: 43 false lemmas, 56 failed approaches tracked. Query before every submission.

### What We Learned About AI Theorem Proving (from 30 research agents)

**Domain success rates (best AI systems, Feb 2026):**
| Domain | AI Success Rate |
|--------|----------------|
| Algebra | 85-100% (MiniF2F 99.2%) |
| Number Theory | 75-97% (Erdos problems solved autonomously) |
| Analysis | 25-100% (level-dependent) |
| Geometry | 0-83% (dedicated solver required) |
| Combinatorics | 7-50% (CombiBench 7-48%) |

**What open problems has AI actually solved (since Dec 2025)?**
- Erdos #728 (NT) — GPT-5.2 + Aristotle. Tao verified.
- Erdos #1026 (combinatorics/Ramsey) — Aristotle autonomous. Tao verified.
- Erdos #1051 (combinatorics) — Aletheia (DeepMind).
- Fel's Conjecture (commutative algebra) — AxiomProver, open 10+ years.
- Chen-Gendron (algebraic geometry) — AxiomProver.
- 15 Erdos problems shifted to solved since Christmas 2025, 11 crediting AI.
- Tao's assessment: "lowest hanging fruit" — ~1-2% of open problems tractable for current AI.

**Key external benchmarks:**
- Aristotle: MiniF2F 90%, IMO 2025 5/6 gold, Polya-Szego 100%
- HILBERT (Apple): MiniF2F 99.2%
- CombiBench (combinatorics): 7-48% across all systems
- Longest AI proof: 2,054 lines (AxiomProver, Putnam 2025)
- Competition-to-research gap: 99% on MiniF2F, 2% on FrontierMath T2-T3

**Why combinatorics is hardest for AI:**
1. Largest formalization gap (every problem is its own micro-theory)
2. Ad hoc constructions vs algebraic rewrite rules (branching factor explosion)
3. Thinnest Mathlib coverage (algebra 9/10, graph theory 4/10, packing 2/10)
4. Proof length explosion (Tutte: 5,757 lines vs algebraic results: 10-50)
5. "Simple counting arguments" = 100 lines in Lean

**Aristotle features we haven't fully exploited:**
- PROVIDED SOLUTION hints (proof sketches in header comments guide MCTS)
- Strategic admit (everything except ONE sorry gap)
- INFORMAL mode (natural language → autoformalizer)

## The Candidate Problems (ranked by AI-amenability score)

### Tier 1: Score 8.0+ (Excellent targets)

**1. Formal Conjectures Falsification Sweep (8.4) — OPEN/MIXED**
- Test ~240 formalized Erdos conjectures for counterexamples on Fin 5-7
- Pre-formalized Lean statements from DeepMind. ~60% genuinely open.
- Our falsification-first skill at scale. Minimal setup per problem.
- Each falsification OR proof is independently publishable.
- Risk: Many may be too hard even for falsification. Volume play.

**2. Brocard's Problem (8.2) — OPEN**
- n! + 1 = m^2 has no solutions beyond n = 4, 5, 7
- Genuinely open. Verified computationally to 10^15.
- Modular arithmetic constraints per range. Listed as "easy formalization target" by DeepMind.
- Approach: Prove nonexistence for specific modular classes.
- Risk: Individual modular results may be trivial (not publishable). Full conjecture is very hard.

**3. Formal Conjectures Proof Sweep (8.1) — OPEN/MIXED**
- Attempt sorry=0 proofs of formalized Erdos conjectures amenable to native_decide
- Cherry-pick from 240 formalized statements. Filter for NT/algebra with finite structure.
- Aristotle has already solved some of these autonomously.
- Risk: The easy ones may already be solved. The remaining ones may be hard.

**4. Erdos-Straus Residue Classes (8.0 each, 6 open classes) — OPEN**
- 4/n = 1/x + 1/y + 1/z for all n >= 2
- Verified to 10^18. 6 problematic residue classes mod 840 remain: r = 1, 121, 169, 289, 361, 529
- Each class is a self-contained sub-problem (like our Tuza case decomposition)
- Pure algebraic manipulation. Strong Mathlib modular arithmetic support.
- Approach: Egyptian fraction decomposition via modular arithmetic per residue class.
- Risk: These 6 classes have resisted decades of effort. They may be the "hard core" that requires new ideas. Not clear our tools give an edge here.

### Tier 2: Score 6.0-7.9 (Good targets)

**5. Lehmer's Totient Problem (7.4) — OPEN**
- phi(n) | (n-1) implies n is prime. Open since 1932.
- Any counterexample needs omega(n) >= 14 (Cohen-Hagis). If 3|n, omega(n) >= 40M.
- Approach: Formalize existing bounds via constraint propagation on prime factors.
- Risk: Formalizing existing bounds is useful but not "solving" the problem. Strengthening bounds requires deep NT.

**6. Seymour's Second Neighborhood n=8 (6.5) — OPEN**
- Every oriented graph on 8 vertices has vertex v with |N++(v)| >= |N+(v)|
- n=7 verified (Jan 2026). n=8 is genuinely open.
- native_decide on Fin 8. Directly in our sweet spot.
- Risk: Fin 8 oriented graphs means 2^(8*7) = 2^56 possible directed graphs. native_decide may timeout. May need symmetry breaking or SAT-backed approach.

**7. Frankl Conjecture: Gilmer Bound Formalization (5.8) — KNOWN result, open formalization**
- Some element in >= 1% of sets in any union-closed family (Gilmer 2022).
- Known result but NOT formalized in Lean. High interest.
- Entropy-based argument. Recent Lean 4 work on averaging problem exists.
- Risk: Entropy argument may be hard to formalize. Not solving anything new.

**8. Seymour's Second Neighborhood: out-degree <= 7 (5.8) — OPEN**
- Extend known out-degree <= 6 result to <= 7.
- Finite case analysis on local structure.
- Risk: May require graph theory infrastructure we don't have.

### For Calibration: Our Current Problem

**Tuza nu=4 PATH_4 both-endpoints (3.7) — OPEN, ACTIVE**
- 978 submissions, 127 proven lemmas, 6 falsified strategies
- First-ever Tuza formalization. Publishable regardless.
- The math gap is real: need a novel combinatorial argument.
- Compensating decomposition strategy not yet falsified.

## Key Strategic Questions for the Debate

1. **Should we continue Tuza or pivot?** We're 6/7 cases done but the last case has resisted 6 strategies. Sunk cost vs. being so close.

2. **Volume vs. depth?** The Formal Conjectures sweep is high-volume (many small wins) vs. Erdos-Straus (one deep problem with case decomposition like Tuza).

3. **Do we have an edge on Erdos-Straus?** The 6 residue classes have resisted decades of number theorists. Our edge is Aristotle + native_decide, but these are infinite claims about all primes in a residue class — not finite verification.

4. **Is Seymour n=8 actually feasible?** Fin 8 for oriented graphs is a massive search space. Is native_decide practical here?

5. **Should we diversify or concentrate?** One problem deeply, or sweep 10 problems for quick wins?

6. **What's publishable?** Which results would constitute a paper vs. just a datapoint?

7. **Do we stay in graph theory (our infrastructure) or move to number theory (AI's strength)?**

## Constraints
- We have Aristotle access with ~600 remaining submission slots
- We have Claude Code + multi-agent pipeline (Grok, Gemini, Codex)
- We have deep Lean 4 expertise in finite graph verification
- We have the scaffold tower architecture and falsification pipeline
- We do NOT have deep number theory expertise
- Switching domains means building new infrastructure from scratch
