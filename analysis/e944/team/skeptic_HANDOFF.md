# skeptic HANDOFF (E944) — for successor verifier

Role: immune system + free agent. Verify the load-bearing; attack smallest instances; demand two
independent χ-checkers agree before anything is called a result. Working dir /Users/patrickkavanagh/math.
NEVER submit to Aristotle. DB erdos_944 rows are mirages.

## 1. VERIFIED GROUND TRUTH (cite these — all dual-checker confirmed)

- **STATEMENT LOCK — skeptic_statement_lock.md.** The Lean theorem `∃ V G, IsErdos944 4 1` over
  arbitrary `V : Type u` is EQUIVALENT to the finite question "∃ a finite simple graph, χ=4,
  vertex-critical, no critical edge." Mechanism = the **ncard infinite trap** (`Set.ncard` of an
  infinite set = 0 ⟹ clause `1 < edges.ncard` fails for any infinite critical edge-set ⟹ any
  infinite-edge G fails; finite-edge + vertex-critical at χ=4 ⟹ finite). NO de Bruijn–Erdős, NO
  compactness needed (Mathlib has neither). Supersedes archivist_definitions.md pt 4 (which asserted
  finiteness by fiat). All Lean facts line-referenced to pinned Mathlib.

- **SMALL-n GROUND TRUTH — skeptic_smalln_groundtruth.md + skeptic_enum.py.** Every 4-vertex-critical
  graph on n ≤ 9 HAS a critical edge. Counts n=4..9 = 1,0,1,7,8,124, all with a critical edge, 0
  witnesses. Two independent χ-checkers (from-scratch backtracking `chi_A` + SAT `chi_B`) agreed on
  EVERY graph (157,905 cross-checks at n=9 alone, 0 disagreements). Triple-sourced: matches hunter's
  geng floor EXACTLY and count's graph_atlas (n≤7). δ≥3 filter validated empirically at n=8.
  ⟹ Any witness has ≥ 11 vertices.

- **STEINER PROBLEM 5.2 FLOOR — skeptic_problem52_floor.md + skeptic_6regular.py.** Exhaustive over ALL
  connected 6-regular graphs: n=11 (266 graphs) → 0 even 4-vtx-critical; n=12 (7,849) → 0; n=13
  (367,860) → exactly 1 four-vtx-critical (= count's C₁₃(1,2,5)), which HAS a critical edge. **No
  6-regular (4,1)-graph on n ≤ 13.** First 6-regular 4-vtx-critical graph appears only at n=13.

- **PROP 5.1 VERIFIED — skeptic_prop51_verification.md.** Skottova–Steiner min-deg≥6 / λ≥6 / |V|≥11
  independently re-derived. Load-bearing identity "smallest critical edge-set size == min monochromatic
  edges over 3-colorings" verified EXACTLY on all 4-crit graphs n≤7 (0 mismatches). Two independent
  derivations of min-deg-6 now exist (mine coloring-side + proximity's hypergraph-side). SOLID — the
  d6 geng filter is justified, loses no witness.

- **JENSEN–SIGGERS E* SIGNATURE — skeptic_jensen_siggers_Estar.md.** On all 141 four-vertex-critical
  graphs n≤9, the critical-edge subgraph E* is ALWAYS nonempty, connected, AND spanning (0 exceptions).
  Strong empirical corroboration of the J–S impossibility conjecture (if E* forced nonempty ⟹ k=4 NO).
  CALIBRATED: small-n universality is NOT proof; E*=∅ demonstrably at k=5, so no degree reason forces
  it at k=4. Evidence, not theorem.

- **C₁₃(1,2,5) VERIFIED** (count's closest approximate witness): 6-regular, χ=4, vertex-critical,
  critical ONLY on difference-1 orbit, 26/39 edges non-critical. Reproduced with my dual checkers.

## 2. IN FLIGHT — KILLED, state recorded
- n=10 FULL sweep (skeptic_enum.py 10, every graph SAT-cross-checked) was REDUNDANT with hunter's
  completed n=10 (2453 four-critical graphs, 0 witnesses, exhaustive). KILLED per snapshot order
  (PID 40686). No loss: hunter's n=10 floor stands; my version only added per-graph SAT which is
  overkill at n=10. If a successor wants the redundant verify, rerun `python3 skeptic_enum.py 10 10 3`.

## 3. NEXT STEPS for successor (in priority order)
1. **Push Problem 5.2 floor to n=14, n=15** if pruning holds: `python3 skeptic_6regular.py 14`.
   n=14 6-regular count is the gate (was being counted; check feasibility — likely a few×10⁶, heavy).
   Same dual-checker standard. This is the team-lead's explicit next ask.
2. **Extend J–S E* test to n=10, 11** — does E* stay connected+spanning? A disconnected/non-spanning
   E* at small n would weaken the conjecture's strong form (nonempty could still hold).
3. **Adversarial review** of wall's circulant impossibility theorem and forge's Jensen–Siggers surgery
   candidates AS THEY LAND. Verify before anything is called a result.

## 4. OPEN UNVERIFIED CLAIMS across the squad (check these)
- **wall** — circulant non-existence theorem (in progress): when it lands, verify the difference-1
  obstruction argument is rigorous, not just empirical. ALSO: I flagged two errors in
  wall_impossibility.md (line 19 de-Bruijn–Erdős justification is WRONG — use ncard trap; §4 table
  mislabels C₇(1,2)/C₁₀(1,2,5)/C₁₆(1,2,5,8)/C₁₉/C₂₂ as 6-regular — they're not, s=n/2 collapse). Confirm
  wall fixed these.
- **forge** — any "candidate witness" from Jensen–Siggers surgery MUST be re-verified with two
  independent χ-checkers before celebration. forge's harness uses networkx+ILP; cross-check with
  skeptic_enum.py chi_A AND chi_B.
- **gallai** THM 2 rainbow-forcing characterization (claims 103 edges, 0 mismatches) and THM 4
  forced-2-2-2 balanced neighborhoods — independently re-derive on a sample if a proof leans on them.
- **jensen** "double-cover ⟹ k≥5" shared failure mode — jensen flags it himself as the conjecture wall
  restated, NOT proven. Do not let it be cited as a theorem.

## VERIFICATION STANDARDS TO ENFORCE (the squad's failure modes)
1. Witness verified with a buggy χ-checker → demand chi_A AND chi_B agree before celebrating ANY witness.
2. Impossibility proof silently assuming finiteness / using a false folklore lemma → the finiteness is
   NOW justified (ncard trap, statement lock); reject any argument leaning on de Bruijn–Erdős/compactness.
3. Literature claims quoted from abstracts not proofs → archivist's J–S + M-S extracts ARE PDF-verified;
   trust those. Re-verify any NEW literature claim against the actual proof.

## TOOLS
- `skeptic_enum.py [Nmax] [Nmin] [mindeg]` — full sweep, dual χ-checkers, self-test on import.
- `skeptic_6regular.py <n>` — Steiner Problem 5.2 exhaustive 6-regular sweep.
- chi_A = backtracking + clique LB; chi_B = SAT (Cadical). Import both from skeptic_enum.
- nauty `geng` at /opt/homebrew/bin/geng. networkx 3.6.1, pysat available.
