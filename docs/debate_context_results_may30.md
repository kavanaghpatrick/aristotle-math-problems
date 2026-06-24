# Strategic Context: May 30 2026 Batch Results

This continues the May 29 debate. Read `/Users/patrickkavanagh/math/docs/debate_context_strategy_may29.md` for the full historical context and `/Users/patrickkavanagh/math/docs/debate_strategy_may29.md` for the prior 3-round debate transcript.

## What Happened

5 sketches drafted by 5 parallel agents per the May 29 consensus, submitted as a batch to Aristotle, all completed within 24 hours.

## Audit Results (5/5 useful — historical hit rate is 0.17%)

### slot736 — Feit-Thompson p=3, q ≡ 71 mod 72, q ≤ 1500
**VERDICT: compiled_advance.** 0 sorry, 0 axiom.
- Extended slot720's family from q ≤ 1000 (7 primes) to q ≤ 1500 (11 primes).
- Added 4 new primes: {1151, 1223, 1367, 1439}. Sketch claimed +5 but 1511 > 1500.
- Proof: `interval_cases` + `native_decide` over `Finset.range 1501`.
- **Mechanical extension. Not novel math — just bumping bounds on slot720's proven mechanism.**
- Next mechanical step (q ≤ 2000) adds {1511, 1583, 1607, 1733, 1823, 1871} but pre-scan said q=1583 breaks because A(1583) is prime.

### slot737 — Erdős 647 Sophie residue subclass
**VERDICT: compiled_advance.** 0 sorry, 0 axiom. (COMPLETE_WITH_ERRORS label was a linter warning on a deliberately preserved unused hypothesis — false alarm.)
- Closes the Sophie Germain branch of slot723's 1 remaining sorry, minus exactly the Cunningham-chain cases.
- Independent witness lemmas with STRONGER σ₀ bounds than slot723 (6 and 7 instead of 4).
- Boolean exclusion `¬Prime((q−1)/2) ∨ ¬Prime((2q−1)/3)` is an honest hypothesis, not an axiom.
- **Genuinely novel.** Narrows the failure region of Erdős 647 to exactly the Cunningham-chain configurations.
- Residual: ~35 cases in [3000, 10⁶] (the 0.82% Cunningham chains). The remaining open piece is now a clean, well-defined sieve question.

### slot738 — Brocard n ∈ [501, 1000]
**VERDICT: compiled_advance.** 0 sorry, 0 axiom.
- Range genuinely verified, not slot722 axiomatized.
- **Methodology improvement**: Aristotle ABANDONED the `nthPrimeComp` recursive bridge from slot722 in favor of explicit witness-table encoding + 10-chunk × 50-entry `native_decide` cascade. Better scaling — per-chunk maxHeartbeats 8M (slot722 used 16M globally for half the range).
- New encoding has headroom — push to [1001, 2000] reasonable.
- **Mechanical extension + an unexpected encoding refactor. Half novel.**

### slot739 — Leinster nonabelian existence (D₃ × C₅)
**VERDICT: compiled_advance per rubric.** 0 sorry, 0 axiom.
- Independently rebuilt the witness lemma (did NOT reuse slot575's `leinster_d3_prod_zmod5`).
- `IsLeinster` definition matches formal-conjectures `LeinsterGroup.lean` (sum of `Nat.card` over normal subgroups equals 2|G|).
- Nonabelian condition verified by `native_decide` over the 30-element type, not assumed.
- **BUT**: formal-conjectures marks `exists_nonabelian_leinster_group` as `@[category research solved]` — this is **formalization of a 2001 Leinster result, not novel mathematics.**
- The truly open Leinster gap is `infinitely_many_leinster_groups` (still `research open`), reducible to the open question of infinitely many even perfect numbers. Untouched.

### slot740 — Erdős 203 index-1 covering, M=8 B=500
**VERDICT: disproven.** 0 sorry, 0 axiom.
- **Aristotle FOUND an explicit covering witness.** At `m = 1579554969991861182625270235031094424159694` (43 decimal digits), index-1 primes ≤ 500 cover ALL 64 cells of the 8×8 (k,l) grid.
- Greedy set cover used 22 of 69 index-1 primes ≤ 500. Realized by CRT.
- Audit agent independently verified all 64 cells covered via Python.
- **This is a counterexample to the impossibility direction we asked for, but strategically MUCH more valuable than confirming impossibility.**
- The slot724 honest assessment that "index-1 density diverges so impossibility doesn't go through" is now provably correct with a constructive witness.
- The path to actually CONSTRUCTING an Erdős 203 witness (Sierpiński-like 2D number m where 2^k·3^l·m+1 is composite for all k,l) just opened.

## Aggregate Pipeline Effectiveness

The May 29→30 pipeline ran:
1. /status to find inflight jobs
2. /fetch + audit to assess artifacts
3. 3-AI debate (Gemini + Codex) to set strategy
4. 5 parallel agents draft sketches under hard rules
5. Batch submit
6. 5 parallel audit agents

Result: 5/5 useful (4 compiled_advance + 1 disproven). Historical baseline: 0.17% advance rate. The pipeline is ~600× the historical rate.

**Caveat**: this is one batch of 5. Sample size too small to declare the pipeline reliably 600× better. But the 5/5 ALL had clean Lean, ALL had honest verdicts, NONE were no-advance restatements — that's the strongest signal we've ever produced.

## Novel-vs-Formalization Split

- **Mathematically novel (advance human understanding):** slot737 (E647 Cunningham narrowing), slot740 (E203 explicit cover witness)
- **Mechanical extension of prior advance:** slot736 (FT q-bound bump), slot738 (Brocard range bump + encoding refactor)
- **Formalization of known-solved math:** slot739 (Leinster 2001)

Per user prime directive: "We care about NOVEL solutions, not formalization." 2/5 of the batch is mathematically novel.

## Debate Questions

1. **Pipeline lock-in.** Is the team→debate→draft→batch protocol genuinely reproducible at this hit rate, or are we cherry-picking? Should we standardize it as the default workflow for all future submissions? What's the failure mode if we run it on harder problems (e.g., the Tuza nu=4 carcass)?

2. **slot740 pivot.** Should we immediately submit a new bare-gap for the EXISTENCE direction of Erdős 203 (∃ m such that 2^k·3^l·m+1 composite for all k,l), using slot740's witness construction as auto-attached context? Or is the witness m=1579... only a finite-grid artifact that doesn't lift to the infinite case? Be specific about whether the path to lifting exists.

3. **Cunningham chain dedicated push.** The residual 35 Cunningham-chain cases in [3000, 10⁶] of E647 are now the only open piece of that conjecture's failure region. Is there a structural angle (the chains are linked by simple linear forms) or is this genuinely a hard sieve problem (Schinzel's hypothesis, etc.)? Should we submit a dedicated bare-gap for it?

4. **Mechanical iter4 worth doing?** FT q ≤ 2000 and Brocard [1001, 2000] are mechanical wins. Each adds `compiled_advance` count but neither is novel math. With user prime directive ("novel, not formalization"), is the rubric-credit worth the compute, or are we cargo-culting metric?

5. **Deprioritize Leinster?** slot739 is a rubric advance but not novel math. The truly open Leinster question (`infinitely_many_leinster_groups`) reduces to the infinitude of even perfect numbers — a famously hard open problem we cannot touch. Should Leinster drop from active rotation?

6. **The next 5 problems for the week of June 1-7.** Given:
   - 2 fresh near-misses (slot737 leaves Cunningham-chain core; slot740 disproved finite-grid impossibility, opens existence direction)
   - 2 mechanical extensions still cheap (FT q≤2000, Brocard [1001,2000])
   - The user wants depth-over-breadth (5 problems, not 500)
   - The novel-math bias
   Which 5? Defend against alternatives. Each AI should give its top 5 with reasoning.
