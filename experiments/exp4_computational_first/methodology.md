# EXP4: Computational-First Conjecture Refinement

**Date**: 2026-05-31
**Target**: Erdős 938 (consecutive powerful 3-APs)
**Hypothesis**: Massive computational exploration FIRST (before theoretical reasoning) produces sharper hypothesis formation than theory-first prompts.

## Protocol

### Phase 1: COMPUTATION (massive enumeration)
Generate ≥10,000 lines of data without any a priori theoretical lens:
- C1: Enumerate all powerful numbers up to N=10^11 (extending MEGA-7's 10^10)
- C2: For each powerful triple in AP (NOT just consecutive), record:
  - n_k, n_k+1, n_k+2 (consecutive index)
  - All "Golomb decompositions" (a, b) with n = a²b³, b cubefree
  - Full factorization
  - Residues mod every prime power up to 144 (12² = lcm(4,9,16,25,...))
  - "Square-distance": min |√n - integer|
  - Differences (n_k+2 - n_k+1) vs (n_k+1 - n_k)
- C3: For powerful 3-APs that are NOT consecutive, count intervening powerfuls and tabulate
- C4: For each powerful number p ≤ 10^9, compute the "powerful-AP score" = number of (d, n) pairs with both n+d and n+2d powerful
- C5: Enumerate solutions to x²-Dy²=k for D in {7³, 8, 5³, 3⁶, 5³·3⁶, ...} systematically up to large bounds, check if any yields a powerful 3-AP
- C6: Generate the data WITHOUT looking at any prior dossier

### Phase 2: PATTERN ANALYSIS
After data is generated, look ONLY at the data:
- Distributional analysis: how does count_powerful_3APs(x) grow?
- Modular signatures: are there hidden modular obstructions beyond mod-4 and mod-9?
- Algebraic invariants: do consecutive 3-APs share any structural invariant we haven't named?
- "What patterns are screaming at us from the data?"

### Phase 3: SUB-CONJECTURE GENERATION
Propose ≥5 sharper sub-conjectures **derived from the data**, not from prior theory:
- Each sub-conjecture must be falsifiable
- Each must have a tractability score (1-10) on:
  - Mathlib readiness
  - Empirical support strength
  - Potential novelty
  - Proof complexity

### Phase 4: TRACTABILITY VOTING
Pick the most tractable + impactful, attempt formal proof outline.

## Comparison Metric

Compare to "theory-first" baseline = MEGA-7 (which used Pell theory + literature first, then computation to verify).

EXP4 succeeds if:
- We find at least one structural pattern that MEGA-7 missed
- The data-derived sub-conjecture(s) are SHARPER (more specific, more testable) than the theory-derived ones

## Falsifiers (failure modes)
- All data confirms prior theory exactly → computational-first adds no new info
- Data reveals no new patterns Beyond MEGA-7's 5³·3⁶ insight
- Computational cost is prohibitive relative to insight gained
