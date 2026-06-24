---
spec: erdos-candidate-assessment
phase: research
created: 2026-03-13
---

# Research: Erdos 389 & 850 Candidate Assessment

## Executive Summary

Both problems are genuinely OPEN and correctly stated in formal-conjectures. However, neither is tractable for AI-assisted proof in any meaningful sense. Erdos 389 asks Aristotle to prove a universal existential statement over natural numbers with no known proof technique. Erdos 850 requires choosing existence vs nonexistence when experts disagree and the ABC conjecture would be needed for nonexistence. Aristotle has produced useful constraint lemmas for 850 but is nowhere near resolving the gap for either problem.

## External Research

### Erdos 389 - Consecutive Product Divisibility

**Status**: OPEN on erdosproblems.com. Cannot be resolved by finite computation.

**Problem**: For every n >= 1, does there exist k >= 1 such that n(n+1)...(n+k-1) | (n+k)...(n+2k-1)?

**Known results**:
- OEIS A375071 (Bhavik Mehta): minimal k computed for n=0..18
- k values: 1, 5, 4, 207, 206, 2475, 984, 8171, 8170, 45144, 45143, 3648830, 3648829, 7979077, 7979076, 58068862, 58068861, 255278295, 255278294
- Growth is super-polynomial (roughly doubling/tripling each step), NOT 3^n as stated in sketch
- k=n always works (central binomial coefficient) -- trivial
- Source: erdosproblems.com/389, OEIS A375071

**Formal statement** (google-deepmind/formal-conjectures):
```lean
theorem erdos_389 : answer(sorry) ↔
    ∀ n ≥ 1, ∃ k ≥ 1, ∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k, (n + k + i)
```

**CRITICAL ISSUE: Submission statement mismatch**
- `erdos389_corrected.txt` (submitted 2026-03-13): MATCHES formal statement. Uses `(n + i)` and `(n + k + i)`.
- `erdos389_consecutive_v2.txt` and `erdos389_consecutive_bare.txt` (submitted 2026-03-12): WRONG. Uses `(n + 1 + i)` and `(n + k + 1 + i)`. This shifts the product window by 1, giving a different (easier?) problem.
- The two wrong-statement submissions are still in queue.

### Erdos 850 - Three Consecutive Same-Radical Pairs

**Status**: OPEN on erdosproblems.com. Cannot be resolved by finite computation.

**Problem**: Do distinct x, y exist with rad(x)=rad(y), rad(x+1)=rad(y+1), rad(x+2)=rad(y+2)?

**Known results**:
- k=2 (two consecutive radical matches) has infinite solutions: x=2^q-2, y=2^q(2^q-2) for q>=2
- One exceptional k=2 pair: (75, 1215)
- k=3: NO witness known (computational search to 10^8)
- Shorey & Tijdeman: under a STRONG form of ABC conjecture, the answer is NO
- Related to Erdos-Woods problem (OEIS A343101)
- Source: erdosproblems.com/850, OEIS A343101

**Formal statement** (google-deepmind/formal-conjectures):
```lean
theorem erdos_850 :
    answer(sorry) ↔ ∃ x y : ℕ, x ≠ y ∧ x.primeFactors = y.primeFactors
      ∧ (x + 1).primeFactors = (y + 1).primeFactors
      ∧ (x + 2).primeFactors = (y + 2).primeFactors
```

**Multi-AI Debate** (Feb 18): Grok-4 says "likely False," Codex/GPT-5.2 says "likely True." No consensus. Core disagreement: whether structural constraints are prohibitive or merely restrictive.

## Codebase Analysis

### Erdos 389 - Submission History

| Submission | Date | Status | Notes |
|-----------|------|--------|-------|
| erdos389_consecutive_v2.txt | 2026-03-12 | submitted | WRONG statement (off-by-1) |
| erdos389_consecutive_bare.txt | 2026-03-12 | submitted | WRONG statement (off-by-1) |
| erdos389_corrected.txt | 2026-03-13 | submitted | CORRECT statement |

No prior Aristotle results for Erdos 389. The 2026-03-12 submissions used a shifted statement and any results from those will prove a different theorem.

### Erdos 850 - Submission History & Aristotle Results

| Submission | Date | Status | Theorems | Key Results |
|-----------|------|--------|----------|-------------|
| slot614 | 2026-02-12 | compiled_clean | 12 | Structural lemmas, 2-adic analysis, parity |
| slot693 | 2026-02-18 | disproven* | 51 | x<10 eliminated, |y-x|>=30, mod 6, smoothness |
| slot702 | 2026-02-19 | compiled_clean | 42 | Built on slot614+693 context |
| slot705 | 2026-02-19 | compiled_clean | 13 | Built on slot702+614 |
| slot706 | 2026-02-19 | compiled_clean | 16 | Parity, mod 3, mod 6, no x<=3, |y-x|>=30, k=2 witness |
| erdos850_v4.txt | 2026-03-12 | submitted | - | P∨¬P formulation (EXPLOITABLE) |
| erdos850_bare.txt | 2026-03-12 | submitted | - | P∨¬P formulation (EXPLOITABLE) |
| erdos850_nonexistence.txt | 2026-03-13 | submitted | - | ¬∃ formulation (commits to False) |

*slot693 marked "disproven" but actually proved 51 constraint theorems without resolving the gap.

**What Aristotle actually proved for 850** (slot693+slot706 combined):
- No solutions with x < 10 (each case individually)
- x ≡ y mod 2 (same parity)
- x ≡ y mod 3
- x ≡ y mod 6
- |y - x| >= 30
- y - x divisible by rad_lcm(x)
- k=2 witness: (2, 8)
- x(x+1)(x+2) is (y-x)-smooth
- consecutive_smooth_limit: x,x+1,x+2 all 3-smooth implies x<=2

These are solid structural lemmas but do NOT approach resolving the gap.

**CRITICAL ISSUE: Exploitable formulations still in queue**
- `erdos850_v4.txt` and `erdos850_bare.txt` use `P ∨ ¬P` which is trivially true by `exact em _`
- These will "compile clean" with zero mathematical content
- `erdos850_nonexistence.txt` commits to ¬∃ which is the right direction per Shorey-Tijdeman, but is a guess

## Feasibility Assessment

| Aspect | Erdos 389 | Erdos 850 |
|--------|-----------|-----------|
| Technical Viability | **Very Low** | **Low** |
| Why | Universal ∀n ∃k — must work for ALL n. No proof technique known. Even heuristic growth rate unclear. | Need ABC-level machinery for ¬∃. Constraints proven but gap enormous. |
| What Aristotle can do | Verify specific n values, prove k=n works (trivial) | More constraint lemmas (already substantial) |
| What Aristotle cannot do | Prove ∀n ∃k without a construction or proof strategy | Prove ¬∃ without ABC-style arguments |
| Effort estimate | XL (decades-open, no approach) | XL (conditional on ABC conjecture) |
| Risk Level | **High** — burns compute with no path to resolution | **Medium** — more constraints useful even if gap not closed |

### Why Erdos 389 is particularly bad for AI proof

The problem asks: for EVERY n, does a k exist? To prove this, you need either:
1. An explicit construction of k(n) — nobody has one
2. A non-constructive existence proof — the p-adic / Legendre approach in `erdos389_consecutive_products.txt` is a hand-wave, not a proof

The minimal k grows super-polynomially. There's no pattern connecting k(n) to k(n+1). The problem has the flavor of "probably true but we have no idea how to prove it" -- similar to Goldbach's conjecture.

Aristotle cannot invent a novel proof technique for a problem where humans have no approach.

### Why Erdos 850 is marginally better but still intractable

Aristotle has proven meaningful constraint lemmas. But the jump from "no solutions with x < 10 and |y-x| >= 30" to "no solutions exist" is enormous. The only known path to nonexistence is via ABC conjecture (Shorey-Tijdeman), which:
- Is conditional on an unproven conjecture
- Uses analytic number theory beyond Mathlib's scope
- Cannot be formalized in Lean currently

Committing to ¬∃ is justified by evidence (zero witnesses to 10^8, Shorey-Tijdeman conditional, k=2 families structurally unable to extend), but we're asking Aristotle to prove something that may require the ABC conjecture.

## Recommendations

1. **Cancel the P∨¬P submissions** (erdos850_v4.txt, erdos850_bare.txt) — they will produce trivial results via excluded middle. Waste of compute.

2. **Cancel the wrong-statement submissions** (erdos389_consecutive_v2.txt, erdos389_consecutive_bare.txt) — they target a shifted version of the problem.

3. **Deprioritize Erdos 389** — No proof technique exists. Universal existential over N with super-polynomial witness size. Not tractable for any known automated prover.

4. **Keep Erdos 850 nonexistence as a long shot** — The constraint-building approach works. Aristotle keeps proving tighter bounds. But be realistic: gap resolution requires ABC-level ideas that won't come from constraint accumulation.

5. **Look for better candidates** — Problems where:
   - A specific construction or witness is sought (existence, not universal)
   - The problem has a known approach that hasn't been carried out formally
   - Bounded/finite case analysis is sufficient
   - The gap is a "last step" not an "entire proof"

6. **For Erdos 850 specifically**: Continue feeding constraint context to build tighter bounds. The smoothness result + mod 6 + |y-x|>=30 creates a severely constrained search space. If Aristotle can push |y-x| higher or eliminate more residue classes, that's genuine progress toward either finding a witness or building an impossibility argument.

## Related Specs

| Spec | Relevance | May Need Update |
|------|-----------|-----------------|
| gap-targeting-pivot | **High** — defines the submission philosophy | No |
| erdos364 | **Medium** — similar problem domain, ABC-conditional approaches | No |
| honest-tooling | **Low** — tracking infrastructure | No |
| fix-skill-infrastructure | **Low** — skill mechanics | No |

## Open Questions

1. Can the `erdos850_v4.txt` and `erdos850_bare.txt` submissions be cancelled via the Aristotle API before compute is wasted?
2. Is there a way to use the `answer(sorry)` predicate that prevents the `em` exploit? (The formal-conjectures repo uses it — does Aristotle have special handling?)
3. Should we reformulate Erdos 850 as "extend the constraint bound" rather than "resolve the gap"? E.g., prove |y-x| >= 210 or x >= 1000?
4. Are there other Erdos problems with more tractable gaps? (e.g., problems where a specific finite computation or case analysis would resolve them)

## Quality Commands

| Type | Command | Source |
|------|---------|--------|
| Test | `bats math-forge/tests/` | gap-targeting-pivot learnings |
| Lint | Not found | - |
| TypeCheck | Not found | - |
| Build | Not found | - |

## Sources

- https://www.erdosproblems.com/389
- https://www.erdosproblems.com/850
- https://oeis.org/A375071 (minimal k for Erdos 389)
- https://oeis.org/A343101 (k=2 pairs for Erdos 850)
- google-deepmind/formal-conjectures repo (389.lean, 850.lean)
- /Users/patrickkavanagh/math/submissions/nu4_final/slot706_result.lean
- /Users/patrickkavanagh/math/submissions/nu4_final/slot693_result.lean
- /Users/patrickkavanagh/math/submissions/nu4_final/slot614_erdos850_prime_factor_triples_result.lean
- /Users/patrickkavanagh/math/docs/debate_erdos850_feb18.md
- /Users/patrickkavanagh/math/submissions/tracking.db
