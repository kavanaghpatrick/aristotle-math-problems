---
spec: erdos672-evaluation
phase: research
created: 2026-03-13
---

# Research: Erdos 672 -- Is This Worth Pursuing?

## Executive Summary

**The k=4, l=3 case (product of 4 coprime AP terms is never a cube) is ALREADY SOLVED.** Gyory, Hajdu, and Pinter (2009) proved impossibility for ALL 4 <= k <= 34 and ALL l >= 2. The full conjecture (all k >= 4) remains open. Aristotle's impressive 340-line proof infrastructure for k=4 is formalizing a known result, not resolving an open gap. The 3 remaining sorry in the 184-line proof are closeable but would yield formalization credit, not novel mathematics.

## Critical Finding: k=4 is NOT Open

### What Erdos 672 Actually Asks

From [erdosproblems.com/672](https://www.erdosproblems.com/672) and the [formal-conjectures repo](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/672.lean):

> Can the product n(n+d)...(n+(k-1)d) with gcd(n,d)=1, k >= 4, be a perfect l-th power (l >= 2)?

The formal statement uses `answer(sorry)` -- meaning the answer itself (yes/no) is part of the conjecture.

### What Is Known (NOT Open)

| Case | Proved By | Year | Status |
|------|-----------|------|--------|
| k=4, l=2 | Euler | ~1770 | SOLVED |
| k=5, l=2 | Oblath | 1951 | SOLVED |
| k=3, l=3,4,5 | Oblath | 1951 | SOLVED |
| **4 <= k <= 11, all l >= 2** | **Bennett, Bruin, Gyory, Hajdu** | **2006** | **SOLVED** |
| **4 <= k <= 34, all l >= 2** | **Gyory, Hajdu, Pinter** | **2009** | **SOLVED** |
| Sufficiently large k, l > e^(10^k) prime | Bennett, Siksek | 2020 | SOLVED |

### What Remains Open

- k >= 35 for general l
- All k >= 4 simultaneously (the full Erdos conjecture)
- The gap between k=34 and "sufficiently large k"

### Key Source

Gyory, Hajdu, Pinter. "Perfect powers from products of consecutive terms in arithmetic progression." *Compositio Mathematica* 145(4), 845-864, 2009.

## Analysis of Aristotle's Work

### What Aristotle Produced

| Slot | Lines | Sorry | Proven | Content |
|------|-------|-------|--------|---------|
| 698 | 380 | 0 | 21 | GCD structure, Pell reduction for k=4 l=2 |
| 703 | 1148 | 0 | 107 | Extended Pell infrastructure, case analysis |
| 712 | 340 | 0 | 16 | **Counterexample** (k=3,l=2 fails), plus Pythagorean triple infrastructure for k=4 l=2 case with d odd |

### Slot 712 Key Results

Aristotle did something clever and somewhat unexpected:

1. **Disproved** the overly broad claim `Erdos672Holds 3 2` -- found that 1*25*49 = 1225 = 35^2 (counterexample for k=3, l=2)
2. **Disproved** the "Step 1" reduction (product is power => each term is power) for k=3, l=2
3. **Built** substantial infrastructure for k=4, l=2 case: Pythagorean triple parametrization, coprime factoring, case elimination for d odd

### The "3 Sorry" Proof (from context)

The user mentions a 184-line proof with 3 sorry:
1. `not_square_27a4_9a2_1`: 27a^4 + 9a^2 + 1 is not a square (mod arithmetic)
2. `no_three_cubes_in_ap`: x^3 + y^3 = 2z^3 implies x=y (Euler's classical result)
3. `erdos_672_l3`: main theorem via reduction to (2)

**All 3 are closeable** but represent formalization of known math, not novel results:
- Sorry (1) is elementary mod arithmetic (checkable by `decide` or `omega` in Lean)
- Sorry (2) is Euler's 18th-century result on no 3 cubes in AP -- classical but NOT in Mathlib
- Sorry (3) follows from (2) via the reduction

## Answers to Specific Questions

### 1. Is this actually an "open problem"?

**For k=4: NO.** Gyory-Hajdu-Pinter (2009) proved impossibility for 4 <= k <= 34, all l >= 2. The k=4 l=3 case was settled 17 years ago. Erdosproblems.com marks the full conjecture (all k) as OPEN, but the specific case being targeted is solved.

### 2. How close is the 184-line proof to complete?

**Very close, but that's the wrong metric.** The 3 sorry are genuinely closeable:
- Sorry (1): Pure arithmetic, likely solvable by `decide` or modular case analysis
- Sorry (2): The hardest piece -- see detailed analysis below
- Sorry (3): Follows directly from (2)

#### Deep dive: `no_three_cubes_in_ap` (x^3 + y^3 = 2z^3 => x = y)

**Verified proof chain** (source: Keith Conrad, "An Example of Descent by Euler", UConn):
1. Euler (1738): y^2 = x^3 + 1 has only rational solutions (-1,0), (0,+/-1), (2,+/-3)
2. Corollary: x^3 + y^3 = 2 has only rational solution (1,1)
3. Corollary: No 3-term AP of nonzero cubes (since a^3+c^3=2b^3 => (a/b)^3+(c/b)^3=2 => a=b=c)

**This does NOT follow from FLT3.** FLT3 says a^3+b^3 != c^3. The equation a^3+c^3=2b^3 is different -- it requires the Mordell equation y^2=x^3+1.

**Mathlib status** (verified 2026-03-13):
- `fermatLastTheoremThree`: PROVEN in Mathlib (via Z[zeta_3] descent, ~1000 lines)
- Mordell equation y^2 = x^3 + 1: NOT in Mathlib (GitHub search "mordell" returns 0 results)
- x^3 + y^3 = 2: NOT in Mathlib (GitHub search returns 0 results)
- `Mathlib.NumberTheory.FLT.Three` uses `Solution'`/`Solution` structures in Z[zeta_3] -- these are tailored to a^3+b^3=u*c^3 (u a unit), NOT to a^3+b^3=2c^3

**Can Aristotle prove it from scratch?** Two possible routes:
1. **Via Mordell equation**: Formalize y^2=x^3+1 -> x^3+y^3=2 -> no cubes in AP. The descent proof (Conrad's exposition) is 5 pages of intricate algebra. Requires: unique factorization in Z, careful gcd tracking, iterated descent construction. Doable but substantial.
2. **Via Z[omega] directly**: Adapt the FLT3 descent. The Z[zeta_3] infrastructure IS in Mathlib (from FLT3 proof), but adapting it to handle the coefficient 2 requires new algebraic arguments.

Estimated difficulty: Sorry (1) is easy, Sorry (2) is hard (~500-1000 lines of new formalization), Sorry (3) is trivial given (2).

### 3. Is this the best use of Aristotle submissions?

**No.** This is formalization of known results, violating the project's core principle:

> "We care about NOVEL solutions, not formalization" -- User directive
> "Every submission targets an OPEN GAP" -- CLAUDE.md rule #1

The k=4 case for ANY l >= 2 was proved in 2006 (Bennett et al.) and extended to k <= 34 in 2009. Completing Aristotle's proof would be a formalization achievement (valuable for Mathlib!) but not gap-targeting.

### 4. Realistic probability Aristotle closes all 3 sorry?

| Sorry | Probability | Reasoning |
|-------|-------------|-----------|
| not_square_27a4_9a2_1 | 90% | Elementary mod arithmetic, Aristotle excels at this |
| no_three_cubes_in_ap | 15-25% | Requires either Mordell equation y^2=x^3+1 (NOT in Mathlib, 0 results) or Z[omega] adaptation. The FLT3 Z[zeta_3] machinery exists but is tailored to a^3+b^3=c^3, not a^3+b^3=2c^3. Conrad's proof is 5 pages of descent. Estimate ~500-1000 new lines needed. |
| erdos_672_l3 | ~95% given (2) | Trivial reduction |

**Overall probability all 3 close: ~15-25%.** The bottleneck is `no_three_cubes_in_ap`. Revised downward after confirming the Mordell equation is absent from Mathlib and FLT3 infrastructure cannot be directly reused.

## What WOULD Be Novel?

If the goal is to genuinely advance Erdos 672:

1. **k=35 case**: First new case beyond Gyory-Hajdu-Pinter 2009. Would be a genuine contribution.
2. **Closing the gap**: Any result that works for all k >= K for some explicit K, or better bounds on the Bennett-Siksek threshold.
3. **Different approach**: The known proofs use Frey curves + modularity. A purely number-theoretic approach avoiding heavy machinery could be novel.

However, all of these are extremely hard and likely beyond current AI capability.

## Related Specs

| Spec | Relevance | mayNeedUpdate |
|------|-----------|---------------|
| gap-targeting-pivot | HIGH: This analysis shows Erdos 672 k=4 violates gap-targeting rules | false |
| erdos364 | LOW: Different problem, similar domain (powerful numbers) | false |
| fix-skill-infrastructure | NONE | false |
| math-forge | NONE | false |
| sierpinski-5n | NONE | false |
| honest-tooling | LOW: Relevant to honest assessment of what's novel | false |

## Quality Commands

| Type | Command | Source |
|------|---------|--------|
| Test | `bats math-forge/tests/` | Known from gap-targeting-pivot spec |
| Lint | Not found | N/A |
| TypeCheck | Not found | N/A |
| Build | Not found | N/A |

## Recommendations

1. **STOP submitting Erdos 672 k=4 to Aristotle as "gap-targeting."** The k=4 case (for all l >= 2) has been solved since 2006/2009. Continued submissions violate the project's own rules.

2. **Reclassify existing work.** Slots 698, 703, 712 contain impressive formalization infrastructure. These have value for Mathlib contribution but are NOT gap resolutions.

3. **If continuing Erdos 672, target k=35.** This is the actual frontier. The formal statement would be `Erdos672With 35 l` for all l >= 2. However, this likely requires Frey curve machinery not available in Lean/Mathlib.

4. **The no_three_cubes_in_ap lemma has independent value.** Formalizing Euler's result (x^3 + y^3 = 2z^3 => x=y) would be a useful Mathlib contribution, even if it's not gap-targeting per se.

5. **Consider pivoting those Aristotle slots** to genuinely open problems where AI has better chances (problems with finite/computational character, or where k <= some bound is the actual open question).

## Open Questions

- Is the user aware that k=4 was solved in 2009? The sketches describe it as "OPEN" which is misleading.
- Does the user want formalization credit (closing sorry in Lean) even for known results? This contradicts stated philosophy but could still be valuable.
- Should the `erdos672` problem_id in the database be updated to reflect "k=4 SOLVED, full conjecture OPEN"?

## Submission History (Full)

| ID | Slot/File | Date | Status | Content |
|----|-----------|------|--------|---------|
| 1213 | slot698 | 2026-02-19 | compiled_clean (0 sorry, 21 proved) | Pell equation infrastructure for k=4 l=2 |
| 1218 | slot703 | 2026-02-19 | compiled_clean (0 sorry, 107 proved) | Extended Pell+SeqA/SeqB infrastructure (1148 lines) |
| 1243 | erdos672_l3_v2 | 2026-03-12 | submitted (pending) | l=3 open case with Pell context |
| 1248 | erdos672_l3_bare | 2026-03-12 | submitted (pending) | l=3 bare (no context, fresh eyes) |
| - | erdos672_descent_v3 | 2026-03-13 | submitted (pending) | Close 3 sorry with 184-line proof as context |
| - | erdos672_bare_v3 | 2026-03-13 | submitted (pending) | no_three_cubes_in_ap (Euler reduction) standalone |

No false_lemmas or failed_approaches recorded for Erdos 672 in tracking.db.

## Sources
- [Erdos Problem 672 - erdosproblems.com](https://www.erdosproblems.com/672)
- [Gyory, Hajdu, Pinter 2009 - Compositio Mathematica](https://www.cambridge.org/core/journals/compositio-mathematica/article/perfect-powers-from-products-of-consecutive-terms-in-arithmetic-progression/AABF84B6AEDB5FF9A80D357180CE837D)
- [Bennett, Bruin, Gyory, Hajdu 2006 - Proc. London Math. Soc.](https://www.cambridge.org/core/journals/proceedings-of-the-london-mathematical-society/article/abs/powers-from-products-of-consecutive-terms-in-arithmetic-progression/67A8B39FD63E83B1F75263C27E7BEC7E)
- [Formal Conjectures 672.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/672.lean)
- [AI contributions to Erdos problems wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)
- [Darmon-Merel 1997 - Winding quotients](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf)
- [Hajdu-Tengely - AP of squares, cubes, n-th powers](https://shrek.unideb.hu/~tengely/HajduTengely.pdf)
- [Keith Conrad, "An Example of Descent by Euler"](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/descentbyeuler.pdf) -- Proves y^2=x^3+1 solutions, x^3+y^3=2 uniqueness, and no 3 cubes in AP as corollary
- [Mathlib FLT/Three.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/FLT/Three.html) -- fermatLastTheoremThree proven, uses Z[zeta_3] descent
- [Mathlib FLT/Basic.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/FLT/Basic.html) -- FLT framework, NO x^n+y^n=kz^n generalizations
- GitHub search: "mordell" in leanprover-community/mathlib4 returns 0 results (verified 2026-03-13)
- `/Users/patrickkavanagh/math/submissions/nu4_final/slot703_result.lean` (1148-line extended proof)
- `/Users/patrickkavanagh/math/submissions/nu4_final/slot698_result.lean` (380-line initial proof)
