# Grok Labeling Taxonomy (Agent #7 External Consultation)

**Model:** grok-4.20-0309-reasoning
**Date:** 2026-05-30
**Tokens:** 1336 prompt -> 1857 completion

---

**Aristotle Solvability Taxonomy (6 orthogonal axes)**

**Axis 1: Computational Tractability**  
**Values:** `NativeDecide` | `Chunkable` | `HeavySearch` | `AnalyticExplosion` | `NonComputational`  
**Decision rule (30s):** Count outer quantifiers and predicate complexity. `NativeDecide` = ∀n≤N, decidable P(n) with N small enough for one `native_decide`. `Chunkable` = obvious partition into 10–100 subgoals. `HeavySearch` = greedy/cover/enumeration still polynomial. `AnalyticExplosion` = L-functions, integrals, or density arguments. `NonComputational` = requires infinite descent or new analytic number theory.  
**Orthogonality:** Purely measures machine resources; says nothing about whether a mathematical idea exists or whether a skeleton is available.

**Axis 2: Witness Character**  
**Values:** `Explicit` | `GreedyCRT` | `FiniteEnum` | `UniversalNegative` | `PureExistence`  
**Decision rule (30s):** Look at the claim. “There exists k with property P” + P decidable → `Explicit`. Covering-system style → `GreedyCRT`. Group/enumeration → `FiniteEnum`. “No solutions exist” → `UniversalNegative`. “There are infinitely many” without witness recipe → `PureExistence`.  
**Orthogonality:** Captures constructive flavor; orthogonal to raw compute (you can have easy `Explicit` that is still `AnalyticExplosion`).

**Axis 3: Reduction Skeleton**  
**Values:** `DescentReady` | `CoveringReady` | `LemmaCascade` | `None`  
**Decision rule (30s):** Does the statement immediately suggest Fermat-style infinite descent, modular covering system, or chaining of already-formalized lemmas (σ bounds, order computations)? If yes, label accordingly; else `None`.  
**Orthogonality:** Measures reuse of known proof shapes. Distinct from innovation threshold (a perfect skeleton can still require a new idea at one step).

**Axis 4: Innovation Demand**  
**Values:** `Routine` | `ParameterSwap` | `EncodingTrick` | `NewIdeaRequired`  
**Decision rule (30s):** Has Aristotle already solved essentially this statement with a different parameter (Brocard range, FT family member)? If yes → `ParameterSwap`. Needs a new encoding or greedy heuristic → `EncodingTrick`. Otherwise, if the obstruction is combinatorial or analytic and no prior Aristotle win exists → `NewIdeaRequired`.  
**Orthogonality:** Captures creativity gap; independent of computational tractability (some `NativeDecide` problems still need `NewIdeaRequired`).

**Axis 5: Breakpoint Risk**  
**Values:** `Low` | `Medium` | `High` | `KnownCliff`  
**Decision rule (30s):** For parameterized families, check literature for “phase transition”, “first counterexample at …”, or “obstruction at prime p=…”. Tuza-style carcass with 300+ failed attempts → `KnownCliff`.  
**Orthogonality:** Specifically tracks the “bound-bump past obstruction” failure mode; orthogonal to whether the skeleton exists.

**Axis 6: Formalization Leverage**  
**Values:** `MathlibHeavy` | `Partial` | `TheoryHeavy`  
**Decision rule (30s):** Prime numbers, factorials, finite groups, elementary number theory → `MathlibHeavy`. Elliptic curves, L-functions, analytic number theory → `TheoryHeavy`. Mixed → `Partial`.  
**Orthogonality:** Measures how much of the language already exists in Lean vs. how many new definitions/axioms will be invented. Distinct from computational tractability.

---

### Application to 10 Sample Problems

**1. Erdős Problem #1 (Davenport constant bounds)**  
Axes: `HeavySearch` | `FiniteEnum` | `LemmaCascade` | `NewIdeaRequired` | `Medium` | `MathlibHeavy`  
**Snipe score: 3/10**  
Finite groups are in mathlib and enumeration is possible, but the exact bound is believed to require a new structural lemma; Aristotle has never produced a new extremal group-theory result.

**2. Erdős Problem #51 (sumsets vs product sets)**  
Axes: `AnalyticExplosion` | `PureExistence` | `None` | `NewIdeaRequired` | `High` | `TheoryHeavy`  
**Snipe score: 1/10**  
Pure analytic-combinatorial density problem. No finite witness, no descent, no native_decide pathway. Aristotle has zero traction in this regime.

**3. Goldbach weak (already proved + formalized)**  
Axes: `NativeDecide` | `Explicit` | `LemmaCascade` | `Routine` | `Low` | `MathlibHeavy`  
**Snipe score: 9/10**  
Completely routine verification given the existing formalization (Helfgott). Aristotle can simply re-prove the bounded version or check the literature formalization. Only risk is “known-formalization” exclusion.

**4. Twin primes finite-N (count twins ≤ 10⁶)**  
Axes: `NativeDecide` | `Explicit` | `None` | `Routine` | `Low` | `MathlibHeavy`  
**Snipe score: 8/10**  
Trivial bounded verification. `prime` and `Nat` are perfectly handled by mathlib. Aristotle should dispatch this in one `native_decide` or simple loop. Only reason not 10 is that it is almost too trivial to count as an “advance.”

**5. BSD Conjecture**  
Axes: `AnalyticExplosion` | `PureExistence` | `None` | `NewIdeaRequired` | `KnownCliff` | `TheoryHeavy`  
**Snipe score: 1/10**  
Requires massive analytic machinery that does not exist in Lean at the required strength. Known to be far beyond current formalization frontier, let alone autonomous search.

**6. Riemann Hypothesis**  
Axes: `AnalyticExplosion` | `UniversalNegative` | `None` | `NewIdeaRequired` | `KnownCliff` | `TheoryHeavy`  
**Snipe score: 1/10**  
The canonical `NewIdeaRequired` + `TheoryHeavy` + `AnalyticExplosion` triple. Zero overlap with demonstrated capabilities.

**7. Brocard’s problem (finiteness)**  
Axes: `Chunkable` | `UniversalNegative` | `LemmaCascade` | `EncodingTrick` | `Medium` | `MathlibHeavy`  
**Snipe score: 6/10**  
Aristotle has already produced bounded verifications and range bumps. Chunking + auto-discovered encodings work. Real obstruction is the possible existence of a 4th solution; Aristotle can push the bound but is unlikely to prove finiteness without a new analytic idea.

**8. Sierpiński 78557 (smallest Sierpiński number)**  
Axes: `HeavySearch` | `GreedyCRT` | `CoveringReady` | `ParameterSwap` | `Low` | `MathlibHeavy`  
**Snipe score: 7/10**  
Exactly the covering-system / greedy-CRT regime where Aristotle already delivered a valuable disproof (E203). The question is whether 78557 admits a covering and all smaller candidates fail. High probability of producing either a covering witness or a disproof via exhaustive search on smaller k.

**9. FT family infinite (all q ≡ 71 mod 72)**  
Axes: `HeavySearch` | `UniversalNegative` | `DescentReady` | `ParameterSwap` | `High` | `Partial`  
**Snipe score: 4/10**  
Aristotle has done fixed-modulus Fermat descent. Extending to the full infinite family hits the classic “bound bump past breakpoint” failure (the skeleton breaks when A(q) becomes prime). High breakpoint risk.

**10. Tuza ν=4 carcass**  
Axes: `HeavySearch` | `PureExistence` | `None` | `NewIdeaRequired` | `KnownCliff` | `Partial`  
**Snipe score: 1/10**  
317 prior polished-irrelevance submissions, zero advances. The combinatorial obstruction is dense and structural. Taxonomy correctly flags `KnownCliff` + `NewIdeaRequired` → immediate NO-GO. Do not burn more slots.

**Summary recommendation**  
Use the six-axis vector as a pre-filter. Any problem scoring `NewIdeaRequired` + (`AnalyticExplosion` or `KnownCliff`) should be excluded from the queue. This would have killed Tuza, RH, BSD, and Erdős #51 before any compute was spent. The taxonomy is deliberately pessimistic; current hit rate is <1 %.