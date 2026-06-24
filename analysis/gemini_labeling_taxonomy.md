# Gemini Labeling Taxonomy for Aristotle Solvability

**Consultation date**: 2026-05-30
**Agent**: #6 of 10 (problems-DB sweep)
**External model**: Gemini 2.5 Flash (gemini-2.5-pro was rate-limited; flash succeeded)
**Invocation**: `gemini -m gemini-2.5-flash -p <prompt>` (OAuth Code Assist endpoint)
**Source brief**: /Users/patrickkavanagh/math/docs/feasibility_filter_rubric.md + CLAUDE.md

The prompt asked Gemini to (1) design a labeling taxonomy with MORE THAN 4 dimensions, (2) apply it to 10 sample open problems with snipe-probability scores (1–10), and (3) name its top 3 SNIPE-NOW, top 3 DO-NOT-BOTHER, and the single most important dimension it adds beyond the current 4-category Feasibility Filter rubric.

Gemini's response is reproduced verbatim below.

---

## Part 1: Design a Labeling Taxonomy

### Dimension 1: Quantifier Depth (QD)
- **Name:** Quantifier Depth
- **Possible values:** `atomic`, `existential (∃)`, `universal (∀)`, `∃∀`, `∀∃`, `nested (>=3)`
- **Decision rule:** Count the maximum nesting depth of quantifiers (∃, ∀) in the conjecture's formal statement.
- **Why it predicts Aristotle solvability:** Deeper nesting of quantifiers, especially `∀∃` and `∃∀`, often indicates higher logical complexity, making automated proof search harder. `atomic`, `existential`, and simple `universal` claims are generally more tractable for automated provers.

### Dimension 2: Carrier Set Complexity (CSC)
- **Name:** Carrier Set Complexity
- **Possible values:** `integer/natural`, `rational/real`, `algebraic/finite_field`, `group/ring/field`, `graph/combinatorial`, `analytic/topological`
- **Decision rule:** Identify the primary mathematical structure/set over which the conjecture is defined.
- **Why it predicts Aristotle solvability:** Lean's `mathlib` has strong coverage for `integer/natural` and `algebraic` structures. `graph/combinatorial` can be difficult if it lacks algebraic handles. `analytic/topological` and `rational/real` often involve concepts (e.g., limits, measure theory) that are less mature in formalization or harder for automated search.

### Dimension 3: Witness Constructibility (WC)
- **Name:** Witness Constructibility
- **Possible values:** `explicit_algorithm`, `bounded_search`, `indirect_existence`, `structural_existence`, `non_constructive`
- **Decision rule:** Determine if a witness (for an existential claim or a counterexample for a universal claim) can be explicitly constructed or found via a bounded search.
- **Why it predicts Aristotle solvability:** Aristotle excels at finding concrete witnesses or counterexamples, especially with `explicit_algorithm` or `bounded_search` (finite-verification, constructive-search patterns). `structural_existence` or `non_constructive` claims (e.g., using excluded middle or infinitude arguments) are typically "structural-open" and hard for Aristotle.

### Dimension 4: Falsifiability/Verifiability (FV)
- **Name:** Falsifiability/Verifiability
- **Possible values:** `falsifiable_bounded`, `verifiable_bounded`, `falsifiable_unbounded`, `verifiable_unbounded`, `neither`
- **Decision rule:** Assess if the conjecture can be disproven by a finite counterexample (`falsifiable`) or proven by verifying all cases in a finite bound (`verifiable`). Distinguish between bounded and unbounded domains.
- **Why it predicts Aristotle solvability:** Aristotle's success in "valuable disproof" highlights `falsifiable_bounded` as a strength. `verifiable_bounded` aligns with `finite-verification`. `unbounded` versions are significantly harder for direct proof unless they can be reduced to a bounded problem.

### Dimension 5: Dependency on Auxiliary Results (DAR)
- **Name:** Dependency on Auxiliary Results
- **Possible values:** `self_contained`, `standard_lemmas`, `deep_theorems`, `famous_open`, `custom_induction`
- **Decision rule:** Estimate the complexity and specificity of mathematical background knowledge required beyond basic definitions.
- **Why it predicts Aristotle solvability:** `self_contained` and `standard_lemmas` are ideal. `deep_theorems` implies a need for rich `mathlib` coverage or significant foundational work. `famous_open` problems are highly unlikely to be solved, as they reduce to known hard problems. `custom_induction` indicates structural complexity.

### Dimension 6: Computational Budget Shape (CBS)
- **Name:** Computational Budget Shape
- **Possible values:** `fast_finite`, `chunked_finite`, `polynomial_search`, `exponential_search`, `unbounded_symbolic`
- **Decision rule:** Characterize the computational effort needed for direct verification or search if the problem were amenable to computation.
- **Why it predicts Aristotle solvability:** `fast_finite` and `chunked_finite` directly map to `finite-verification` successes (Brocard). `polynomial_search` for constructive witnesses is also effective. `exponential_search` or `unbounded_symbolic` searches quickly exceed Aristotle's capabilities.

### Dimension 7: `mathlib` Coverage Alignment (MCA)
- **Name:** `mathlib` Coverage Alignment
- **Possible values:** `high_direct_match`, `moderate_related_theorems`, `low_foundational_gap`, `novel_structure`
- **Decision rule:** How directly and extensively the conjecture's concepts and required theorems are covered by existing `mathlib` formalizations.
- **Why it predicts Aristotle solvability:** High alignment means Aristotle can leverage existing formalizations and tactics. `low_foundational_gap` or `novel_structure` implies Aristotle would need to formalize new mathematical ideas, which it is not designed to do. `mechanical_extension` benefits from `high_direct_match`.

## Part 2: Apply the Taxonomy to 10 Sample Open Problems

Selected problems:
1.  **Erdős 1** (covering systems with distinct moduli)
2.  **Erdős 51** (small set with no 3-AP cover)
3.  **Goldbach weak** (every odd n ≥ 7 is sum of 3 primes)
4.  **Twin primes finite-N** (∀ n ≤ N, ∃ p prime such that p+2 prime, for some specific large N)
5.  **BSD** (Birch–Swinnerton-Dyer Conjecture)
6.  **Riemann Hypothesis**
7.  **Brocard's problem** (n!+1 = m² for n=4,5,7 only?)
8.  **Sierpiński 78557** (78557 is the smallest Sierpiński number)
9.  **Tuza ν=4** (matching-number-4 case of Tuza's conjecture: τ(G) ≤ 2ν(G) for triangle-covers)
10. **FT family infinite** (Fermat-Toricelli–style: no solution to a^p + b^p = c^p · q^r in infinitely many q)

---

| Problem Name | One-line Statement | QD | CSC | WC | FV | DAR | CBS | MCA | Snipe Probability | Justification |
|---|---|---|---|---|---|---|---|---|---|---|
| Erdős 1 | Does there exist a covering system with distinct moduli, all of which are odd? | ∃ | integer/natural | indirect_existence | falsifiable_unbounded | deep_theorems | unbounded_symbolic | moderate_related_theorems | 2 | Deep number theory; existence claim, but no constructive recipe, related to harder problems. |
| Erdős 51 | Is there a set A ⊆ {1, ..., N} of size N/3 s.t. A contains no 3-term AP, for sufficiently large N? | ∀∃ | integer/natural | structural_existence | falsifiable_unbounded | deep_theorems | unbounded_symbolic | low_foundational_gap | 1 | Structural combinatorial problem, existence for large N, no clear construction method. |
| Goldbach weak | Every odd integer n ≥ 7 is the sum of three prime numbers. | ∀∃ | integer/natural | indirect_existence | verifiable_unbounded | deep_theorems | unbounded_symbolic | high_direct_match | 3 | Known hard problem; infinite domain, but number theory is well-covered in `mathlib`. |
| Twin primes finite-N | For a given N, are there twin primes p, p+2 up to N? | ∀∃ | integer/natural | bounded_search | verifiable_bounded | standard_lemmas | fast_finite | high_direct_match | 9 | Bounded verification, direct search, primes are well-defined in `mathlib`. |
| BSD Conjecture | Relates the rank of an elliptic curve to the order of vanishing of its L-function. | structural_existence | algebraic/finite_field | non_constructive | verifiable_unbounded | famous_open | unbounded_symbolic | low_foundational_gap | 1 | Extremely deep, foundational, abstract, and involves real/complex analysis. |
| Riemann Hypothesis | All non-trivial zeros of the Riemann zeta function have real part 1/2. | ∀ | rational/real | non_constructive | verifiable_unbounded | famous_open | unbounded_symbolic | low_foundational_gap | 1 | Foundational, involves complex analysis, very high dependency on deep, unproven results. |
| Brocard's problem | n!+1 = m² has solutions only for n=4,5,7. | universal (∀) | integer/natural | bounded_search | falsifiable_bounded | standard_lemmas | chunked_finite | high_direct_match | 10 | Bounded search, known finite solutions, exactly the type Aristotle has succeeded with. |
| Sierpiński 78557 | 78557 is the smallest Sierpiński number. | ∃ | integer/natural | explicit_algorithm | verifiable_bounded | standard_lemmas | polynomial_search | high_direct_match | 8 | Specific constant verification, finite search for counterexample/proof. |
| Tuza ν=4 | For a graph G, τ(G) ≤ 2ν(G) for triangle covers when ν=4. | ∀ | graph/combinatorial | structural_existence | falsifiable_unbounded | deep_theorems | exponential_search | novel_structure | 2 | Structural combinatorial, not easily reducible to finite cases, "dead end" for Aristotle. |
| FT family infinite | No solution to a^p + b^p = c^p · q^r in infinitely many q. | ∀∃ | integer/natural | indirect_existence | falsifiable_unbounded | deep_theorems | unbounded_symbolic | moderate_related_theorems | 3 | "Infinite many" claims are difficult, relates to Diophantine equations. |

## Part 3: Verdict

-   **Top 3 "SNIPE NOW"**
    1.  **Brocard's problem:** (QD: universal (∀), FV: falsifiable_bounded, CBS: chunked_finite, MCA: high_direct_match)
    2.  **Twin primes finite-N:** (FV: verifiable_bounded, CBS: fast_finite, MCA: high_direct_match)
    3.  **Sierpiński 78557:** (WC: explicit_algorithm, FV: verifiable_bounded, CBS: polynomial_search, MCA: high_direct_match)

-   **Top 3 "DO NOT BOTHER"**
    1.  **BSD Conjecture:** (CSC: algebraic/finite_field, WC: non_constructive, DAR: famous_open, MCA: low_foundational_gap)
    2.  **Riemann Hypothesis:** (CSC: rational/real, WC: non_constructive, DAR: famous_open, MCA: low_foundational_gap)
    3.  **Erdős 51:** (CSC: graph/combinatorial, WC: structural_existence, DAR: deep_theorems, MCA: low_foundational_gap)

-   **The single most important dimension you added beyond the current 4-category rubric**
    -   **Witness Constructibility (WC):** This dimension directly addresses Aristotle's strength in concrete witness finding and its weakness with non-constructive or structural existence claims. It distinguishes solvable "constructive-search" from intractable "structural-open" problems more granularly than the original rubric.
