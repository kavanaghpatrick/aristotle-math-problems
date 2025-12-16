# Algorithm Connection Discovery Framework

## Core Thesis

Algorithm discovery is **connection discovery among known mathematics**.

We're NOT asking Aristotle to invent new math. We're asking:
> "Given your knowledge of ALL formalized mathematics, does a known result from Area X imply a better approach to Problem P?"

This is exactly what Boris did with Erdős #124 - the formalization exposed a connection to Brown's criterion that humans hadn't noticed.

**Key Principle**: Aristotle is a 200B+ parameter system with Monte Carlo Graph Search and informal reasoning. It CAN explore and decide. We provide clear problems; it finds connections.

---

## The Formula

```
1. Formalize: "Current algorithm A solves Problem P using Mathematical Structure M"
2. Ask: "∃ M' : M'.solves(P) ∧ M'.performance < M.performance"
3. Let Aristotle search its knowledge graph for connections
4. If found: Extract M' as the new algorithm
```

---

## Phase 1: Problem Selection

### What Makes a Good Target for Aristotle?

| Criterion | Why It Matters | Example |
|-----------|----------------|---------|
| **Gap exists** | Optimality unknown = room for discovery | Merge 6+7: best=11, optimal=? |
| **Rich math structure** | More areas Aristotle knows to search | Sorting = groups, Coxeter, coding |
| **Mathlib coverage** | Aristotle needs formalized theorems to connect | Matrix mult has tensor algebra |
| **Small enough n** | Tractable for exploration | n=11 sorting vs n=100 |
| **Known near-misses** | Prior work suggests connections exist | ω < 2.37 improvements |

### Target List (Revised by Tractability)

| Problem | Best | Lower | Gap | Probability | Why |
|---------|------|-------|-----|-------------|-----|
| **Matrix Mult ω** | 2.371 | 2 | 0.371 | 70% | Algebraic connections in Mathlib, active research |
| **Merge 6+7** | 11 | 11? | 0? | 60% | Likely optimal - can prove OR find improvement |
| **Selection 3rd/9** | 12 | 7 | 5 | 40% | Info theory + adversary, smaller state space |
| **Sorting n=11** | 35 | 29 | 6 | 20% | Large gap but n=11 is computationally intensive |

---

## Phase 2: Mathematical Essence Extraction

### Goal
Identify WHAT mathematical structure the current algorithm exploits, so we can ask if ANOTHER structure does better.

### Template
```lean
-- Current approach uses Structure M
structure CurrentApproach (n : ℕ) where
  structure : MathStructure
  solves : structure.solves_problem n
  performance : ℕ := current_best n

-- Example: Sorting networks
-- Current: Decompose permutations into adjacent transpositions
-- Structure M: Word length in Cayley graph of Sₙ with generators = {(i,i+1)}
-- Performance: 35 for n=11
```

### Key Questions
1. What is the implicit mathematical structure?
2. What properties of that structure determine performance?
3. What other structures have similar properties?
4. What areas of math study these structures?

---

## Phase 3: Connection Discovery Theorem

### Principle
Frame as EXISTENCE theorem, not CONSTRUCTION request.

### Bad (Construction Request)
```lean
-- DON'T: Sounds like "search for me"
def find_better_network : Option (SortingNetwork 11) := ...
```

### Good (Existence via Connection)
```lean
-- DO: Asks for proof that something EXISTS in known math
theorem better_structure_exists :
  ∃ (M : MathStructure),
    M.solves_sorting 11 ∧
    M.comparators < 35 ∧
    ∃ (T : KnownTheorem), T.implies M
```

### Even Better (Specific Connection Invitation)
```lean
-- BEST: Names specific areas to search
theorem group_theory_connection :
  -- From representation theory of Sₙ
  (∃ bound, RepTheory.minimal_generating_set_bound Sₙ = bound ∧ bound < 35) ∨
  -- From coding theory
  (∃ code, CodingTheory.sorting_code_bound 11 code < 35) ∨
  -- From Coxeter theory
  (∃ decomp, Coxeter.reduced_word_length Sₙ decomp < 35)
```

---

## Phase 4: Lean Submission Templates

### Key Principles for Templates
1. **Clean definitions** - Use Mathlib types where possible
2. **Clear goal** - State the existence/optimality question
3. **Mathematical context** - List relevant areas (Aristotle will explore)
4. **Minimal constraints** - Don't prescribe proof strategy

---

### Matrix Multiplication Exponent (70% probability)

```lean
/-
ALGORITHM CONNECTION DISCOVERY: Matrix Multiplication Exponent

CURRENT STATE:
- Best known: ω ≈ 2.371 (Alman-Williams 2024)
- Lower bound: ω ≥ 2 (trivial)
- Gap: 0.371 - UNKNOWN if ω = 2 achievable

MATHEMATICAL ESSENCE:
Matrix multiplication complexity is determined by tensor rank.
For n×n matrices: complexity ~ n^ω where ω is the exponent.
Strassen showed ω < 2.81 via tensor decomposition.

CONNECTIONS IN MATHLIB:
- Tensor algebra (Mathlib.LinearAlgebra.TensorProduct)
- Bilinear maps
- Ring theory

GOAL: Prove ω < 2.371 via algebraic connection, OR prove obstruction.
-/

import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Ring.Basic

open TensorProduct Matrix

-- Matrix multiplication as bilinear map
def matMulTensor (n : ℕ) : (Matrix (Fin n) (Fin n) ℚ) ⊗[ℚ] (Matrix (Fin n) (Fin n) ℚ) →ₗ[ℚ]
                           (Matrix (Fin n) (Fin n) ℚ) := sorry

-- Tensor rank determines complexity
def tensorRank {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (t : M ⊗[R] M) : ℕ := sorry

-- The exponent
noncomputable def matMulExponent : ℝ :=
  Real.log (tensorRank (matMulTensor 2)) / Real.log 2

-- Current best bound
axiom current_omega_bound : matMulExponent ≤ 2.371

-- THE DISCOVERY THEOREM
theorem omega_improvement :
  (matMulExponent < 2.371) ∨
  (∀ (method : TensorDecomposition), method.implies_exponent ≥ 2.371)
```

---

### Merge 6+7 (60% probability)

```lean
/-
ALGORITHM CONNECTION DISCOVERY: Merging Sorted Sequences 6+7

CURRENT STATE:
- Best known: 11 comparisons
- Information-theoretic lower bound: ⌈log₂(C(13,6))⌉ = 11
- Gap: 0 or very small - likely OPTIMAL

MATHEMATICAL ESSENCE:
Merging = interleaving two sorted sequences.
The number of valid merged orderings is C(m+n, m).
Batcher's odd-even merge achieves this via recursive structure.

CONNECTIONS:
- Binomial coefficients, entropy (Mathlib.Analysis.SpecialFunctions.Log)
- Decision tree complexity
- Information theory bounds

GOAL: Prove 11 is optimal (likely) OR find sub-optimal structure.
-/

import Mathlib.Combinatorics.Choose
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.Sort

open Nat Real

-- A merge algorithm as comparison sequence
structure MergeAlgorithm (m n : ℕ) where
  comparisons : List (Fin (m + n) × Fin (m + n))
  correct : ∀ (a : Fin m → ℕ) (b : Fin n → ℕ),
    (∀ i j, i < j → a i ≤ a j) →
    (∀ i j, i < j → b i ≤ b j) →
    let result := applyComparisons comparisons (interleave a b)
    ∀ i j, i < j → result i ≤ result j

def numComparisons (alg : MergeAlgorithm m n) : ℕ := alg.comparisons.length

-- Information-theoretic lower bound
theorem info_lower_bound (m n : ℕ) :
    ∀ alg : MergeAlgorithm m n, numComparisons alg ≥ Nat.clog 2 (choose (m + n) m) := sorry

-- For m=6, n=7: C(13,6) = 1716, log₂(1716) ≈ 10.74, so ⌈⌉ = 11
#check (choose 13 6 : ℕ)  -- 1716

-- THE DISCOVERY THEOREM
theorem merge_6_7_optimality :
  -- Either 11 is optimal...
  (∀ alg : MergeAlgorithm 6 7, numComparisons alg ≥ 11) ∨
  -- ...or there's a better algorithm
  (∃ alg : MergeAlgorithm 6 7, numComparisons alg < 11)
```

---

### Selection 3rd of 9 (40% probability)

```lean
/-
ALGORITHM CONNECTION DISCOVERY: Selection (3rd smallest of 9)

CURRENT STATE:
- Best known: 12 comparisons
- Information lower bound: ⌈log₂(C(9,3))⌉ = 7
- Gap: 5 comparisons

MATHEMATICAL ESSENCE:
Selection = find k-th order statistic via comparisons.
Each comparison partitions the space of possible orderings.
Adversary arguments give stronger bounds than information theory.

CONNECTIONS:
- Tournament graphs (partial orders from comparisons)
- Entropy and information theory
- Adversary/oracle lower bounds
- Poset theory (linear extensions)

GOAL: Find tighter bound via mathematical connection.
-/

import Mathlib.Combinatorics.Choose
import Mathlib.Order.PartialOrder
import Mathlib.Data.Finset.Sort

-- A selection algorithm as decision tree
inductive SelectionTree (n k : ℕ) : Type
  | leaf : Fin n → SelectionTree n k
  | compare : (i j : Fin n) → (lt : SelectionTree n k) → (ge : SelectionTree n k) → SelectionTree n k

def treeDepth : SelectionTree n k → ℕ
  | .leaf _ => 0
  | .compare _ _ lt ge => 1 + max (treeDepth lt) (treeDepth ge)

def selectsCorrectly (t : SelectionTree n k) : Prop :=
  ∀ (input : Fin n → ℕ) (hinj : Function.Injective input),
    let result := evalTree t input
    (Finset.univ.filter (fun j => input j < input result)).card = k - 1

-- Current best
axiom current_best_3_9 : ∃ t : SelectionTree 9 3, selectsCorrectly t ∧ treeDepth t = 12

-- THE DISCOVERY THEOREM
theorem selection_3_9_bound :
  (∃ t : SelectionTree 9 3, selectsCorrectly t ∧ treeDepth t < 12) ∨
  (∀ t : SelectionTree 9 3, selectsCorrectly t → treeDepth t ≥ 12)
```

---

### Sorting Networks n=11 (20% probability - moonshot)

```lean
/-
ALGORITHM CONNECTION DISCOVERY: Sorting Networks n=11

CURRENT STATE:
- Best known: 35 comparators
- Lower bound: 29 (information theoretic)
- Gap: 6 comparators - optimality UNKNOWN

MATHEMATICAL ESSENCE:
Sorting networks decompose permutations in Sₙ into comparator swaps.
This connects to:
- Cayley graph diameter of Sₙ with transposition generators
- Coxeter groups and reduced word length
- Bruhat order on symmetric group

CONNECTIONS:
- Mathlib.GroupTheory.Perm.Basic
- Mathlib.GroupTheory.SpecificGroups.Symmetric
- Coxeter theory (word length bounds)

GOAL: Find group-theoretic connection implying better bound.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.SpecificGroups.Symmetric
import Mathlib.Combinatorics.Partition

open Equiv.Perm

-- Sorting network as comparator sequence
structure SortingNetwork (n : ℕ) where
  comparators : List (Fin n × Fin n)
  valid : ∀ (i, j) ∈ comparators, i < j

def applySortNet (net : SortingNetwork n) (input : Fin n → ℕ) : Fin n → ℕ := sorry

def sorts (net : SortingNetwork n) : Prop :=
  ∀ input : Fin n → ℕ, ∀ i j : Fin n, i < j → (applySortNet net input) i ≤ (applySortNet net input) j

-- Current best for n=11
axiom current_best_11 : ∃ net : SortingNetwork 11, sorts net ∧ net.comparators.length = 35

-- THE DISCOVERY THEOREM
theorem sorting_network_11_bound :
  (∃ net : SortingNetwork 11, sorts net ∧ net.comparators.length < 35) ∨
  (∀ net : SortingNetwork 11, sorts net → net.comparators.length ≥ 35)
```

---

## Phase 5: Iteration Protocol

### First Submission
- Minimal spec (< 200 lines)
- State the problem and goal
- List possible math areas to search
- "You decide" on approach

### After Results
1. **If SUCCESS**: Extract the proof, understand the connection, verify algorithm
2. **If PARTIAL**:
   - Extract proven lemmas
   - These become axioms in next submission
   - Focus remaining effort on gap
3. **If TIMEOUT**:
   - Break into smaller theorems
   - Try specific connection hypotheses
4. **If COUNTEREXAMPLE**:
   - We learned something!
   - Adjust our understanding

### Iteration Template
```lean
-- From Run N: Aristotle proved these
axiom lemma_from_run_N_1 : [statement]
axiom lemma_from_run_N_2 : [statement]

-- Remaining goal (Run N+1)
theorem remaining_gap : [focused statement]
```

---

## Phase 6: Success Criteria

### Full Success
- Aristotle proves better bound exists
- Extracts constructive witness = new algorithm
- We verify it actually works

### Partial Success
- Proves structural theorems about the problem
- Finds unexpected connections even if not improvement
- Proves optimality (also valuable!)

### Learning Success
- Counterexample shows our formalization was wrong
- Timeout with partial progress gives direction
- Any non-trivial Aristotle output teaches us something

---

## Key Principles

1. **Connection, not creation**: We're searching known math, not inventing
2. **Existence, not construction**: Ask for proofs, not algorithms
3. **Minimal spec**: Don't constrain the search space
4. **Iterate on Aristotle's work**: Build on what it proves
5. **Multiple areas**: Name specific math areas to search
6. **Disjunctive goals**: "Better exists OR current is optimal"

---

## Comparison to Erdős Approach

| Aspect | Erdős Problems | Algorithm Discovery |
|--------|----------------|---------------------|
| Goal | Prove/disprove P | Find M' beating M |
| Theorem form | `∀ x, P(x)` | `∃ M', better(M')` |
| Success | Proof or counterexample | New algorithm or optimality proof |
| Iteration | Build on proven lemmas | Build on proven lemmas |
| Connection discovery | Yes | Yes |

**Same fundamental approach**: Minimal spec, connection discovery, iterative building.

---

## Next Steps

1. [ ] Submit Sorting Network n=11 (minimal spec)
2. [ ] Submit Selection 3rd/9 (minimal spec)
3. [ ] Submit Merge 6+7 (minimal spec)
4. [ ] Analyze results, extract proven lemmas
5. [ ] Iterate with enhanced versions
