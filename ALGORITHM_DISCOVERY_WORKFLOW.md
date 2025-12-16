# Algorithm Discovery Workflow for Aristotle

## Core Insight

Algorithms ARE mathematics. Discovering better algorithms means discovering better mathematical structures, not searching through possibilities.

**Historical precedent:**
- Strassen didn't search for matrix multiplication - he discovered a bilinear form decomposition
- FFT wasn't enumerated - it came from recognizing group structure in roots of unity
- Karatsuba came from algebraic insight about polynomial products

---

## The Workflow

### Phase 1: SELECT Target Algorithm

**Criteria for good targets:**
- Current best is KNOWN but optimality is UNKNOWN
- Finite, bounded problem (specific n, not asymptotic)
- Prior computer-assisted improvements exist (shows tractability)
- Rich mathematical structure underneath

**Examples:**
| Problem | Current Best | Optimality Known? | Math Structure |
|---------|-------------|-------------------|----------------|
| Sorting Network n=11 | 35 comparators | NO | Symmetric groups, Bruhat order |
| Merge 6+7 | 11 comparators | NO | Wreath products, Young tableaux |
| Selection 3rd/9 | 12 comparisons | NO | Posets, tournament graphs |

---

### Phase 2: FORMALIZE the Mathematical Essence

**Goal:** Extract WHY the current algorithm works, not just WHAT it does.

**Questions to answer:**
1. What mathematical STRUCTURE does it exploit?
2. What INVARIANT does it maintain?
3. What PROPERTY of the input/output does it rely on?
4. What's the ALGEBRAIC or COMBINATORIAL essence?

**Template:**
```lean
-- Current best algorithm for [PROBLEM]
-- It works because it exploits [MATHEMATICAL PROPERTY]

structure CurrentApproach where
  property : [Type] → Prop  -- The key property it exploits
  correctness : ∀ x, property x → achieves_goal x
  complexity : [metric] = [current_best]

-- Why this property enables the solution
theorem property_suffices :
  [mathematical theorem about why the property works]
```

**Example for Sorting Networks:**
```lean
-- Sorting network works by decomposing permutations into transpositions
-- Key insight: Any σ ∈ Sₙ can be written as product of comparator swaps

def ComparatorDecomposition (n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (swaps : List (Fin n × Fin n)),
    swaps.length ≤ current_best ∧
    apply_swaps swaps = σ ∧
    valid_comparator_sequence swaps

-- The mathematical essence: this is about word length in Cayley graphs
theorem sorting_is_cayley_word_length :
  min_comparators n = min_word_length_in_cayley_graph Sₙ generators
```

---

### Phase 3: IDENTIFY Improvement Vectors

**Question:** What mathematical approaches could achieve the same goal with better metrics?

**Strategies:**
1. **Different Structure:** Is there an alternative property (not the one current algorithm uses) that also suffices?
2. **Tighter Bounds:** Can we prove the current structure is suboptimal?
3. **Unexpected Connection:** Does this connect to a different area of math with known results?
4. **Generalization/Specialization:** Does a more general theorem imply better bounds?

**Template:**
```lean
-- Improvement Question: Does there exist a DIFFERENT approach?

theorem alternative_structure_exists :
  ∃ (P : AlternativeProperty),
    (∀ x, P x → achieves_goal x) ∧  -- Also achieves the goal
    (∃ method, method.uses P ∧ method.complexity < current_best)  -- But cheaper
```

---

### Phase 4: FORMULATE as Theorem for Aristotle

**Key principle:** Ask for a PROOF, not a CONSTRUCTION.

**Bad (search-like):**
```lean
-- DON'T: This sounds like enumeration
theorem find_better_network :
  ∃ net : SortNet 11, net.sorts ∧ net.size ≤ 34
```

**Good (mathematical):**
```lean
-- DO: This asks for mathematical insight
theorem sorting_network_group_theory_bound :
  ∀ n, ∃ d, (∀ σ : Perm (Fin n), σ expressible in d transpositions) ∧
            d < best_known_bound n ∧
            (d is optimal OR there exists algebraic obstruction)
```

**Even Better (unexpected connection):**
```lean
-- BEST: Invite discovery of connections
theorem sorting_networks_coding_theory_connection :
  ∃ correspondence : SortingNetwork n ≃ LinearCode n k d,
    (min_comparators n = some_coding_theory_invariant) ∧
    (known_coding_bounds imply improved sorting_bounds)
```

---

### Phase 5: SUBMIT with Boris Pattern

**Principles:**
- Minimal specification (< 400 lines)
- "You decide" autonomy for Aristotle
- State theorem clearly, don't prescribe method
- Include verification criteria

**Template submission:**
```lean
/-
ALGORITHM DISCOVERY: [Problem Name]

CURRENT STATE: Best known is [X], optimality unknown

MATHEMATICAL ESSENCE: [Brief description of the structure]

GOAL: Prove a theorem that implies existence of better approach,
OR prove current bound is optimal via [obstruction type]

You decide: proof strategy, mathematical connections to explore
-/

import Mathlib

-- Core definitions (minimal, just what's needed)
[definitions]

-- The mathematical structure of current approach
[formalization of current best]

-- THE DISCOVERY THEOREM
theorem improvement_exists_or_optimal :
  (∃ better_approach, [properties]) ∨
  (∀ approach, [lower_bound_obstruction])
```

---

### Phase 6: INTERPRET Results

**If Aristotle proves improvement exists:**
- Extract the constructive witness → this IS the new algorithm
- Verify it actually works
- Understand WHAT mathematical insight it found

**If Aristotle proves optimality:**
- Understand the obstruction
- This is also a significant result!

**If Aristotle finds counterexample/negation:**
- Like Erdős #593 shift graph - Aristotle proved our lemma FALSE
- This is DISCOVERY - we learned something

**If timeout:**
- May need to break into smaller lemmas
- Or formalization needs refinement

---

## Example: Full Workflow for Sorting Network n=11

### Phase 1: Target
- Current best: 35 comparators
- Optimal unknown (lower bound: 29)
- Rich math: symmetric groups, Bruhat order, Cayley graphs

### Phase 2: Mathematical Essence
```lean
-- Sorting = expressing identity permutation as product of comparators
-- Comparators are specific transpositions (i,j) with constraint i < j
-- This is word length problem in Cayley graph of S₁₁

def sorting_as_group_word :
  SortingNetwork 11 ≃ { w : List (Fin 11 × Fin 11) |
    (∀ (i,j) ∈ w, i < j) ∧
    (∀ σ : Perm (Fin 11), apply_word w σ = sorted σ) }
```

### Phase 3: Improvement Vectors
1. Is 35 the minimum word length, or is there a shorter decomposition?
2. Does Bruhat order theory give us bounds?
3. Connection to Coxeter groups - what do Kazhdan-Lusztig polynomials say?

### Phase 4: Theorem for Aristotle
```lean
theorem sorting_network_improvement :
  -- Either there's a better network...
  (∃ net : SortNet 11, net.sorts ∧ net.size ≤ 34) ∨
  -- ...or 35 is optimal with algebraic proof
  (∀ net : SortNet 11, net.sorts → net.size ≥ 35 ∧
   ∃ obstruction : BruhatObstruction, proves_lower_bound obstruction 35)
```

### Phase 5: Submit Boris-style
- ~300 lines
- Definitions + theorem + "you decide"
- Let Aristotle find the mathematical insight

---

## Success Criteria

**We succeed if Aristotle:**
1. Proves a new bound (improvement OR optimality)
2. Discovers an unexpected mathematical connection
3. Finds a counterexample that teaches us something
4. Proves structural theorems even if not the main result

**We fail only if:**
- Pure timeout with no partial progress
- The formalization was wrong/ill-typed

---

## Key Differences from Search Approach

| Search Approach | Mathematical Approach |
|-----------------|----------------------|
| "Find network with 34" | "Prove theorem about structure" |
| Enumerate possibilities | Discover connections |
| SAT solver mindset | Theorem prover mindset |
| 2^30 search space | Mathematical insight space |
| Construction-first | Proof-first (construction follows) |

---

## Next Steps

1. [ ] Formalize mathematical essence of Sorting Network n=11
2. [ ] Formalize mathematical essence of Merge 6+7
3. [ ] Formalize mathematical essence of Selection 3rd/9
4. [ ] Draft theorems in style above
5. [ ] Submit to Aristotle with Boris pattern
