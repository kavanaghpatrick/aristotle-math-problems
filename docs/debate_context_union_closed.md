# Debate Context: Union-Closed Sets — Tight Cardinality Conjecture

## The Problems

The union-closed sets conjecture (Frankl's conjecture) states that for every finite union-closed family of sets (other than {∅}), some element belongs to at least half the sets. The MAIN conjecture is open, but there's an interesting OPEN sub-conjecture about tight cases.

## Lean Formalizations (from formal-conjectures/Wikipedia/UnionClosed.lean)

```lean
-- MAIN CONJECTURE (OPEN — likely too hard)
theorem union_closed [Nonempty n] (h_ne_singleton_empty : A ≠ {∅})
    (h_union_closed : IsUnionClosed A) :
    ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x} := by sorry

-- SUB-CONJECTURE: Tight cases have power-of-2 cardinality (OPEN)
theorem union_closed.variants.cardinality_even_of_union_closed_tight
    [Nonempty n] (hA : A ≠ {∅} ∧ A ≠ ∅) (hA : IsUnionClosed A)
    (UCC_tight : ∀ i, #{x ∈ A | i ∈ x} = (1 / 2 : ℝ) * #A) :
    ∃ k, #A = 2 ^ k := by sorry

-- SOLVED: Yu's weaker bound (0.38234 instead of 1/2)
-- SOLVED: Universe cardinality ≤ 12
-- SOLVED: Family cardinality ≤ 50
-- SOLVED: When a singleton is in the family (PROVEN in the file)
-- SOLVED: Sharpness of 1/2 constant (PROVEN in the file)
```

## The Tight Cardinality Sub-Conjecture

This is from Conjecture 3 in a 2023 paper (https://www.nieuwarchief.nl/serie5/pdf/naw5-2023-24-4-225.pdf):
- IF the union-closed conjecture is tight (every element appears in EXACTLY half the sets)
- THEN the family size |A| must be a power of 2

This is a conditional result — it doesn't require proving the main conjecture, just analyzing what happens when it's tight.

## Key Questions

1. Is the tight cardinality conjecture more tractable than the main conjecture?
2. What's the proof structure? Is it combinatorial or algebraic?
3. Could Aristotle handle this with finite combinatorics tools?
4. Or should we target the solved variants instead (Yu's bound, small universe, small family)?
5. Are there other open sub-conjectures in the union-closed literature worth considering?
