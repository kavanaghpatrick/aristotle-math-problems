# Summary of changes
## Brocard's Problem — Open Problem

The file `RequestProject/Brocard.lean` contains the formal statement of Brocard's problem:

```lean
theorem brocard (n : ℕ) (hn : n ≥ 8) :
    ¬ ∃ m : ℕ, n.factorial + 1 = m ^ 2 := by sorry
```

**This theorem remains `sorry`'d because it is a genuine open problem in mathematics.** No proof is known, and the theorem proving subagent was unable to find one (as expected).

### Why no proof exists

Brocard's problem (1876) / Ramanujan's question (1913) asks whether `n! + 1 = m²` has solutions beyond `n = 4, 5, 7`. Despite extensive effort:

- **Modular arithmetic** cannot work alone: for any prime `p ≤ n`, we have `n! + 1 ≡ 1 (mod p)`, and `1` is always a quadratic residue modulo any integer.
- **Growth-rate arguments** show solutions become increasingly sparse but cannot rule them out.
- The **ABC conjecture** would imply only finitely many solutions, but this is itself unproven and wouldn't give an effective bound.
- **Computational verification** confirms no solutions for `n ≤ 10⁹` (Berndt–Galway, 2000).

The file includes detailed documentation of the problem's history, known results, and why current techniques are insufficient. The statement is correctly formalized and the file compiles cleanly against Mathlib.