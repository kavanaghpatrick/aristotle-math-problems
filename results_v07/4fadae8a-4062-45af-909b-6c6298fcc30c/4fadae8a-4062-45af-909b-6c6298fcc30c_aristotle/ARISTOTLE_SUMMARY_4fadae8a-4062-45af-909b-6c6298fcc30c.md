# Summary of changes
## Juggler Conjecture — Formalization

The Juggler Conjecture is a **genuinely open problem** in number theory, closely analogous to the Collatz conjecture. No proof of termination is known for all starting values, despite computational verification for n ≤ 10^6.

### What was done

In `RequestProject/Juggler.lean`, I formalized:

1. **The conjecture statement** (`theorem juggler`): exactly as specified, using `Nat.iterate` with the juggler step function. This remains `sorry` — as expected for an open problem.

2. **The juggler step function** (`def jugglerStep`): a clean, computable definition of the map.

3. **Two proven helper lemmas** that capture what *is* known:
   - `jugglerStep_lt_of_even`: The even step always strictly decreases the value (for n ≥ 4). This is the "easy half" — even steps make progress.
   - `jugglerStep_pos`: The step function preserves positivity (the sequence never hits 0).

4. **Detailed documentation** explaining why the conjecture is hard: odd steps can grow the value (⌊n^{3/2}⌋ ≥ n for odd n ≥ 3), and no Lyapunov function / decreasing measure is known.

### Why the main theorem remains `sorry`

The core difficulty is identical to Collatz: for odd inputs, the map increases the value, and there is no known monotone quantity that decreases at every step. Proving termination requires showing that growth at odd steps is eventually overwhelmed by shrinkage at even steps — but no mathematical technique currently achieves this for all starting values.