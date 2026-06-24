# Summary of changes for run 48cfce4c-9293-4875-8011-437e560a487f
## Erdős Problem 938 — Formalization Report

**Status: OPEN problem — the main theorem remains `sorry`'d.**

### What was accomplished

I created `RequestProject/Erdos938.lean` containing:

1. **Definitions:**
   - `Nat.Powerful`: a natural number n is powerful if n ≠ 0 and every prime dividing n also has its square dividing n
   - `Set.IsAPOfLength`: a set S ⊆ ℕ is an AP of length k if S = {a + i·d | i < k} for some a, d with d > 0

2. **Proved helper lemmas:**
   - `powerful_of_sq`: every perfect square of a positive number is powerful
   - `Nat.Powerful_infinite`: the set of powerful numbers is infinite (needed for `Nat.nth` to be well-defined)
   - `sq_in_interval`: gap constraint for perfect squares in intervals

3. **Main theorem statement** (`erdos_938`): formalized exactly as specified, left with `sorry`

### Why the main theorem remains open

This is a **genuinely open problem** in number theory. It is closely related to the Erdős–Mollin–Walsh conjecture (no three consecutive integers are all powerful), which itself remains unproved. The informal proof outline provided (Maier matrix method + Selberg sieve) is speculative and has significant gaps:

- The Maier matrix method, Selberg sieve with dimension-1/2 bounds, and level-of-distribution results for the powerful indicator are all absent from Mathlib
- The logical connection between "Maier irregularity forces many small gaps" and "AP-consecutiveness is contradicted" is not rigorous as stated — the density arguments in Steps 5–6 conflate different notions

### Computational evidence

Computational search up to 10⁶ found only **3** consecutive powerful 3-APs:
- (1728, 1764, 1800) with d = 36
- (6912, 7056, 7200) with d = 144 (this is 4× the first triple)
- (729000, 729316, 729632) with d = 316

This strongly suggests the conjecture is true, but no proof is known.