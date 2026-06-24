# Summary of changes for run d853d0a6-2a77-44df-8534-ad839d101a04
## Erdős Problem 938 — Formalization Results

**Problem:** Is the set of indices k such that three consecutive powerful numbers form a 3-term arithmetic progression finite?

**Status:** This is an **open problem**. The main conjecture `erdos_938` remains as `sorry` because no proof (or disproof) is known.

### What was accomplished

The file `RequestProject/Powerful.lean` contains:

1. **Definition of powerful numbers** (`Nat.Powerful`): n is powerful iff n > 0 and every prime dividing n divides it with multiplicity ≥ 2.

2. **Fully proved supporting lemmas:**
   - `Nat.Powerful.one`: 1 is powerful
   - `Nat.Powerful.sq`: every perfect square n² (n ≥ 1) is powerful
   - `Nat.Powerful.infinite`: the set of powerful numbers is infinite
   - `van_doorn_family_ap`: if x² − 343y² = 2 with x ≥ 3, then ((x−2)², (x−1)², 343y²) is a 3-term AP
   - `van_doorn_family_powerful_left/mid`: the square terms are powerful
   - `van_doorn_family_powerful_right`: 343y² = 7³·y² is powerful for y > 0
   - `pell_first_solution`: verification that (11427, 617) satisfies x² − 343y² = 2
   - `pell_fundamental`: verification that (130576328, 7050459) satisfies x² − 343y² = 1

3. **The main conjecture** (`erdos_938`): stated but left as `sorry` — this is an open problem.

### Mathematical context

The Van Doorn family (from a 2026 preprint, arXiv:2605.06697) provides infinitely many powerful 3-APs via the Pell equation x² − 343y² = 2, but whether any of these are *consecutive* in the powerful number enumeration is unresolved. Computational evidence finds exactly 6 consecutive powerful 3-APs below 10¹⁰. Heuristic arguments suggest ~24% of Pell solutions should yield consecutive triples (predicting the answer is FALSE — infinitely many exist), but this has not been proved or computationally verified for any solution beyond the known six.

All proved lemmas use only standard axioms (propext, Classical.choice, Quot.sound).