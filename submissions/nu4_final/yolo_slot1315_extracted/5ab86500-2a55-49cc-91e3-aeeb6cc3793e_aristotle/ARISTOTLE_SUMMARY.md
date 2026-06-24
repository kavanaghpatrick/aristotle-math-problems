# Summary of changes for run 5ab86500-2a55-49cc-91e3-aeeb6cc3793e
## Erdős Problem 938 — abc-conditional sandwich theorem

I formalized the abc-conditional structural sandwich theorem on consecutive powerful 3-APs. The project is organized into four files:

### File structure

1. **`RequestProject/Definitions.lean`** — Core definitions (fully proved, no sorry):
   - `Nat.Powerful`: A natural number n is powerful if 0 < n and every prime dividing n divides it with exponent ≥ 2
   - `ABC.radical`: The product of distinct prime factors of n
   - `powerful_sq`: Perfect squares of positive numbers are powerful
   - `powerful_infinite`: The set of powerful numbers is infinite
   - `powerful_one`: 1 is powerful

2. **`RequestProject/ABCHelpers.lean`** — Radical and abc infrastructure (fully proved, no sorry):
   - `coprime_sum_pairwise`: For coprime a, b, the set {a, b, a+b} is pairwise coprime
   - `abc_finite_to_bound`: Extracts a bound from finiteness of the abc-exception set
   - `radical_sq_le_of_powerful`: For powerful n, rad(n)² ≤ n
   - `radical_mul_le`: rad(a·b) ≤ rad(a)·rad(b) (submultiplicativity)
   - `radical_sq`: rad(a²) = rad(a)
   - `radical_pos`: rad(n) > 0 for n > 0
   - `radical_le`: rad(n) ≤ n for n > 0

3. **`RequestProject/LowerBound.lean`** — abc-conditional lower bound:
   - `ap_sq_identity`: The AP identity n₁² = n₀·n₂ + d² (fully proved)
   - `powerful_gap_pos`: Consecutive powerful numbers have gap ≥ 1 (fully proved)
   - `lower_bound_common_diff`: d > N^{1/2-ε} under abc (**sorry** — requires Chan 2022's refined analysis)

4. **`RequestProject/Main.lean`** — Upper bound and main theorem:
   - `no_powerful_between_consecutive`: No powerful number strictly between consecutive enumerated powerfulss (fully proved)
   - `interval_contains_square`: Long intervals contain perfect squares (fully proved)
   - `upper_bound_common_diff`: d < 2√N + 2 — the consecutive-square interloper argument (**fully proved**)
   - `erdos_938_abc_sandwich`: The main sandwich theorem combining both bounds (proved modulo lower bound)

### What is proved vs. what remains

- **Fully proved**: The upper bound `d < 2√N + 2`, all radical properties, all helper lemmas, and the theorem's structural combination.
- **Remaining sorry**: The abc-conditional lower bound `d > N^{1/2-ε}` (`lower_bound_common_diff`). This is a deep number-theoretic result: the proof requires constructing pairwise coprime abc-triples from the AP identity and bounding their radicals using the powerful structure. The full argument achieving the 1/2−ε exponent (rather than the simpler 1/6) requires the refined gcd analysis from Chan 2022 (arXiv:2210.00281, Theorem 2), which is beyond what could be formalized from scratch in this session.

### Mathematical note

The informal proof sketch provided had an algebraic error in Step 2: the stated simplification "n_{k+1}^{1-2ε} ≤ K_ε · d^{1+ε}" does not follow from the radical bounds as written. The standard abc application to the triple (d², n₀·n₂, n₁²) yields an exponent of approximately 1/6, not 1/2. Achieving the 1/2−ε exponent requires a more sophisticated analysis of the gcd structure in the coprime reduction, as developed in Chan 2022.

The theorem statement matches the exact target signature provided in the problem.