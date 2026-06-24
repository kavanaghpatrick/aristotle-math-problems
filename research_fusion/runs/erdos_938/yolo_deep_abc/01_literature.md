# Literature for Erdős 938 — abc-conditional angle (deep iteration)

## CONFIRMED-EXISTS citations (May 30 2026, via grok-search live web)

1. **Chan 2022** — "Consecutive powerful numbers in arithmetic progressions"
   - arXiv: https://arxiv.org/abs/2210.00281
   - **Thm 2 (abc-conditional):** For any 3-AP (m₁, m₂, m₃) of powerful integers with common difference d and m₁ = N, under abc: d ≫_ε N^{1/2-ε}.
   - The bound is uniform over all powerful 3-APs (NOT just consecutive).
   - Constants: non-effective (existence only via abc).

2. **van Doorn 2026** — arXiv:2605.06697
   - CONFIRMED EXISTS. Title relates to consecutive powerful integers / 3-APs.
   - Provides construction of 18 explicit consecutive powerful 3-APs ≤ 10^14.
   - Pell-family d ≈ 2√N + 1 saturates the upper bound.

3. **Granville-Tucker 2002** — "It's as easy as abc" (Notices AMS)
   - URL: https://www.ams.org/notices/200210/fea-granville.pdf
   - Survey of abc consequences. No theorem specifically on powerful + AP + finiteness.

4. **Heath-Brown 1988** — "Ternary Quadratic Forms and Sums of Three Square-Full Numbers"
   - (Séminaire de Théorie des Nombres, Paris 1986-87)
   - Every sufficiently large integer is sum of three powerful/squarefull numbers.

5. **Erdős-Mollin-Walsh conjecture** — no 3 consecutive integers are all powerful.
   - erdosproblems.com/364 (related to 938 but distinct).
   - Status as of 2026: OPEN. No published abc-conditional proof of EMW.

6. **erdosproblems.com/938** — current page CONFIRMS OPEN.

7. **Cushing arXiv:1611.01192** — connects abc to powerful triples in APs.
   - Earlier paper, less precise than Chan 2022.

## Mathlib status (CONFIRMED via search)

- **Mainline Mathlib**: NO `Nat.Powerful`, NO `ABCConjecture`, NO number-theoretic `radical` function (only ring-theoretic `Radical`).
- **formal-conjectures**:
  - `FormalConjectures/Wikipedia/ABC.lean` provides:
    - `def radical (n : ℕ) : ℕ := n.primeFactors.prod id`
    - `theorem ABC.abc (ε : ℝ) (hε : 0 < ε) : { ... rad(abc)^(1+ε) < c }.Finite`
    - `theorem ABC.abc.variants.lt_constant_mul`: gives constant K with c < K · rad(abc)^(1+ε)
    - `theorem ABC.abc.variants.quality`: quality > 1+ε is finite
  - `FormalConjectures/ErdosProblems/938.lean` defines:
    - `theorem erdos_938 : answer(sorry) ↔ { ... AP of length 3 in consecutive powerful}.Finite`

## Key technical inputs needed for the abc-conditional sandwich

- `Nat.Powerful` — locally defined in `RequestProject/Erdos938.lean` (from slot 1300):
  `def Nat.Powerful (n : ℕ) : Prop := n ≠ 0 ∧ ∀ p, p.Prime → p ∣ n → p^2 ∣ n`
- `Nat.nth Nat.Powerful k` — Mathlib's `Nat.nth` selects k-th element of a set
- `Set.IsAPOfLength` — locally defined in `RequestProject/Erdos938.lean`
- `ABC.radical` — from `FormalConjectures/Wikipedia/ABC.lean`
- `ABC.abc.variants.lt_constant_mul` — abc conjecture as hypothesis

## What this dossier delivers

A **fully rigorous abc-conditional STRUCTURAL theorem** that:
1. Is honestly NOT a finiteness theorem (finiteness is beyond abc, per Codex+Grok verdict)
2. Sandwiches d in (c_ε · N^{1/2-ε}, 2√N + 2]
3. Combines Chan 2022 Thm 2 (lower) with the consecutive-square interloper (upper)
4. Has 8 Lean-formalizable lemmas keyed to existing Wikipedia/ABC.lean + RequestProject/Erdos938.lean
5. Explicitly flags the open finiteness gap (sieve/density input needed)
