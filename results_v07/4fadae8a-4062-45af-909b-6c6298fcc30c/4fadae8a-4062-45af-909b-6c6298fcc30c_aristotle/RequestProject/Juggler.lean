import Mathlib

/-!
# Juggler Conjecture

The Juggler Conjecture states that for every positive integer n, the juggler sequence
defined by
  J(n) = ⌊n^{1/2}⌋  if n is even,
  J(n) = ⌊n^{3/2}⌋  if n is odd,
eventually reaches 1.

## Status: OPEN

This is an **open problem** in number theory / dynamical systems, attributed to Erdős.
It has been verified computationally for all n ≤ 10^6, but no proof of termination
is known for all starting values.

### Why is it hard?

- For even n, one step of the juggler map gives ⌊√n⌋ < n, which is progress.
- For odd n ≥ 3, one step gives ⌊n^{3/2}⌋ ≥ n, so the value can *grow*.
- The conjecture asserts that despite possible growth at odd steps, the sequence
  always eventually reaches 1.
- No monotone decreasing quantity (Lyapunov function) is known for this map.
- The analogous problem for 3n+1 (Collatz conjecture) is also famously open,
  and juggler sequences share the same "growth at some steps, shrinkage at others"
  difficulty.

### What is formalized here

We state the conjecture and leave it as `sorry`. We also provide:
- A computable definition of the juggler step function.
- A proof that the even step always decreases (for n ≥ 4).
- A proof that the step function preserves positivity.
-/

/-- The juggler step function: square root for even, cube-root-of-cube for odd. -/
def jugglerStep (m : ℕ) : ℕ :=
  if m % 2 = 0 then Nat.sqrt m else Nat.sqrt (m * m * m)

/-- The juggler step decreases for even numbers ≥ 4. -/
lemma jugglerStep_lt_of_even {n : ℕ} (hn : n ≥ 4) (heven : n % 2 = 0) :
    jugglerStep n < n := by
  unfold jugglerStep
  rw [if_pos heven, Nat.sqrt_lt]; nlinarith

/-- The juggler step is positive for positive inputs. -/
lemma jugglerStep_pos {n : ℕ} (hn : n ≥ 1) : jugglerStep n ≥ 1 := by
  unfold jugglerStep
  split_ifs <;>
    nlinarith [Nat.sqrt_pos.2 (by positivity : 0 < n),
               Nat.sqrt_pos.2 (by positivity : 0 < n * n * n)]

/-- **Juggler Conjecture** (OPEN): every juggler sequence eventually reaches 1. -/
theorem juggler (n : ℕ) (hn : n ≥ 1) :
    ∃ k : ℕ, (Nat.iterate
      (fun m => if m % 2 = 0 then Nat.sqrt m
                else Nat.sqrt (m * m * m)) k n) = 1 := by
  sorry
