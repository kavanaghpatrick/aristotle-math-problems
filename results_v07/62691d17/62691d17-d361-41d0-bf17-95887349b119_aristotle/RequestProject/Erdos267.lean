import Mathlib

/-!
# Erdős Problem 267 — Lacunary Reciprocal Sum Irrationality

**Conjecture (Erdős).** If `(n k)` is a strictly increasing sequence of positive integers with
`n(k+1) / n(k) → c` where `1 < c < 2`, then `∑ 1/n(k)` is irrational.

## Status

**OPEN.** This problem remains unsolved as of 2025.

### What is known

* **c ≥ 2 (solved):** When the ratio `n(k+1)/n(k) ≥ 2` eventually, Badea's criterion (1993) and
  related results (Erdős–Straus, Hančl) establish irrationality. The key is that sufficiently
  fast-growing denominators force the partial sums to be "too well approximable" by rationals
  with denominators dividing `∏ n(i)`, contradicting rationality.

* **c = 1 (false):** The harmonic-like subsequences can yield rational sums, so some growth
  condition is necessary.

* **1 < c < 2 (open):** The intermediate growth rate is too slow for known irrationality
  criteria (Badea, Hančl, Oppenheim) to apply directly. The denominators grow geometrically
  but not fast enough to guarantee the Oppenheim-type gap condition
  `n(k+1) > n(k)(n(k) − 1)` that would immediately give irrationality.

### Why this is hard

The difficulty lies in the "gap" between growth rates:
- For c ≥ 2, the sequence grows fast enough that each new term "refines" the approximation
  sufficiently to prevent rational convergence.
- For 1 < c < 2, the sequence grows faster than any polynomial but slower than sequences
  satisfying Badea's quadratic gap condition. New techniques beyond classical irrationality
  criteria appear to be needed.

## References

* P. Erdős, "Some problems and results on the irrationality of the sum of infinite series",
  J. Math. Sci. 10 (1975).
* C. Badea, "The irrationality of certain infinite series", Glasgow Math. J. 35 (1993), 361–366.
-/

/-- **Erdős Problem 267** (OPEN): If `n` is a strictly increasing sequence of positive integers
whose consecutive ratios converge to some `c ∈ (1, 2)`, then the sum `∑ 1/n(k)` is irrational.

This conjecture is **open** — no proof or counterexample is known for the regime `1 < c < 2`.
The statement is left as `sorry`. -/
theorem erdos267 (n : ℕ → ℕ) (hn_pos : ∀ k, 0 < n k)
    (hn_inc : StrictMono n) (c : ℝ) (hc1 : 1 < c) (hc2 : c < 2)
    (hlim : Filter.Tendsto (fun k => (n (k+1) : ℝ) / n k)
      Filter.atTop (nhds c)) :
    Irrational (∑' k, (1 : ℝ) / n k) := by sorry
