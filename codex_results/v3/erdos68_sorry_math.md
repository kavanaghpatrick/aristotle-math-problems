`erdos_68` cannot be completed unconditionally from current math: this is still an open problem as of **March 13, 2026**.

You already reached the key reduction in [Erdos68.lean:95](/Users/patrickkavanagh/math/results_v07/56fe24e4/56fe24e4-e0a1-44c6-a809-092f253196e1_aristotle/RequestProject/Erdos68.lean:95), and the unresolved theorem is [Erdos68.lean:114](/Users/patrickkavanagh/math/results_v07/56fe24e4/56fe24e4-e0a1-44c6-a809-092f253196e1_aristotle/RequestProject/Erdos68.lean:114).

Maximum Lean progress you can add now is conditional:

```lean
/-- If the remainder is rational, Erdős #68 follows from irrationality of `exp 1`. -/
theorem erdos_68_of_remainder_rat
    (hExp : Irrational (exp 1))
    (hRrat :
      ∃ r : ℚ,
        (∑' n : ℕ,
          1 / ((n + 2).factorial * ((n + 2).factorial - 1) : ℝ)) = r) :
    Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) := by
  rcases hRrat with ⟨r, hr⟩
  rw [sum_decomposition, hr]
  have h1 : (exp 1 - 2) + (r : ℝ) = exp 1 + (r - 2) := by ring
  rw [h1]
  have hI : Irrational (exp 1 + (r - 2 : ℚ)) := (irrational_add_ratCast_iff).2 hExp
  simpa [Rat.cast_sub] using hI

/-- If the whole sum were rational, then (assuming `exp 1` irrational) the remainder is irrational. -/
theorem remainder_irrational_of_sum_rat
    (hExp : Irrational (exp 1))
    (hSrat :
      ∃ q : ℚ, (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) = q) :
    Irrational
      (∑' n : ℕ,
        1 / ((n + 2).factorial * ((n + 2).factorial - 1) : ℝ)) := by
  intro hRrat
  rcases hSrat with ⟨q, hq⟩
  rcases hRrat with ⟨r, hr⟩
  have hExpEq : exp 1 = q - r + 2 := by
    linarith [sum_decomposition, hq, hr]
  exact hExp ⟨q - r + 2, by simpa using hExpEq.symm⟩
```

Where it breaks:
1. Your idea (1) is correct: `S ∈ ℚ` implies `R` irrational (assuming `exp 1` irrational).  
2. No contradiction follows, because we cannot prove `R ∈ ℚ` (or any incompatible arithmetic property).  
3. Continued-fraction / irrationality-measure methods fail with current approximants: denominator growth from partial sums is roughly `exp(c N^2 log N)`, while tail error is only `exp(-N log N)`, far too weak for standard irrationality criteria.  
4. Nesterenko/Zudilin-style machinery is not directly applicable: we lack suitable finite-dimensional integer linear forms/recurrences for values attached to `1/(n! - 1)`.

What would be needed for the final `sorry`:
1. A new arithmetic theorem forcing rationality or controlled linear relation of `R`.  
2. Or a strong prime-divisor/valuation structure for `n! - 1` enabling a p-adic contradiction for rational `S`.  
3. Or a new transcendence/linear-independence result tailored to this series.

Sources checked:
- Erdős Problems #68 (status shown as open; page shows last edit Sep 28, 2025): https://www.erdosproblems.com/68  
- OEIS A331373 (still describes this as an Erdős irrationality question; page modified Feb 17, 2026): https://oeis.org/A331373

I did not find any 2025–2026 source claiming a full proof; that negative evidence is not a proof of impossibility, but it supports that the final theorem remains genuinely open.