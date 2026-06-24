# E267 Badea Citation Verification

**Submission:** UUID `4f5fd762-c61c-4c59-a5b1-cf60e4eea7b4`, problem `erdos267_fusion` (DB id 1262).
**Aristotle result:** `submissions/nu4_final/e267_pisot_extracted/eb7120ca-d6dc-4eec-9ced-fa5cf8c2db4b_aristotle/RequestProject/Erdos267.lean`. Theorem `erdos267_c_ge_2`. The full conjecture (1 < c < 2) is left as `sorry`.

**Classification: HYBRID (reinvented proof of the c ≥ 2 corollary; the *theorem* is Badea's, the *proof technique* is not).**

## What Badea (1987) actually does

Source: C. Badea, "The irrationality of certain infinite series," *Glasgow Math. J.* 29 (1987), 221–228. Verified by full PDF download from Cambridge Core (DOI 10.1017/S0017089500006868).

- Main Theorem: if $a_{n+1} > (b_{n+1}/b_n) a_n^2 - (b_{n+1}/b_n) a_n + 1$, then $\sum b_n/a_n$ is irrational.
- Proof method: invokes **Brun's 1910 irrationality criterion** (ref [3]: V. Brun, *Arch. Math. og Naturvidenskab* 31 (1910), 3). Brun's criterion says: an increasing $\alpha = \lim y_n/x_n$ with $\frac{y_{n+2}-y_{n+1}}{x_{n+2}-x_{n+1}} < \frac{y_{n+1}-y_n}{x_{n+1}-x_n}$ eventually is irrational.
- Badea sets $x_n = P_n = a_1\cdots a_n$, $y_n = A_n = \sum_{j\le n} b_j P_n/a_j$, derives recurrence $A_{n+1} = a_{n+1}A_n + b_{n+1}P_n$, then algebraically manipulates Brun's inequality (eqn 4 → 6 → 7 → 1) into the growth hypothesis.
- **Corollary 1** ($b_n=1$): $a_{n+1} > a_n^2 - a_n + 1 \Rightarrow \sum 1/a_n$ irrational.
- Corollary 4 / 5: applies Corollary 1 to $a_k = F_{2^k+1}$ (resp. $L_{2^n}$) using the identity $F_{2k+1} = F_k^2 + F_{k+1}^2$.

Note: Badea's c ≥ 2 deduction for E267 is not in this paper (it covers only doubling, $n_k = 2^k$). The c ≥ 2 result is folklore corollary attributed to Badea via Corollary 1.

## What Aristotle's proof actually does

`Erdos267.lean` proves `irrational_of_quadratic_growth_reciprocal_sum`:
- Hypothesis: $a_{n+1} \geq a_n^2$ (a *strict integer specialization*; Badea allows $> a_n^2 - a_n + 1$).
- Assume $\sum 1/a_n = q \in \mathbb{Q}$. Define $t_n := q - \sum_{k<n} 1/a_k \in \mathbb{Q}$.
- Lemmas: `tail_sum_upper_bound`/`tail_sum_lower_bound` give $1/a_n < t_n < 1/(a_n-1)$.
- `growth_step_bound`: $1/a + 1/(b-1) < 1/(a-1)$ when $b \geq a^2$, $a \geq 2$. This is a *one-step telescoping inequality*; it never appears in Badea.
- `rat_num_decrease`: if $r \in \mathbb{Q}$ in lowest terms and $1/a < r < 1/(a-1)$, then $\text{num}(r - 1/a) < \text{num}(r)$. Pure Fermat-descent on the rational numerator.
- Conclusion: $(t_n).\text{num}$ is a strictly decreasing sequence of positive integers — impossible. `StrictAnti` + `Set.infinite_range_of_injective` closes the goal.
- **No Brun's criterion. No $A_n/P_n$ recurrence. No comparison of successive Brun differences. No invocation of inequality (4) of Badea.**

## Cross-check

| Ingredient | Badea 1987 | Aristotle `Erdos267.lean` |
|---|---|---|
| Growth hypothesis | $a_{n+1} > a_n^2 - a_n + 1$ | $a_{n+1} \geq a_n^2$ (strictly stronger) |
| Core tool | Brun 1910 (ratio-of-differences criterion) | Fermat infinite descent on rational numerator |
| Auxiliary identity | $A_{n+1} = a_{n+1}A_n + b_{n+1}P_n$ | $1/a + 1/(b-1) < 1/(a-1)$ |
| Tail bound used | $A_n/P_n \uparrow \sum b_n/a_n$ (Brun premise) | $1/a_n < t_n < 1/(a_n-1)$ (direct telescoping) |
| Fibonacci doubling step | $F_{2k+1} = F_k^2 + F_{k+1}^2$ | $F_{2n} \geq F_n^2$ via `Nat.fib_two_mul` |

These are different proofs of the same statement. Aristotle's argument is the classical "tail-as-reduced-fraction, numerator-must-descend" descent — a known textbook technique (used historically in Erdős's 1975 *J. Math. Sci.* note and predating Brun). Erdős–Straus 1963 uses *yet a third* technique (modular arithmetic on $bN_k \bmod n_{k+1}$). The doubling-index Fibonacci reduction $F_{2n} \geq F_n^2$ is a textbook identity; Badea's analogue $F_{2k+1} = F_k^2 + F_{k+1}^2$ is sharper but Aristotle's weaker bound is sufficient.

## Honest assessment of formalization value

- **Citation:** misleading. Aristotle's comment "first proved by Badea (1987)" attributes the *theorem* correctly but the *proof technique formalized* is not Badea's. A defensible header would read "result due to Badea 1987 / Corollary 1; proof here is the classical descent variant."
- **Mathematical content:** The c ≥ 2 case is a textbook corollary; not a novel result. The formalization is solid Mathlib engineering on a known result. Roughly 320 lines of Lean for a 1-page paper proof.
- **Gap status:** **Did not advance the open gap.** The actual Erdős conjecture 267 (1 < c < 2) remains `sorry` on line 320. The c ≥ 2 corollary was known and routine.
- **Submission status in DB:** `target_resolved = 0`, `contribution_statement` empty — correctly recorded as no advance. Tracking is honest; only the in-file `STATUS:` comment overstates.

## Recommendation

Update the file header comment in `Erdos267.lean` (lines 9, 311) to read: *"Result due to Badea (1987, Corollary 1, Glasgow Math. J. 29). The proof formalized here is the classical descent on the reduced-fraction numerator of the tail; Badea's own argument routes through Brun's 1910 ratio-of-differences criterion."* Then this becomes a defensible piece of Mathlib infrastructure for a known result — but it is not progress on Erdős 267 and should not be cited as such.

## Sources

- C. Badea, *Glasgow Math. J.* 29 (1987), 221–228 — Cambridge Core PDF (DOI 10.1017/S0017089500006868). Full text verified.
- P. Erdős and E. G. Straus, *J. Indian Math. Soc.* 27 (1963), 129–133 — combinatorica.hu/~p_erdos/1964-19.pdf. Full text verified; uses mod-$n_{k+1}$ argument, not descent.
- V. Brun, *Arch. for Math. og Naturvidenskab (Kristiania)* 31 (1910), 3 — primary source for the ratio-of-differences criterion Badea actually uses.
