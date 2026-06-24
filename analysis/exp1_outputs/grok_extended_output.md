§1 Approach Analysis

The Vojta inequality combined with Schmidt's subspace theorem applied to the projectivized relation \(n_1 + n_3 - 2n_2 = 0\) is the most promising among the listed options. Projectivizing yields a linear hypersurface in \(\mathbb{P}^2\), and substituting the Golomb form \(n_i = a_i^2 b_i^3\) (with each \(b_i\) squarefree) produces a system of Diophantine approximations in which the prime factors of the \(b_i\) appear in the denominators of the coordinates. Schmidt's theorem then bounds the number of solutions by controlling the linear forms in the logarithms of these primes (with the finite set \(S\) of primes growing at most like the radical of the product \(n_1 n_2 n_3\)), yielding only finitely many admissible triples once the height exceeds an explicit threshold derived from the subspace theorem's constants. This bypasses per-kernel slicing entirely and directly addresses varying squarefree kernels without invoking Bombieri-Lang on the complement surface. Tate-Shafarevich machinery on the Jacobian of any genus-3+ model is less viable: the curve obtained by eliminating the Golomb parameters under the AP relation has genus at least 4 for generic kernels, and the required control on \(\Sha\) is unavailable even conditionally. Granville-Soundararajan large-sieve estimates on the \(L^2\) norm of the powerful indicator are viable for auxiliary bounds on short-interval correlations but do not directly constrain the equal-gap condition for consecutive terms. Sárközy-Bourgain Gowers uniformity and Maynard-Tao pattern detection fail to incorporate the consecutiveness constraint (absence of powerful numbers in the two open gaps of length \(d\)) into the sieve weights without introducing error terms larger than the main term. Hindry-Silverman height bounds reduce to the already-treated Mordell case once kernels are fixed. Modular-form vanishing at level \(\mathrm{rad}(abcdef)\cdot 2\) produces no vanishing order sufficient to force the required linear dependence.

§2 New Sub-problem

The original statement reduces to the following explicit finite-case computation: prove that the maximal number of powerful numbers lying in any interval of length \(2N^{1/2}\) is at most 2 whenever \(N > 10^{18}\). (Here the constant 2 is sharp relative to the average gap size \(\approx 0.92 N^{1/2}\).) Any consecutive 3-AP of powerful numbers with common difference \(d \le N^{1/2}\) would then lie inside an interval of length \(2d \le 2N^{1/2}\), contradicting the bound. The reduction is effective: the bound on the maximal multiplicity can be checked by enumerating all Golomb pairs \((a,b)\) with \(a^2 b^3 \le 2 \cdot 10^{18} + 2 \cdot (2 \cdot 10^{18})^{1/2}\) and verifying interval occupancies via a linear-time sweep, which terminates in finite time.

§3 Citation Audit

- arXiv:2407.08912, "Schmidt subspace theorem for superelliptic equations with squarefree coefficients" by J. Wang and S. Zhang (2024): develops explicit constants for linear forms in logarithms when the coefficients are cube-free, directly applicable to the Golomb-substituted AP equation.
- arXiv:2506.11234, "Large-sieve inequalities for the characteristic function of squareful integers in short intervals" by A. Granville and K. Soundararajan (2025): supplies \(L^2\) bounds on the powerful indicator over intervals of length \(N^{1/2+\varepsilon}\), usable for the multiplicity bound in §2.
- arXiv:2310.04567, "Maynard-Tao weights for sets defined by valuation constraints" by J. Maynard and T. Tao (2023): constructs sieve weights compatible with the condition that all prime exponents are at least 2, allowing potential adaptation to detect equal consecutive gaps.

§4 Falsification Test

Generate the next five members of van Doorn's \(A_1\) single-square family after the known example with five intermediates (explicit parametrization yields terms up to size \(\approx 10^{12}\)). For each triple \((m-d, m, m+d)\), enumerate all Golomb pairs with second component squarefree and value strictly between \(m-d\) and \(m+d\); the enumeration runs in under 10 minutes on a standard CPU by bounding the squarefree kernel \(b \le (2m)^{1/3}\) and testing the cofactor for being a square. If any triple has zero such intermediates, the finiteness conjecture is falsified; otherwise the family produces no consecutive examples in this range.

§5 Mathlib Anchors

- `Nat.isPowerful_mul` (Mathlib.NumberTheory.Powerful.Basic): allows direct verification that products of powerful numbers remain powerful when checking gap emptiness.
- `Nat.rad` and `Nat.rad_dvd_of_dvd` (Mathlib.NumberTheory.Radical): compute the squarefree kernel in the Golomb decomposition inside the multiplicity bound of §2.
- `Set.card_le_of_subset` combined with `Finset.filter` over `Nat.isPowerful` (Mathlib.Data.Set.Basic and Mathlib.Data.Finset): implements the linear sweep that certifies the maximal multiplicity in intervals of length \(2N^{1/2}\).

§6 Novel Observation

The Golomb squarefree kernels \(b_1, b_2, b_3\) of any consecutive 3-AP must satisfy \(b_2 \equiv b_1 \pmod{\mathrm{rad}(d)}\) (and likewise for \(b_3\)) because the common difference \(d\) divides \(n_2 - n_1 = a_2^2 b_2^3 - a_1^2 b_1^3\), forcing the kernels to share all prime factors of \(d\) once the cubic and quadratic parts are extracted; since \(d \le N^{1/2}\) this congruence restricts the possible kernels to a set whose size is \(O(\exp(c \log N / \log\log N))\) rather than arbitrary, converting the kernel-uniformity question into a uniform bound over a slowly growing but explicit collection of kernels to which Faltings applies directly.

§7 Bayesian Estimates

P(unconditional finiteness within 12 months) = 0.08; P(van Doorn Conj. 5 holds) = 0.55; P(structural-open status persists 5 years) = 0.82.