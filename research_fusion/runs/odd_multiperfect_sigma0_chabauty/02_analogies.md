# Analogies: Chabauty-Coleman ↔ multiperfect impossibility

Produced 2026-05-30 by YOLO-W2-A2 angle C.

## Cross-domain transplant attempted
**Source side**: Stoll arXiv:1506.06463 + Coleman 1985 Duke. Effective p-adic
integration on a smooth projective curve C/Q with Jacobian J. Counts integer
points by integrating a holomorphic differential against a p-adic logarithm.
Stoll's refinement removes the r < g hypothesis at the cost of effective
constants depending only on p and reduction type.

**Target side**: Diophantine equation
  Phi_q(p) = k * p^(q-1),  q prime in {11, 13, 17, 19}, p odd prime, k >= 2
realized as a superelliptic curve C_q : y^(q-1) = Phi_q(x), and the question
of whether integer points (x, y) with x prime can be ruled out uniformly in q.

## Feasibility check
- Grok-4 (with no live web search): the curve C_q has genus
  g(C_q) = (q - 4)(q - 3) / 2 (Riemann-Hurwitz on cyclic Phi_q cover).
- Grok-4 (refined query): Stoll's refinement is "formally applicable yet
  practically inert" --- the p-adic integration on a g >= 28 model produces
  height bounds far beyond any computable range, and uniformity in q fails.
- Mihailescu congruence Phi_q(p) congruent to 1 mod p already closes the q=11
  case (wave-1 angle), supplying no extra Diophantine finiteness beyond it.

## Verdict
The Chabauty-Coleman / Stoll transplant is a NEGATIVE feasibility result for
this family: the technique applies in principle but cannot deliver effective
bounds at the relevant genus. The valuable sub-claim that can be formalized
is the explicit genus / rank-bound computation for C_q itself, as supporting
infrastructure for the broader odd-multiperfect impossibility lineage.

## Cross-domain credit
The honest contribution is the **negative analog witness**: a precise
statement of WHY Chabauty-Coleman cannot close this family, which deletes
one potential attack vector and concentrates effort on the cyclotomic /
Mihailescu line (wave-1).
