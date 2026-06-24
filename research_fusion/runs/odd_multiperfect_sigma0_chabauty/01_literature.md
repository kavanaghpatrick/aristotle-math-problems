# Literature: Chabauty-Coleman / Stoll for sigma_0(n) in {11,13,17,19}

Produced 2026-05-30 by YOLO-W2-A2 angle C.

## Primary sources
- Coleman, R., 1985. "Effective Chabauty." Duke Math. J. 52, 765-770.
- Stoll, M., 2017. "Chabauty without the Mordell-Weil group." arXiv:1506.06463.
  Refines Coleman 1985 by allowing rank r >= g (removing the rank-<-genus
  hypothesis), at the cost of effective explicit constants depending on the
  prime p and reduction type.
- Mihailescu, P., 2004. "Primary cyclotomic units and a proof of Catalan's
  conjecture." J Reine Angew Math 572, 167-195. (Wave-1 angle.)

## Status of multiperfect impossibility lineage
- For sigma_0(n) = 11, slot 746 / DB id 1258 closed the case via the
  cyclotomic-Mihailescu transplant (status compiled_no_advance, but the
  Lean term is correct as a Phi_q(p) congruent to 1 mod p barrier).
- sigma_0(n) in {13, 17, 19} are not in Mathlib and not in formal-conjectures.
- The squarefree-product reformulation (n = p_1 * ... * p_q) is not the
  applicable reduction; sigma_0 multiplicativity forces n = p^(q-1).

## Chabauty applicability for n = p^(q-1)
Reformulated as a superelliptic-curve family
  C_q : y^(q-1) = Phi_q(x), q prime in {11, 13, 17, 19}
the affine model is a cyclic cover of P^1 ramified at the q roots of Phi_q
plus infinity. Riemann-Hurwitz:
  g(C_q) = (q - 4)(q - 3) / 2
which gives g(11) = 28, g(13) = 45, g(17) = 91, g(19) = 120.

The Mordell-Weil rank is expected to grow at least linearly in q (cyclotomic
G_m-action on the Jacobian), exceeding the Coleman 1985 r < g threshold for
every q in this family. Stoll arXiv:1506.06463 removes the rank hypothesis
but the resulting explicit p-adic integration on a g >= 28 model is
computationally inert.
