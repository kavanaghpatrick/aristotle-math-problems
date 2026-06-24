# Techniques: short-listed cross-domain transplants

Produced 2026-05-30 by YOLO-W2-A2 angle C.

## Short-listed (in priority order)

### 1. Stoll Chabauty without Mordell-Weil (arXiv:1506.06463) - PRIMARY
- Status: FORMALLY APPLICABLE BUT PRACTICALLY INERT (Grok-4 verdict).
- Genus growth g(C_q) = (q-4)(q-3)/2 = 28, 45, 91, 120 makes p-adic
  integration computationally infeasible.
- Useful as INFRASTRUCTURE: formalize the genus computation in Lean as a
  building block for future attacks.

### 2. Coleman 1985 Effective Chabauty - SUBSIDIARY
- Original r < g hypothesis fails: cyclotomic G_m-action on Jacobian gives
  rank >= q - 1, exceeding the genus threshold for the smaller q values.
- Cannot be invoked uniformly in q.

### 3. Mordell-Weil sieve - PARALLEL TRACK
- Could be combined with Stoll for specific (q, p) pairs.
- Out of scope for uniform-in-q closure.

## Sub-claim closure target
The honest formalizable contribution is the genus / rank-bound LEMMA
  genus_super_elliptic_Phi_q : g(C_q) = (q - 4) * (q - 3) / 2
  rank_bound_J_C_q : rank_Q J(C_q) >= q - 1
which together establish that Coleman 1985 fails uniformly on the family,
ruling out one attack vector and supporting wave-1's Mihailescu line.

## Honest disclaimer
This is a NEGATIVE feasibility witness: we did NOT find a Chabauty-based
closure of the family. We characterized WHY the technique cannot close it.
The cyclotomic / Mihailescu line (wave-1) remains the only known closure.
