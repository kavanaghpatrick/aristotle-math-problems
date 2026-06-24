# Techniques — yolo_e938_deep_heath_brown

## 3-round cross-critique log

### Round 1 — formulation (Grok-4.20-reasoning, 2026-05-30 15:14:35)
File: `yolo_deep_heath_brown_r1_grok.md`. 461 words. Proposed: E_3(N) := #{(n, n+d, n+2d) all powerful, n ≤ N}. Heath-Brown energy on pairs gives E_2(N) = O(N^θ). Second-difference rigidity (n+2d) - 2(n+d) + n = 0 forces multiplicative dependence among cubefree kernels (b, b', b'') via Bourgain-Glibichuk + Pell-system collapse. Conclusion: E_3(N) = O((log N)^c).

### Round 2 — critique (Grok-4.20-reasoning, 2026-05-30 15:16:50)
File: `yolo_deep_heath_brown_r2_grok_critique.md`. BRUTAL KILL. Key findings:
- **(Q1) Fatal**: Heath-Brown 1988 contains NO unconditional pair-energy upper bound E_2(N) ≪ N^{1-δ}. The paper proves existence (infinitely many consecutive powerful pairs), not an upper bound. E_2 upper bound is a phantom citation. The 2-descent argument referenced is for the existence direction (constructing solutions), not for bounding solution counts.
- **(Q2)** Kernel-rigidity gives a degree-6 surface in 6 variables, NOT a Pell equation on a rank-1 lattice. "Multiplicative dependence" is not a proof. The surface admits ≫ N^ε solutions in dyadic ranges via Bombieri-Vinogradov.
- **(Q3)** Even granting hypothetical E_2(N) ≪ N^θ, summation over d ≤ √N gives √N · N^θ ≪ N^{(1+θ)/2}; for o(√N) one needs θ < 0, impossible.
- **(Q4)** Bourgain-Glibichuk operates on F_p^* multiplicative groups. The set of cubefree kernels of powerful numbers is not a subgroup of any multiplicative group; literal transfer to Z fails.
- **(Q5)** If the kernel-surface argument works, Bombieri-Lang gives FINITENESS directly (general-type surface), overshooting log-N. The proof can't decide between log-N and finiteness; both are unsupported.

### Round 3 — refinement (Grok-4.20-reasoning, 2026-05-30 15:18:21)
File: `yolo_deep_heath_brown_r3_refined.md`. Accepted R2's kill. Pivoted to existence-finiteness via Mollin-Walsh paired-Pell + Bombieri-Lang. Refined argument now:
- L1 (Square-gap, UNCONDITIONAL, Mathlib-ready): d ≤ √(n_{k+2}) + 1.
- L2 (Golomb 1970, UNCONDITIONAL): n = x² y³ unique.
- L3 (Arithmetic surface): 3-AP condition becomes 2 c² d³ = a² b³ + e² f³ on a surface S in A⁶ with height bound H << n^C from L1.
- L4 (Mollin-Walsh paired-Pell, IJMMS 1986): two adjacent pairs form a paired binary-cubic Pell system on S.
- L5 (Degenerate-strata enumeration): three known triples are recovered.
- L6 (Bombieri-Lang on S^0): CONDITIONAL on Vojta dim-2.
- L7 (Faltings on kernel-bounded slices, UNCONDITIONAL): for any fixed B, kernels ≤ B gives finite many Thue equations, each genus ≥ 2; Faltings applies.
- Smallest unconditional sub-result: L7 (kernel-bounded finiteness).
- Honest gap: only L7 is unconditional; full result requires Bombieri-Lang/Vojta in dim 2 (open).

## Citation re-verification (web search 2026-05-30)
- Mollin-Walsh: IJMMS 1986, doi 10.1155/S0161171286000984 — NOT JNT 1986 21:231-243.
- Heath-Brown: Sém. Théorie Nombres Paris 1986-87, Birkhäuser pp.137-163 — NOT Math Comp 50:155-168.
- Chan 2025: arXiv:2503.21485, Integers 25 (2025) Paper No. A7.

Prior E938 dossiers used the wrong Mollin-Walsh + Heath-Brown anchors; corrected in this submission.
