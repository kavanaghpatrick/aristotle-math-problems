You are doing a final synthesis on Erdős 938 (consecutive powerful 3-APs finiteness). Prior W-team work has converged on these facts:

KNOWN FACTS (verified):
1. Powerful number = n>=1 such that p|n => p^2|n. Equivalently n = a^2 b^3, b squarefree (Golomb).
2. Consecutive powerful 3-AP (n_k, n_{k+1}, n_{k+2}) up to 10^14: only 18 examples known. Up to 10^6: only 3 known triples (1728/1764/1800, 6912/7056/7200, 729000/729316/729632).
3. UNCONDITIONAL upper bound (slot 1316 L1): d <= sqrt(n_{k+2}) + 1, because every perfect square is powerful — if d were larger, an interloper square would sit in the gap (slot 1316).
4. abc-CONDITIONAL lower bound (Chan 2022 arXiv:2210.00281 Thm 2): d >> N^{1/2 - eps}.
5. Combined slot 1315 sandwich (under abc): c_eps * N^{1/2-eps} < d < 2*sqrt(N) + 2. NOT FINITENESS — sandwich is non-empty for all N.
6. Bajpai-Bennett-Chan 2024 IJNT 20:19-45 (arXiv:2302.03113):
   - UNCONDITIONAL: infinitely many 4-term APs of pairwise-COPRIME powerful numbers (A(2) >= 4).
   - abc-CONDITIONAL Corollary 1.3: A∞(2) = 4 (no 5-term coprime powerful APs under abc).
7. van Doorn 2026 arXiv:2605.06697 Conj 5: infinitely many CONSECUTIVE powerful 3-APs from family A_1 (Pell x^2 - 7^3 y^2 = 2). Would FALSIFY E938.
8. van Doorn's first triple (130530625, 130553476, 130576327) is a powerful 3-AP but NOT CONSECUTIVE (5 intermediate powerfuls between endpoints).
9. mod-8 admissible powerful residues = {0,1,3,4,5,7}; mod-72 has 593 compatible AP triples — 2-adic obstruction does NOT close.
10. Stark CM elliptic angle DEAD by (1728,1764,1800) — product 1728*1800 = 3110400 = 2^7 * 3^5 * 5^2 (not a square; CM angle does not apply).

YOUR TASK:
Propose a load-bearing claim combining BOUNDED-KERNEL + UNBOUNDED-KERNEL via a uniformity lemma derived from Bajpai-Bennett-Chan 2023.

Key question: Does Bajpai-Bennett-Chan's coprime A∞(2)=4 give us anything for the CONSECUTIVE (not coprime!) case? The consecutive powerful numbers in a 3-AP need NOT be coprime: e.g., 1728 = 2^6 * 3^3, 1764 = 2^2 * 3^2 * 7^2, 1800 = 2^3 * 3^2 * 5^2 all share factor 12.

Construct a careful argument that:
(A) States the FINITENESS conjecture explicitly for E938 (consecutive case).
(B) Splits into bounded-kernel and unbounded-kernel sub-cases. Bounded kernel = max(b_1,b_2,b_3) <= B where n_i = a_i^2 b_i^3.
(C) For bounded kernel: per-kernel-triple Mordell-Siegel finiteness (slot 1316 L4). This is unconditional per kernel triple.
(D) For unbounded kernel: argue that the abc-sandwich (slot 1315) FORCES kernel growth. Specifically, the unconditional upper d <= 2*sqrt(N) + 2 combined with the powerful structure n_i = a_i^2 b_i^3 implies that if b_i grows, then a_i must shrink for the same N. Use the AP identity n_{k+1}^2 = n_k * n_{k+2} + d^2 to extract a kernel-uniformity diophantine condition.
(E) THEN attempt to bound the kernel a priori via the Bajpai-Bennett-Chan coprime classification (after reducing the AP to its coprime core: divide through by gcd to get a coprime triple).
(F) STATE HONESTLY whether your synthesis closes E938 or only delivers a partial result.

DO NOT bluff. If a step is open or speculative, label it OPEN/SPECULATIVE.
DO NOT claim a citation unless you have verified it (we have verified arXiv:2210.00281 Chan and arXiv:2302.03113 BBC).
Output: a structured analysis with 4 to 6 numbered claims, each marked PROVEN / abc-CONDITIONAL / BBC-CONDITIONAL / OPEN.
