FINAL REFINEMENT: Erdős 938 (consecutive powerful 3-APs finiteness).

CONVERGED CROSS-CRITIQUE (rounds 1+2, codex-high + grok-4-fast-reasoning):

CONSENSUS:
- E938 (consecutive powerful 3-AP finiteness) splits into bounded-kernel + unbounded-kernel.
- BOUNDED-KERNEL (max(b_i) <= B): finite by per-kernel-triple Mordell-Siegel on the ternary form b_1 a_1^2 + b_3 a_3^2 = 2 b_2 a_2^2 (or its consecutive variant). Slot 1316 L4. UNCONDITIONAL per fixed B.
- UNBOUNDED-KERNEL: requires a uniformity lemma stating that kernel growth is incompatible with consecutiveness. This is INDEPENDENT of Bajpai-Bennett-Chan (BBC 2024 arXiv:2302.03113), because BBC's A∞(2)=4 result is about pairwise-COPRIME powerful APs; dividing a consecutive powerful AP by gcd destroys powerfulness (1728,1764,1800)/36 = (48,49,50) not powerful.
- The unbounded-kernel ternary form is a SURFACE (not a curve), so Mordell-Siegel does not bound integer points uniformly across kernels.

YOUR JOB (Round 3 final refinement):

Write the FINAL SYNTHESIS as a 4-component bridge lemma for Aristotle's informal subsystem:

L1 (UNCONDITIONAL): square-gap upper bound. For consecutive powerful 3-AP (n_k, n_{k+1}, n_{k+2}) with common difference d, d <= sqrt(n_{k+2}) + 1. Proof: every perfect square is powerful, so if d > sqrt(n_{k+2}) + 1 a square would interlope.

L2 (abc-CONDITIONAL): Chan 2022 arXiv:2210.00281 Thm 2 lower bound. d >> N^{1/2 - eps}. Application of abc to the AP identity (n_{k+1})^2 = n_k * n_{k+2} + d^2.

L3 (UNCONDITIONAL): bounded-kernel finiteness. For B > 0 fixed, restricted to consecutive powerful 3-APs (n_k, n_{k+1}, n_{k+2}) where each n_i = a_i^2 b_i^3 with b_i squarefree and max(b_1, b_2, b_3) <= B, only finitely many such APs exist. Proof: for each (b_1, b_2, b_3), the equation b_1 a_1^2 + b_3 a_3^2 = 2 b_2 a_2^2 with consecutiveness gate (no powerful in the open interval) and a_i >= 1 has finitely many solutions by Mordell-Siegel.

L4 (OPEN CORE): kernel-uniformity. There exists B*(N) growing in N such that any consecutive powerful 3-AP (n_k, n_{k+1}, n_{k+2}) with n_k >= K satisfies max(b_1, b_2, b_3) <= B*(N). Equivalently, the kernel-bounded slice in L3 already contains all sufficiently large consecutive powerful 3-APs.

EXACTLY what task should Aristotle's informal reasoner do?

Option A: Aristotle formalizes L1+L2+L3, axiomatizes L4, and proves the conditional: "L4 + L1 + L2 + L3 implies E938 finiteness."
Option B: Aristotle attempts L4 directly via its own MCGS/lemma-system, perhaps via a different angle (additive combinatorics on the ternary form? height bounds?).
Option C: Aristotle attempts to construct a counterexample family from van Doorn's A_1 family (would falsify).

Recommend ONE option as the primary informal-mode submission target. Justify briefly.

Also produce:
- Final 1-paragraph bridge lemma statement (under 600 chars) for the .fusion.json companion.
- Final 1-line "named technique" (under 120 chars) for the companion.
- Estimate P(compiled_partial), P(target_resolved), P(disproven), P(compiled_no_advance).

DO NOT BLUFF. The synthesis must be honest about what's open.
