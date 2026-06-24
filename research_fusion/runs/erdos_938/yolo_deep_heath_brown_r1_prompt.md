ROUND 1 — Formulate Heath-Brown energy bound EXTENSION for Erdős 938.

PROBLEM: Erdős 938 — Are there only finitely many three-term arithmetic progressions formed by THREE CONSECUTIVE terms (n_k, n_{k+1}, n_{k+2}) of the powerful-number sequence? (powerful = p|n ⟹ p²|n)

KNOWN INPUTS:
- Heath-Brown 1988 (Math Comp 50:155-168) proved infinitely many consecutive POWERFUL PAIRS (n, n+1) exist via Pell equation 8x² - y² = 1 with both x, y powerful. The proof uses an *energy bound* on solutions to a Pell-type quadratic form.
- Define E_2(N) = #{(n, n+d) : both powerful, n ≤ N}, the *pair-energy* of the powerful set.
- Heath-Brown's argument bounds E_2(N) = O(N^θ) for some θ ∈ (0,1), via 2-descent on the Pell-curve solution set.
- Mollin-Walsh JNT 1986 21:231-243 conjectured no triple of consecutive powerful integers (n, n+1, n+2).
- Chan 2022 arXiv:2210.00281 Thm 1.2: under abc, any powerful 3-AP has common difference d >> N^{1/2-ε}.
- Density: |P_N| ~ ζ(3/2)/ζ(3) * √N ≈ 2.173 √N.
- Consecutive-square gap obstruction (L3): every square is powerful, so n_{k+2} - n_k ≤ 2√(n_{k+2}) + O(1).

YOUR TASK — Round 1:
Define the TRIPLE-energy
  E_3(N) := #{(n, n+d, n+2d) : all three powerful, n ≤ N}.

The crucial NEW IDEA: the second-difference rigidity. For (n, n+d, n+2d) to be a 3-AP with all three powerful and CONSECUTIVE, the constraint
  (n+2d) - (n+d) = (n+d) - n = d  (second difference vanishes)
combined with consecutiveness (no other powerful number in (n, n+2d)), forces d to lie in a *sparse* set of admissible "shift values".

PROPOSE: prove E_3(N) = O((log N)^c) for some constant c > 0.

REASONING STRATEGY (sketch in 400-600 words):
1. Two-step decomposition: count 3-APs by choosing a base pair (n, n+d) then counting compatible "third points" (n+2d) that ARE powerful AND that ARE the next consecutive term.
2. The pair count from Heath-Brown's energy bound gives E_2(N) = O(N^θ).
3. Conditional on the pair, the third point lies in a specific arithmetic position. The consecutiveness constraint then forces a 3-AP-witness equation of the form
     n + 2d = m₁² b₁³ for some squarefree b₁, m₁ ∈ Z_{>0}.
4. The set of admissible "shift values" d such that (n+d, n+2d) BOTH powerful is itself a 1-dimensional sublattice of Z, intersected with the powerful set. By Heath-Brown's argument applied to the (n+d, n+2d) pair: the count is O((d log N)^θ').
5. The double-count: E_3(N) ≤ ∑_{d ≤ √N} (#{n ≤ N : n powerful AND n+d powerful}) * (P[third point hits powerful set with correct second difference]).
6. The second-difference rigidity gives a LOGARITHMIC gain over the trivial bound: the probability that a "generic" arithmetic-shifted lift hits the powerful set is ~ 1/√N, but the second-difference constraint forces a multiplicative dependency among the cubefree kernels (b, b', b'') that, by Heath-Brown's 2-descent, reduces the effective dimension by 1.

KEY MATHEMATICAL CLAIM to validate:
"For a fixed pair (n, n+d) of consecutive powerful integers, the number of admissible d-shifts such that n+2d is ALSO powerful AND consecutive is O(log N)."

Output as a formal informal proof outline in 6 steps (Step 1 through Step 6), each step ≤ 100 words, ending with the conclusion E_3(N) = O((log N)^c) hence the set in the Erdős 938 theorem is finite.

State explicitly: which steps invoke published machinery (Heath-Brown 1988, Chan 2022, Bourgain-Glibichuk 2009, Mollin-Walsh 1986), and which steps are NOVEL extensions. Be precise about the logarithmic gain and where the second-difference rigidity bites.
