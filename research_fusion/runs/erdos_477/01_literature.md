# Erdős 477 — Stage 1 Literature (W4-D, May 31 2026)

## Problem statement (verified from formal-conjectures/FormalConjectures/ErdosProblems/477.lean)

E477 (Erdős–Sekanina): Is there a polynomial f ∈ Z[X] of degree ≥ 2 and a set A ⊂ Z such that for every z ∈ Z, there is exactly one (a, n) with a ∈ A, n > 0, z = a + f(n)?

- **X^2 case CLOSED (negative):** Sekanina (1959), Czechoslovak Math J 9:485–495. No such A exists for f(n) = n^2.
- **Degree-2 generalisation CLOSED (negative):** AlphaProof (Jan 7 2026, formal-conjectures #477) — for f(n) = a·n^2 + b·n + c with a | b, a ≠ 0, b ≠ 0, no such A exists. Comment in 477.lean line 56: "This was found by AlphaProof for the specific instance X^2 - X + 1 and then generalised."
- **X^3 case OPEN.** Theorem `erdos_477.X_pow_three` in formal-conjectures with `sorry`. Wiki note ("partial AI progress") confirmed via teorth/erdosproblems AI-contributions table (snapshot 2026-05-30); AlphaProof Nexus attempted but did not solve (listed in erdos_problems_attempted.txt, absent from APNOutputs/ErdosProblems/).
- **Monomial X^k for k ≥ 2 OPEN.** This is the form Sekanina himself asked in 1959.

## Cross-domain literature (verified via WebSearch May 31 2026)

1. **Ruzsa (2015)** "Exact additive complements", arXiv:1510.00812. Verified existence: settles **how close** A(x)B(x)/x can be to 1 for exact complements. Refines Sárközy–Szemerédi (A(x)B(x) - x → ∞) and Chen–Fang. **Does NOT mention cubes, Sekanina, or unique-representation.** Concerned with sumset covering (z = a + b for almost all z), not with **uniqueness**.

2. **Ding–Sun–Wang–Xia and successors (2025–2026)** "No exact on average additive complements of squares", arXiv:2512.15407. Proves: for r ≥ 2, if W_r is an additive complement of S_r = {1^r, 2^r, ...}, then Σ_{n ≤ N} f_r(n) - N ≫_r N^{1−1/r}. For r = 2 the bound is N^{1/2}(log N)^δ (Cilleruelo 1993 conjecture). **This rules out "exact on average" complements of cubes (r=3) — a weaker non-uniqueness statement than what E477 demands. The unique-representation version is still open.**

3. **Konyagin–Lev (2009)** "The Erdős–Turán problem in infinite groups", arXiv:0901.1649. Constructs perfect additive bases in abelian groups; the technique is structural (avoids exponent 3 and order 2 in G). **Not directly applicable to Z with the polynomial-sequence constraint.**

4. **Additive completion of thin sets (2022)** arXiv:2209.08509. Generalises Sárközy–Szemerédi to thin sets, sharpens log factors. Bibliography keys: Ruzsa1, Ruzsa2, ChenFang. **Does not cite Sekanina or E477.**

5. **Sumsets in complement of a set (2024)** arXiv:2410.22664. Ratio test for additive complements outside A. Cites Lorentz 1954 (Erdős conjecture). **Does not address the unique-representation question.**

## Mod-9 (cube residue) baseline fact

Cubes mod 9 ∈ {0, 1, 8}. Hence {n^3 : n ≥ 1} mod 9 misses residues {2,3,4,5,6,7}. For Z = A ⊕ {n^3 : n>0} via unique sum, A must intersect every residue class mod 9 with cardinality consistent with the missing residues being covered by A alone. No coset-mod-9 collapse follows from this directly; the obstruction (if any) must be quantitative.

## Mod-2 (parity) baseline fact

Cubes: n^3 has the same parity as n. So {n^3 : n ≥ 1} contains both parities equally. No immediate parity obstruction.

## Density baseline

|{n^3 : n ≥ 1} ∩ [1,N]| ~ N^{1/3}. Hence A ∩ [-N, N] must have density ~ N^{2/3} for the sumset to cover Z. This is **denser than the squares case** (which needed N^{1/2}), suggesting the X^3 case is structurally HARDER than X^2, not easier.

## Status of search for the *unique-representation* X^3 result

After WebSearch + WebFetch on arXiv (multiple distinct queries May 31 2026):
**No paper found** that proves or even seriously attacks the unique-representation X^3 case of Erdős 477. The closest is arXiv:2512.15407 (Cilleruelo-style "exact on average"), which is strictly weaker. **Therefore the X^3 case of E477 is verifiably open per the current literature.**
