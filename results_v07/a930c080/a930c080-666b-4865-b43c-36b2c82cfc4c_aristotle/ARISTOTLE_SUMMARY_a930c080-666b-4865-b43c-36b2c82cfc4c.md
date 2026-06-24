# Summary of changes
# Erdős Problem 828: φ(n) | (n+1) — Status: OPEN

The theorem statement has been formalized in `RequestProject/Erdos828.lean` but remains unproven (`sorry`) because this is a **genuinely open problem**.

## Key Findings

**The user's stated solutions {1, 2, 4, 8, 12} are incorrect** — they do not satisfy φ(n) | (n+1). For example, φ(4) = 2 does not divide 5, and φ(8) = 4 does not divide 9.

**The actual known solutions** (verified computationally) are: **{1, 2, 3, 15, 255, 65535, 4294967295}**

These arise from a single family: n = 2^(2^k) − 1 = F₀·F₁·…·F_{k−1}, where Fᵢ = 2^(2^i) + 1 are Fermat numbers. When all F₀, …, F_{k−1} are prime:
- φ(n) = 2^(2^k − 1)  
- n + 1 = 2^(2^k)  
- So φ(n) divides n + 1 ✓

Only five Fermat primes are known (F₀=3, F₁=5, F₂=17, F₃=257, F₄=65537), giving exactly 7 solutions (including the trivial n=1,2). Whether infinitely many Fermat primes exist is itself a major open problem, and no other infinite family of solutions is known.

Exhaustive case analysis confirms no other structural families exist for small prime factorizations. The file contains detailed documentation of all this analysis.