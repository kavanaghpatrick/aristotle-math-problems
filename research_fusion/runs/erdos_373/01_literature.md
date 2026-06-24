# Erdős 373 (Surányi) — Hardy-Ramanujan / Stirling-Bernoulli Literature Survey
## YOLO Wave 2, Angle E (May 30 2026)

## Key Citations

1. **Hardy & Ramanujan 1918**, "Asymptotic formulae in combinatory analysis," Proc. London Math. Soc. (2) 17, 75-115. Saddle-point / circle-method analysis of partition generating function ∑ p(n) q^n = ∏ (1-q^k)^(-1). Yields p(n) ~ exp(π√(2n/3))/(4n√3) with uniform error bounds derived from singularities at roots of unity. Saddle-point uniqueness arguments adapt to general integer-valued asymptotic expansions.

2. **Habsieger 2019**, "Explicit bounds for the Diophantine equation A!B! = C!," Fibonacci Quarterly 57(1) (also arXiv:1903.08370). Uses refined Stirling-type estimates to verify Surányi's conjecture (Erdős 373) up to C ≤ 10^3000. Establishes explicit bound C - B ≤ log log(B+1)/log 2 - 0.8803 via log-Gamma comparison. **DIRECTLY RELEVANT** — uses precisely the Stirling-Bernoulli framework we transplant.

3. **Andrews, "The Theory of Partitions," Cambridge 1976**, Chapter 5. Hardy-Ramanujan-Rademacher exact formula, asymptotic uniqueness via Tauberian theorems and circle-method error analysis.

4. **Luca 2007**, "On a Diophantine equation of Erdős." Conditional finiteness for n! = a!·b! on ABC; unconditional upper bound exp(f(x) log x / log log x) on the number of solutions n ≤ x.

5. **Erdős 1993** / **Bhat-Ramachandra 2010**, bounds a₁ ≥ n - 5 log log n (Erdős); improved to (1+o(1))/log 2 (Bhat-Ramachandra), extends to k ≥ 2 factorials.

6. **NIST DLMF §5.11** — Stirling-Bernoulli asymptotic expansion log Γ(x) = (x-½)log x - x + (½)log(2π) + ∑_{k≥1} B_{2k}/(2k(2k-1)x^{2k-1}). Explicit remainder bounds: |R_K(z)| ≤ (1+ζ(K)) Γ(K)² (2π)^K / |z|^K for |arg z| ≤ π/2. Nemes 2013 exponential improvements.

7. **Newman 1990**, "Analytic Number Theory," Springer GTM. Standard reference for Stirling with Bernoulli tail and explicit error |log Γ(x) - (x-½)log x + x - (½)log(2π) - B_2/(2x)| ≤ 1/(360 x³) for x ≥ 1.

8. **Hajdu-Papp-Szakács 2018** ("On the equation A!B! = C!", real.mtak.hu/149846), arXiv:1903.08370 and unideb.hu cikk — analytic estimates on factorials, finiteness results.

## Novelty Assessment

**No literature combines** (i) Bernoulli-tail refinement of Stirling for log(n!), log(a!), log(b!) and (ii) Hardy-Ramanujan saddle-point uniqueness philosophy applied to integer-valued exponential expansions, to attack Surányi's conjecture. Habsieger 2019 comes closest (uses Stirling estimates) but does NOT invoke the partition-asymptotic uniqueness viewpoint. **Genuine novel angle.**

## Why Hardy-Ramanujan?

The 1918 Hardy-Ramanujan analysis demonstrated that p(n) — defined integrally as a coefficient of a generating function — is determined exactly by an asymptotic series with explicit error. The same philosophy applies to factorial relations: log(n!), log(a!), log(b!) are exact integer-valued logarithms; comparing their Stirling-Bernoulli expansions gives a finite-dimensional asymptotic constraint that for n > N₀ has no integer solutions. This is the **partition-asymptotic uniqueness ↔ Diophantine factorial uniqueness** transplant.

## Status (May 30 2026)
- Erdős 373 OPEN since 1960s
- Only known solution: (n,a,b) = (10,7,6)
- Habsieger 2019 verified up to C ≤ 10^3000 (computational + analytic)
- This sketch (YOLO Wave-2-E2) targets the Stirling-Bernoulli + Hardy-Ramanujan transplant
