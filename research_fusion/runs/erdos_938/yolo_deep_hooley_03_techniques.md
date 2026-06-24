# E938 deep-Hooley dossier — Techniques (May 30 2026)

## Primary technique: Hooley dispersion on the powerful indicator
Apply Linnik-Hooley dispersion to Σ_{n ≤ N} 1_P(n) · 1_P(n+d) · 1_P(n+2d) where 1_P is the indicator of powerful numbers. Use the convolution identity 1_P(n) = Σ_{a²b³ = n, b cubefree} 1, decompose into Type II bilinear sums in (a,b), and apply Cauchy-Schwarz over a-variable with b-equidistribution.

## Codex Round 2 cross-critique
Grok Round 1: **Hooley dispersion has not been applied to powerful indicator. Blocked at every stage.** Codex Round 2: confirms blockage, but offers alternative — convert to ternary Diophantine a²b³ + f²g³ = 2c²e³, apply Hooley 1979 Selberg sieve over cubic kernels.

## Triple correlation level of distribution
Required: level of distribution θ for the powerful indicator in arithmetic progressions, uniformly in d. Currently UNKNOWN. Heath-Brown 1992 gets θ = 1/2 + 0.1318 for one-point counts in short intervals — far from what triple-correlation dispersion needs (θ > 2/3 typically).

## Bombieri-Iwaniec-Mozzochi double large sieve (Codex 1c)
BIM handles dimension-1/2 sieves AFTER conversion to monomial exponential sums with controlled spacing. Possible sub-lemma but not method.

## Selberg sieve on intervening-powerful condition (Codex Round 2 fallback)
For each kernel triple (b, e, g), the Pell family is at most one infinite parametric solution. Sift the condition "no powerful in (n_k, n_{k+1})" using Selberg upper-bound sieve à la Hooley 1979 Acta Arith. — gives an upper bound on the count of consecutive Pellian triples up to N.

## Combined strategy
1. Classify all consecutive powerful 3-APs by squarefree-cubic kernel triple (b,e,g).
2. For each (b,e,g), the equation a²b³ + f²g³ = 2c²e³ is a ternary form whose integer solutions form a finite union of Pell-type parametric families (Bennett-Bajpai-Chan).
3. For each parametric family, apply Hooley Selberg sieve to bound the count of solutions with no intervening powerful in (a²b³, c²e³) ∪ (c²e³, f²g³).
4. Sum over (b,e,g); the kernel-triple sum is bounded by Chan's abc-conditional d ≫ N^{1/2-ε} combined with the unconditional d ≪ √N from consecutiveness — forces only finitely many kernel triples contribute.

## Honest cross-critique summary
Round 1 (Grok): 1/10 plausibility — virgin literature territory, no precedent.
Round 2 (Codex): 1/10 for pure dispersion, 3/10 as averaged-statistics input. Recommends Diophantine reframe.
Round 3 (Grok): 6/10 plausibility for advance (not closure) with hybrid dispersion + Diophantine + van-Doorn-aware reframe.

## Aristotle hand-off
Aristotle's informal-reasoner (subsystem #2) is the right target: hybrid Diophantine + sieve work is what its lemma-decomposition handles best, NOT the MCGS formalizer alone. Submit INFORMAL.
