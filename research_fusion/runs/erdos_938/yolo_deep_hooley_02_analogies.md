# E938 deep-Hooley dossier — Analogies (May 30 2026)

## Closest analogue: squarefree APs
Nunes (arXiv:1402.0684, 1602.00311) and Mangerel (arXiv:2008.11163) treat squarefree integers in APs via dispersion. The squarefree indicator μ²(n) has density 6/π², dimension 1 (Erdős-Selberg framework). Dispersion saves because squarefree has the clean factorization n = m·d² with d the squareful kernel.

## Why powerful is harder
Powerful numbers have density c/√N (dimension 1/2). Decomposition n = a²b³ with b cubefree is multiplicative but has TWO free parameters at unequal scales (a ~ N^{1/2-ε}, b ~ N^{ε}). Dispersion needs Type II factorization at controlled scale; the a-b split is rigid.

## Linnik dispersion vs Hooley dispersion
Linnik's original dispersion (Mat. Sb. 1961) handles sums Σ_n f(n) g(n+a) via Cauchy-Schwarz on the diagonal and equidistribution of g. Hooley extended this in Tract 70 §6 to the divisor function and 3-square representations. The triple-correlation version (3-AP) has been worked out for primes (Green-Tao) but never for powerful.

## Diophantine analogue (Codex Round 2 alternative)
A 3-AP of consecutive powerfuls n_k = a²b³, n_{k+1} = c²e³, n_{k+2} = f²g³ with d = n_{k+1}-n_k satisfies the ternary equation
  a²b³ + f²g³ = 2 c²e³.
For fixed squarefree-cubic kernels (b, e, g), this is a Pell-type conic in three variables. Hooley's 1979 Acta Arith. paper applies the Selberg sieve to count representation multiplicities of cubic forms; the same machinery extends.

## Van Doorn obstruction (May 2026)
Van Doorn's Pellian family (x²−7³y²=2 → (x-2)²+(x²-2)=2(x-1)²) shows the kernel triple (b,e,g) = (1,1,7) admits infinitely many integer solutions. So the ternary-equation framework alone cannot give finiteness; finiteness must come from the intervening-powerful constraint that rules out the Pellian family.

## Reframe (per Grok Round 3)
The natural target is now a STRUCTURE THEOREM: every consecutive powerful 3-AP arises from a finite list of (kernel-triple, Pell-family) data. Finiteness then reduces to deciding which kernel-triple Pell families have intervening powerfuls absent infinitely often — a problem amenable to Hooley's Selberg-sieve + Brun-Titchmarsh apparatus.
