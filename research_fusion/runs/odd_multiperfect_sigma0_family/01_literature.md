# Literature — odd multiperfect σ₀ uniform family (YOLO1 fusion lane)

## Parent slot
- Slot 746 (DB id 1258), problem_id `odd_multiperfect_sigma0_11`, status `compiled_no_advance`.
- Aristotle returned a clean Lean 4 proof of: no odd multiperfect n with σ₀(n) = 11.
- File: `submissions/nu4_final/slot746_extracted/4dab36cf-5ed8-4df9-ac5f-cfd93a2c3e71_aristotle/RequestProject/OddMultiperfect.lean`.
- The proof is a 4-step elementary p-adic chain that does NOT use any property of "11" beyond "11 is prime > 2", so it is begging to be uniformized.

## Target uniform family
- σ₀(n) ∈ {11, 13, 17, 19}.
- All four are primes. Each forces n = p^(q-1) for some odd prime p when n is odd.
- q − 1 ∈ {10, 12, 16, 18}: even, not divisible by p; the q-th cyclotomic polynomial Φ_q(p) = 1 + p + … + p^(q-1) is the relevant arithmetic object.

## Closed problems exhibiting the SAME uniform p-adic barrier
- Skolem-Mahler-Lech (Mahler 1935; Lech 1953). The vanishing set of a linear recurrence sequence over a number field is a finite union of arithmetic progressions, proved by p-adic continuation and Strassmann's theorem. Canonical: Mahler, "Eine arithmetische Eigenschaft der Taylor-Koeffizienten rationaler Funktionen", 1935.
- Mihăilescu's Catalan-conjecture proof (J. reine angew. Math. 572, 2004): the "primary cyclotomic units" obstruction. For x^p − y^q = 1 with p, q odd primes, the relation forces (x − 1)/Φ_q(x) and (y − 1)/Φ_p(y) to be q-th and p-th powers respectively, and the p-adic valuation of these ratios provides a uniform-in-(p,q) contradiction. Canonical: Mihăilescu 2004; Bilu's "Catalan without logarithmic forms" exposition (Astérisque 294, 2004) §4-§6.
- Ankeny–Artin–Chowla congruence (Ann. Math. 56, 1952): the regulator of Q(√p) satisfies a uniform p-adic identity h(p)·R(p) ≡ −something (mod p), giving a Wieferich-type uniform obstruction for class numbers. Not the right analog for σ-arithmetic.

## Why we pick the Mihăilescu / Bilu cyclotomic unit transplant
The uniform structure is exactly Φ_q(p) ≡ 1 (mod p) for all distinct odd primes p, q. Mihăilescu's argument is the canonical place where THIS identity is used as the load-bearing p-adic barrier, uniformly across a prime family. Bilu's exposition makes the q-uniformity explicit. The Skolem-Mahler-Lech framing (Grok's pick) is the same identity viewed from the linear-recurrence side: u_m = (p^m − 1)/(p − 1) satisfies u_m = (p + 1)u_{m-1} − p·u_{m-2}, with u_{q-1} = Φ_q(p) when q is prime.

## Erdős/multiperfect background
- A perfect number is 2-perfect. k-multiperfect: σ(n) = kn.
- No odd perfect number is known; the smallest hypothetical odd perfect has ω(n) ≥ 10 (Hare-Nielsen 2007; later improved).
- The σ₀(n) = q with q prime case is the ω(n) = 1 prime-power case. n = p^(q-1). Mersenne arguments rule out odd p^(q-1) being perfect for many q immediately.
- Recent: Ochem & Rao "Odd perfect numbers are greater than 10^1500" (Math. Comp. 81, 2012) — finite-verification work.
