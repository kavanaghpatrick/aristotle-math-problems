# Stage 2 — Cross-domain Analogies for Erdős 251

## Anchor: Σ p_n / 2^n irrational

## Analogy A — Σ ω(n)/2^n (Tao–Teräväinen 2025)

- **Mechanism that worked**: ω is multiplicative; two-point correlation estimates (Pilatte 2024) give power-saving in log scale, sufficient to defeat eventual periodicity of the tail.
- **Why E251 differs**: the n-th prime function p_n is NOT multiplicative; there is no two-point correlation framework for it.
- **Transferable kernel**: the *logical schema* — rationality ⇔ eventual periodicity of binary expansion ⇒ forbid via a quantitative non-periodicity criterion.

## Analogy B — Stoneham numbers, Σ b^{-k!} (Liouville 1844)

- **Mechanism**: extreme lacunarity in support (factorial growth) gives super-fast convergence of dyadic-rational approximants ⇒ irrationality measure ≥ 2.
- **Why E251 differs**: the support {n : 2^n appears} is dense (all n), not lacunary. We cannot get a direct Liouville construction.

## Analogy C — Champernowne's constant 0.123456789101112... (1933)

- **Mechanism**: digit-block analysis — the binary digits of S are determined by the binary digits of (Σ_{k ≤ n} p_k · 2^{N-k}) for each truncation level. As N → ∞, fresh primes inject "noisy" binary blocks at fixed positions.
- **Hook**: the rationality assumption forces the digit stream of S to be eventually periodic. The contribution of p_{N+1} to digit position N+1 down to N+1 - log_2(p_{N+1}) is a "fresh injection" of a prime's binary expansion. Eventually periodic implies all such injections agree on residues modulo period P — implausible.

## Analogy D — Algebraic complexity (Adamczewski–Bugeaud 2007)

- **Mechanism**: if a real number's base-b expansion has subword complexity p(n) = O(n), it is either rational or transcendental — NEVER algebraic of degree ≥ 2.
- **Application to E251**: the binary subword complexity of S is bounded below by the variety of binary patterns produced by primes. If subword complexity p(n) ≪ n, irrationality follows because S is not a quadratic surd (the only "simple" algebraic candidates).
- **Open piece**: must lower-bound the subword complexity of the binary digits of S.

## Analogy E — Mahler-functional values M(z) = Σ a_n z^n with M(z^2) = R(z) M(z)

- **Mechanism**: when the generating function satisfies a polynomial Mahler equation, values at algebraic points are either transcendental or rational with effective bounds.
- **Why E251 differs**: there is no known Mahler-type self-similarity in the sequence (p_1, p_2, ...). No functional equation relating Σ p_n z^n to Σ p_{2n} z^n.

## Bridge selection

Analogies A and B give NO direct lever (mechanism not portable). Analogies C and D both attack the *digit complexity* of the binary expansion of S. D is the more mature: Adamczewski–Bugeaud gives an UNCONDITIONAL irrationality criterion via subword complexity, which has been used to prove irrationality of e.g. the prime-counting binary constants.

The Stage 3 named technique is built around D (automatic-sequence / Christol-Adamczewski-Bugeaud digit complexity) with a quantitative input from prime gap distribution (Guth–Maynard 2024 zero-density) controlling the local injection of fresh prime binary blocks.
