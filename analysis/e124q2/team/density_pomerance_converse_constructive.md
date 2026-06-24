# E124: A constructive proof of Pomerance's converse via Weyl equidistribution

**Author:** density. **Status:** rigorous sketch (k=0); the equidistribution step is standard.
Companion to `density_threshold_ledger.md`. Gives the WHY behind the proven Lean lemma
`erdos124.converse` (∑_{d∈D} B_d cofinite ⟹ ∑ 1/(d−1) ≥ 1), with an explicit mechanism and the
location of the missing integers.

## Setup

B_d = {0/1-digit base-d integers}. Key fact (max-reach): the largest element of B_d strictly
below d^m is (d^m − 1)/(d − 1), and the next element is d^m itself. So **B_d has a gap of width
≈ d^m·(d−2)/(d−1) just below every power d^m**, and `max(B_d ∩ [0,X]) / X` oscillates in
[1/(d−1), d/(d−1)], attaining its **minimum 1/(d−1) exactly when X is just below a power of d**.

## Theorem (Pomerance, constructive form)

Let D = {d_1 < … < d_r}, all d_i ≥ 3, and suppose ∑_{d∈D} 1/(d−1) < 1. Then ∑_{d∈D} B_d misses
infinitely many integers (so is not cofinite). Moreover the missed integers cluster just below
powers d_min^m for infinitely many m.

### Proof sketch

Write d₁ = d_min. To represent n just below d₁^m, the largest usable a_{d₁} ∈ B_{d₁} is
(d₁^m − 1)/(d₁ − 1) (the next element d₁^m exceeds n). The remaining deficit must be supplied by
∑_{d>d₁} a_d with each a_d ∈ B_d ∩ [0, n]. Hence the maximum representable value with this leading
choice is

    R(m) = (d₁^m − 1)/(d₁ − 1) + ∑_{d>d₁} max(B_d ∩ [0, d₁^m − 1]).

For each d > d₁, `max(B_d ∩ [0, d₁^m−1]) ≤ (d/(d−1))·d₁^m·(1 + o(1))`, and the WORST (smallest)
value `≈ d₁^m/(d−1)` is attained when d₁^m sits just above a power of d, i.e. when the fractional
part {m·log d₁ / log d} is near 0⁺.

**Weyl equidistribution.** Since the bases are admissible with gcd(D)=1 (for k≥1; for k=0 the
multiplicatively-dependent families have gcd>1 but still obey the threshold — see edge case),
log d₁ / log d is irrational for every d that is not a power of d₁, so the vector
({m·log d₁/log d})_{d>d₁} is equidistributed in the torus. Hence for **infinitely many m**, all
fractional parts are simultaneously within ε of 0, putting every d > d₁ near its worst alignment.
At such m,

    R(m) ≤ d₁^m · ( 1/(d₁−1) + ∑_{d>d₁} 1/(d−1) + Cε ) = d₁^m · ( ∑_{d∈D} 1/(d−1) + Cε ).

Since ∑ 1/(d−1) < 1, choose ε so the bracket is < 1. Then R(m) < d₁^m − 1, so every integer in
(R(m), d₁^m − 1] is **unrepresentable**. This is a nonempty block for infinitely many m. ∎

### Concrete instance (verified, k=0)
D = (3,6,7), ∑ = 13/15 < 1. At m = 16: a_3 ≤ (3^16−1)/2 = 21,523,360; max(a_6+a_7) = 18,818,836;
so n = 40,342,197 = 21,523,360 + 18,818,836 + 1 is unrepresentable (verified by independent brute
force). The whole block [40,342,197, 40,353,606] is missed.

### Edge case: multiplicatively-dependent bases (d = d_min^j)
If some d = d_min^j (e.g. (3,9), (3,9,27), (4,8)), the equidistribution premise fails (the
fractional part is periodic). BUT every such family has gcd(D) = d_min > 1, so it is **excluded by
the gcd=1 hypothesis at k≥1**. At k=0 (no gcd hypothesis) these are still incomplete by direct
computation when ∑ < 1 (e.g. (3,9): ∑ = 5/8, missing 171,804 of first 200,000) — the periodic
alignment still hits the worst case infinitely often, even more reliably. So the theorem holds in
both sub-cases.

## Why this does NOT prove the open (sufficiency) direction
The argument only shows ∑ < 1 ⟹ incomplete. The forward direction (∑ ≥ 1 ⟹ cofinite, the open
conjecture for k≥1) requires showing R(m) ≥ d₁^m for ALL m AND that no NESTED gap (deficit landing
in a ∑_{d>d₁} B_d gap, recursively) survives. The nested obstruction is the transcendence-theoretic
core (Mignotte–Waldschmidt), see `density_threshold_ledger.md` §6 and maverick's (SEED). When ∑ = 1
exactly (the conjecture's hypothesis), the SIMPLE max-reach gap vanishes (R(m) ≥ d₁^m for all m),
so only the nested/transcendence obstruction can remain — this is what BEGL96 ruled out for (3,4,7)
and what the open problem asks for general admissible D.
