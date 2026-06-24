# E124: Admissible families cannot be prime-power-collinear (settles scholar's sharp test)

**Author:** density, prompted by scholar's Melfi-lineage finding. **Status:** PROVED (elementary).
Answers scholar's question: does any BEGL-admissible D have the Melfi-collinearity pathology?
**No** — the harmonic threshold forbids it, quantitatively.

## Background (scholar's flag)

Melfi (2001) needs PAIRWISE coprimality for his positive-density conjecture, not just gcd(D)=1.
His counterexample A = {3,9,81,104}: gcd=1 but Σ(Pow(A;s)) has zero lower density, because the
powers of 3 (3,9,81) contribute almost no NEW density and the single extra base 104 cannot fix it.
(Verified: ∑1/(d−1) for {3,9,81,104} = 5333/8240 ≈ 0.647 < 1, so it is NOT BEGL-admissible —
it does not threaten Q2, but its mechanism is the question.)

## Definition

Call D **prime-power-collinear** if every d ∈ D is a power of one fixed prime p (d = p^{e}).

## Lemma (no admissible collinear family)

No BEGL-admissible D — i.e. all d ≥ 3, ∑_{d∈D} 1/(d−1) ≥ 1, gcd(D)=1 — is prime-power-collinear.

### Proof

Let `T_p := ∑_{j≥1} 1/(p^j − 1)` be the TOTAL harmonic mass available on all powers of p.

- **Odd prime p ≥ 3.** `T_p` is maximized at p=3: `T_3 = ∑_{j≥1} 1/(3^j−1) = 0.68215… < 1`
  (and T_5 = 0.3017, T_7 = 0.1909, decreasing). So any D consisting of distinct powers of a
  single odd prime has ∑ 1/(d−1) ≤ T_p < 1 — it **fails the harmonic threshold**.
- **p = 2.** The constraint d ≥ 3 forces powers 4, 8, 16, … (exponent ≥ 2), so
  gcd(D) ≥ 4 > 1 — it **fails gcd=1** (relevant at k≥1). (Also ∑_{j≥2} 1/(2^j−1) = 0.6067 < 1,
  so it fails the threshold too.)

In every case a prime-power-collinear D violates admissibility. ∎

## Stronger quantitative form (the structural antidote)

For ANY prime p, the harmonic mass an admissible D may place on {powers of p} is bounded:

    M_p(D) := ∑_{d∈D, d a power of p} 1/(d−1)  ≤  T_p  <  1.

Hence an admissible D (∑ ≥ 1) must carry **at least 1 − T_p of its harmonic mass off the powers
of any single prime p**. In particular ≥ 1 − T_3 = 0.318 of the mass lies off the powers of 3.
This is a forced **multiplicative spread**: the threshold cannot be met by concentrating on one
prime tower; the family must spread across multiplicatively-independent bases.

### Audit of known-complete admissible families (every one has the spread)

| D | ∑1/(d−1) | gcd | max mass on a single prime's powers | spread off it |
|---|---|---|---|---|
| (3,4,7) | 1 | 1 | 0.500 (p=3) | ≥ 0.500 |
| (3,4,5) | 13/12 | 1 | 0.500 (p=3) | ≥ 0.583 |
| (3,5,7,13) | 1 | 1 | 0.500 (p=3) | ≥ 0.500 |
| (3,4,10,19) | 1 | 1 | 0.500 (p=3) | ≥ 0.500 |
| (3,5,6,21) | 1 | 1 | 0.500 (p=3) | ≥ 0.500 |
| (3,4,9,25) | 1 | 1 | 0.625 (p=3) | ≥ 0.375 |

## Why this matters for Q2 (the deep reason the conjecture is plausibly TRUE)

My converse mechanism (`density_pomerance_converse_constructive.md`) shows the binding obstruction
to completeness lives at powers of d_min, and is defeated by (i) enough max-reach mass and
(ii) multiplicatively-independent bases that supply, via Weyl equidistribution, residue coverage
that fills the d_min-power shadow. Melfi's pathology is exactly the FAILURE of (ii): a
prime-power-collinear family has no equidistribution (the alignments are periodic, perpetually
worst-case) and no coprime base to fix residues.

**This lemma shows the harmonic threshold ∑1/(d−1) ≥ 1 STRUCTURALLY RULES OUT Melfi's pathology
for every admissible D.** The forced multiplicative spread (≥ 0.318 off any prime tower) is
precisely the ingredient that makes the equidistribution argument applicable and the residue
coverage available. So the threshold is not just a counting bound — it is the exact condition that
guarantees the bases are multiplicatively spread enough for the covering mechanism to work. This is
a candidate for the "deep reason Q2 is TRUE" scholar asked for: combined with modular's residue
lemma (gcd=1 ⇒ all residues) and maverick's (SEED), the open problem reduces to making the
"spread ⇒ no surviving nested gap" step uniform — the transcendence core.

## Caveat / honest scope
This rules out PURE collinearity and bounds single-prime concentration. It does NOT rule out
families with a large (but sub-threshold) collinear SUBSET plus coprime bases — but those, by the
quantitative bound, must still carry ≥ 1−T_p of mass on a spread part. Whether that spread part
ALWAYS suffices for completeness is exactly Q2 (and is the transcendence question, not settled
here). The contribution is: the threshold provably forces the spread; it does not by itself prove
the spread is sufficient.
