# E124 k≥1: Why gcd(D)=1 is the right condition (NECESSITY proven)

**Author:** lift | **Status:** SOLID — proven + computationally verified

## Setup (verbatim-faithful)

`sumsOfDistinctPowers d k = {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑_{i∈s} d^i = x}`.

Structural identity (immediate from the definition):
```
S(d,k) := sumsOfDistinctPowers d k  =  d^k · S(d,0)
```
because every i ∈ s has i ≥ k, so d^i = d^k · d^(i-k) and the map s ↦ (i ↦ i−k) is a bijection
onto Finsets of ℕ. So **S(d,k) = d^k · {base-d 0/1 numbers}**. In particular every element of
S(d,k) is divisible by d^k.

The target sumset is `∑_{d∈D} S(d,k)` (Pointwise sum). We ask: is every large n in it?

## The obstruction that gcd=1 removes

**Claim.** If a prime p divides *every* d ∈ D, then every representable n is divisible by p
(for any k ≥ 1). Hence no n with p∤n is representable, and the conclusion (`∀ᶠ n, n ∈ sumset`)
is FALSE.

*Proof.* Each term a_d ∈ S(d,k) is divisible by d^k. If p | d then p | d^k | a_d. If this holds
for all d ∈ D, then p | ∑ a_d = n. ∎

**gcd(D)=1 ⟺ no prime divides all of D ⟺ this obstruction is absent for every prime.**

This is exactly why the k=0 statement needs NO gcd hypothesis but k≥1 does: at k=0, a_d need not
be divisible by anything (1 = d^0 ∈ S(d,0)), so the divisibility obstruction never arises.

## Computational confirmation

`/tmp/e124_gcd.py`: all-even D = {4,6,8,10,12,14,16}, ∑1/(d−1) = 1.022 ≥ 1, gcd = 2.
At k=1, window N=5000:
- total missing = 2501
- odd missing = 2500 (i.e. **every** odd number 1,3,5,…,4999 is missing)
- max even number missing = 2

So with gcd=2 the all-odd residue class is entirely absent — necessity is not just asymptotic,
it's a hard congruence wall. The conjecture's gcd(D)=1 hypothesis is exactly necessary.

## Where the open difficulty lives: is gcd=1 SUFFICIENT?

Necessity is settled. The OPEN content is sufficiency: given gcd(D)=1 and ∑1/(d−1) ≥ 1, does the
covering still go through for all k? gcd=1 kills the *global* prime obstruction, but at k≥1 each
S(d,k) lives in d^k·ℤ, so the low-order "digits" of n (mod d^k) must be assembled across DIFFERENT
d's whose d^k are coprime-ish but not aligned. The question is whether the CRT-style assembly of
low residues always succeeds for large n. That is the real lift target — see lift_sufficiency.md.
