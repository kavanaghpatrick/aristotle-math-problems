# Feit-Thompson p=3 Proof: Strategy Debate Context

## The Problem

The Feit-Thompson conjecture states: for distinct primes p, q,
gcd((p^q - 1)/(p - 1), (q^p - 1)/(q - 1)) = 1

For p=3: we need to show A(q) = q²+q+1 does NOT divide Φ_q(3) = (3^q-1)/2 for all primes q > 3.

This is an OPEN problem. No complete proof exists in the literature.

## What We've Proven (Formally Verified in Lean 4, 0 sorry, 0 axiom)

### slot560 (345 lines) — General + p=2
- p=2 case: fully proven unconditionally
- Prime divisor congruence: any prime r | gcd(Φ_p(q), Φ_q(p)) satisfies r ≡ 1 (mod pq)
- Cyclotomic congruence: Φ_p(q) | Φ_q(p) → Φ_p(q) ≡ 1 (mod pq)
- Size bound: q^{p-1} < p^q via Jacobi symbols and MVT

### slot590 (437 lines) — p=3 case
PROVEN UNCONDITIONALLY:
1. A(q) is prime if A | (3^q-1)/2
2. q ≡ 2 (mod 3) if A | (3^q-1)/2
3. **q ≡ 1 (mod 4) case FULLY RESOLVED**: Jacobi(3,A) = -1 when q ≡ 1 (mod 4), q ≡ 2 (mod 3). By Euler's criterion: 3^{(A-1)/2} ≡ -1 (mod A). But if 3^q ≡ 1, then 3^{(A-1)/2} = (3^q)^{(q+1)/2} = 1 ≠ -1. Contradiction.
4. If 3^q ≡ 1 (mod A) and q ≡ 2 (mod 3), then 3 IS a cubic residue mod A. Proof: 3^{(A-1)/3} = (3^q)^{(q+1)/3} = 1 (since 3 | (q+1)).
5. Bounded verification: FT conjecture holds for all q < 20,000 via native_decide
6. q is a primitive cube root of 1 in ZMod A: q³ ≡ 1 (mod A), q ≢ 1 (mod A)

PROVEN CONDITIONAL ON CubicReciprocityLaw:
7. q ≡ 3 (mod 4), q ≢ 8 (mod 9): 3 is NOT a cube mod A → contradiction with #4

OPEN GAP:
8. q ≡ 8 (mod 9): 3 IS a cube mod A, so cubic reciprocity gives no contradiction

## The Two Remaining Gaps

### Gap 1: Remove the Cubic Reciprocity assumption
The proof for q ≡ 3 (mod 4), q ≢ 8 (mod 9) currently ASSUMES the Cubic Reciprocity Law:
```
def CubicReciprocityLaw : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (hp1 : p ≡ 1 [MOD 3])
  (a b : ℤ) (h_rep : 4 * p = (2 * a - b)^2 + 3 * b^2) (h_prim : IsPrimaryEisenstein a b),
  IsCube (3 : ZMod p) ↔ b ≡ 0 [ZMOD 9]
```
Cubic reciprocity is NOT in Mathlib. To make this unconditional, we need to either:
(a) Prove CR from scratch (requires Eisenstein integers Z[ω], not in Mathlib)
(b) Prove the specific case needed directly (3 is not a cube mod A when 9 ∤ (q+1))
(c) Find an entirely different approach that avoids CR

### Gap 2: The q ≡ 8 (mod 9) subcase
When q ≡ 8 (mod 9), 3 IS a cubic residue mod A. So the argument from #4+#7 gives no contradiction.
This is genuinely hard — we need a fundamentally different approach.

Key constraints for this case:
- q ≡ 35 (mod 36) (combining q ≡ 2 mod 3, q ≡ 3 mod 4, q ≡ 8 mod 9)
- A-1 = q(q+1) with 9q | A-1
- First examples: q = 71, 107, 179, 251, 359, ...
- 3 is a cube, QR, quartic residue, 6th power residue — ALL standard power residue characters give χ(3) = 1

## Key Mathematical Structure

In ZMod A:
- q² ≡ -q-1 (mod A)
- q³ ≡ 1 (mod A) — q is a primitive cube root of unity
- q^{-1} ≡ -(q+1) (mod A)
- (Z/AZ)* is cyclic of order q(q+1)
- Under assumption 3^q ≡ 1: ord_A(3) = q, and 3 generates the unique subgroup of order q
- 3 = g^{(q+1)m} where g generates (Z/AZ)* and gcd(m,q) = 1
- 3^{q+1} ≡ 3 (mod A) (direct consequence of 3^q = 1)

## What Approaches Have Been Tried/Considered

### For Gap 1 (removing CR):
- Direct computation of χ₃(3) = 3^{(A-1)/3} — requires computing 3^{q(q+1)/3} mod A
- Eisenstein integer structure: Z[ω]/(π) ≅ Z/AZ where π = q - ω, ω = primitive cube root of 1
- The cubic residue symbol involves (1-ω)/π decomposition
- Native_decide bounded verification works but isn't a proof for all q

### For Gap 2 (q ≡ 8 mod 9):
- Higher power residue characters (6th, 9th, q-th): ALL give χ = 1 under assumption 3^q = 1
- Lifting the exponent: v_A(Φ_q(3)) = 1 when A | Φ_q(3), but this doesn't help directly
- Cyclotomic polynomial reciprocity: Φ_3(q) vs Φ_q(3) — no known contradiction
- Order-theoretic arguments: 3 generates unique order-q subgroup, consistent with group structure
- Size bounds: Φ_q(3) ≈ 3^q/2, A ≈ q² — no contradiction from sizes
- Wieferich-type conditions: A² ∤ 3^q - 1 by standard cyclotomic theory, but doesn't help

### Falsified approaches:
- CubicReciprocityCondition (too strong, false for q ≡ 8 mod 9)
- Standard QR for q ≡ 3 (mod 4): (3/A) = 1 always, no contradiction

## Research Findings on Novelty

The approach in slot590 appears to be GENUINELY NOVEL:
- The Jacobi symbol / Euler criterion technique for q ≡ 1 (mod 4) is unpublished
- The cubic reciprocity connection for q ≡ 3 (mod 4) appears original to our work
- Le Maohua (2012) proved the q=3 case, not the p=3 case (different!)
- Motose (2009, 2010) studied p=3 and p=5 but in limited form
- No formalization of ANY case of the FT conjecture existed before our work

## Aristotle's Capabilities (INFORMAL Mode)

Aristotle is a proof co-discoverer. Given a ~50-100 line natural language sketch, it:
- Constructs entire formal Lean 4 proofs from scratch (5:1 output ratio)
- Discovers Mathlib API calls autonomously
- Invents novel proof structures and lemma decompositions
- Can handle speculative/incomplete strategies and fill gaps
- Has access to full Mathlib (v4.24.0) including: ZMod, orderOf, jacobiSym, legendreSym, Polynomial.cyclotomic, Nat.Prime, native_decide
- Does NOT have: Eisenstein integers, cubic reciprocity, quintic reciprocity, algebraic number theory beyond basic cyclotomic polynomials
- Success rate on NT/algebra: ~90%+ for well-structured sketches
- Can prove deep multi-lemma results (647-line Wolstenholme, 711-line Wall-Sun-Sun)

## What We Need From This Debate

1. Mathematical strategies for closing Gap 2 (q ≡ 8 mod 9)
2. Whether Gap 1 can be closed without full CR (direct cubic non-residuacity proof)
3. Novel angles we haven't considered
4. Whether there's a completely different approach to p=3 that avoids case-splitting by q mod 4/9 entirely
5. Concrete sketch strategies that Aristotle could attempt
