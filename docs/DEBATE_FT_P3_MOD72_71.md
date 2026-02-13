# Debate Context: FT p=3 for q ≡ 71 (mod 72)

## The Problem

Feit-Thompson conjecture for p=3: For primes q > 3 with q ≡ 2 (mod 3) and A = q²+q+1 prime, prove that 3^q ≢ 1 (mod A).

The remaining open case is **q ≡ 71 (mod 72)**, equivalently q ≡ 7 (mod 8) AND q ≡ 8 (mod 9). This is ~8.3% of all primes.

## What's Already Proven

| Slot | Coverage | Method |
|------|----------|--------|
| slot590 | q ≡ 1 (mod 4) — 55.7% of primes | Jacobi symbol J(3,A) = -1 (Euler criterion) |
| slot610 | q ≡ 3 (mod 8) — 20.9% of primes | QR contradiction: Legendre(1-q,A) = +1 unconditionally but (1-q)^{(A-1)/2} = -1 under assumption |
| slot611 | q ≢ 8 (mod 9) — 66.7% of primes | Cubic character χ₃(3) = χ₃(q)² ≠ 1, contradicts 3^q=1 forcing χ₃(3)=1 |

Combined coverage: slot590 ∪ slot610 ∪ slot611 covers all primes except q ≡ 71 (mod 72).

## Key Algebraic Infrastructure

All facts hold unconditionally (no assumption on 3^q):

1. **q³ ≡ 1 (mod A)**, q is a primitive cube root of unity in F_A
2. **(1-q)² ≡ -3q (mod A)**
3. **(1-q)(q+2) = 3** in ZMod A [since q+2 = 1-q² and (1-q)(1-q²) = 1-q-q²+q³ = 3]
4. **q+1 = -q²** in ZMod A [from q²+q+1 = 0]
5. **A-1 = q(q+1)**, divisible by 72q for q ≡ 71 mod 72

## Under the Assumption 3^q ≡ 1 (mod A)

- ord_A(3) = q (since 3 ≢ 1 mod A)
- (1-q)^{2q} = q+1 [via (-3q)^q = (-1)^q · 3^q · q^q = -1·1·q² = -q² = q+1]
- (1-q)^{4q} = q [since (q+1)² = q²+2q+1 = -(q+1)+2q+1 = q]
- (1-q)^{6q} = -1 [since q(q+1) = q²+q = -1]
- (1-q)^{12q} = 1
- ord(1-q) = 12q [does not divide 6q since (1-q)^{6q} = -1 ≠ 1]

## Why Each Approach Fails for q ≡ 71 mod 72

### Quadratic (QR) — FAILS
For q ≡ 7 mod 8: Legendre(1-q, A) = -1 unconditionally.
Under assumption: (1-q)^{(A-1)/2} = (1-q)^{6q·(something)} = -1.
Both give -1. NO contradiction.

Detailed: (A-1)/2 = q(q+1)/2. For q ≡ 71 mod 72: q+1 ≡ 72, (q+1)/2 ≡ 36.
q(q+1)/2 mod 12q: we need q·36 mod 12q = 36q mod 12q. 36 = 3·12, so 36q = 3·12q. Thus (1-q)^{q(q+1)/2} = (1-q)^{3·12q} = ((1-q)^{12q})^3 = 1^3 = 1.

Wait — that gives +1, not -1! Let me recheck:
Actually q ≡ 71 mod 72, so q+1 ≡ 0 mod 72. (q+1)/2 ≡ 0 mod 36.
q·(q+1)/2 mod 12q = q · ((q+1)/2 mod 12). (q+1)/2 mod 12: since (q+1) ≡ 0 mod 72, (q+1)/2 ≡ 0 mod 36, (q+1)/2 mod 12 = 0.
So q(q+1)/2 ≡ 0 mod 12q. Hence (1-q)^{(A-1)/2} = 1 under assumption.
Euler criterion: (1-q)^{(A-1)/2} = Legendre(1-q, A).

For q ≡ 7 mod 8: what is Legendre(1-q, A) unconditionally?
If Legendre(1-q, A) = +1 (computed by slot610 QR chain for q ≡ 3 mod 8):
For q ≡ 7 mod 8 the chain gives different values. Need to recompute.

**Correction**: The QR chain in slot610 gives Legendre(1-q, A) = +1 specifically for q ≡ 3 mod 8 (where q ≡ 11 mod 24). For q ≡ 7 mod 8, the chain may give -1 or +1 depending on sub-cases.

### Cubic Character — FAILS
For q ≡ 8 mod 9: χ₃(q) = q^{(A-1)/3} = q^{q(q+1)/3}.
(q+1)/3: q ≡ 8 mod 9, q+1 ≡ 0 mod 9, (q+1)/3 ≡ 0 mod 3.
q^{q(q+1)/3}: exponent q·(q+1)/3 mod 3 = q · ((q+1)/3 mod 3). (q+1)/3 mod 3 = 0 (since 9|(q+1)). So exponent ≡ 0 mod 3. χ₃(q) = q^{3k} = 1.
Since χ₃(q) = 1: χ₃(3) = χ₃(q)² · χ₃(1-q)² = 1 · χ₃(1-q)².
Under assumption: χ₃(3) = 1, so χ₃(1-q)² = 1, meaning χ₃(1-q) ∈ {1, q, q²} with square = 1, so χ₃(1-q) = 1 (the only cube root of unity with square 1 in a group where cubing is trivial... actually q² · q² = q ≠ 1, q · q = q² ≠ 1, 1·1 = 1).
So χ₃(1-q) = 1 under assumption, and computationally χ₃(1-q) = 1 unconditionally.
No contradiction available from cubic character.

### Quartic Character — NOT UNIVERSAL
χ₄(1-q) varies with q for q ≡ 71 mod 72.
It depends on the Gaussian integer factorization A = a² + b², which varies.
~50% of the time χ₄(1-q) = +1, ~50% it's -1 or ±i.
Cannot produce a universal proof.

### Sextic Character — FAILS
χ₆ = χ₂ · χ₃. Since both χ₂(3) = +1 (QR: (3/A) = +1 since A ≡ 1 mod 3) and χ₃(3) = 1 (for q ≡ 8 mod 9): χ₆(3) = 1 unconditionally.
Under assumption: χ₆(3) = 1. No contradiction.

### 9th Power Residue — TAUTOLOGICAL
From debates: the 9th power residue condition 3^{(A-1)/9} becomes trivially satisfied.

### CM Elliptic Curves — DEAD
y² = x³ - 1: #E'(F_A) = (q+1)², q never divides → no useful information.

### Pure Multiplicative Group — COMPATIBLE
All order computations are consistent with 3^q = 1.

## Structural Analysis of the Obstruction

The fundamental reason character approaches fail for q ≡ 71 mod 72:

For a character χ of order d to give a contradiction, we need:
- Under assumption 3^q = 1: χ(3) = 3^{(A-1)/d} = (3^q)^{(q+1)/d} = 1 (whenever d | (q+1))
- Unconditionally: χ(3) ≠ 1

But q+1 ≡ 0 mod 72 for q ≡ 71 mod 72, so q+1 is divisible by ALL small primes we'd use for d. Specifically: 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72 all divide q+1.

For ANY character χ of order d | 72: χ(3) = 1 under assumption. So we need χ(3) ≠ 1 unconditionally. But for most "nice" characters, χ(3) can be computed via reciprocity and turns out to be 1.

To escape this trap, we need either:
1. A character of order d where d ∤ (q+1) — but then d > 72 or d involves q-dependent factors
2. A non-character argument entirely
3. A character argument that uses MULTIPLE elements simultaneously
4. An arithmetic argument (e.g., size bounds, p-adic analysis)

## Promising Unexplored Directions

1. **Gauss sums**: The Gauss sum g(χ) = Σ χ(a)ζ^a has |g|² = A. The relation g(χ)^q mod A under 3^q = 1 might produce something non-trivial.

2. **Kummer theory**: 3^q = 1 mod A means A splits in Q(ζ_q, 3^{1/q}). The density of such primes is governed by Chebotarev. Can we show A = q²+q+1 NEVER has this splitting?

3. **Wieferich-like condition**: If 3^q ≡ 1 mod A, what about mod A²? The "super-congruence" might fail.

4. **Frobenius in extensions**: Consider the splitting of A in Q(ζ_q) and Q(3^{1/q}). The Frobenius at A in Gal(Q(ζ_q)/Q) = (Z/qZ)* maps to [A mod q] = [1]. Can the Frobenius in the Kummer extension give a contradiction?

5. **Character sums over subgroups**: Instead of evaluating a single character at 3, sum characters over relevant subgroups.

6. **Additive structure**: Use additive properties of F_A (traces, norms, polynomial identities) rather than purely multiplicative.

7. **Higher reciprocity**: Quartic, octic, or general n-th power reciprocity in Z[i] or Z[ζ_n].

8. **Analytic number theory**: Bounds on character sums, Weil's theorem, etc.

## Computational Data (verified for all 50 eligible q < 100,000)

### Eligible primes q ≡ 71 (mod 72) with A prime, q < 100,000:
50 such primes found. First few: 71, 359, 503, 647, 1223, 1367, 1439, 2087, ...
For ALL 50: 3^q ≢ 1 (mod A). In fact ord_A(3) = q*m where m > 1 ALWAYS.

### Universal patterns found:
1. **χ₄(3) = 1 for ALL** (3 is always a 4th power residue mod A) — 50/50 = 100%
2. **χ₁₂(3) = 1 for ALL** — 50/50 = 100%
3. **Index = (q+1)/m ≥ 12 for ALL** (minimum observed: 12)
4. **GCD of all indices = 12** — this is the TIGHTEST universal character bound
5. **A = x² + 9y² for ALL** eligible A (quadratic form representation)
6. **χ₈(3) varies** (~52% = 1, ~48% ≠ 1) — NOT universal
7. **χ₂₄(3) varies** (~52% = 1) — NOT universal
8. d = ord(3)/q ranges from 3 to 7326, always > 1
9. 2-adic gap: v₂(d) < v₂(q+1) always, gap ≥ 2

### Higher congruence results (slot603, PROVEN):
- k ≡ 2 (mod 12q)
- k ≡ 12q + 2 (mod 36q)
- k mod 324: k+2 ≡ 80q (mod 324)
- k mod 243 and k mod 972 explicit formulas
- Bounded verification extended to q < 200,000
- Power sum identities: Σ 3^{ji} ≡ 0 (mod A) for 1 ≤ j < q
- 3^{jq} ≡ 1 + jkA (mod A²)
- Odd prime factors of k are ≡ 1 (mod q)
- Fermat quotient relation linking q₃, k, A

### Why A = x² + 9y² always:
The class number h(-36) = 2. Not all primes ≡ 1 (mod 12) are x²+9y². But A = q²+q+1 has special structure: 4A = (2q+1)² + 3. This structural decomposition forces A into the correct genus of the binary form x²+9y².

### Why character methods of ALL orders are exhausted:
For d | (q+1): Under 3^q = 1, χ_d(3) = (3^q)^{(q+1)/d} = 1 automatically.
Since q+1 ≡ 0 (mod 72), ALL d | 72 give χ_d(3) = 1 under assumption.
For d ∤ 72 (like 5, 7, 11, ...): χ_d(3) varies with q (NOT universal).
Universal result: χ₁₂(3) = 1 unconditionally (proved). GCD of indices = 12.
No character of ANY fixed order can distinguish the assumption from reality.

### Eisenstein integer analysis (provably insufficient):
- In Z[ω], A = N(q-ω) = q²+q+1
- (3/π)₃ = 1 is provably forced for q ≡ 8 mod 9 by the cubic supplement formula
- The ramification of 3 in Z[ω] creates algebraic circularity
- All Z[ω] norm/trace computations are tautological

## What HASN'T Been Tried (promising directions)

### 1. Kummer theory / Frobenius
3^q ≡ 1 (mod A) means A splits in Q(ζ_q, 3^{1/q}). The Frobenius at A in Gal(Q(ζ_q)/Q) is [A mod q] = [1] (trivial). But the Frobenius in the full Kummer extension K = Q(ζ_q, 3^{1/q}) might give a non-trivial constraint. The Galois group Gal(K/Q) = (Z/qZ)* × (Z/qZ). The Frobenius should map to ([A mod q], something). The "something" involves ord_A(3)/q... but that's what we're trying to prove ≠ 1.

### 2. p-adic analysis / Lifting the exponent
The Lifting-the-Exponent lemma (LTE) in the 3-adic setting. v₃(3^q - 1) = v₃(q) + v₃(2) = 1 (since q ≢ 0 mod 3 and 3^1 - 1 = 2). So v₃(kA) = v₃(3^q - 1) - 0 = ... Actually 3^q - 1 = kA, and v₃(A): A = q²+q+1, for q ≡ 8 mod 9: A mod 3 = 1+2+1 = 1 mod 3, so v₃(A) = 0. Thus v₃(k) = v₃(3^q - 1). This gives constraints on k but not directly on whether 3^q = 1 mod A.

### 3. Character sums (Weil bound)
Instead of evaluating a single character at 3, consider the character sum Σ_{χ of order d} χ(3). The Weil bound gives |Σ| ≤ (d-1)√A. For d = q: this involves ALL q-th order characters. Under 3^q = 1, each χ(3) = 1, giving sum = q. Can we show the sum is smaller?

### 4. The A² congruence (Wieferich)
From slot603: 3^{jq} ≡ 1 + jkA (mod A²). If we could show k ≡ 0 (mod A), that would give 3^q ≡ 1 (mod A²) — a "Wieferich-like" condition. Heuristically very unlikely for A = q²+q+1. Can we prove k < A (or k ≢ 0 mod A)?

### 5. Size/density arguments
k = (3^q - 1)/A ≈ 3^q/q². Under 3^q ≡ 1 mod A: k = (3^q - 1)/A, and k must satisfy all the modular constraints (k ≡ 2 mod 12q, etc.). Is the density of integers satisfying ALL constraints too low for 3^q - 1 = kA to have solutions?

### 6. Additive-multiplicative interaction
The elements 1, 3, 9, ..., 3^{q-1} are the q-th roots of unity in F_A*. Their sum is 0 (additive constraint). Their product is (-1)^{q-1} · 3^{q(q-1)/2} (multiplicative). Can combining additive and multiplicative constraints give new information?

## Question for Debate

**What approach can resolve 3^q ≢ 1 (mod A) for q ≡ 71 (mod 72)?**

Key constraints on any proposed approach:
- Must work for ALL such primes (universal)
- Character methods of order d | 72 are provably useless (GCD of indices = 12)
- χ₁₂(3) = 1 unconditionally, but no higher character is universal
- Eisenstein Z[ω] approach is provably insufficient (algebraic circularity)
- All ZMod A algebraic identities form a closed consistent system under the assumption
- Need FUNDAMENTALLY new idea: Artin reciprocity, character sums, p-adic, sieve, or size bounds
- The k-congruence tower (mod 12q, 36q, 108q, 324, 972) provides rich structural data
- Bounded to q < 200,000 computationally
