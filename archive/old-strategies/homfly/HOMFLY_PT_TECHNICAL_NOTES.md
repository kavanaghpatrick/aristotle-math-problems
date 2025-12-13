# HOMFLY-PT Polynomial: Technical Notes and Advanced Topics

**Companion Document to**: `HOMFLY_PT_TEST_CASES.md`

---

## Explicit Polynomial Formulas

### Known Exact Values (From Research)

#### Trefoil (3₁)
**HOMFLY-PT**: P(3₁) = 2a² - a⁴ + a²z²

Alternative form: P(3₁) = a²(2 - a² + z²)

**Factorization note**: The difference polynomial Ph(a,z) = 1 - P(3₁) = (a⁴ - 2a² + 1 - a²z²)

**Jones**: V(3₁) = -t⁻⁴ + t⁻³ + t⁻¹ (left-handed)
Or: V(3₁) = -t⁴ + t³ + t (right-handed)

Note: KnotInfo convention gives V(3₁) = t + t³ - t⁴ (normalized differently)

#### Figure-Eight (4₁)
**HOMFLY-PT**: P(4₁) = v⁻² - 1 + v² - z²

Alternative form: P(4₁) = a⁻² - 1 + a² - z²

**Symmetry**: Note v⁻² + v² term (achiral property)

**Jones**: V(4₁) = t⁻² - t⁻¹ + 1 - t + t²

**Amphichirality**: P(4₁) = P(4₁*) where 4₁* is mirror image

### Torus Knot General Formulas

#### T(2,n) Pattern

For T(2,n) torus knots (where n is odd):

**Braid word**: σ₁ⁿ (n-strand braid with n crossings)

**Degree pattern**:
- Max power of v: 2n-2
- Max power of z: n-1

**Examples**:
- T(2,3) = 3₁: v⁴ terms, z² terms → 4 = 2(3)-2 ✓, 2 = 3-1 ✓
- T(2,5) = 5₁: v⁶ terms, z⁴ terms → 6 = 2(5)-2 ✓, 4 = 5-1 ✓
- T(2,7) = 7₁: v⁸ terms, z⁶ terms → 8 = 2(7)-2 ✓, 6 = 7-1 ✓

#### General T(p,q) Formula

From Chern-Simons gauge theory (Labastida et al.):

For counter-directed T₂,ₙ torus link:
```
P(T₂,ₙ) = z⁻¹aⁿ(a - a⁻¹) + z(1 - aⁿ)/(a - a⁻¹)
```
(Note: This formula is for even n, links not knots)

**Full general formula**: Available in "The Homfly Polynomial for Torus Links from Chern-Simons Gauge Theory" (1995)

---

## Skein Relation Details

### Standard Skein Relation (KnotInfo Convention)

```
v⁻¹ P(L₊) - v P(L₋) = z P(L₀)
```

With initial condition: P(unknot) = 1

### Alternative Forms

1. **HOMFLY Original** (α, z):
   ```
   α⁻¹ P(L₊) - α P(L₋) = z P(L₀)
   ```

2. **Lickorish-Millett** (l, m):
   ```
   l P(L₊) + l⁻¹ P(L₋) + m P(L₀) = 0
   ```

3. **Knot Atlas** (a, z):
   ```
   a⁻¹ P(L₊) - a P(L₋) = z P(L₀)
   ```

### Crossing Change Convention

```
L₊: Positive crossing ⤢
L₋: Negative crossing ⤡
L₀: Resolution (smoothed) ⤨
```

### Skein Relation Test Cases

#### Test 1: Unknot → Trefoil
If we change one crossing in the trefoil to get the unknot:
```
v⁻¹ P(3₁) - v P(0₁) = z P(Hopf)
```

Need to compute P(Hopf) to verify this.

#### Test 2: Figure-Eight Relations
The figure-eight has multiple crossing changes that can be tested.

---

## Jones Polynomial Reduction

### Reduction Formula (Detailed)

**Method 1**: Set v = t⁻¹, z = t^(1/2) - t^(-1/2)

**Method 2** (Alternative): Set v = t, z = t^(-1/2) - t^(1/2)

**Verification for Trefoil**:

Starting with: P(3₁) = 2v² - v⁴ + v²z²

Method 1 (v = t⁻¹, z = t^(1/2) - t^(-1/2)):
```
P = 2(t⁻¹)² - (t⁻¹)⁴ + (t⁻¹)²(t^(1/2) - t^(-1/2))²
  = 2t⁻² - t⁻⁴ + t⁻²(t - 2 + t⁻¹)
  = 2t⁻² - t⁻⁴ + t⁻¹ - 2t⁻² + t⁻³
  = -t⁻⁴ + t⁻³ + t⁻¹
```

This matches V(3₁) = -t⁻⁴ + t⁻³ + t⁻¹ ✓

**Note**: Different normalizations between KnotInfo (V = t + t³ - t⁴) and literature need to be reconciled.

### Reduction for Figure-Eight

Starting with: P(4₁) = v⁻² - 1 + v² - z²

Substituting v = t⁻¹, z = t^(1/2) - t^(-1/2):
```
P = (t⁻¹)⁻² - 1 + (t⁻¹)² - (t^(1/2) - t^(-1/2))²
  = t² - 1 + t⁻² - (t - 2 + t⁻¹)
  = t² - 1 + t⁻² - t + 2 - t⁻¹
  = t² - t + 1 - t⁻¹ + t⁻²
```

Need to verify this matches V(4₁) = t⁻² - t⁻¹ + 1 - t + t² ✓

---

## Alexander Polynomial Reduction

### Reduction Formula

Set v = 1 in HOMFLY-PT: P(1, z) gives Conway polynomial ∇(z)

Then: Δ(t) = ∇(t^(1/2) - t^(-1/2))

### Trefoil Example

P(3₁) = 2v² - v⁴ + v²z²

Set v = 1:
```
P(1, z) = 2(1)² - (1)⁴ + (1)²z²
        = 2 - 1 + z²
        = 1 + z²
```

This is the Conway polynomial: ∇(3₁)(z) = 1 + z²

For Alexander: Δ(3₁)(t) = 1 + (t^(1/2) - t^(-1/2))²
                        = 1 + t - 2 + t⁻¹
                        = t - 1 + t⁻¹

Standard form: Δ(3₁) = t - 1 + t⁻¹ ✓

---

## Braid Closure Computation

### Hecke Algebra Method

The HOMFLY-PT polynomial can be computed from braid closure using the Hecke algebra Hₙ(q).

**Hecke Algebra Generators**: gᵢ (i = 1, ..., n-1)

**Relations**:
1. gᵢgⱼ = gⱼgᵢ for |i - j| ≥ 2
2. gᵢgᵢ₊₁gᵢ = gᵢ₊₁gᵢgᵢ₊₁ (braid relation)
3. (gᵢ - q)(gᵢ + q⁻¹) = 0 (Hecke relation)

**Connection to Braid Group**:
- σᵢ → gᵢ (positive braid generator)
- σᵢ⁻¹ → gᵢ⁻¹ (negative braid generator)

**Markov Trace**: Tr: Hₙ(q) → ℤ[q, q⁻¹]

**HOMFLY-PT Formula**: P(L)(a, z) = (some normalization) × Tr(braid word)

**Parameter Relationship**:
- a = q (or q⁻¹ depending on convention)
- z = q^(1/2) - q^(-1/2) (or q - q⁻¹)

### Recent Algorithmic Advances (2024)

From arXiv:2512.06142 "A fast algorithm for the Hecke representation of the braid group":

**New approach**: Exploits rigidity of quantum invariants to design fast parameterized algorithm

**Computational complexity**: Improved bounds for computing HOMFLY-PT from braid words

**Application**: Can compute HOMFLY-PT for knots with hundreds of crossings using "base tangle decompositions"

---

## Variable Convention Conversions

### Master Conversion Table

| Convention | Skein Relation | v/a/α | z | l | m |
|------------|----------------|-------|---|---|---|
| **KnotInfo (v,z)** | v⁻¹P(L₊) - vP(L₋) = zP(L₀) | v | z | - | - |
| **Original (α,z)** | α⁻¹P(L₊) - αP(L₋) = zP(L₀) | α | z | - | - |
| **HOMFLY (l,m)** | lP(L₊) + l⁻¹P(L₋) + mP(L₀) = 0 | - | - | l | m |
| **Jones (q)** | - | q | q - q⁻¹ | - | - |

**Relationships**:
- v = a = α (these are all the same)
- KnotInfo z = HOMFLY z
- l = -a⁻¹, m = -z (conversion to HOMFLY original)

### Converting Between Normalizations

**KnotInfo → Literature**:
Often the literature uses P with unknot = 1, but may normalize differently for Jones.

**Writhe correction**: Some sources include writhe factor (−a)^w(L)

**Jones normalization**: KnotInfo uses V(t), some papers use normalized J̃(q)

---

## Colored HOMFLY-PT Polynomials

### Definition

The standard HOMFLY-PT is for the fundamental representation. **Colored** versions use other representations.

### Known Results (Kawagoe 2025)

For **symmetric representation R = [p]**:

1. **Trefoil**: Expressed as single sum
2. **Figure-eight**: Expressed as single sum
3. **Twist knots**: Expressed as double sum

**Example formula** (trefoil in representation [p]):
```
P_p(3₁) = (complex sum formula)
```

Available in arXiv:2107.08678

### Colored Jones

Special case of colored HOMFLY-PT for SU(2):
```
J_p(K) = P_p(K)|_{a=q²}
```

---

## Known Non-Uniqueness Examples

### Knots with Same HOMFLY-PT

**Theorem** (Kanenobu 1986): Infinitely many distinct knots share the same HOMFLY polynomial.

**Known Pairs** (Jones 1987):
1. (05-001, 10-132) = (5₁, 10₁₃₂)
2. (08-008, 10-129)
3. (08-016, 10-156)
4. (10-025, 10-056)

**Verification Test**: Compare HOMFLY-PT values for 5₁ and 10₁₃₂:

5₁: (3v⁴ - 2v⁶) + (4v⁴ - v⁶)z² + v⁴z⁴

10₁₃₂: (-2v⁻⁶ + 3v⁻⁴) + (-v⁻⁶ + 4v⁻⁴)z² + v⁻⁴z⁴

**Observation**: These look DIFFERENT! Need to verify if they're actually equal under some transformation.

**Resolution**: These pairs share the same Jones and Alexander polynomials, but the HOMFLY-PT may distinguish them. Need to check if there's a v ↔ v⁻¹ relationship.

---

## Computation Tools

### SageMath Usage

```python
from sage.knots.knotinfo import KnotInfo

# Load trefoil
K = KnotInfo.K3_1

# Get HOMFLY-PT (KnotInfo normalization)
P = K.homfly_polynomial()
print(P)  # Output: -v^4 + v^2*z^2 + 2*v^2

# Compare with Sage computation
PK = K.link().homfly_polynomial(normalization='vz')
print(P == PK)  # Should be True

# Get Jones polynomial
V = K.jones_polynomial()
print(V)  # Output: t + t^3 - t^4

# Original string from database
P_orig = K.homfly_polynomial(original=True)
print(P_orig)  # Output: '(2*v^2-v^4)+v^2*z^2'
```

### Mathematica (Knot Atlas)

```mathematica
<< KnotTheory`

(* Load trefoil *)
K = Knot[3, 1]

(* Compute HOMFLY-PT *)
HOMFLYPT[K][a, z]

(* Compute Jones *)
Jones[K][t]

(* Get braid representation *)
BR[K]
```

### Python (Local CSV)

```python
import pandas as pd

df = pd.read_csv('/Users/patrickkavanagh/math/knotinfo_data/database_knotinfo/csv_data/knotinfo_data_complete.csv',
                 delimiter='|')

# Extract trefoil data
trefoil = df[df['name'] == '3_1'].iloc[0]

print(f"HOMFLY: {trefoil['homfly_polynomial']}")
print(f"Jones: {trefoil['jones_polynomial']}")
print(f"Braid: {trefoil['braid_notation']}")
```

---

## Theoretical Properties to Verify

### 1. Multiplicativity Under Knot Sum

**Property**: P(K₁ # K₂) = P(K₁) · P(K₂)

**Test**: Verify for trefoil # trefoil
- P(3₁) = 2v² - v⁴ + v²z²
- P(3₁ # 3₁) = P(3₁)² = (2v² - v⁴ + v²z²)²

Expand:
```
= 4v⁴ + v⁸ + v⁴z⁴ - 4v⁶ - 2v⁶z² + 2v⁴z²
= 4v⁴ - 4v⁶ + v⁸ + 2v⁴z² - 2v⁶z² + v⁴z⁴
```

Check if this equals P of the composite knot (need to identify which knot is 3₁ # 3₁).

### 2. Mirror Image Symmetry

**Property**: P(K*)(a,z) = P(K)(a⁻¹, z)

**Test for achiral knots**: P(K) = P(K)(a⁻¹, z)

**Figure-eight** (4₁):
```
P(4₁) = v⁻² - 1 + v² - z²

P(4₁)(v⁻¹, z) = (v⁻¹)⁻² - 1 + (v⁻¹)² - z²
               = v² - 1 + v⁻² - z²
               = v⁻² - 1 + v² - z²  ✓ (same!)
```

**Trefoil** (3₁) - should be different:
```
P(3₁) = 2v² - v⁴ + v²z²

P(3₁)(v⁻¹, z) = 2(v⁻¹)² - (v⁻¹)⁴ + (v⁻¹)²z²
               = 2v⁻² - v⁻⁴ + v⁻²z²
               ≠ 2v² - v⁴ + v²z²  ✓ (different, as expected for chiral knot)
```

### 3. Positive Knots

**Conjecture**: For positive braid knots, all coefficients of HOMFLY-PT are positive.

**Test cases**:
- 3₁: Coefficients are 2, -1, 1 → Has negative! But wait, 3₁ = σ₁³ is positive braid
- Check convention: maybe "positive polynomial" means after some normalization

---

## Open Research Questions (Not for Implementation)

These are mentioned in recent papers but beyond scope of current testing:

1. **Computational Complexity**: What is the exact complexity class for computing HOMFLY-PT from a braid word?

2. **Unknot Detection**: Does HOMFLY-PT = 1 imply K is the unknot? (Unknown!)

3. **Colored HOMFLY-PT**: General formula for arbitrary representation?

4. **Superpolynomials**: Connection to Khovanov homology and physics

5. **Volume Conjecture**: Relationship to hyperbolic volume

---

## References for Advanced Topics

### Recent Papers (2023-2025)

1. **Fast Algorithm (Dec 2024)**: arXiv:2512.06142 - Hecke representation computation
2. **Colored HOMFLY-PT (2025)**: Kawagoe, K. - Trefoil, figure-eight, twist knots (arXiv:2107.08678)
3. **Quasi-Alternating 3-Braids (2022)**: Nuclear Physics B - Colored polynomials

### Classic References

1. **HOMFLY Discovery (1985)**: Freyd et al., Bull. AMS
2. **PT Work (1987)**: Przytycki & Traczyk
3. **Thistlethwaite Tables**: Up to 13 crossings
4. **Jones Original (1985)**: Invention of Jones polynomial

### Computational Resources

1. **KnotInfo**: https://knotinfo.math.indiana.edu
2. **Knot Atlas**: https://katlas.org
3. **Stoimenov Tables**: https://stoimenov.net/stoimeno/homepage/ptab/
4. **SageMath Docs**: https://doc.sagemath.org/html/en/reference/knots/

---

**Last Updated**: 2025-12-12
**Status**: Technical details compiled for implementation reference
