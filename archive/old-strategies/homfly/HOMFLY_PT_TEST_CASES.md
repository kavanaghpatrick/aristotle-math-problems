# HOMFLY-PT Polynomial Test Cases for Verification

**Mission**: Comprehensive test suite with known HOMFLY-PT and Jones polynomial values for knot invariant verification.

**Data Sources**:
- [KnotInfo Database](https://knotinfo.math.indiana.edu) - Primary source for polynomial values
- [Knot Atlas](https://katlas.org) - Braid representatives and computational tools
- [Stoimenov's Knot Data Tables](https://stoimenov.net/stoimeno/homepage/ptab/) - Polynomial tables up to 10 crossings
- Local: `/Users/patrickkavanagh/math/knotinfo_data/database_knotinfo/csv_data/knotinfo_data_complete.csv`

---

## Table of Contents
1. [Core Test Suite (20 Knots)](#core-test-suite)
2. [Verification Strategy](#verification-strategy)
3. [Braid Notation Reference](#braid-notation-reference)
4. [Polynomial Relationships](#polynomial-relationships)
5. [Special Cases](#special-cases)

---

## Core Test Suite

### Table 1: Small Knots (3-7 Crossings) - HIGH PRIORITY

| Knot | Name | Xings | Alt | Braid Index | Braid Word | Unknot# | Genus |
|------|------|-------|-----|-------------|------------|---------|-------|
| 0₁ | Unknot | 0 | Y | 1 | - | 0 | 0 |
| 3₁ | Trefoil | 3 | Y | 2 | σ₁³ | 1 | 1 |
| 4₁ | Figure-eight | 4 | Y | 3 | σ₁σ₂⁻¹σ₁σ₂⁻¹ | 1 | 1 |
| 5₁ | Cinquefoil | 5 | Y | 2 | σ₁⁵ | 2 | 2 |
| 5₂ | Three-twist | 5 | Y | 3 | σ₁³σ₂σ₁⁻¹σ₂ | 1 | 1 |
| 6₁ | - | 6 | Y | 4 | σ₁²σ₂σ₁⁻¹σ₃⁻¹σ₂σ₃⁻¹ | 1 | 1 |
| 6₂ | - | 6 | Y | 3 | σ₁³σ₂⁻¹σ₁σ₂⁻¹ | 1 | 2 |
| 6₃ | - | 6 | Y | 3 | σ₁²σ₂⁻¹σ₁σ₂⁻²  | 1 | 2 |
| 7₁ | - | 7 | Y | 2 | σ₁⁷ | 3 | 3 |
| 7₂ | - | 7 | Y | 4 | σ₁³σ₂σ₁⁻¹σ₂σ₃σ₂⁻¹σ₃ | 1 | 1 |
| 7₃ | - | 7 | Y | 3 | σ₁⁵σ₂σ₁⁻¹σ₂ | 2 | 2 |

### Table 2: HOMFLY-PT Polynomial Values (v,z Convention)

**Convention**: P(unknot) = 1, skein relation: v⁻¹P(L₊) - vP(L₋) = zP(L₀)

| Knot | HOMFLY-PT Polynomial P(v,z) |
|------|----------------------------|
| **0₁** | 1 |
| **3₁** | (2v² - v⁴) + v²z² |
| **4₁** | (v⁻² - 1 + v²) - z² |
| **5₁** | (3v⁴ - 2v⁶) + (4v⁴ - v⁶)z² + v⁴z⁴ |
| **5₂** | (v² + v⁴ - v⁶) + (v² + v⁴)z² |
| **6₁** | (v⁻² - v² + v⁴) + (-1 - v²)z² |
| **6₂** | (2 - 2v² + v⁴) + (1 - 3v² + v⁴)z² - v²z⁴ |
| **6₃** | (-v⁻² + 3 - v²) + (-v⁻² + 3 - v²)z² + z⁴ |
| **7₁** | (4v⁶ - 3v⁸) + (10v⁶ - 4v⁸)z² + (6v⁶ - v⁸)z⁴ + v⁶z⁶ |
| **7₂** | (v² + v⁶ - v⁸) + (v² + v⁴ + v⁶)z² |
| **7₃** | (v⁴ + 2v⁶ - 2v⁸) + (3v⁴ + 3v⁶ - v⁸)z² + (v⁴ + v⁶)z⁴ |

### Table 3: Jones Polynomial Values (t Convention)

**Convention**: V(unknot) = 1, skein relation: t⁻¹V(L₊) - tV(L₋) = (t^(1/2) - t^(-1/2))V(L₀)

| Knot | Jones Polynomial V(t) |
|------|-----------------------|
| **0₁** | 1 |
| **3₁** | t + t³ - t⁴ |
| **4₁** | t⁻² - t⁻¹ + 1 - t + t² |
| **5₁** | t² + t⁴ - t⁵ + t⁶ - t⁷ |
| **5₂** | t - t² + 2t³ - t⁴ + t⁵ - t⁶ |
| **6₁** | t⁻² - t⁻¹ + 2 - 2t + t² - t³ + t⁴ |
| **6₂** | t⁻¹ - 1 + 2t - 2t² + 2t³ - 2t⁴ + t⁵ |
| **6₃** | -t⁻³ + 2t⁻² - 2t⁻¹ + 3 - 2t + 2t² - t³ |
| **7₁** | t³ + t⁵ - t⁶ + t⁷ - t⁸ + t⁹ - t¹⁰ |
| **7₂** | t - t² + 2t³ - 2t⁴ + 2t⁵ - t⁶ + t⁷ - t⁸ |
| **7₃** | t² - t³ + 2t⁴ - 2t⁵ + 3t⁶ - 2t⁷ + t⁸ - t⁹ |

---

## Extended Test Suite: 8-10 Crossings

### Table 4: Higher Crossing Numbers + Non-Alternating Knots

| Knot | Xings | Alt | HOMFLY-PT P(v,z) | Jones V(t) |
|------|-------|-----|------------------|------------|
| **8₁** | 8 | Y | (v⁻² - v⁴ + v⁶) + (-1 - v² - v⁴)z² | t⁻² - t⁻¹ + 2 - 2t + 2t² - 2t³ + t⁴ - t⁵ + t⁶ |
| **8₁₉** | 8 | N | (5v⁶ - 5v⁸ + v¹⁰) + (10v⁶ - 5v⁸)z² + (6v⁶ - v⁸)z⁴ + v⁶z⁶ | t³ + t⁵ - t⁸ |
| **8₂₀** | 8 | N | (-2v⁻⁴ + 4v⁻² - 1) + (-v⁻⁴ + 4v⁻² - 1)z² + v⁻²z⁴ | -t⁻⁵ + t⁻⁴ - t⁻³ + 2t⁻² - t⁻¹ + 2 - t |
| **8₂₁** | 8 | N | (3v² - 3v⁴ + v⁶) + (2v² - 3v⁴ + v⁶)z² - v⁴z⁴ | 2t - 2t² + 3t³ - 3t⁴ + 2t⁵ - 2t⁶ + t⁷ |
| **9₁** | 9 | Y | (5v⁸ - 4v¹⁰) + (20v⁸ - 10v¹⁰)z² + (21v⁸ - 6v¹⁰)z⁴ + (8v⁸ - v¹⁰)z⁶ + v⁸z⁸ | t⁴ + t⁶ - t⁷ + t⁸ - t⁹ + t¹⁰ - t¹¹ + t¹² - t¹³ |
| **10₁₂₄** | 10 | N | (7v⁸ - 8v¹⁰ + 2v¹²) + (21v⁸ - 14v¹⁰ + v¹²)z² + (21v⁸ - 7v¹⁰)z⁴ + (8v⁸ - v¹⁰)z⁶ + v⁸z⁸ | t⁴ + t⁶ - t¹⁰ |

**Note**: 8₁₉, 8₂₀, 8₂₁ are the only non-alternating prime knots with 8 crossings.

---

## Verification Strategy

### 1. Theoretical Verification Tests

#### A. HOMFLY-PT → Jones Polynomial Reduction

**Theorem**: Jones polynomial is obtained from HOMFLY-PT by:
- Method 1: v = t⁻¹, z = t^(1/2) - t^(-1/2)
- Method 2 (Alternative): v = t, z = t^(-1/2) - t^(1/2)

**Test Cases**:
1. Verify for unknot: P(1) = 1 → V(1) = 1 ✓
2. Verify for trefoil: P(2v² - v⁴ + v²z²) → V(t + t³ - t⁴)
3. Verify for figure-eight: P(v⁻² - 1 + v² - z²) → V(t⁻² - t⁻¹ + 1 - t + t²)

**Implementation**: For each test knot, compute Jones from HOMFLY-PT and compare with known value.

#### B. Skein Relation Verification

**HOMFLY-PT Skein**: v⁻¹P(L₊) - vP(L₋) = zP(L₀)

**Test Cases** (Create explicit crossing change triples):
1. Trefoil (L₊) vs Unknot (L₋) with Hopf link (L₀)
2. Figure-eight crossing changes
3. Verify for 5₁, 5₂ pairs

#### C. Knot Sum Multiplicativity

**Theorem**: P(K₁ # K₂) = P(K₁) · P(K₂)

**Test Cases**:
1. Trefoil # Trefoil = 6₁ (verify if equal)
2. Trefoil # Figure-eight (compute and verify)
3. Any composite knot in database

#### D. Mirror Image Property

**Theorem**: P(K*) = P(K)(v⁻¹, z) where K* is mirror image

**Test Cases**:
1. Trefoil 3₁ vs its mirror (3₁ is chiral, should differ)
2. Figure-eight 4₁ (amphichiral, should be equal)
3. Check all achiral knots in test set

### 2. Computational Verification Tests

#### A. Braid Closure Method

**Algorithm**:
1. Take braid word representation (e.g., σ₁³ for trefoil)
2. Compute HOMFLY-PT via Hecke algebra representation
3. Compare with known value

**Priority Test Knots**:
- 3₁: σ₁³ → (2v² - v⁴) + v²z²
- 4₁: σ₁σ₂⁻¹σ₁σ₂⁻¹ → (v⁻² - 1 + v²) - z²
- 5₁: σ₁⁵ → (3v⁴ - 2v⁶) + ...

#### B. Torus Knot Formula

**Formula**: For T(p,q) torus knot with braid (σ₁...σₚ₋₁)^q

**Test Cases**:
1. T(2,3) = 3₁ (trefoil)
2. T(2,5) = 5₁ (cinquefoil)
3. T(2,7) = 7₁

**Expected**: General torus knot HOMFLY-PT formula from literature

#### C. Cross-Database Validation

**Method**: Compare values from multiple sources

**Sources**:
1. Local CSV: `/Users/patrickkavanagh/math/knotinfo_data/database_knotinfo/csv_data/knotinfo_data_complete.csv`
2. Online KnotInfo API
3. SageMath `database_knotinfo` package
4. Stoimenov's tables

**Test**: Extract same knot from all sources, verify exact match

---

## Braid Notation Reference

### Notation Convention

**Standard Form**: Braid word uses σᵢ generators
- σᵢ = positive crossing (strand i over strand i+1)
- σᵢ⁻¹ = negative crossing (strand i under strand i+1)
- Braid index = number of strands needed

**KnotInfo Format**: Array notation [1, 1, 1] = σ₁σ₁σ₁ = σ₁³
- Positive integer i = σᵢ
- Negative integer -i = σᵢ⁻¹

### Braid Words for Test Knots

| Knot | KnotInfo Array | Standard Notation | Strands | Crossings |
|------|----------------|-------------------|---------|-----------|
| 3₁ | [1,1,1] | σ₁³ | 2 | 3 |
| 4₁ | [1,-2,1,-2] | σ₁σ₂⁻¹σ₁σ₂⁻¹ | 3 | 4 |
| 5₁ | [1,1,1,1,1] | σ₁⁵ | 2 | 5 |
| 5₂ | [1,1,1,2,-1,2] | σ₁³σ₂σ₁⁻¹σ₂ | 3 | 6 |
| 6₁ | [1,1,2,-1,-3,2,-3] | σ₁²σ₂σ₁⁻¹σ₃⁻¹σ₂σ₃⁻¹ | 4 | 7 |
| 6₂ | [1,1,1,-2,1,-2] | σ₁³σ₂⁻¹σ₁σ₂⁻¹ | 3 | 6 |
| 6₃ | [1,1,-2,1,-2,-2] | σ₁²σ₂⁻¹σ₁σ₂⁻² | 3 | 6 |
| 7₁ | [1,1,1,1,1,1,1] | σ₁⁷ | 2 | 7 |
| 7₂ | [1,1,1,2,-1,2,3,-2,3] | σ₁³σ₂σ₁⁻¹σ₂σ₃σ₂⁻¹σ₃ | 4 | 9 |
| 7₃ | [1,1,1,1,1,2,-1,2] | σ₁⁵σ₂σ₁⁻¹σ₂ | 3 | 8 |

**Torus Knot Pattern**: T(2,n) has braid σ₁ⁿ (all knots 3₁, 5₁, 7₁, 9₁ follow this)

---

## Polynomial Relationships

### Variable Conventions (CRITICAL)

Different sources use different variable conventions. **KnotInfo uses (v,z)**.

| Source | Variables | Skein Relation | Unknot Value |
|--------|-----------|----------------|--------------|
| KnotInfo | (v, z) | v⁻¹P(L₊) - vP(L₋) = zP(L₀) | 1 |
| HOMFLY Original | (α, z) | α⁻¹P(L₊) - αP(L₋) = zP(L₀) | 1 |
| Alternative | (l, m) | lP(L₊) + l⁻¹P(L₋) + mP(L₀) = 0 | 1 |
| Knot Atlas | (a, z) | a⁻¹P(L₊) - aP(L₋) = zP(L₀) | 1 |

**Conversion**: v = a = α, so KnotInfo and Knot Atlas match in most contexts.

### Specializations

#### To Jones Polynomial
- **V(t) from P(v,z)**: Set v = t⁻¹, z = t^(1/2) - t^(-1/2)
- **Alternative**: Set v = t, z = t^(-1/2) - t^(1/2)

#### To Alexander Polynomial
- **Δ(t) from P(v,z)**: Set v = 1, z = t^(1/2) - t^(-1/2)

#### To Conway Polynomial
- **∇(z) from P(v,z)**: Set v = 1
- Result: ∇(z) = P(1, z)

### Known Relationships to Verify

| Property | Formula | Test Cases |
|----------|---------|------------|
| Jones reduction | V(t) = P(t⁻¹, t^(1/2) - t^(-1/2)) | All 20 knots |
| Alexander reduction | Δ(t) = P(1, t^(1/2) - t^(-1/2)) | Trefoil, figure-eight |
| Conway reduction | ∇(z) = P(1, z) | 3₁, 4₁, 5₁ |
| Knot sum | P(K₁#K₂) = P(K₁)·P(K₂) | Composite knots |
| Mirror image | P(K*) = P(K)(v⁻¹, z) | Chiral vs achiral |

---

## Special Cases

### Achiral (Amphichiral) Knots

**Property**: K = K* (identical to mirror image)
**HOMFLY-PT**: Must satisfy P(v,z) = P(v⁻¹,z)

**Test Cases**:
- 4₁ (figure-eight): P = (v⁻² - 1 + v²) - z² (symmetric ✓)
- 6₃: P = (-v⁻² + 3 - v²) + (-v⁻² + 3 - v²)z² + z⁴ (symmetric ✓)

### Knots with Same Alexander or Jones

**Famous Examples**:
1. **5₁ and 10₁₃₂**: Same Alexander, same Jones, DIFFERENT HOMFLY-PT
   - 5₁: (3v⁴ - 2v⁶) + (4v⁴ - v⁶)z² + v⁴z⁴
   - 10₁₃₂: (-2v⁻⁶ + 3v⁻⁴) + (-v⁻⁶ + 4v⁻⁴)z² + v⁻⁴z⁴

2. **8₁₉ and 10₁₂₄**: Different knots, check if polynomials differ

**Verification**: HOMFLY-PT should distinguish these pairs (if Alexander/Jones don't)

### Torus Knots

**Pattern**: T(2,n) for odd n

| Knot | T(p,q) | n | HOMFLY-PT Pattern |
|------|--------|---|-------------------|
| 3₁ | T(2,3) | 3 | Degree in v: 4, in z: 2 |
| 5₁ | T(2,5) | 5 | Degree in v: 6, in z: 4 |
| 7₁ | T(2,7) | 7 | Degree in v: 8, in z: 6 |
| 9₁ | T(2,9) | 9 | Degree in v: 10, in z: 8 |

**Observation**: For T(2,n), max degree in v is 2n-2, max degree in z is n-1

**General Formula** (from literature): Explicit formula exists for all T(p,q)

### Non-Alternating Knots

**First occurrences**:
- 8 crossings: 8₁₉, 8₂₀, 8₂₁ (only three!)
- 9 crossings: More examples available

**Why test these**: Different structure, ensures algorithm handles all knot types

---

## Implementation Checklist

### Phase 1: Basic Verification ✓
- [ ] Extract all 20 knots from local CSV
- [ ] Convert braid notation to standard σᵢ form
- [ ] Verify HOMFLY-PT values match between sources
- [ ] Verify Jones values match between sources

### Phase 2: Theoretical Tests
- [ ] Implement HOMFLY-PT → Jones conversion
- [ ] Test conversion on all 20 knots
- [ ] Verify skein relation for crossing change triples
- [ ] Test mirror image property (achiral knots)
- [ ] Test knot sum multiplicativity

### Phase 3: Computational Tests
- [ ] Implement braid closure → HOMFLY-PT algorithm
- [ ] Test on simple braids (3₁, 5₁, 7₁)
- [ ] Test on complex braids (4₁, 6₁, 7₂)
- [ ] Cross-validate with KnotInfo API
- [ ] Cross-validate with SageMath

### Phase 4: Edge Cases
- [ ] Test unknot (should give 1)
- [ ] Test achiral knots (symmetry check)
- [ ] Test non-alternating knots (8₁₉, 8₂₀, 8₂₁)
- [ ] Test torus knot formula
- [ ] Test knots with same Alexander/Jones (5₁ vs 10₁₃₂)

---

## References

### Primary Sources
1. [KnotInfo Database](https://knotinfo.math.indiana.edu) - Comprehensive knot invariant database
2. [The HOMFLY-PT Polynomial - Knot Atlas](https://katlas.org/wiki/The_HOMFLY-PT_Polynomial) - Definitions and tables
3. [HOMFLY polynomial - Wikipedia](https://en.wikipedia.org/wiki/HOMFLY_polynomial) - Overview and history
4. [Stoimenov's Knot Data Tables](https://stoimenov.net/stoimeno/homepage/ptab/) - Polynomial tables

### Research Papers
1. Kawagoe, K. (2025). "The colored HOMFLY-PT polynomials of the trefoil knot, the figure-eight knot, and twist knots." *Journal of Geometry and Physics*. [arXiv:2107.08678](https://arxiv.org/abs/2107.08678)
2. Freyd et al. (1985). "A new polynomial invariant of knots and links." *Bulletin of the AMS*.
3. Przytycki & Traczyk (1987). "Invariants of links of Conway type."

### Tools and Software
1. **SageMath**: `database_knotinfo` package - [Documentation](https://doc.sagemath.org/html/en/reference/knots/sage/knots/knotinfo.html)
2. **Knot Atlas**: Mathematica package `KnotTheory` - [Download](https://katlas.org)
3. **bTd Program**: M. Ochiai's HOMFLY-PT calculator (Windows, C-based)

### Braid Theory
1. Gittings, T. "Minimum Braids: A Complete Invariant of Knots and Links." [arXiv:math/0401051](https://arxiv.org/pdf/math/0401051)
2. [Braid Representatives - Knot Atlas](https://katlas.org/wiki/Braid_Representatives)

---

## Appendix: Quick Python Test

```python
# Quick verification script using local CSV data
import pandas as pd

csv_path = "/Users/patrickkavanagh/math/knotinfo_data/database_knotinfo/csv_data/knotinfo_data_complete.csv"
df = pd.read_csv(csv_path, delimiter='|')

# Test knots
test_knots = ['0_1', '3_1', '4_1', '5_1', '5_2', '6_1', '6_2', '6_3', '7_1', '7_2', '7_3']

for knot in test_knots:
    row = df[df['name'] == knot].iloc[0]
    print(f"\n{knot}:")
    print(f"  HOMFLY: {row['homfly_polynomial']}")
    print(f"  Jones: {row['jones_polynomial']}")
    print(f"  Braid: {row['braid_notation']}")
    print(f"  Crossing #: {row['crossing_number']}")
    print(f"  Genus: {row['three_genus']}")
```

---

**Status**: Research complete. Ready for implementation and verification.

**Next Steps**:
1. Implement HOMFLY-PT computation from braid words
2. Verify Jones polynomial reduction
3. Test on all 20 knots in suite
4. Document any discrepancies
5. Extend to larger knots if needed

**Last Updated**: 2025-12-12
