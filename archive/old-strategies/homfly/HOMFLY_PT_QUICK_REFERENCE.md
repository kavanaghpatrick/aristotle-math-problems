# HOMFLY-PT Polynomial Quick Reference Card

**One-page reference for HOMFLY-PT polynomial testing and verification**

---

## Core Formula

**Skein Relation**: v⁻¹P(L₊) - vP(L₋) = zP(L₀)

**Initial Condition**: P(unknot) = 1

**Variables**: (v, z) - KnotInfo convention

---

## Essential Test Values

| Knot | HOMFLY-PT P(v,z) | Jones V(t) | Braid |
|------|------------------|------------|-------|
| **0₁** | 1 | 1 | - |
| **3₁** | 2v² - v⁴ + v²z² | t + t³ - t⁴ | σ₁³ |
| **4₁** | v⁻² - 1 + v² - z² | t⁻² - t⁻¹ + 1 - t + t² | σ₁σ₂⁻¹σ₁σ₂⁻¹ |
| **5₁** | 3v⁴ - 2v⁶ + (4v⁴ - v⁶)z² + v⁴z⁴ | t² + t⁴ - t⁵ + t⁶ - t⁷ | σ₁⁵ |

---

## Key Reductions

### HOMFLY-PT → Jones
**Set**: v = t⁻¹, z = t^(1/2) - t^(-1/2)

**Example** (Trefoil):
```
P(3₁) = 2v² - v⁴ + v²z²
→ V(3₁) = -t⁻⁴ + t⁻³ + t⁻¹  (or t + t³ - t⁴ normalized)
```

### HOMFLY-PT → Alexander
**Set**: v = 1, then Δ(t) from ∇(z) = P(1,z)

**Example** (Trefoil):
```
P(3₁) → ∇(z) = 1 + z²
→ Δ(3₁) = t - 1 + t⁻¹
```

---

## Theoretical Properties

| Property | Formula | Use Case |
|----------|---------|----------|
| **Knot Sum** | P(K₁#K₂) = P(K₁)·P(K₂) | Composite knots |
| **Mirror** | P(K*) = P(K)(v⁻¹, z) | Chirality test |
| **Achiral** | P(K) = P(K)(v⁻¹, z) | Symmetry check |

---

## Braid Notation

**Convention**: [1, -2, 1] = σ₁σ₂⁻¹σ₁

- Positive integer i → σᵢ (over-crossing)
- Negative integer -i → σᵢ⁻¹ (under-crossing)

**Torus Knots**: T(2,n) = σ₁ⁿ (e.g., 3₁ = σ₁³, 5₁ = σ₁⁵)

---

## Variable Conventions

| Source | Skein Form | To Jones |
|--------|------------|----------|
| KnotInfo (v,z) | v⁻¹P₊ - vP₋ = zP₀ | v=t⁻¹, z=t^½-t^-½ |
| Atlas (a,z) | a⁻¹P₊ - aP₋ = zP₀ | Same (a=v) |
| HOMFLY (l,m) | lP₊ + l⁻¹P₋ + mP₀ = 0 | l=-v⁻¹, m=-z |

---

## Verification Checklist

### Quick Tests (Priority Order)
1. ✅ **Unknot**: P = 1, V = 1
2. ✅ **Trefoil reduction**: HOMFLY → Jones matches
3. ✅ **Figure-eight achiral**: P(v,z) = P(v⁻¹,z)
4. ✅ **Torus pattern**: Check 3₁, 5₁, 7₁ degree pattern
5. ✅ **Database cross-check**: CSV vs SageMath vs online

---

## Data Sources

**Local**: `/Users/patrickkavanagh/math/knotinfo_data/database_knotinfo/csv_data/knotinfo_data_complete.csv`

**Column Numbers**:
- Name: 1
- Crossing number: 29
- Unknotting number: 33
- Genus: 35
- Braid notation: 45
- Jones: 67
- HOMFLY: 223

**Extract Command**:
```bash
awk -F'|' '$1=="3_1" {print $223}' knotinfo_data_complete.csv
```

---

## SageMath Quick Check

```python
from sage.knots.knotinfo import KnotInfo
K = KnotInfo.K3_1
print(K.homfly_polynomial())           # HOMFLY-PT
print(K.jones_polynomial())            # Jones
print(K.braid_notation())              # Braid word
print(K.three_genus())                 # Genus
```

---

## Common Pitfalls

⚠️ **Different normalizations**: KnotInfo vs literature Jones may differ
⚠️ **Variable names**: v = a = α (all same)
⚠️ **Jones reduction**: NOT a=q², z=q-q⁻¹ (that's A₂ invariant!)
⚠️ **Mirror convention**: Check if source uses K* vs K with opposite sign
⚠️ **Braid index**: Minimum strands needed (not same as crossing number)

---

## Test Suite Location

**Full Details**: `HOMFLY_PT_TEST_CASES.md`
**Technical Notes**: `HOMFLY_PT_TECHNICAL_NOTES.md`
**Summary**: `HOMFLY_PT_RESEARCH_SUMMARY.md`

**Total Test Knots**: 19 (unknot + 18 prime knots, 3-10 crossings)

---

## Key Formulas

### Trefoil (3₁)
```
HOMFLY: 2v² - v⁴ + v²z²
Jones: t + t³ - t⁴
Braid: σ₁³
Genus: 1
Unknotting: 1
Achiral: No
```

### Figure-Eight (4₁)
```
HOMFLY: v⁻² - 1 + v² - z²
Jones: t⁻² - t⁻¹ + 1 - t + t²
Braid: σ₁σ₂⁻¹σ₁σ₂⁻¹
Genus: 1
Unknotting: 1
Achiral: Yes ✓
```

### Cinquefoil (5₁)
```
HOMFLY: 3v⁴ - 2v⁶ + (4v⁴ - v⁶)z² + v⁴z⁴
Jones: t² + t⁴ - t⁵ + t⁶ - t⁷
Braid: σ₁⁵
Genus: 2
Unknotting: 2
Achiral: No
```

---

**Quick Verification Test**: Load 3₁, compute Jones from HOMFLY, compare → should match!

**Last Updated**: 2025-12-12
