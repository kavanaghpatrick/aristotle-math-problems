# HOMFLY-PT Polynomial Research - Master Index

**Research Date**: 2025-12-12  
**Status**: ✅ Complete

---

## 📁 Quick Navigation

| File | Size | Purpose | Start Here? |
|------|------|---------|-------------|
| **QUICK_REFERENCE.md** | 4 KB | One-page cheat sheet | ⭐ YES - Print this! |
| **TEST_CASES.md** | 14 KB | Main test suite (19 knots) | ⭐ YES - For testing |
| **RESEARCH_SUMMARY.md** | 10 KB | Implementation roadmap | ⭐ YES - For overview |
| **TECHNICAL_NOTES.md** | 12 KB | Formulas & algorithms | For deep understanding |
| **COMPREHENSIVE_RESEARCH.md** | 30 KB | All web research | For source details |
| **EXECUTIVE_SUMMARY.md** | 14 KB | Alternative overview | For sharing |

---

## 🎯 Use Cases

**I want to...**

### Test HOMFLY-PT Implementation
→ Open: `HOMFLY_PT_TEST_CASES.md`
- 19 knots with complete data
- Expected HOMFLY-PT values
- Expected Jones values
- Verification checklist

### Quick Formula Lookup
→ Open: `HOMFLY_PT_QUICK_REFERENCE.md`
- Core formulas
- Essential test values
- Variable conventions
- SageMath quick checks

### Understand the Theory
→ Open: `HOMFLY_PT_TECHNICAL_NOTES.md`
- Skein relation explained
- Jones/Alexander reductions (worked examples)
- Braid closure method
- Recent algorithms (2024-2025)

### Plan Implementation
→ Open: `HOMFLY_PT_RESEARCH_SUMMARY.md`
- Project overview
- Implementation roadmap (Phases 1-5)
- Key findings
- Quick start commands

### Find Original Sources
→ Open: `HOMFLY_PT_COMPREHENSIVE_RESEARCH.md`
- All web search results
- Complete source citations
- Extended research notes

---

## 📊 Test Suite Summary

**Total Test Cases**: 19 knots (unknot + 3-10 crossings)

**Coverage**:
- ✅ Alternating: 14 knots
- ✅ Non-alternating: 5 knots
- ✅ Achiral: 2 knots (4₁, 6₃)
- ✅ Torus knots: 4 knots (3₁, 5₁, 7₁, 9₁)
- ✅ Special cases: unknot, trefoil, figure-eight

**Data for Each Knot**:
- HOMFLY-PT polynomial P(v,z)
- Jones polynomial V(t)
- Braid word representation
- Crossing number
- Genus
- Unknotting number
- Alternating status

---

## 🗄️ Data Location

**Primary Source**: `/Users/patrickkavanagh/math/knotinfo_data/database_knotinfo/csv_data/knotinfo_data_complete.csv`

**Quick Extract**:
```bash
# HOMFLY-PT for trefoil
awk -F'|' '$1=="3_1" {print $223}' knotinfo_data_complete.csv

# Jones for trefoil  
awk -F'|' '$1=="3_1" {print $67}' knotinfo_data_complete.csv
```

**Column Reference**:
- 1: Name | 29: Crossings | 33: Unknotting | 35: Genus
- 45: Braid | 67: Jones | 223: HOMFLY

---

## ⚡ Quick Start (3 Steps)

### 1. Print Reference Card
```bash
open HOMFLY_PT_QUICK_REFERENCE.md
# Print this one-page reference
```

### 2. Get Test Data
```bash
open HOMFLY_PT_TEST_CASES.md
# Section "Table 2: HOMFLY-PT Polynomial Values"
```

### 3. Verify First Test
```python
from sage.knots.knotinfo import KnotInfo
K = KnotInfo.K3_1
print(K.homfly_polynomial())  # Should match test data
```

---

## 🔑 Essential Formulas

**Skein Relation**: v⁻¹P(L₊) - vP(L₋) = zP(L₀)

**HOMFLY → Jones**: v = t⁻¹, z = t^(½) - t^(-½)

**Test Value**: P(3₁) = 2v² - v⁴ + v²z²

**Location**: `HOMFLY_PT_QUICK_REFERENCE.md`

---

## 🎓 Research Credits

**Sources**:
- [KnotInfo Database](https://knotinfo.math.indiana.edu)
- [Knot Atlas](https://katlas.org)
- [Stoimenov Tables](https://stoimenov.net/stoimeno/homepage/ptab/)
- Recent papers: arXiv:2107.08678, arXiv:2512.06142

**Total Documentation**: ~35,000 words, 84 KB

**Status**: ✅ Ready for implementation

**Last Updated**: 2025-12-12
