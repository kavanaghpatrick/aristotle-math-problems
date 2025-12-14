# Boris Pattern Problem Ranking

## Scoring Criteria
- **+10**: Pre-formalized in Formal Conjectures
- **+5**: Has SOLVED variants (Boris's #124 had known result that applied!)
- **+3**: Finite/bounded (no asymptotics)
- **+3**: Graph theory / combinatorics
- **+2**: Concrete bounds (not "for all large n")
- **-3**: Has prize $500+
- **-5**: Uses limits / density / asymptotics
- **-5**: Famous hard problem (projective planes, etc.)

---

## TOP CANDIDATES

### 🥇 #944 - Critical Vertices/Edges (SCORE: 21)
| Factor | Score | Notes |
|--------|-------|-------|
| Pre-formalized | +10 | ✅ In FC repo |
| **SOLVED VARIANTS** | +5 | ✅ k=5 (Brown 1992), k≥5 (Jensen 2002), k-1 not prime (Lattanzio 2002) |
| Finite/bounded | +3 | ✅ Existence for specific k, r |
| Graph theory | +3 | ✅ SimpleGraph, chromatic number |
| No prize | +0 | ✅ $0 |

**Why this is IDEAL**:
- Multiple solved cases already formalized with `sorry`
- Only k=4, r=1 case remains open
- Aristotle could prove a SOLVED variant by finding existing construction!

**Lean theorems to target**:
```lean
-- SOLVED - Brown 1992
theorem erdos_944.variants.dirac_conjecture.k_eq_5 :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 5 1 := by sorry

-- SOLVED - Jensen 2002
theorem erdos_944.variants.dirac_conjecture.k_ge_five (k : ℕ) (hk : 5 ≤ k) :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by sorry
```

---

### 🥈 #128 - Triangle in Dense Induced Subgraph (SCORE: 16)
| Factor | Score | Notes |
|--------|-------|-------|
| Pre-formalized | +10 | ✅ In FC repo |
| Finite/bounded | +3 | ✅ Concrete n, n²/50 bound |
| Graph theory | +3 | ✅ SimpleGraph, CliqueFree |
| Low prize | +0 | ⚠️ $250 (acceptable) |

**Lean theorem**:
```lean
theorem erdos_128 :
    ((∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
        50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) → ¬ G.CliqueFree 3)
    ↔ answer(sorry) := by sorry
```

---

### 🥉 #108 - High Chromatic Subgraph with High Girth (SCORE: 16)
| Factor | Score | Notes |
|--------|-------|-------|
| Pre-formalized | +10 | ✅ In FC repo |
| Finite/bounded | +3 | ✅ Existence of finite f(k,r) |
| Graph theory | +3 | ✅ SimpleGraph, chromaticNumber, girth |
| No prize | +0 | ✅ $0 |

**Note**: Likely requires Ramsey-type construction

---

### #61 - Erdős-Hajnal Conjecture (SCORE: 13)
| Factor | Score | Notes |
|--------|-------|-------|
| Pre-formalized | +10 | ✅ In FC repo |
| **SOLVED VARIANTS** | +5 | ✅ ErHa89, BNSS23 bounds |
| Graph theory | +3 | ✅ |
| Asymptotics | -5 | ❌ Uses `∀ᶠ n in atTop` |

**Solved variants could be targeted**:
```lean
-- SOLVED - Erdős-Hajnal 1989
theorem erdos_61.variants.erha89 :
    ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n => exp (c * sqrt (log n))) := by sorry
```

---

### #705 - Unit Distance Graph χ ≤ 3 (SCORE: 13)
| Factor | Score | Notes |
|--------|-------|-------|
| Pre-formalized | +10 | ✅ |
| Finite/bounded | +3 | ✅ Finite vertex set |
| No prize | +0 | ✅ |
| Geometric | -0 | ⚠️ Uses ℝ², UnitDistancePlaneGraph |

**Risk**: UnitDistancePlaneGraph may not be well-developed in Mathlib

---

## RECOMMENDATION

**Submit #944 SOLVED variants first!**

1. `erdos_944.variants.dirac_conjecture.k_eq_5` - Brown 1992 construction
2. `erdos_944.variants.dirac_conjecture.k_ge_five` - Jensen 2002 construction

These are KNOWN RESULTS that just need formalization - exactly Boris's pattern!

---

## AVOID

| Problem | Reason |
|---------|--------|
| #723 | Projective plane - famous hard |
| #85 | Uses `∀ᶠ n in atTop` |
| #30 | $1000 prize, asymptotics |
| #64 | $1000 prize |
| #172 | "arbitrarily large" - unbounded |
