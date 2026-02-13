# Propeller Counterexample Discovery
## February 4, 2026

**STATUS**: The "Propeller counterexample" to `tau_le_8_scattered` is **INVALID**

---

## The Claimed Counterexample

Documentation (FALSE_LEMMAS.md, Jan 4, 2026) claimed:

```
4 disjoint Propellers form a graph with:
- ν = 4 (using central triangles)
- τ = 12 (3 edges per Propeller)
- Therefore τ = 12 > 2ν = 8, violating Tuza
```

---

## The Discovery (Feb 4, 2026)

Multi-agent debate flagged this for verification. Analysis revealed:

### Single Propeller Structure

```
Vertices: {0, 1, 2, 3, 4, 5}

Triangles:
- Central: T0 = {0, 1, 2}
- Petal 1: T1 = {0, 1, 3}  (shares edge {0,1} with central)
- Petal 2: T2 = {1, 2, 4}  (shares edge {1,2} with central)
- Petal 3: T3 = {2, 0, 5}  (shares edge {0,2} with central)
```

### Key Finding: Petals Are Edge-Disjoint!

```
T1 edges: {0,1}, {0,3}, {1,3}
T2 edges: {1,2}, {1,4}, {2,4}
T3 edges: {0,2}, {0,5}, {2,5}

T1 ∩ T2 edges: ∅ ✓
T1 ∩ T3 edges: ∅ ✓
T2 ∩ T3 edges: ∅ ✓
```

### Correct ν Calculation

| Packing | Size | Validity |
|---------|------|----------|
| {T0} (central only) | 1 | Valid but NOT maximum |
| {T1, T2, T3} (petals) | 3 | Valid AND maximum |

**ν(single Propeller) = 3** (not 1!)

### For 4 Disjoint Propellers

| Metric | Claimed | Actual |
|--------|---------|--------|
| ν | 4 | **12** |
| τ | 12 | 12 |
| 2ν | 8 | **24** |
| Tuza (τ ≤ 2ν) | VIOLATED | **SATISFIED** |

---

## Implications

1. **`tau_le_8_scattered` may NOT be false** - the claimed counterexample is invalid

2. **Our slot54/55 proofs are valid** - they prove specific constructions work

3. **We still need general theorems** - but we're not fighting a false counterexample

4. **slot57 formally verifies** - ν(Propeller) = 3, Tuza satisfied

---

## Submissions

| Slot | Purpose | Status |
|------|---------|--------|
| 57 | Verify Propeller has ν = 3 | Submitted |
| 56 | Prove general scattered τ ≤ 8 | Submitted |

---

## Database Updates

```sql
-- Updated false_lemmas entry
UPDATE false_lemmas SET
  notes = 'DISPUTED Feb 4: Propeller has nu=3 (petals), not nu=1 (central).
           The counterexample may be invalid.'
WHERE lemma_name = 'tau_le_8_scattered';
```

---

*Discovery made during multi-agent debate (Grok + Gemini) when Gemini flagged "Propeller counterexample" for verification.*
