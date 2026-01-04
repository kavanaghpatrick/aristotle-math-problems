# ARISTOTLE DISCOVERY FRAMEWORK
## A Generalizable Guide for AI-Assisted Mathematical Discovery

> Synthesized from 8 parallel deep-dive analyses of 228 submissions
> Generated: Jan 4, 2026

---

## THE CORE INSIGHT

**Aristotle is a finite-domain mathematical explorer that excels at:**
1. **Counterexample construction** on small graphs (Fin 5-7)
2. **Proof discovery** via tactic search when given clear structure
3. **Correction suggestion** when false lemmas are detected

**The key pattern: Aristotle finds things humans miss on small finite domains.**

---

## PART 1: THE 4-TIER CAPABILITY TAXONOMY

### TIER 1: HIGH CONFIDENCE DISCOVERY (70-90% success)

| Capability | Size Limit | Example |
|------------|------------|---------|
| **Counterexample search** | Fin 3-7 | G6 graph disproving slack bound |
| **Cardinality bounds** | |S| ≤ 15 | M_edges.card ≤ 12 |
| **Decidable predicates** | Any | isClique, membership |
| **Finite case analysis** | ≤12 cases | Cycle4 vertex proofs |

**Key tactics:** `simp_all +decide`, `native_decide`, `fin_cases`, `aesop`

### TIER 2: MODERATE DISCOVERY (30-50% success)

| Capability | Requirement | Example |
|------------|-------------|---------|
| **Subadditivity** | Explicit construction | τ(A∪B) ≤ τ(A)+τ(B) |
| **Induction** | Clear base/step | Build from singleton |
| **LP bounds** | Direct witness | ν* ≤ 4 |
| **Helly-type** | Check truth first! | Common edge lemma |

**Requires:** Good scaffolding, proven helper lemmas

### TIER 3: VERIFICATION ONLY (10-20% success)

| Capability | Why Limited | Workaround |
|------------|-------------|------------|
| **Deep combinatorics** | Needs strategic insight | Human outlines proof |
| **König-type** | Must verify bipartite first | Pre-check structure |
| **Multi-element coordination** | Greedy fails | Human selects |

### TIER 4: CANNOT HELP (<5% success)

| Problem Type | Fundamental Barrier |
|--------------|---------------------|
| Asymptotics | Infinite domain |
| Optimal selection | Exponential search |
| Global coordination | Local tactics only |
| Insight-dependent existence | No constructive path |

---

## PART 2: COUNTEREXAMPLE DISCOVERY PATTERN

### The Structure Aristotle Finds

All 5 Aristotle-discovered counterexamples share:

| Property | Pattern |
|----------|---------|
| **Size** | 5-6 vertices (Fin 5, Fin 6) |
| **Structure** | Central triangle + attachments |
| **Edge set** | Explicitly enumerable |
| **Weight function** | Boundary cases (w=0 or w=1) |

### Template for Counterexample Hunting

```lean
/-
COUNTEREXAMPLE SEARCH: Test if L is false
Use Fin 6 for exhaustive search
-/
import Mathlib

-- Concrete finite type
abbrev V := Fin 6

-- Your conjecture (Aristotle will try to disprove)
lemma conjecture_L (G : SimpleGraph V) [DecidableRel G.Adj] ... :
    your_claim := by
  sorry  -- Let Aristotle search
```

### What Aristotle Does Internally

1. **Negate** the lemma using `negate_state`
2. **Push negation** to find existential form
3. **Search** the finite space for witness
4. **Construct** explicit counterexample
5. **Prove** all properties with `native_decide`
6. **Suggest correction** if pattern is clear

---

## PART 3: PROOF DISCOVERY PATTERN

### What Makes Proofs Discoverable

| Factor | Sweet Spot | Why |
|--------|------------|-----|
| **Lines** | 100-200 | Processing efficiency |
| **Lemmas** | 3-7 | Focused scope |
| **Sorries** | 0-1 | Single attack point |
| **Dependency depth** | 1-2 | Flat structure |
| **Type** | Fin n | Decidable |

### The Discoverable Proof Template

```lean
/-
TARGET: One focused theorem
SCAFFOLDING: All helpers proven
ONE SORRY: The target only
-/

import Mathlib
set_option maxHeartbeats 400000

-- Copied definitions (not imported)
def isTrianglePacking ... := ...

-- PROVEN helpers (full proof code)
lemma helper1 ... := by [actual proof from prior run]
lemma helper2 ... := by [actual proof from prior run]

-- TARGET (single sorry)
theorem main_result ... := by
  have h1 := helper1 ...
  have h2 := helper2 ...
  sorry  -- Aristotle fills this
```

### Tactics Aristotle Discovers

```lean
-- Aristotle's signature patterns
simp_all +decide [Finset.ext_iff]
rcases h with ⟨a, b, c⟩ <;> simp_all +decide
fin_cases x <;> native_decide
by grind +ring
by aesop
by omega
by linarith [...]
```

---

## PART 4: CORRECTION SUGGESTION PATTERN

### How Aristotle Suggests Fixes

When finding counterexample, Aristotle often:
1. Identifies **precise failure point**
2. Derives **correct multiplier** (often 3×)
3. **Proves** corrected version

### The 3× Pattern

| Original Claim | Counterexample Showed | Correct Bound |
|----------------|----------------------|---------------|
| externals.sum ≤ 1× slack | 3 externals on 3 edges | ≤ 3× slack |
| 2 edges cover sharing | Third edge used | All 3 edges |
| τ_S ≤ 2 per element | Propeller needs 3 | τ_S ≤ 3 |

**Root cause:** Triangles have 3 edges; different triangles can independently use each.

### Example: slot172_counterexample

```lean
-- Human claimed:
lemma externals_sum_le_totalSlack ... :
    (externals G M).sum w ≤ totalSlack M w

-- Aristotle found counterexample G6 where 3 > 1

-- Aristotle suggested AND PROVED:
lemma externals_sum_le_three_totalSlack ... :
    (externals G M).sum w ≤ 3 * totalSlack M w := by
  [complete 70-line proof]
```

---

## PART 5: MATHEMATICAL DOMAINS

### Where Aristotle Has Proven Success

| Domain | Success Rate | Example Results |
|--------|--------------|-----------------|
| **Triangle packing/covering** | HIGH | τ ≤ 12, maximality |
| **Link graph theory** | HIGH | local Tuza bounds |
| **Set cardinality** | HIGH | pigeonhole arguments |
| **Graph matching** | MEDIUM | König-type (check bipartite!) |
| **LP/fractional** | LOW | needs axioms |

### Specific Proven Theorems

```
τ ≤ 2ν for ν ∈ {0, 1}     ← COMPLETE
τ ≤ 12 for ν = 4          ← COMPLETE
Subadditivity             ← COMPLETE
Maximality lemma          ← COMPLETE
External structure        ← PARTIAL
τ ≤ 8 for ν = 4          ← OPEN (blocked by 6 false lemmas)
```

---

## PART 6: THE OPTIMAL WORKFLOW

### Falsification-First Pipeline

```
┌─────────────────────────────────────────┐
│  1. GENERATE CONJECTURES (LLMs)         │
│     - Multiple candidates L₁...L₅       │
│     - Include uncertain ones            │
└─────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────┐
│  2. FALSIFY (Aristotle on Fin 6)        │
│     - Submit each with sorry            │
│     - Aristotle disproves or proves     │
│     - Get counterexamples + corrections │
└─────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────┐
│  3. DECOMPOSE (Human)                   │
│     - Break into 5-10 lemmas            │
│     - One sorry per file                │
│     - Flat dependencies                 │
└─────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────┐
│  4. PROVE (Aristotle with scaffolding)  │
│     - Submit with 7+ proven helpers     │
│     - Use safe_discard pattern          │
│     - Iterate on near-misses            │
└─────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────┐
│  5. SYNTHESIZE (Human + LLMs)           │
│     - Combine proven lemmas             │
│     - Handle global coordination        │
│     - Interpret counterexamples         │
└─────────────────────────────────────────┘
```

---

## PART 7: ATTACK CHECKLIST

### Before Submitting to Aristotle

**Structural checks:**
- [ ] Is the type finite? (Fin n, explicit Finset)
- [ ] Is n ≤ 7 for counterexample search?
- [ ] Are all predicates decidable?
- [ ] Is file 100-200 lines?
- [ ] Are there 3-7 lemmas?
- [ ] Is there at most 1 sorry?

**Mathematical checks:**
- [ ] Check false_lemmas table first
- [ ] Check failed_approaches table
- [ ] Is the lemma actually TRUE?
- [ ] Have similar approaches failed?

**Scaffolding checks:**
- [ ] Include 7+ proven helpers (38% → success)
- [ ] Copy FULL proof code (not just statements)
- [ ] Use safe_discard pattern for definitions

### SQL Quick Reference

```sql
-- Is my lemma already disproven?
SELECT * FROM false_lemmas WHERE lemma_name LIKE '%my_idea%';

-- Has this approach failed?
SELECT * FROM failed_approaches WHERE approach_name LIKE '%my_idea%';

-- What's proven as scaffolding?
SELECT filename FROM submissions WHERE sorry_count=0
ORDER BY proven_count DESC;

-- Aristotle's counterexamples
SELECT * FROM false_lemmas WHERE evidence_level='aristotle_verified';
```

---

## PART 8: GENERALIZING TO ALL MATH PROBLEMS

### Problem Types to Attack

| Domain | Aristotle Role | Human Role |
|--------|----------------|------------|
| **Finite combinatorics** | Counterexamples, bounds | Strategy |
| **Graph theory (small)** | Structure lemmas | Architecture |
| **Number theory (small)** | Divisibility, mod | Conjectures |
| **Set theory** | Cardinality, containment | Decomposition |
| **Group theory (finite)** | Verification | Structure |

### Problem Types to Avoid

| Domain | Why | Alternative |
|--------|-----|-------------|
| **Analysis** | Infinite, limits | Pure human |
| **Optimization** | Exponential search | Hybrid |
| **Asymptotics** | Unbounded | Pure human |
| **Abstract algebra** | Infinite groups | Finite reps |

### The Meta-Strategy

**Aristotle is your falsification oracle:**
1. Generate conjectures quickly (LLMs)
2. Let Aristotle kill the false ones (saves weeks)
3. Build on proven infrastructure
4. Iterate rapidly on small lemmas

**The winning formula:**
```
Discovery = (Finite Domain) × (Clear Structure) × (Rich Scaffolding) × (Single Target)
```

---

## APPENDIX: KEY STATISTICS

| Metric | Value | Implication |
|--------|-------|-------------|
| Total submissions | 228 | Large dataset |
| Zero-sorry success | 39 (17%) | Room for improvement |
| Counterexamples found | 5 | Aristotle DISCOVERS |
| Corrections suggested | 3+ | Aristotle FIXES |
| False lemmas blocked | 16 | Falsification saves time |
| Failed approaches | 50+ | Learning accumulated |

---

## APPENDIX: FILE LOCATIONS

| Resource | Path |
|----------|------|
| Proven results | `/Users/patrickkavanagh/math/proven/` |
| Counterexamples | `/Users/patrickkavanagh/math/proven/tuza/nu4/slot172_counterexample/` |
| Database | `/Users/patrickkavanagh/math/submissions/tracking.db` |
| Scaffolding | `/Users/patrickkavanagh/math/proven/scaffolding_library.lean` |
| This guide | `/Users/patrickkavanagh/math/docs/ARISTOTLE_DISCOVERY_FRAMEWORK.md` |

---

*Framework synthesized from 8 parallel analysis agents examining 228 submissions.*
*Core insight: Aristotle discovers on finite domains - use it for falsification first.*
