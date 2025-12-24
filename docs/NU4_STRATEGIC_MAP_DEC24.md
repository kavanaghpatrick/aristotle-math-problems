# TUZA ν=4: COMPLETE STRATEGIC MAP
*Generated: 2024-12-24 | Last Updated: 2024-12-24*

## Current Position Summary

| Metric | Value |
|--------|-------|
| **Proven Lemmas** | 94 total |
| **Key Universal Bounds** | τ(S_e) ≤ 2, τ(X_ef) ≤ 2, τ_union_le_sum |
| **Base Cases Solved** | ν ∈ {0, 1, 2, 3} (Parker 2024) |
| **Active Aristotle Slots** | 4 new strategies running |
| **Documented Failures** | 12 approaches negated |
| **Counterexample Constraints** | 11 (mad≥7, χ≥5, tw≥7, etc.) |

---

## THE CORE PROBLEM

**Parker's proof breaks at ν=4 because:**
- τ(T_e) ≤ 2 requires bridges attach to ≤2 other elements
- At ν=4, bridges can attach to 3 other elements
- This creates configurations where τ(T_e) = 3 for ALL e ∈ M
- Induction gives τ ≤ 3 + 6 = 9, but we need τ ≤ 8

**The insight needed:** Find decomposition that avoids single-element removal

---

## PROVEN SCAFFOLDING (Available for all strategies)

```
┌─────────────────────────────────────────────────────┐
│  UNIVERSAL BOUNDS (Proven, High Confidence)        │
├─────────────────────────────────────────────────────┤
│  τ(S_e) ≤ 2      │ Slot 6   │ Any packing element  │
│  τ(X_ef) ≤ 2     │ Slot 24  │ Bridges between pair │
│  τ_union_le_sum  │ Slot 16  │ τ(A∪B) ≤ τ(A)+τ(B)   │
│  Te = Se ∪ bridges│ Slot 6  │ Partition theorem    │
└─────────────────────────────────────────────────────┘
```

**Critical insight from Gemini:** τ(T_e) ≤ 3 is TRIVIAL (use 3 edges of e). Any bound > 3 per element or > 6 per pair is worthless.

---

## 4 ACTIVE STRATEGIES (Running Dec 24)

| Slot | Strategy | Target | UUID | Probability |
|------|----------|--------|------|-------------|
| **34** | Pair Decomposition | ∃ pair: τ(T_pair) ≤ 4 | `0b8a1495` | 15% |
| **35** | V-Decomposition | τ(T_pair) ≤ 4 via overlap | `da605278` | 35% |
| **36** | Leaf Removal | τ(T_leaf) ≤ 2 | `da4e4a07` | 20% |
| **37** | LLL Probabilistic | τ ≤ 8 existence | `1bb416d7` | 5% |

**Combined success probability:** ~55%

---

## CRITICAL GAPS (Prioritized)

### Gap 1: τ(T_e ∪ T_f) ≤ 4 (THE HOLY GRAIL)
- **If proven:** Tuza ν=4 follows immediately (2 pairs × 4 = 8)
- **Currently known:** τ ≤ 6 trivially (2+2+2)
- **The missing insight:** Where does the 2-edge slack come from?
- **Strategies attacking:** Slots 34, 35

### Gap 2: Bridge Structure
- **12 matching assumptions NEGATED** by Aristotle
- Bridges can share multiple vertices (not matching-like)
- **DO NOT** assume bridge absorption by S_e covers
- **Strategy attacking:** Slot 36 (uses explicit tau_X_le_2)

### Gap 3: Leaf Existence in Sharing Graph
- If leaf exists with τ(T_leaf) ≤ 2, then τ ≤ 2 + 6 = 8
- Requires sharing graph to have degree-1 vertex
- **Strategy attacking:** Slot 36

---

## DEAD ENDS (Don't Retry)

| Failed Approach | Why | Counterexample |
|-----------------|-----|----------------|
| Bridge matching | Bridges share multiple vertices | t₁={0,1,3}, t₂={0,1,4} share {0,1} |
| Bridge absorption | S_e covers don't hit bridges | Explicit 5-vertex example |
| τ(containing v) ≤ 2 | Need 3 edges for star | {v,a,b},{v,c,d},{v,e,f} |
| Cycle opposite disjoint | Sharing graph ≠ vertex structure | C4 counterexample |

---

## COUNTEREXAMPLE LANDSCAPE

**Probability assessment:**
- 60-70%: No counterexample exists (Tuza holds)
- 25-30%: Exists in algebraic family (hard to find)
- 5-10%: Sparse intricate construction

**Remaining candidate families:**
- Non-abelian Cayley graphs (A₅, S_n)
- Kneser graphs
- Polarity graphs (finite geometry)

**Constraints any counterexample must satisfy:**
- mad(G) ≥ 7, χ(G) ≥ 5, treewidth ≥ 7
- NOT: tripartite, threshold, planar, random, 4-partite

---

## DEPENDENCY GRAPH

```
                    ┌──────────────┐
                    │ Tuza ν=4     │
                    │   τ ≤ 8      │
                    └──────┬───────┘
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
        ▼                  ▼                  ▼
   ┌─────────┐       ┌─────────┐       ┌─────────┐
   │ Slot 34 │       │ Slot 35 │       │ Slot 36 │
   │  Pair   │       │ V-Decomp│       │  Leaf   │
   │  ≤ 4    │       │  ≤ 4    │       │  ≤ 2    │
   └────┬────┘       └────┬────┘       └────┬────┘
        │                 │                 │
        │           ┌─────┴─────┐     ┌─────┴─────┐
        │           │           │     │           │
        ▼           ▼           ▼     ▼           ▼
   [Minimal]   [tau_union] [v_decomp] [tau_S]  [tau_X]
                   ≤ sum       ✓       ≤ 2       ≤ 2
                    ✓                   ✓         ✓
```

---

## BREAKTHROUGH SCENARIOS

**Scenario A (Best case):**
> Slot 35 proves τ(T_pair) ≤ 4 via overlap argument
> → Immediately: τ(G) ≤ 4 + 4 = 8 ✓

**Scenario B:**
> Slot 36 proves τ(T_leaf) ≤ 2 for sharing graph leaves
> → With Parker ν=3: τ(G) ≤ 2 + 6 = 8 ✓

**Scenario C:**
> Aristotle finds structural insight we missed
> → Novel decomposition none of us predicted

**Scenario D (Failure mode):**
> All strategies fail → Counterexample hints emerge
> → Pivot to explicit construction search

---

## KEY FILES

| Purpose | Location |
|---------|----------|
| Running strategies | `submissions/nu4_strategy/slot34-37_*.lean` |
| Proven lemmas | `proven/tuza/lemmas/*.lean` |
| Database | `submissions/tracking.db` |
| Failed approaches | `failed_approaches` table |

---

## MONITOR STATUS

```bash
# Check running submissions
sqlite3 submissions/tracking.db "SELECT uuid, filename, status FROM submissions WHERE status='running';"

# Download when complete
aristotle download 0b8a1495-a511-4df3-80c6-6ba765dde47b  # slot34
aristotle download da605278-c788-458e-bcfa-0404a47d6983  # slot35
aristotle download da4e4a07-305d-4074-b55a-6f588e1aad83  # slot36
aristotle download 1bb416d7-8490-44fa-88a4-3df9362128c6  # slot37
```

---

## ADDITIONAL INSIGHTS (From Deep Dive Agents - Dec 24)

### From Fractional Relaxation Analysis
- **K₅ integrality gap = 2/3** (small!) - suggests ν≤4 rounding is nearly exact
- **Chapuy bound**: τ ≤ 2ν* - (1/√6)√ν* ≈ 7.18 for ν=4
- **LP duality**: τ* = ν* proven - fractional bounds are tight
- **Route**: If we prove integrality gap ≤ 0 for ν=4, Tuza follows
- **Krivelevich**: K₃,₃-free graphs satisfy τ ≤ 2ν directly

### From Hypergraph (r=4) Transfer
- **Bridge lemma PROVEN for r=4**: Transfers directly to triangle case
- **Strong Aharoni-Zerbib is FALSE**: τ > 2.5ν counterexample exists for r=4
- **Key transfer**: Union of two face-disjoint 4-edges has ≤5 vertices
- **Implication**: Bridge structure is MORE constrained than naive analysis suggests
- **Files**: `aristotle_hypergraph_r4_COMPLETE.lean` (481 lines, 20+ lemmas)

### From Erdős Problems Technique Mining
- **Structural decomposition**: 100% success rate (20/20 Tuza lemmas)
- **Intersecting family dichotomy**: isStar ∨ isK4 - universal and proven
- **Probabilistic methods**: 0% success for finite ν - DO NOT USE
- **Induction + case splits**: 87% success (Parker's technique)
- **Boris Alexeev insight**: Formalization gaps can unlock proofs

### From Split Graphs Frontier
- **20 lemmas proven** by Aristotle (ee09f2e2)
- **Threshold subclass**: SOLVED (Bożyk et al. 2021)
- **Key lemma**: Every split graph triangle has ≥2 clique vertices
- **Gap**: Missing recursive decomposition for general case
- **Insight**: Clique structure constraints enable proof

### From Extremal Techniques
- **MAD ≥ 7 required** (Puleo) - counterexample must be dense
- **Treewidth ≥ 7 required** (Botler) - high complexity
- **K₃,₃ subdivision required** (Haxell) - structural constraint
- **Complete 4-partite**: τ ≤ 1.5ν (BETTER than Tuza!) - excludes this class
- **CRITICAL**: Bridge absorption FAILED - Aristotle found counterexample
  - Cover of S_e ∪ S_f does NOT cover bridges X(e,f)
  - Must use τ(S_e) + τ(X_ef) separately

### From Sharing Graph Classification
**Complete enumeration of 6 types for ν=4:**

| Type | Structure | Leaves | Best Strategy |
|------|-----------|--------|---------------|
| K̄₄ | Empty (all disjoint) | N/A | Trivial (τ≤8) |
| P₄ | Path | 2 | **Leaf removal (Slot 36)** |
| K₁,₃ | Star | 3 | **Leaf removal (Slot 36)** |
| C₄ | Cycle | 0 | All-bridges (hard) |
| K₄-e | Almost complete | 0 | Pair decomposition |
| K₄ | Complete | 0 | V-decomposition (hardest) |

**KEY INSIGHT**: Path and Star have LEAVES → Slot 36 strategy applies!
- If τ(T_leaf) ≤ 2 proven, covers 3 of 6 sharing graph types
- Cycle (C₄) is hardest: opposite pairs NOT disjoint (Negation #8)

### Novel Approaches Identified
1. **Sharing graph case split**: Prove by exhaustion over 6 types
2. **Leaf-first strategy**: Slot 36 covers Path + Star cases
3. **Bridge vertex concentration**: All bridges through shared vertex v
4. **Hypergraph transfer**: Use proven r=4 lemmas as scaffolding
5. **Fractional rounding**: Prove small integrality gap for ν≤4

---

## CRITICAL NEGATIONS (From Failed Approaches)

| # | Assumption | Why FALSE | Counterexample |
|---|------------|-----------|----------------|
| 8 | Cycle opposite pairs disjoint | e₁,e₃ can share vertices | C₄ with shared vertices |
| 9 | S_e cover absorbs bridges | Bridges escape | 5-vertex explicit example |
| 10 | Path non-adjacent disjoint | Can form hidden cycle | Path that wraps around |
| 11 | Bridges form matching | Share >1 vertex | t₁={0,1,3}, t₂={0,1,4} |
| 12 | Outer vertex unique | Repeats across bridges | Multiple bridges through v |

**LESSON**: All "nice" structural assumptions fail. Must use proven bounds only.
