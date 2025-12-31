# CYCLE_4 ROUND 5 SYNTHESIS - AI CONSENSUS
## December 30, 2025

---

## UNANIMOUS AGREEMENT ACROSS ALL THREE AIs

### 1. External Triangles CAN Exist ✓

All three AIs (Grok, Gemini, Codex) confirm:

**Construction:** T = {v_ab, b_priv, x_ext} where x_ext is external
- Add edges {v_ab, x_ext} and {b_priv, x_ext}
- Triangle T shares edge {v_ab, b_priv} with B
- ν(G) = 4 is maintained

### 2. Gemini's FIXED Cover FAILS ✓

All three AIs confirm the fixed 8-edge cover fails:

**Gemini's cover:**
- Cycle edges: {v_ab,v_da}, {v_ab,v_bc}, {v_bc,v_cd}, {v_cd,v_da}
- Private edges: {v_ab,a_priv}, {v_bc,b_priv}, {v_cd,c_priv}, {v_da,d_priv}

**Failure case:** T = {v_ab, b_priv, x_ext}
- {v_ab, b_priv}: NOT in cover
- {v_ab, x_ext}: NOT in cover
- {b_priv, x_ext}: NOT in cover
- **Triangle T is completely uncovered!**

### 3. τ ≤ 8 IS Achievable (with ADAPTIVE cover) ✓

All three AIs agree an adaptive 8-edge cover exists.

---

## KEY DISCOVERY: LINK GRAPH BIPARTITENESS

**Codex's critical insight:**

External vertices CANNOT form cliques in link graphs because:
- Triangle {v_ab, x_1, x_2} (where x_1, x_2 are external) would need to share edge with M
- But no edge of {v_ab, x_1, x_2} is in any M-element!
- This violates the proven edge-sharing lemma
- **Therefore:** External vertices can only connect to M-neighbors, not to each other

**Consequence:**
- Link graphs have star forest structure (bipartite)
- König's theorem applies: τ(L_v) = ν(L_v)
- ν(L_v) = 2 per corner (two M-elements contribute one edge each)
- τ(L_v) = 2 per corner
- **Total: 4 × 2 = 8 edges**

---

## ADAPTIVE COVER STRATEGY

### Algorithm
For each corner v:
1. Construct link graph L_v
2. Find minimum vertex cover (size 2 by König)
3. Include spokes {v, s} for each s in cover

### Key Difference from Gemini's Cover

**Gemini at v_ab:** Uses {v_da, v_bc} as vertex cover
- Covers {v_da, a_priv} ✓
- Covers {v_bc, b_priv} ✓
- Does NOT cover {b_priv, x_ext} ✗

**Correct adaptive at v_ab:** When external triangles attach to b_priv, use {v_da, b_priv}
- Covers {v_da, a_priv} ✓
- Covers {v_bc, b_priv} ✓
- Covers {b_priv, x_ext} ✓

---

## REMAINING QUESTION: FIXED vs ADAPTIVE

| Approach | Edge Count | Complexity |
|----------|------------|------------|
| Gemini's fixed cover | 8 | Low (but FAILS) |
| Adaptive cover | 8 | Medium-High |
| Fixed cover (all M-edges) | 12 | Low |

### Gemini's Pessimistic View
"Fixed cover needs 12 edges because adversary can attach satellite to any M-edge"

### Codex's Optimistic View
"Adaptive 8-edge cover always exists via König's theorem"

### Synthesis
Both are correct:
- **Fixed cover:** 12 edges needed (covers worst case)
- **Adaptive cover:** 8 edges sufficient (for any specific graph)

---

## ARISTOTLE STRATEGY OPTIONS

### Option A: τ ≤ 8 (ADAPTIVE)
**Pros:**
- Mathematically optimal
- Matches Tuza bound τ ≤ 2ν
- Beautiful proof via König's theorem

**Cons:**
- Complex formalization
- Requires link graph construction
- Requires König's theorem (or proof)
- Requires adaptive vertex cover computation

### Option B: τ ≤ 12 (FIXED)
**Pros:**
- Simple: just cover all 12 M-edges
- No adaptivity needed
- Easy to verify

**Cons:**
- Not tight (wastes 4 edges)
- Already proven (slot113)

### Option C: τ ≤ 10 (HYBRID)
**Pros:**
- Middle ground
- Potentially simpler than full adaptive

**Cons:**
- Need to design fixed cover that works for "most" cases
- May not exist

---

## CONSENSUS RECOMMENDATION

**Go for τ ≤ 8 with adaptive cover.**

### Proof Outline
1. At each corner v, construct link graph L_v
2. Prove L_v is bipartite (external vertices can't form edges - edge-sharing lemma)
3. Apply König: τ(L_v) = ν(L_v) = 2
4. Adaptive spoke selection: 4 corners × 2 = 8 edges
5. Coverage: every triangle contributes edge to some L_v

### Formalization Path
```lean
-- 1. Define link graph
def linkGraph (G : SimpleGraph V) (v : V) : SimpleGraph V := ...

-- 2. Prove bipartiteness
lemma linkGraph_bipartite (G : SimpleGraph V) (v : V)
  (hM : hasCycle4Packing G M) (hν : ν G = 4) :
  (linkGraph G v).Bipartite := ...

-- 3. Apply König
lemma tau_linkGraph_le_2 (G : SimpleGraph V) (v : V)
  (hbi : (linkGraph G v).Bipartite) :
  τ (linkGraph G v) ≤ 2 := ...

-- 4. Assemble
theorem tau_cycle4_le_8 (G : SimpleGraph V)
  (hM : hasCycle4Packing G M) (hν : ν G = 4) :
  τ G ≤ 8 := ...
```

---

## ROUND 5 QUESTIONS - ANSWERED

| Question | Answer |
|----------|--------|
| Q1: Can external triangles exist? | **YES** - explicit construction |
| Q2: Does Gemini's cover work? | **NO** - misses external triangles |
| Q3: Link graph bounds? | τ(L_v) = 2 via König |
| Q4: Fixed or adaptive? | **ADAPTIVE** required for 8 edges |
| Q5: Counterexample or proof? | **BOTH** provided |

---

## NEXT STEPS

1. **Round 6 needed?** No - we have consensus on τ ≤ 8 adaptive
2. **Formalize link graph approach in Lean**
3. **Submit to Aristotle**
4. **Fallback:** If too complex, submit τ ≤ 12 fixed cover

---

## AI RECOMMENDATIONS SUMMARY

| AI | Conclusion | Confidence |
|----|------------|------------|
| Grok | External triangles exist, cover fails | HIGH |
| Gemini | Fixed=12, Adaptive=8 | HIGH |
| Codex | τ ≤ 8 via König (bipartite link graphs) | HIGH |

**Consensus:** τ(cycle_4) ≤ 8 with adaptive spoke selection
