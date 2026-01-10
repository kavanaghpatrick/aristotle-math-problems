# CYCLE_4 ROUND 3 CONSENSUS PROPOSAL
## January 4, 2026 - Debate Moderator Synthesis

---

## PREAMBLE: What We Have Learned

After 7 rounds of intensive debate (December 29-30, 2025), the AI agents have:

1. **Disproved** multiple naive approaches (4+4, sunflower, fixed 8-edge covers)
2. **Proven** tau <= 12 is achievable (slot139)
3. **Identified** the External/Bridge distinction as CRITICAL
4. **Discovered** Pattern 17-21 (five new false lemmas)

The current state is a 4-edge gap: we can prove tau <= 12, but Tuza requires tau <= 8.

---

## SECTION 1: REFRAMING THE COUNTING PROBLEM

### The Triangle Taxonomy for Cycle_4

Given M = {A, B, C, D} in cycle configuration (A-B-C-D-A):

| Category | Definition | Count Bound | Cover Strategy |
|----------|------------|-------------|----------------|
| **M-elements** | The 4 triangles in M | Exactly 4 | Each needs ~1-2 edges from its edges |
| **True Externals** | T shares edge with EXACTLY ONE X in M | Up to 4 per vertex | Fan structure around apex |
| **Bridges (Multi-M)** | T shares edges with 2+ M-elements | Unknown | Must handle separately |

### Critical Clarification from Round 2

**Externals vs Bridges are DISJOINT by definition:**
- `isExternalOf G M A T` = T shares edge with A AND with NO other M-element
- Bridges = T shares edges with 2+ M-elements
- These partition all non-M triangles: every triangle sharing edge with M is either:
  - An M-element itself, OR
  - External to exactly one M-element, OR
  - A bridge across 2+ M-elements

### The Proven Structural Lemma

**`triangle_contains_shared`**: Every triangle T in cycle_4 contains at least one shared vertex (v_ab, v_bc, v_cd, or v_da).

**Implication**: All triangles can be partitioned by which shared vertex they contain. At each shared vertex v, we have:
- M-elements containing v (exactly 2)
- Externals of those M-elements at v
- Bridges that contain v

---

## SECTION 2: THE KEY LEMMA ALL AGENTS MUST AGREE ON

### Proposed Key Lemma: `externals_at_v_tau_le_2`

**Statement**:
```
At shared vertex v in cycle_4, the set of all triangles containing v
can be covered by at most 2 edges.
```

**Why This Is Key**:
- 4 shared vertices x 2 edges = 8 edges total
- This directly implies tau <= 8

### Sub-lemmas Required

1. **Fan apex for externals using SAME M-element** (PROVEN: slot224f)
   - If T1, T2 are externals of same M-element A, using DIFFERENT A-edges, they share common external vertex x

2. **Fan apex for externals using DIFFERENT M-elements** (DISPUTED)
   - Pattern 6 counterexample: T1 = {v_ab, a', x1} uses edge from A, T2 = {v_ab, b', x2} uses edge from B
   - Counterexample claims x1 != x2 is possible
   - This breaks the naive 4+4 approach

3. **Bridge handling** (NOT ADDRESSED)
   - Bridges like {v_ab, a_priv, b_priv} need separate treatment
   - Do they break the 2-edge-per-vertex bound?

---

## SECTION 3: LIKELIHOOD ASSESSMENT

### tau <= 8

| Approach | Confidence | Blocker |
|----------|------------|---------|
| Naive 4x2 (sunflower) | 0% | Pattern 6-7 disproved |
| Fixed 8-edge cover | 0% | Pattern 9 disproved |
| Adaptive via Konig | 40% | Konig not in Mathlib, complex formalization |
| Link graph + bipartiteness | 35% | Pattern 20-21 show gaps in approach |
| Fan structure (1+1 per M) | 50% | Current best bet, needs bridge handling |

### tau <= 12

| Approach | Confidence | Status |
|----------|------------|--------|
| All 12 M-edges | 95% | slot139 PROVEN |
| 3 edges per vertex | 90% | Trivial fallback |

### tau <= 10

| Approach | Confidence | Notes |
|----------|------------|-------|
| 2.5 edges/vertex avg | 60% | Not explored in detail |
| Hybrid approach | 55% | May be simpler than full tau <= 8 |

**CONSENSUS ASSESSMENT**: tau <= 8 has ~40% chance with current tools. tau <= 12 is proven. tau <= 10 might be a valuable intermediate target.

---

## SECTION 4: CONSENSUS PROPOSAL

### What All Agents Should Agree On

1. **tau <= 12 is PROVEN** and we should not revisit this.

2. **Pattern 6-7 are REAL blockers** - the naive fan apex assumption fails for externals using different M-elements at the same shared vertex.

3. **Pattern 17 (Bridge Externals)** is a REAL phenomenon - triangles like {v_ab, a_priv, b_priv} share edges with BOTH A and B, and are NOT counted as externals of either.

4. **The Key Challenge**: At shared vertex v_ab, we have:
   - M-elements: A, B (need ~2 edges to cover)
   - Externals of A at v_ab (form fan around x_A)
   - Externals of B at v_ab (form fan around x_B, possibly x_B != x_A)
   - Bridges: {v_ab, a_priv, b_priv} etc.

   Can we cover ALL of these with just 2 edges from v_ab?

5. **The Answer Depends On**: Whether x_A = x_B (all externals share apex) or x_A != x_B (externals split).

---

## SECTION 5: CONCRETE NEXT STEP

### Proposed Next Action: Prove or Disprove `bridge_externals_share_apex`

**Statement to investigate**:
```
At shared vertex v_ab, if T1 is external of A and T2 is external of B,
both containing v_ab, then T1 and T2 share a common external vertex.
```

**If TRUE**: Then 2 edges from v_ab suffice (the spokes to x and one M-edge)
**If FALSE**: Then tau <= 8 via vertex-local approach is BLOCKED

### Methodology

1. **Attempt counterexample construction**:
   - Build cycle_4 with specific external triangles at v_ab
   - Try to make T1 = {v_ab, a', x1} and T2 = {v_ab, b', x2} with x1 != x2
   - Verify nu = 4 is maintained

2. **Attempt proof via nu = 4 constraint**:
   - If x1 != x2, can we form a 5-packing?
   - The extra triangles would be T1, T2 plus... what?

3. **Submit to Aristotle**:
   - If proof direction seems sound, formalize in Lean
   - Let Aristotle find the gaps

---

## SECTION 6: WHAT NOT TO DO

### Avoid These Mistakes

1. **DO NOT assume externals partition by M-element** (Pattern 17)
2. **DO NOT assume common edge in sunflower** (Pattern 16, 18)
3. **DO NOT assume fixed cover works** (Pattern 9)
4. **DO NOT assume Link Graph covers all triangles** (Pattern 21)
5. **DO NOT use Konig's theorem** (not in Mathlib, complexity trap)

---

## SECTION 7: FALLBACK STRATEGY

If tau <= 8 proves intractable:

1. **Accept tau <= 12** for cycle_4 (already proven)
2. **Investigate tau <= 10** as intermediate result
3. **Try alternative cycle_4 decompositions**:
   - Adjacent pairs: T_pair(A,B) and T_pair(C,D)
   - Opposite pairs: T_pair(A,C) and T_pair(B,D) (but A,C share no vertex...)
   - Greedy algorithm with proof of bound

4. **Consider LP relaxation**:
   - Prove nu* = 4 directly
   - Use tau <= 2*nu* (Krivelevich)
   - This avoids constructive cover

---

## MODERATOR'S VERDICT

### The Single Most Important Question

**Can externals of A and externals of B at shared vertex v_ab share a common apex vertex?**

- If YES (they must share due to nu=4): tau <= 8 is achievable
- If NO (they can have different apexes): tau <= 8 via this approach is BLOCKED

### Recommended Immediate Actions

1. **Agent Task**: Construct explicit counterexample OR prove impossibility of x_A != x_B
2. **Parallel**: Submit any tau <= 10 approaches that avoid this question
3. **Fallback**: Continue treating tau <= 12 as the proven result

### Sign-Off Request

All agents should confirm:
- [ ] Pattern 6-7 are real blockers
- [ ] Pattern 17 (bridge externals) must be handled
- [ ] The x_A = x_B question is the key
- [ ] tau <= 12 is our proven baseline
- [ ] Further work focuses on bridge_externals_share_apex

---

## APPENDIX: Summary of All False Lemmas (Patterns 1-21)

| # | Pattern | Impact on tau <= 8 |
|---|---------|-------------------|
| 1 | local_cover_le_2 | Blocks 4x2 sunflower |
| 6 | external_share_common_vertex | Blocks naive 4+4 |
| 7 | sunflower_cover_at_vertex_2edges | Blocks 4x2 approach |
| 9 | fixed_8_edge_M_subset | Blocks fixed covers |
| 16 | helly_three_triangles | Blocks common edge claim |
| 17 | externals_partition_by_M_element | Bridges exist! |
| 18 | common_edge_in_cluster | No sunflower center edge |
| 20 | four_vertex_cover | Link graph approach incomplete |
| 21 | trianglesThroughVinS domain | Link graph misses externals |

---

*This consensus proposal was synthesized from 7 rounds of AI debate and the full FALSE_LEMMAS.md documentation. The moderator recommends focusing all future work on the bridge_externals_share_apex question.*
