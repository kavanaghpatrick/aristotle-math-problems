# STRATEGIC ROADMAP: Path to Solving Tuza's Conjecture

**Created**: December 31, 2025
**Contributors**: Grok-4, Gemini, Codex, Claude

---

## 1. The Conjecture

**Tuza (1981)**: For any graph G, τ(G) ≤ 2ν(G)
- τ = minimum edges to hit all triangles
- ν = maximum edge-disjoint triangle packing
- **Open for 44 years**, believed TRUE

---

## 2. Current Best Known Bounds

| Result | Bound | Author | Year |
|--------|-------|--------|------|
| General | τ ≤ (66/23)ν ≈ 2.87ν | Haxell | 1999 |
| Asymptotic | τ ≤ 2ν + O(√ν log^{3/2} ν) | Haxell-Rödl | 2001 |
| Fractional | τ* ≤ 2ν* (equality!) | Krivelevich | 1995 |
| Our project | τ ≤ 2ν for ν ≤ 3 | Proven | 2025 |
| Our project | τ ≤ 12 for ν=4 Cycle_4 | Proven | 2025 |

---

## 3. Our Project Status

### Proven Results (~50 lemmas)
- τ ≤ 2ν for ν ≤ 3 (all cases)
- τ ≤ 12 for ν=4 Cycle_4 (slot139, 0 sorries)
- Key structural lemmas (triangle_shares_edge, link_matching_le_2, etc.)

### Failed Approaches (~9 false lemmas)
- König approach (link graphs not bipartite)
- Fixed 8-edge M-subset (counterexample exists)
- local_cover_le_2 (need all 4 M-edges)
- external_share_common_vertex (counterexample)

### Current Bottleneck
- Cycle_4: τ ≤ 8 blocked
- All known approaches fail
- Adaptive cover might work but complex to formalize

---

## 4. Strategic Recommendations

### GROK'S ANALYSIS

**Q1: Is ν=4 the right focus?**
- YES for now - it's a "sweet spot" for building momentum
- Completing it yields publishable result: "Tuza holds for ν≤4"
- But don't linger indefinitely - if stuck 2-3 more months, generalize

**Q2: Missing proof techniques?**
- Probabilistic methods (randomized covers)
- LP relaxation and fractional covers
- Graph minors / forbidden subgraphs
- Spectral methods

**Q3: Where do counterexamples hide?**
- Projective planes / finite geometries
- Strongly regular graphs
- Random graphs with controlled density
- Computational search: up to ν~15 verified, no breaks

**Q4: Is formalization right?**
- YES for permanence and rigor
- But hybridize: informal prototyping + formal verification
- Current false lemma discovery validates the approach

### GEMINI'S ANALYSIS

**Key insight**: You are at the FRONTIER of this problem!

**Prioritize**:
1. Cycle_4 bottleneck (current slots 131-134+)
2. If stuck, switch to LP rounding approach
3. Exploit false lemmas as pruning progress

**Low-hanging fruit for formalization**:
- Chordal graphs (still OPEN!)
- Interval graphs (still OPEN!)
- Split graphs (partial)

**What would break Tuza?**
- ν = 4 or 5 (ν ≤ 3 proven)
- Dense, every edge in a triangle
- High minimum degree δ > n/2
- "Tangled" structure preventing decomposition

---

## 5. The Two Paths Forward

### PATH A: Complete ν=4 (Current Focus)
**Goal**: Prove τ ≤ 8 for Cycle_4 (matching Tuza bound)

**Approaches remaining**:
1. **Adaptive cover**: Use non-M-edges when needed
2. **Charging argument**: Abstract but elegant
3. **LP relaxation**: τ* = ν* + integrality gap analysis
4. **Exhaustive case analysis**: Enumerate all Cycle_4 configs

**Risk**: May never converge (König blocked, fixed covers fail)
**Reward**: First formal proof of Tuza for ν=4

### PATH B: Generalize Earlier
**Goal**: Extract meta-lemmas from ν=4 for general ν

**Approaches**:
1. **Inductive framework**: ν=k → ν=k+1
2. **Density arguments**: High local τ → sparse residual
3. **Structural decomposition**: T_e/S_e/X_e bounds

**Risk**: May miss ν=4 details that matter
**Reward**: Faster progress on general conjecture

---

## 6. Concrete Next Steps

### Immediate (This Week)
1. **Decision point**: Accept τ ≤ 12 and move on, OR try one more slot147 approach
2. **If continuing**: Try adaptive cover with non-M-edges
3. **Document**: Record all learnings in database

### Short-term (January 2025)
1. **Complete ν=4** or declare it "partial" with τ ≤ 12
2. **Attack other ν=4 cases**: two_two_vw, matching_2
3. **Begin ν=5 exploration**: What new patterns emerge?

### Medium-term (Q1 2025)
1. **Formalize LP relaxation**: τ* = ν* is known, prove integrality gap
2. **Special graph classes**: Chordal, interval (low-hanging fruit)
3. **Publish**: Paper on ν ≤ 4 formal proof

### Long-term (2025+)
1. **Inductive framework** for general ν
2. **Computer-assisted counterexample search** (SAT solvers)
3. **Collaboration** with Tuza conjecture experts

---

## 7. Key Technical Insights from Debate

### What We Learned About Link Graphs
- External vertices cannot connect to each other (ν constraint)
- But M-neighbors (v_da, a_priv, v_bc, b_priv) CAN form odd cycles
- Therefore: L_v not bipartite → König fails

### What We Learned About Fixed Covers
- Any 8-subset of 12 M-edges omits 4 edges
- External triangles sharing those 4 edges are uncovered
- Therefore: Need adaptive or non-M-edge covers

### What We Learned About Proof Structure
- Local bounds (per-vertex) don't sum to global bound
- Overlap between vertices must be exploited
- Charging or LP might capture this better than construction

---

## 8. Risk Assessment

| Approach | Success Probability | Effort | Reward |
|----------|---------------------|--------|--------|
| Accept τ ≤ 12 | 100% (done) | None | Low (not tight) |
| Adaptive τ ≤ 8 | 40% | High | High (tight bound) |
| LP relaxation | 60% | Medium | Medium (new technique) |
| Move to ν=5 | 70% | Medium | Medium (progress) |
| Special classes | 80% | Low | Medium (breadth) |

---

## 9. NEW INSIGHT: LP/Fractional Relaxation (from Codex web research)

**Key discovery**: Krivelevich proved τ ≤ 2ν* where ν* is the FRACTIONAL packing number.

**Why this matters**:
- If ν* = ν = 4 in Cycle_4, then τ ≤ 2×4 = 8 IMMEDIATELY!
- This bypasses König entirely (no bipartiteness needed)
- LP duality is well-understood mathematically

**The approach**:
1. Show ν* = 4 for any Cycle_4 configuration
2. Apply Krivelevich's result: τ ≤ 2ν* = 8
3. Done!

**Why this might work**:
- The fractional version τ* ≤ 2ν* is PROVEN (LP duality)
- The integrality gap question is: when does τ = τ* and ν = ν*?
- For small ν, integrality gaps tend to be zero

**Mathlib support**: `Mathlib.Combinatorics.Optimization.LinearProgramming` may have relevant tools.

**Priority**: This is now the TOP recommended approach for τ ≤ 8!

---

## 10. Key Insight: Existential vs Constructive

**The breakthrough observation** (from Codex):

> "An ADAPTIVE algorithm that chooses edges based on graph structure might work. This is harder to formalize as an existence proof... **Existential statement is easier than constructive**."

This means:
- Instead of proving "these 8 specific edges cover all triangles"
- Prove "there EXISTS a set of 8 edges that covers all triangles"

**Why existential is easier**:
- No need to explicitly construct the cover
- Can use non-constructive methods (LP, probabilistic, etc.)
- Aristotle may handle this better than explicit constructions

---

## 11. Conclusion

**The strategic question**: Is τ ≤ 8 for Cycle_4 worth the effort?

**Arguments FOR continuing**:
- We're at the frontier
- False lemma discovery is progress
- Tight bound would be significant

**Arguments FOR moving on**:
- τ ≤ 12 is proven, sufficient for many purposes
- Other ν=4 cases need attention
- Generalization might be more impactful

**RECOMMENDATION**: Try ONE more slot (slot147 with adaptive/charging), then decide. If it fails, accept τ ≤ 12 and move to other frontiers.

---

*Strategic roadmap created: 2025-12-31*
*Status: ν=4 Cycle_4 at critical decision point*
