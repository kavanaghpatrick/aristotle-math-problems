# Round 2 Debate Consensus: Approach B (Shared Edges)

## Voting Results

| AI | Vote | Confidence |
|----|------|------------|
| **Grok** | Approach B (Shared Edges) | High |
| **Gemini** | Approach B (Shared Edges) | High |
| **Codex** | (Previous round favored similar) | Medium |

**CONSENSUS: 2/3 vote for Approach B**

## What is Approach B?

### Core Insight
The 4 shared vertices (v_ab, v_bc, v_cd, v_da) are the key. The PROVEN lemma `bridges_contain_shared_vertex` shows every bridge triangle contains at least one of these vertices.

### Strategy
1. **Define shared edges**: Pick edges incident to each shared vertex
2. **Prove coverage**: These edges cover all bridge triangles
3. **Bound**: τ(bridges) ≤ 4 × 2 = 8 (or better with overlap)

### Why This Approach?
- Builds on PROVEN lemmas (bridges_contain_shared_vertex, tau_containing_v_in_pair_le_4)
- Avoids FALSE patterns (local_cover_le_2, bridge_absorption)
- Constructive - provides explicit cover

## Proposed Lemmas (from AI Debate)

### From Grok:
1. `define_shared_edges` - Formalize 4 shared edges at each vertex
2. `shared_edges_hit_all_bridges` - Prove these cover all bridges
3. `tau_bridges_le_4_via_shared_edges` - Get τ(bridges) ≤ 4

### From Gemini:
1. `Se_cover_exists_with_spoke` - Local covers can use edges at shared vertices
2. `bridges_covered_by_docked_cover` - Spokes at shared vertices cover bridges "for free"

### Combined Strategy:
Use **Link Graph** approach:
- Triangles at v ↔ edges in link graph G[N(v)]
- τ(triangles at v) = vertex_cover(link graph)
- Vertex cover ≤ 2 × matching
- Need to prove: matching in link graph ≤ 2

## Files Ready for Submission

1. **slot120_shared_edges_foundation.lean**
   - Bridge definition and shared vertex containment
   - Foundation for shared edge coverage

2. **slot121_spoke_cover_exists.lean**
   - Gemini's key lemma: Se covers can use spokes at shared vertices
   - Base edge + spoke construction

3. **slot122_link_graph_cover.lean**
   - Link graph definition and bijection
   - Vertex cover → triangle cover reduction
   - Key claim: link_matching_le_2

## Potential Failure Modes (from debate)

1. **Definition ambiguity**: "Shared edges" may not be uniquely formalizable
2. **Tightness issues**: local_cover_le_2 is FALSE (can need 4 edges locally)
3. **Non-disjoint coverage**: Shared edges may overlap in coverage
4. **Link graph not bipartite**: König's theorem doesn't directly apply

## Key Open Question

The critical missing piece is proving:
```
link_matching_le_2: matching(link graph at v) ≤ 2
```

If this is TRUE, we get τ(triangles at v) ≤ 4, and with 4 shared vertices:
- τ ≤ 16 (naive partition)
- τ ≤ 8 (with proper overlap exploitation)

## Status

- [x] Round 1 debate complete
- [x] Round 2 consensus reached
- [x] Submission files created
- [ ] Submit to Aristotle (network issue - DNS unreachable)

## Next Steps

1. When network is restored, submit slots 120-122
2. Monitor Aristotle results for slots 110, 113-116 (already submitted)
3. If link_matching_le_2 fails, try alternative approaches:
   - SAT/SMT enumeration (Gemini's suggestion)
   - Fractional relaxation bounds
   - Case split on link graph structure
