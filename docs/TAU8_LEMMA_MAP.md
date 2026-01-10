# τ ≤ 8 Lemma Dependency Map

## Status: 2026-01-09

### PROVEN LEMMAS (by Aristotle)

| # | Lemma | Source | Dependencies | Purpose |
|---|-------|--------|--------------|---------|
| 1 | `triangle_card_three` | slot319, 321 | None | Basic: T ∈ cliqueFinset 3 → T.card = 3 |
| 2 | `sharesEdgeWith_iff_card_inter_ge_two` | slot319, 321 | None | Iff for edge sharing |
| 3 | `external_inter_card_two` | slot319, 321 | 1, 2 | External T ∩ X has card 2 |
| 4 | `packing_inter_le_one` | slot319 | None | Packing elements share ≤1 vertex |
| 5 | `nonpacking_shares_edge` | slot319, 321 | 2 | Non-M shares edge with some M |
| 6 | `edge_in_sym2_iff` | slot319, 321 | None | s(u,v) ∈ T.sym2 ↔ u,v ∈ T |
| 7 | `triangle_classification` | slot319 | 5 | T is M, external, or bridge |
| 8 | `m_element_covered_by_own_edge` | slot319 | 6 | X covered by its edges |
| 9 | `external_covered_by_shared_edge` | slot319 | 6 | External has edge with X |
| 10 | `bridge_covered_by_some_m_edge` | slot319, 321 | 6 | Bridge shares edge with M |
| 11 | `two_externals_share_X_vertex` | slot319 | 3 | PAIRWISE: Two externals share v ∈ X |
| 12 | `apex_edges_cover_X_external` | slot319 | 3 | If v in both X and T, ∃w with s(v,w) ∈ T.sym2 |
| 13 | `two_externals_share_edge` | slot321 | 1, 2 | Two externals share edge (packing argument) |
| 14 | `common_external_vertex` | slot321 | 3, 13 | KEY: Different-edge externals share t ∉ X |

### GAP ANALYSIS

**The PAIRWISE → UNIVERSAL gap:**
- `two_externals_share_X_vertex` proves: ∀ T₁ T₂, ∃ v ∈ X, v ∈ T₁ ∧ v ∈ T₂
- `common_external_vertex` proves: If different edges, ∃ t ∉ X in both
- NEEDED: `universal_apex_exists`: ∃ apex, ∀ T external, apex ∈ T

**The covering gap:**
- We have lemmas proving externals can be covered
- NEEDED: Construct explicit cover from apex

### WHAT'S STILL NEEDED (0-1 sorry each)

| Lemma | Sorry | Dependencies | Strategy |
|-------|-------|--------------|----------|
| `universal_apex_exists` | 1 | 11, 14 | Case split on # supported edges |
| `cover_with_internal_apex` | 1 | 6, 12 | If apex ∈ X, use two X-edges through apex |
| `cover_with_external_apex` | 1 | 6, 14 | If apex ∉ X, use {s(a,t), s(b,c)} |
| `cover_no_externals` | 1 | 6 | Any 2 edges of X work |
| `two_edges_cover_X_and_externals` | 1 | above 4 | Combine cases |
| `tau_le_8` | 1 | above + 7, 10 | Sum over M |

### SUBMISSION PLAN

**Phase 1: Prove `universal_apex_exists` (slot325)**
- Include ALL proven scaffolding (14 lemmas)
- 1 sorry target
- Proof sketch: case split by supported edges

**Phase 2: Prove covering lemmas (slot326-328)**
- `cover_with_internal_apex`
- `cover_with_external_apex`
- `cover_no_externals`
- Each with 1 sorry

**Phase 3: Final assembly (slot329)**
- `tau_le_8` with all helpers proven
- 1 sorry target

### CRITICAL INSIGHT FROM GROK

Case split by "supported edges" (edges of X with ≥1 external):
- 0 supported: No externals → any 2 edges
- 1 supported: All externals on same edge → common vertex IN X
- 2 supported: Two edges have externals → shared vertex v ∈ X
- 3 supported: All edges have externals → common t ∉ X (use common_external_vertex)

This decomposition helps Aristotle because each case is simpler.
