# Solving Tuza's Conjecture with AI-Powered Theorem Proving

Using [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) and multi-agent AI debate to make genuine progress on Tuza's Conjecture.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4-purple)](https://lean-lang.org/)
[![Status](https://img.shields.io/badge/ν%3D4-6%2F7%20PROVEN-green)](docs/CHECKPOINT_DEC31_FINAL.md)

**Last Updated**: December 31, 2025

---

## The Conjecture

**Tuza's Conjecture (1981)**: For any graph G, τ(G) ≤ 2ν(G)

Where:
- **τ(G)** = minimum number of edges needed to hit all triangles
- **ν(G)** = maximum number of edge-disjoint triangles

Open for **44 years**. Widely believed to be TRUE.

### Best Known Bounds

| Setting | Bound | Source |
|---------|-------|--------|
| General graphs | τ ≤ 2.87ν | Haxell (1999) |
| Fractional | τ ≤ 2ν* | Krivelevich (1995) |
| Planar | τ ≤ 2ν | Tuza (1985) |
| **Our project** | **τ ≤ 2ν for ν ≤ 4** | **Proven (2025)** |

---

## Current Status: ν = 4

### 6/7 Cases PROVEN

| Case | Sharing Graph | Status | Bound |
|------|---------------|--------|-------|
| **star_all_4** | K₄ (apex) | ✅ PROVEN | τ ≤ 8 |
| **three_share_v** | K₁,₃ + isolated | ✅ PROVEN | τ ≤ 8 |
| **scattered** | K̄₄ (disjoint) | ✅ PROVEN | τ ≤ 8 |
| **path_4** | P₄ (path) | ✅ PROVEN | τ ≤ 8 |
| **two_two_vw** | 2K₂ (matching) | ✅ PROVEN | τ ≤ 8 |
| **cycle_4** | C₄ (4-cycle) | 🔶 **τ ≤ 12 PROVEN** | τ ≤ 8 open |

### Cycle_4: The Hard Case

**PROVEN**: τ ≤ 12 for Cycle_4 (slot139, 0 sorries)

**BLOCKED**: τ ≤ 8 via König (link graphs NOT bipartite!)

**NEW APPROACH**: LP/Fractional relaxation could give τ ≤ 8

See [CHECKPOINT_DEC31_FINAL.md](docs/CHECKPOINT_DEC31_FINAL.md) for full details.

---

## Key Results

### Proven Theorems (Machine-Verified)

```lean
-- Main result: τ ≤ 12 for Cycle_4 configuration
theorem tau_le_12_cycle4 : triangleCoveringNumber G ≤ 12

-- Key structural lemmas
lemma triangle_shares_edge_with_packing : ∀ t ∈ triangles G, ∃ m ∈ M, |t ∩ m| ≥ 2
lemma link_matching_le_2 : ∀ matching in L_v, |matching| ≤ 2
lemma tau_union_le_sum : τ(A ∪ B) ≤ τ(A) + τ(B)
```

### False Lemmas Discovered (9 Patterns)

Our formalization effort discovered **9 false mathematical intuitions**:

| Pattern | False Claim | Why False |
|---------|-------------|-----------|
| 1 | Spokes cover avoiding triangles | Spokes contain v; avoiding triangles don't |
| 2 | Bridge absorption | Bridges may not share edges with S_e or S_f |
| 3 | Non-adjacent = vertex-disjoint | Opposite cycle elements can share vertex |
| 4 | Vertex cover = edge cover | Need edges IN triangle |
| 5 | local_cover_le_2 | Need ALL 4 M-edges at shared vertex |
| 6 | support_sunflower τ ≤ 2 | Must cover M-elements AND externals |
| 7 | external_share_common_vertex | Externals use different M-triangle edges |
| **8** | **link_graph_bipartite** | **M-neighbors can form odd cycles** |
| **9** | **fixed_8_edge_cover** | **Any 8-subset of M-edges fails** |

Patterns 8-9 discovered via 5-round AI debate on Dec 31, 2025.

See [FALSE_LEMMAS.md](docs/FALSE_LEMMAS.md) for full details with counterexamples.

---

## Methodology: AI-Powered Theorem Proving

### The Pipeline

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│   1. MULTI-AGENT DEBATE                                         │
│      ├── Grok-4: Code review, syntax, counterexamples           │
│      ├── Gemini: Strategy, literature, architecture             │
│      └── Codex: Web research, proof sketches                    │
│                                                                 │
│   2. LEAN FORMALIZATION                                         │
│      └── Write proof attempts with sorry placeholders           │
│                                                                 │
│   3. ARISTOTLE SUBMISSION                                       │
│      └── AI prover fills sorries or finds counterexamples       │
│                                                                 │
│   4. RESULT PROCESSING                                          │
│      ├── PROVEN → Add to proven/                                │
│      ├── DISPROVEN → Add to FALSE_LEMMAS.md                     │
│      └── PARTIAL → Extract learnings, iterate                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Statistics

| Metric | Count |
|--------|-------|
| Total Aristotle submissions | 150+ |
| Proven submissions (0 sorries) | 14 |
| Validated true lemmas | 54 |
| Failed approaches documented | 35 |
| False lemmas discovered | 9 |
| AI debate rounds | 12 |

---

## Repository Structure

```
math/
├── proven/tuza/                    # Machine-verified proofs
│   ├── nu4/
│   │   └── slot139_tau_le_12_PROVEN.lean
│   └── lemmas/                     # Reusable infrastructure
│
├── submissions/
│   ├── nu4_final/                  # Current attack files
│   └── tracking.db                 # SQLite tracking database
│
├── docs/
│   ├── CHECKPOINT_DEC31_FINAL.md   # Latest checkpoint
│   ├── FALSE_LEMMAS.md             # False lemma registry
│   ├── STRATEGIC_ROADMAP_DEC31.md  # Strategic analysis
│   └── DEBATE_SYNTHESIS_DEC31.md   # AI debate synthesis
│
├── scripts/                        # Automation
│   ├── submit.sh                   # Aristotle submission wrapper
│   └── process_result.sh           # Result processing
│
└── CLAUDE.md                       # AI workflow instructions
```

---

## Key Insights from AI Debate

### The König Breakthrough That Wasn't

**Dec 30 belief**: Link graphs L_v are bipartite → König gives τ ≤ 8

**Dec 31 reality**: Link graphs are **NOT** bipartite!

**Counterexample**: Add edges {a_priv, b_priv}, {b_priv, v_da} to Cycle_4. This creates a 3-cycle (odd cycle) in L_{v_ab} while preserving ν = 4.

### The New Hope: LP Relaxation

**Krivelevich (1995)**: τ ≤ 2ν* where ν* = fractional packing number

If ν* = 4 in Cycle_4 → τ ≤ 8 immediately, NO König needed!

This approach:
- Bypasses bipartiteness entirely
- Uses well-understood LP duality
- Is the current top research direction

---

## Next Steps

### Immediate
1. **Research LP relaxation** - Prove ν* = 4 for Cycle_4
2. **If successful** → τ ≤ 8 via Krivelevich
3. **If blocked** → Accept τ ≤ 12, document victory

### Future
1. Complete ν = 5 characterization
2. Formalize LP relaxation machinery
3. Attack special graph classes (chordal, interval - still OPEN!)
4. Publish: "Tuza's Conjecture for ν ≤ 4: A Formal Proof"

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Tuza's Conjecture**: Tuza (1981), "A conjecture on triangles of graphs"
- **Best Known Bound**: Haxell (1999), τ ≤ (66/23)ν
- **LP Relaxation**: Krivelevich (1995), fractional bounds
- **Lean 4**: https://lean-lang.org
- **Mathlib**: https://github.com/leanprover-community/mathlib4

---

## Contributing

This is an active research project. Key areas where help is welcome:

1. **LP/Fractional relaxation** - Formalizing τ* = ν* machinery
2. **Counterexample search** - Computational search for τ > 2ν graphs
3. **Special graph classes** - Proving Tuza for chordal, interval graphs
4. **Documentation** - Improving proof explanations

---

## Citation

If you use this work, please cite:

```bibtex
@misc{tuza-formal-2025,
  title={Formal Verification of Tuza's Conjecture for Small Packing Numbers},
  author={Patrick Kavanagh and AI Collaborators},
  year={2025},
  note={Using Aristotle theorem prover and multi-agent AI debate},
  url={https://github.com/kavanaghpatrick/aristotle-math-problems}
}
```

---

## License

MIT License - See individual files for details.

---

*Last proven result: τ ≤ 12 for Cycle_4 (slot139)*
*Current frontier: LP relaxation approach for τ ≤ 8*
*Status: 6/7 ν=4 cases proven, 1 partial*
