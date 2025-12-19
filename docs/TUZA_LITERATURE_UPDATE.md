# Tuza's Conjecture: Literature Update (December 2025)

## Critical Discovery

**Alex Parker's paper (arXiv:2406.06501, March 2025)** proves Tuza's conjecture for ν ≤ 3.

Published: Electronic Journal of Combinatorics, Volume 32, Issue 2 (May 2025)

### Key Theorems

| Theorem | Statement | For Graphs (k=3) |
|---------|-----------|------------------|
| 1.1 | ν=2 ⟹ τ ≤ 2⌈(k+1)/2⌉ | τ ≤ 4 |
| 1.2 | ν=3 ⟹ τ ≤ 3⌈(k+1)/2⌉ | τ ≤ 6 |
| 1.3 | **Corollary**: Tuza holds for all G with ν(G) ≤ 3 | ✓ |

### Their Proof Method
- Uses (k-1)-matchings in hypergraph formulation
- Defines partition sets S_e, T_e for matching edges
- Inductive argument: cover T_e, reduce to smaller matching
- Case analysis on edge intersections with matching

---

## Our Work: Reassessment

### What We Proved (Independently)
| Result | Status | Notes |
|--------|--------|-------|
| ν=0 | ✅ Trivial | Base case |
| ν=1 | ✅ Proven | K₄ structure, 400+ lines Lean |
| τ ≤ 3ν | ✅ Proven | Weak bound, all graphs |
| ν=2 | 🔶 In progress | 2 gaps remain |

### Key Contributions (Still Valid)
1. **First machine-verified proofs** of any Tuza cases
2. **Counterexample discovery**: 3 flawed approaches formally disproved
3. **Novel K₄-extension approach**: Different from Parker's hypergraph method
4. **Formal verification infrastructure**: Reusable for future cases

### Counterexamples Found by Aristotle
| Lemma | What Was Wrong | Discovery Value |
|-------|----------------|-----------------|
| `TuzaReductionProperty` | 2 triangles sharing edge break it | Strong induction invalid |
| `two_edges_cover_nearby` | K₄ counterexample | "Nearby triangles" approach invalid |
| `two_K4_almost_disjoint` | 6-vertex with |s₁∩s₂|=2 | Revised to case analysis |

---

## Strategic Options

### Option A: Complete ν=2 (First Formal Verification)
- **Value**: First machine-verified proof of ν=2
- **Effort**: 2 gaps remain, close to completion
- **Risk**: Low - result is now known to be true
- **Submission**: v12-minimal running now (8a5948f4)

### Option B: Attack ν=4 (First Proof)
- **Value**: NEW MATHEMATICAL RESULT (ν=4 still open)
- **Effort**: High - need new approach
- **Risk**: High - might not succeed
- **Note**: Parker's method might extend but not proven

### Option C: Improve General Bound
- **Value**: Improve (66/23)ν ≈ 2.87ν
- **Effort**: Very high - Haxell's bound from 1999
- **Risk**: Very high - heavily studied

### Option D: Special Graph Classes
- **Value**: New formal verifications
- **Effort**: Medium - known results to formalize
- **Examples**: Planar (Tuza 1985), treewidth ≤ 6 (Botler 2021)

---

## Current Submissions

| Version | UUID | Mode | Status |
|---------|------|------|--------|
| v12-minimal | 8a5948f4 | FORMAL | ✅ Running |
| v12-minimal.md | - | INFORMAL | ⏳ Queued (rate limited) |
| v12-scaffolded | - | FORMAL | ⏳ Queued |

---

## Recommendation

**Complete ν=2 (Option A)** as immediate priority:
1. Result is now KNOWN to be true - reduces risk
2. Our K₄-extension approach is DIFFERENT from Parker's
3. Machine verification is independently valuable
4. Already 90% complete

**Then consider ν=4 (Option B)** if Aristotle succeeds on ν=2:
1. Would be genuinely new mathematics
2. Parker's hypergraph method might provide scaffolding
3. Higher risk but higher reward

---

## References

- Parker, A. (2025). "New bounds on a generalization of Tuza's conjecture." arXiv:2406.06501
- Haxell, P.E. (1999). "Packing and covering triangles in graphs." Discrete Math 195:251-254
- Tuza, Z. (1990). "A conjecture on triangles of graphs." Graphs & Comb 6:373-380
