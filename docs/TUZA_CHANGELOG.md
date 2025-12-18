# Tuza Work Timeline/Changelog

This changelog documents the progression of Tuza work, including version submissions, key changes, and results.

## December 17-18, 2025

### v4 (d50cf3fb / b4549d16)
**Date:** Dec 18, 2025 07:51 CST
- First full Tuza attempt
- Strong induction via 2-edge reduction
- **Result:** FAILED - reduction property not proven

### v5 (e900e161 / ef7e7f99)
**Date:** Dec 18, 2025 ~08:00 CST
- Fixed variable naming bug from v4
- **Result:** MAJOR DISCOVERY
  - Aristotle found **COUNTEREXAMPLE** to TuzaReductionProperty
  - Graph: Two triangles {0,1,2} and {0,1,3} sharing edge {0,1}
  - Proved 10+ helper lemmas with full proofs
  - Proved conditional theorem: "If reduction property, then Tuza"

### v6 (380fb7d3 / cca06048)
**Date:** Dec 18, 2025 14:29 CST
- Corrected approach: NearbyTriangles direct construction
- 160 lines prescriptive (detailed strategy hints)
- **Result:** SECOND COUNTEREXAMPLE
  - K₄ counterexample disproves this approach too
  - Each nearby triangle shares only ONE edge with packing
  - Formally proven: `two_edges_cover_nearby_counterexample`

### v7 (a64e90b3 / 085f46d5)
**Date:** Dec 18, 2025 14:34 CST
- **Boris pattern:** 47 lines minimal
- Just definitions + theorem statement, no hints
- **Result:** PARTIAL SUCCESS - BEST OUTCOME
  - **PROVEN:** τ ≤ 3ν (weak Tuza, full formal proof ~120 lines)
  - **PROVEN:** τ(K₄) = 2ν(K₄) - K₄ is tight
  - **PROVEN:** τ(K₅) = 2ν(K₅) - K₅ is tight
  - Full conjecture τ ≤ 2ν NOT proven (expected)

### v8 (21873a56 / 4828661f)
**Date:** Dec 18, 2025 14:49 CST
- Scaffolded: 7 proven lemmas as building blocks
- No strategic hints (Grok rated 9/10)
- **Result:** Still running at time of documentation

## Key Events Summary

| Time | Event |
|------|-------|
| Dec 18, 07:51 | Initial v4 attempt with strong induction |
| Dec 18, ~12:00 | v5 output analyzed - counterexample discovered |
| Dec 18, 14:29 | v6 submitted with corrected approach |
| Dec 18, 14:34 | v7 (Boris pattern) submitted |
| Dec 18, ~16:00 | v6 output analyzed - SECOND counterexample |
| Dec 18, ~16:30 | v7 output analyzed - τ ≤ 3ν PROVEN |
| Dec 18, ~17:00 | Strategic decision: pivot from Tuza |
| Dec 18, ~18:00 | Full documentation created |

## Lessons Encoded

1. **v4→v5:** Bug fixes matter - variable naming broke pattern matching
2. **v5 output:** Counterexamples are valuable discoveries, not failures
3. **v6 failure:** Prescriptive approaches can be systematically disproved
4. **v7 success:** Boris pattern (minimal intervention) works best
5. **Overall:** Let AI explore freely → proves what it CAN prove

## Files Created

| Version | Formal UUID | Informal UUID | Key File |
|---------|-------------|---------------|----------|
| v5 | e900e161 | ef7e7f99 | tuza_SUCCESS_conditional.lean |
| v6 | 380fb7d3 | cca06048 | tuza_COUNTEREXAMPLE_v6.lean |
| v7 | a64e90b3 | 085f46d5 | tuza_PROVEN_weak_bound.lean |
| v8 | 21873a56 | 4828661f | tuza_FULL_v8_scaffolded.lean |
