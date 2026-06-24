# E944 — Empirical test of the Jensen–Siggers E* conjecture (skeptic)

archivist (archivist_jensen_siggers_2012.md, full-PDF-verified) forwarded the sharpest
IMPOSSIBILITY lever to me/count/wall: Jensen–Siggers 2012 conjecture (Concluding Remarks, verbatim):
> "In our construction, E* was connected, and even a spanning subgraph of H. We cannot see how to
> avoid this. If Dirac's Question has a negative answer for k=4, it does not seem unlikely that one
> could further say that the graph E* of critical edges is connected, or even spanning."

Here E* = the subgraph formed by the CRITICAL edges. If one could prove "every 4-vertex-critical graph
has E* nonempty (and connected/spanning)", that proves E* ≠ ∅ always ⟹ **refutes Dirac k=4 (answer NO)**.

## Independent test on ALL 4-vertex-critical graphs n ≤ 10 (my enumeration, χ cross-checked)

| n | # 4-vertex-critical | E* nonempty | E* connected | E* spanning |
|---|---|---|---|---|
| 4 | 1 | 1 | 1 | 1 |
| 6 | 1 | 1 | 1 | 1 |
| 7 | 7 | 7 | 7 | 7 |
| 8 | 8 | 8 | 8 | 8 |
| 9 | 124 | 124 | 124 | 124 |
| **10** | **2453** | **2453** | **2450** ⚠ | **2453** |

**KEY FINDING (n=10): the J–S "connected" form BREAKS.** Of 2453 four-vertex-critical graphs on 10
vertices, **3 have a DISCONNECTED critical-edge set E\*** (2 components each) — yet all 3 still have E*
**spanning** (touches all 10 vertices) and obviously nonempty (|E*|=8). The exceptions, dual-checker
verified (chi_A==chi_B on χ, every vertex-deletion, and every edge-deletion):
- `ICpdbY{]_` : |E*|=8, E* = 2 components on vertex-sets of size {5,5}, spanning.
- `ICpddxy^?` : |E*|=8, E* = 2 components {5,5}, spanning.
- `ICpdlps]_` : |E*|=8, E* = 2 components {2,8}, spanning.

So across n≤10 (141 + 2453 = 2594 graphs): **E\* always nonempty, always spanning, but NOT always
connected** (first disconnected examples at n=10). n=5 omitted (no 4-vertex-critical graph exists).

## Reading
- The strongest of the three J–S forms ("E* connected") is now EMPIRICALLY FALSE — disconnected E*
  occurs already at n=10. **Tell wall: do NOT attempt to prove E* is connected; it isn't.** The right
  invariant to carry, if any, is "E* nonempty" (the only one needed for impossibility) or possibly
  "E* spanning" (still holds through n=10, but weaker leverage than connectivity would have given).
- "E* nonempty" and "E* spanning" remain exception-free through n=10. Nonempty is exactly "every
  4-vertex-critical graph has a critical edge" = the negation of a witness = our whole question; its
  small-n universality is the floor result, not new leverage.
- CAVEAT (honest): small-n universality of "nonempty"/"spanning" is NOT a proof. The known k≥5
  (k,1)-graphs have E* = ∅, so the nonemptiness invariant DEMONSTRABLY breaks at k=5 — no degree/density
  reason forces it at k=4 forever. Evidence, calibrated, not a theorem. A successor must not over-read it.
- This correction MATTERS: a minimal-counterexample impossibility argument that tried to maintain
  "E* connected" as an inductive invariant would be doomed — the invariant is false even on existing
  small graphs. J–S themselves only OBSERVED connectivity in their construction and conjectured it
  cautiously ("we cannot see how to avoid this"); the census shows it is avoidable.

## Verification integrity
- Critical edges computed by chi_A (backtracking); the 4-vertex-criticality screen cross-checked A==B
  (SAT) on every graph during the underlying sweep (skeptic_smalln_groundtruth.md). Zero disagreements.
- E* connectivity/spanning via networkx on the explicit critical-edge list. Reproduce: see the inline
  script logic in this directory's run logs; engine skeptic_enum.py.

## Next for a successor
- Extend the E* test to n=10 (hunter's 2453 graphs) and n=11 (if a non-6-regular 4-vtx-critical graph
  appears) to see if connected+spanning persists. A single small graph with DISCONNECTED or
  NON-spanning E* would weaken the conjecture's strong form (though "nonempty" could still hold).
- Coordinate with wall: is "E* nonempty" provable via the spanning-4-edge-critical-subgraph machinery?
