# E944 — The r-hierarchy: exactly which Lean statement falls (count)

## The Lean statements (verbatim from 944.lean)

```
IsErdos944 G k r  :=  G.IsCritical k  ∧  (∀ edges, G.IsCriticalEdges edges → r < edges.ncard)

erdos_944                  : answer ↔ ∀ k≥4, ∀ r≥1, ∃ V G, IsErdos944 G k r       -- the full problem
erdos_944.dirac_conjecture : answer ↔ ∀ k≥4,         ∃ V G, IsErdos944 G k 1       -- Dirac, all k≥4 at r=1
erdos_944.dirac_conjecture.k_eq_four : answer ↔      ∃ V G, IsErdos944 G 4 1       -- THE OPEN CASE
```

## Monotonicity in r (the hierarchy direction)

Fix `k`, fix the vertex/edge structure. The predicate
`P_r(G) := ∀ edges, IsCriticalEdges edges → r < edges.ncard`
says "every critical edge-set has size ≥ r+1", i.e. **the minimum size of a critical edge-set is ≥ r+1**.

Define `m(G) := min { |edges| : G.IsCriticalEdges edges }` = minimum critical-edge-set size.
(For any k-vertex-critical G with χ=k>0, the full edge set E is critical — deleting all edges gives χ=1<k — so the min is well-defined and ≤ |E|.)

Then `IsErdos944 G k r  ⟺  G is k-vertex-critical  ∧  m(G) ≥ r+1`, equivalently `m(G) > r`.

**Key fact: P_r is monotone DECREASING in r.** If `m(G) ≥ r+1` then `m(G) ≥ r'+1` for all `r' ≤ r`.
So:  IsErdos944 G k r  ⟹  IsErdos944 G k r'  for every  r' ≤ r  (same G, same k).

Therefore as a *statement about existence of some witness*:
- `∃G IsErdos944 G k r` is **monotone DECREASING in r**: existence for large r ⟹ existence for all smaller r ≥ 1.
- **r=1 is the WEAKEST / EASIEST existence claim** (hardest to *violate*, i.e. easiest to satisfy). It only asks: no critical edge-set of size 1, i.e. **no single critical edge**.
- `IsErdos944 G k r` for larger r is **STRICTLY STRONGER**: it demands the minimum critical-edge-set be large.

This confirms the team-lead's framing: at fixed k, **r=1 is the easiest case**, and resolving r=1 says nothing automatically about larger r (a witness with no single critical edge can still have a critical *pair*).

## What the k=4, r=1 resolution implies for the full problem

### If k=4,r=1 is TRUE (a 4-vertex-critical graph with no critical edge exists):
Then `erdos_944.dirac_conjecture` (`∀k≥4 at r=1`) becomes **fully TRUE**, because:
- k=4: the new witness.
- k≥5: already proven (Brown k=5, Jensen k≥5, Lattanzio k−1 not prime). The k=4 case is the *only* missing piece of Dirac's conjecture.
⟹ **`erdos_944.dirac_conjecture.k_eq_four = answer(True)` immediately closes `erdos_944.variants.dirac_conjecture` to TRUE as well.**

It does NOT immediately close the full `erdos_944` (the ∀r problem). That needs every r at every k≥4.
- For k≥5, every r is handled *for large k* by Martinsson–Steiner (∀ᶠ k), but NOT for ALL k≥5 at all r. So even the full problem's k≥5 slice is not fully closed by existing results — only the eventual-k slice. (See note below.)
- For k=4 specifically, the r≥2 cases would remain open even after r=1 is settled TRUE.

So: **k=4,r=1 TRUE  ⟹  Dirac's conjecture (the r=1 problem) fully resolved TRUE.** It is a *necessary* ingredient and the *last* ingredient for Dirac. It is NOT sufficient for the full ∀r `erdos_944`.

### If k=4,r=1 is FALSE (no such graph):
Then `∃ V G, IsErdos944 G 4 1` is False, so:
- `erdos_944.dirac_conjecture.k_eq_four` answer = **False**.
- `erdos_944.variants.dirac_conjecture` (`∀k≥4 ∃...`) is **False** (fails at k=4). Dirac's conjecture disproved.
- `erdos_944` (the full ∀k∀r) is also **False** (fails at k=4,r=1). The full problem disproved.

So a FALSE answer at k=4,r=1 is **decisive for all three** theorems at once (all become False), because k=4,r=1 sits at the bottom of both hierarchies (smallest k≥4, smallest r≥1).

## Logical summary table

| k=4,r=1 verdict | k_eq_four | variants.dirac_conjecture (∀k≥4, r=1) | erdos_944 (∀k≥4 ∀r≥1) |
|---|---|---|---|
| TRUE  | answer=True  | answer=True (k=4 was the only gap)        | still OPEN (r≥2 unsettled) |
| FALSE | answer=False | answer=False (fails at k=4)               | answer=False (fails at k=4,r=1) |

## Caveat on the full `erdos_944` even for k≥5

Martinsson–Steiner give `∀ᶠ k in atTop` for each r — i.e. for each r there is k₀(r) s.t. existence holds for k ≥ k₀(r). The Lean `erdos_944` demands ALL k≥4 and ALL r≥1 simultaneously. The "every r at large k" result does NOT cover small k at large r (e.g. k=5, r=1000). So the full `erdos_944` has open territory beyond k=4,r=1 regardless. The *named open target* of this squad is `k_eq_four` (k=4, r=1), and that is precisely the bottom-left cell whose resolution flips Dirac's conjecture.

## Practical consequence for the squad

- We are hunting the **easiest** existence instance (r=1, smallest k). If it does not exist, no harder instance at k=4 exists either, and Dirac is false.
- A construction (TRUE) is the target most peers should pursue; a non-existence proof (FALSE) would be the bigger result (disproves a 55-year-old Dirac conjecture) but must rule out ALL n.
- **The single Lean statement that falls is `erdos_944.dirac_conjecture.k_eq_four`.** Its resolution co-resolves `variants.dirac_conjecture` (and, if FALSE, the full `erdos_944`).
