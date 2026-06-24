# E944 — The density ledger: precise edge-count window for a (4,1)-witness (count)

Consolidated rigorous bounds on a hypothetical witness G (4-vertex-critical, no
critical edge), with sources. This is the "Kostochka–Yancey ledger made precise"
the team-lead asked for. All bounds are DERIVED or cited; none assume the witness
exists beyond the hypothesis.

## The constraints (all rigorous)

Let G be a (4,1)-graph on n vertices, m edges.

1. **n ≥ 11.** [Skottova–Steiner 2025 Prop 5.1, via proximity extraction]
   (Also: my exhaustive census rules out n ≤ 7 directly; hunter/skeptic push the
   exact floor higher. Prop 5.1 gives n ≥ 5r+6 = 11 for r=1.)

2. **min-degree δ(G) ≥ 6, and edge-connectivity λ(G) ≥ 6.** [Prop 5.1]
   ⟹ m ≥ 6n/2 = **3n**. (A (4,1)-graph is at least as dense as 6-regular.)

3. **max-degree Δ(G) ≤ n − 5.** [Prop 5.1]
   ⟹ m ≤ n(n−5)/2 (trivially), and more usefully no vertex dominates.

4. **wall's spanning lower bound (independent of Prop 5.1):**
   for every edge e, G−e contains a SPANNING 4-edge-critical subgraph H_e (e∉H_e),
   so by Kostochka–Yancey on H_e (legitimate: H_e IS edge-critical):
   m ≥ |E(H_e)| + 1 ≥ (5n−2)/3 + 1 = **(5n+1)/3 ≈ 1.667n + 0.33**. [wall §2.1]
   This is DOMINATED by constraint 2 (3n > 1.667n for all n>0), so Prop 5.1's
   min-degree-6 is the binding lower bound. The K-Y floor is slack.

## The binding window

   **3n ≤ m ≤ n(n−5)/2,    n ≥ 11.**

The lower edge is the live constraint. At the **sparsest extreme (Steiner's
Problem 5.2 target): m = 3n exactly, i.e. G is 6-REGULAR.** This is why the
6-regular search is the canonical first target.

### Worked smallest cases (the search frontier)
| n | min m (=3n, 6-regular) | K-Y floor (5n+1)/3 | is K-Y binding? |
|---|---|---|---|
| 11 | 33 | 18.67 | no (3n wins) |
| 12 | 36 | 20.33 | no |
| 13 | 39 | 22.00 | no |
| 14 | 42 | 23.67 | no |

So the witness, if 6-regular, has m=3n and lives at n≥11. My exhaustive **6-regular
circulant** search covered exactly this sparsest case for n=11..40 and found none —
i.e. the entire circulant slice of Steiner's Problem 5.2 is empirically empty up to
n=40.

## Why the squeeze does NOT close (negative, but clean)
There is **no rigorous UPPER bound on m better than the trivial n(n−5)/2**, because
vertex-critical 4-chromatic graphs densify freely (add edges, χ stays 4, vertex-
criticality can be preserved). So:
- The lower bound (3n) and the absence of a real upper bound mean the window is WIDE.
- Both cardinality-based impossibility routes — global K-Y (wall §2.1) and overlap
  double-counting (count L3, count_overlap_L3.md) — fail because the window has room.
- **An impossibility proof cannot come from the density ledger.** It must come from
  fine 3-coloring structure (potential method / Gallai-tree local analysis).

## Cross-confirmation with the squad (2026-06-10)
- **gallai** independently re-proved δ(G) ≥ 6 elementarily (gallai_local_structure.md
  Thm 3, = Prop 5.1) and verified the KY-density bridge e(G) ≥ (5n−2)/3 on n≤7 with
  0 violations — matches constraint 4 here exactly. gallai's correction is precise:
  the DENSITY half of KY transfers (via a minimal spanning edge-critical H⊆G), the
  Gallai-tree STRUCTURAL half does not. My ledger uses only the density half. ✓
- **skeptic** + **hunter** census: n=4..9 = {1,0,1,7,8,124} 4-vtx-critical graphs,
  ALL with a critical edge, 0 witnesses — my atlas census (n≤7) is the third
  independent enumeration agreeing. Confirms the n≥11 lower bound is not vacuous:
  witnesses are genuinely absent through n=9 (now n≤10 by skeptic), and Prop 5.1
  independently forbids them through n=10.
- **proximity**: the Martinsson–Steiner hypergraph route is EMPTY at k=4 (its densest
  reachable graph has min-deg ≤ 4 < 6), independently re-deriving the min-deg-6 floor
  from the hypergraph side. So the density floor is now triply confirmed (Prop 5.1,
  gallai elementary proof, M-S hypergraph degree obstruction).

## Net for the squad
- The density ledger PRECISELY locates the witness search: **6-regular, n≥11**, and
  the sparsest target m=3n is Steiner's Problem 5.2.
- It does NOT, by itself, decide TRUE vs FALSE.
- Combined with my relaxation probe (no fractional gap) and overlap probe (no
  counting surplus), the total counting/extremal evidence is: **no obstruction
  visible at the cardinality/density level** ⟹ mild lean TRUE, but the object (if it
  exists) is provably dense (≥ 6-regular) and at least 11 vertices, consistent with
  why 30+ years of search missed it.
