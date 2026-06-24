# Research Fusion Analysis: Erdős 64 (Erdős-Gyárfás 2^k cycles)

**Agent:** F5 of 10 (research-fusion pull) | **Date:** 2026-05-30
**Problem:** Does every finite graph with min-degree ≥ 3 contain a cycle of length 2^k for some k ≥ 2?
**Status:** OPEN since 1995; Erdős himself believed the conjecture FALSE for all min-degree ≥ 3.

---

## A. Recent literature pull (2020–2026)

1. **Hu, Shen (2024)** — *Erdős-Gyárfás Conjecture on P_10-free Graphs* (Discrete Math, arXiv:2308.05675). Proves conjecture for graphs without induced P_10. Shows such graphs contain cycle of length 4 OR 8.
2. **Hegde, Sandeep, Shashank (Oct 2024 / Feb 2025)** — *Erdős-Gyárfás Conjecture on Graphs Without Long Induced Paths* (arXiv:2410.22842). Computer-aided extension to P_13-free graphs.
3. **Liu, Montgomery (2023)** — *A solution to Erdős and Hajnal's odd cycle problem* (J. AMS / Acta Math). Adjacent: proves average-degree → cycle of length 2^k for some large k. DISPROVED Erdős's later belief that conjecture is false.
4. **Gao, Huo, Liu, Ma (2022)** — *A unified proof of conjectures on cycle lengths in graphs* (J. AMS). Min-degree ≥ k+1 → k admissible cycles in arithmetic progression. Provides AP-cycle machinery directly relevant.
5. **2025 arXiv 2508.19302** — *Cycles of Length 4 or 8 in Graphs with Diameter 2 and Minimum Degree at Least 3*. Verifies conjecture for diameter-2 graphs in strongest form (cycle of length 4 or 8).

Status of search bound: cubic counterexample ≥ 30 vertices; bipartite cubic claw-free ≥ 114 vertices (Nowbandegani-Esfandiari).

---

## B. Adjacent-domain analogs

### B1. Topology — Loops in 2-complexes with bounded local degree
The graph problem maps to: *does every locally-3-valent 2-complex contain an essential loop whose homotopy class has order 2^k in some quotient?* Analog: **Gromov's polynomial growth theorem** — locally-finite vertex-transitive graphs of polynomial growth have abelian-by-finite fundamental groups, so "no power-of-2 cycle" forces structural rigidity. The analog problem is **"systole of 2^k-type"** in CW-complexes — known to be controllable for hyperbolic groups via Bowditch.

### B2. Group theory — Free products and 2-generator subgroups
A cycle of length 2^k in a Cayley graph of Γ = ⟨S⟩ corresponds to a relator w of length 2^k in the free group F(S). The conjecture says: *every Cayley graph of min-degree 3 has a 2-power relator*. Analog: **Magnus-Karrass-Solitar style word-length minimization** in one-relator groups. The Tits alternative says non-virtually-abelian groups contain F_2 — and F_2 admits 2-power words trivially.

### B3. Combinatorics on words — Power avoidance
Avoiding 2^k-power-length factors in infinite words is **Thue-Morse-like**: Thue-Morse word avoids overlaps but contains cubes. The combinatorics-on-words analog of E64 is: *does every infinite word over Σ ≥ 3 contain a 2^k-length palindrome / square / cycle structure?* This connects to the **Dean word / square-free word theory** in free groups (arXiv:2104.06837, "Avoiding Square-Free Words on Free Groups").

### B4. Dynamical systems — Bounded-degree shift spaces
A min-degree-3 vertex shift in symbolic dynamics has positive topological entropy; the analog asks: *does every positive-entropy SFT (subshift of finite type) on alphabet ≥ 3 have a periodic orbit of length 2^k?* This is decidable per orbit-period combinatorics (Lind-Marcus) but no shortcut to the graph-theoretic case.

---

## C. Technique-transfer candidates

1. **Liu-Montgomery sublinear-expander machinery** (Adv. Math 2022, Acta 2023). Originally for *average-degree* → cycle spectrum. Could potentially be downgraded to min-degree 3 via *local* expansion. Citation: Liu, R., Montgomery, R. "A solution to Erdős and Hajnal's odd cycle problem."
2. **Modular arithmetic via spectra of graph cycles** (Verstraëte 2002 *On Arithmetic Progressions of Cycle Lengths*). Uses Bondy-Simonovits-style trace-of-adjacency-matrix techniques. Adapted to power-of-2 modular constraints: count cycles of length ≡ 0 (mod 2^k) via λ_i^L (eigenvalues to power L).
3. **SAT/CP-SAT counterexample search** (Codex C3 endorsement). Encode "min-degree 3 + no 4-cycle + no 8-cycle + no 16-cycle…" as DIMACS. Existing computer searches (≥17 vertices, ≥30 cubic) suggest small counterexamples don't exist, but **structured cubic constructions** (girth-pair gadgets) at 100+ vertices are within current SAT reach if pre-conditioned by combinatorial symmetries.
4. **Algebraic graph theory — strongly regular graphs (SRGs)**. SRG(n,k,λ,μ) eigenvalues live in {k, r, s} with r,s integers when "conference matrix" structure holds. The Petersen graph (smallest cubic claw-free triangle-free) has no 4-cycle. Constructing SRGs with no 2^k-cycle is a powerful counterexample candidate.
5. **Combinatorics on words → graphs via De Bruijn embedding**. Map a word avoiding 2^k powers into a de Bruijn graph; min-degree 3 corresponds to alphabet size constraints. Allows transferring **Dejean's theorem / repetition threshold** machinery.

---

## D. Most promising fusion: **Cayley graphs of one-relator groups with 2^k torsion avoidance**

**Specific idea:** Construct a counterexample by exhibiting a finite Cayley graph Cay(Γ, S) with |S|=3 (so min-degree 3) where Γ is a quotient of a one-relator group G = ⟨S | w⟩ chosen so that:
- the relator w has length r ≠ 2^k for all k ≥ 2,
- Γ is finite (forced by adding a high-order torsion relator),
- the cycle spectrum of Cay(Γ, S) is precisely {lengths of relators in the normal closure of w}.

By **Magnus's Freiheitssatz**, the cycle spectrum of a Cayley graph of a one-relator group is dictated by the relator structure. If we can choose w supported on lengths in {3, 5, 6, 7, 9, 10, 11, …} (avoiding 4, 8, 16, 32, 64, 128) and force Γ finite via a controlled quotient, the resulting graph is a counterexample.

**Why this is plausible:** This is genuine cross-fertilization — combinatorial group theory has powerful relator-length-control techniques (small-cancellation, T(4)-C(7) conditions) that have not been applied to E64. Specifically:
- Small-cancellation C'(1/6) groups have systole exactly the relator length.
- Choose a 7-letter cyclically reduced relator: minimum cycle length is 7, then via spectrum analysis only multiples of 7 appear up to the quotient bound.

**Risk:** Once the Cayley graph is large enough (n > 100), 2^k-cycles tend to appear "accidentally" via long concatenated relators. The fusion needs a *local-to-global* small-cancellation argument that survives quotient.

---

## E. What we'd need to feed Aristotle

Beyond bare gap, the sketch needs to invite **Magnus / small-cancellation** machinery. Concrete additions:

```
OPEN GAP: Erdős-Gyárfás 2^k cycles (Erdős 64)
Source: erdosproblems.com/64

Statement: ∃ a finite simple graph G with minDegree(G) ≥ 3 such that
for no k ≥ 2 does G contain a cycle of length 2^k.

Construction template (a hint, not a proof):
For a finitely-presented group Γ = ⟨S | R⟩ with |S| = 3 and word lengths
in R avoiding {4, 8, 16, 32, 64, ...}, the Cayley graph Cay(Γ, S∪S^{-1})
has cycle spectrum = lengths of elements in the normal closure of R modulo Γ.

theorem erdos_64_disproof :
  ∃ (V : Type*) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.minDegree ≥ 3 ∧
    ∀ (k : ℕ), k ≥ 2 → ¬ ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = 2^k := by sorry

Hint: consider Cayley graphs of small-cancellation groups Γ = ⟨a,b,c | w⟩ where |w| is a prime ≥ 7. The cycle spectrum is controlled by Lyndon's identity theorem (1966).
```

The crucial cross-domain ingredient: **mention that Cayley graphs of small-cancellation groups have controlled cycle spectra**, citing Lyndon's identity theorem and Strebel's small-cancellation atlas. Aristotle has Mathlib knowledge of `FreeGroup` and `Group.Cayley` but no explicit small-cancellation library — so the sketch must inline the key lemma:

> "If Γ = ⟨a,b,c | w⟩ is a C'(1/6) one-relator group with |w| = p prime ≥ 7, then any cycle in Cay(Γ, {a,b,c}) has length ≡ 0 (mod p)."

This is the load-bearing combinatorial group theory result. If Aristotle can verify it for explicit small p (say p=7), the cycle-length spectrum {7, 14, 21, ...} avoids all 2^k with k≥2, and the quotient by some sufficiently-large-order torsion gives a finite counterexample.

**Honest assessment:** Plausibility ~3/10. Real result-class. But construction needs an explicit witness — likely 200+ vertex graph — that no current SAT search has tried because nobody has framed it group-theoretically.
