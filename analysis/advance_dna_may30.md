# Aristotle Advance DNA — May 30 Audit

Structural fingerprint of every compiled_advance and strategically-valuable disproof Aristotle has produced. Sources: tracking.db + ARISTOTLE_SUMMARY.md + RequestProject/Main.lean inside each `submissions/nu4_final/slot<N>_extracted/.../` tarball expansion.

## Successes (chronological)

| slot | problem | DB status | proof_pattern | key_tactic | novelty |
|---|---|---|---|---|---|
| 114 | Tuza ν=4 diagonal-exclusion | disproven | 8-vertex graph G_ex + explicit triangle | decide on adjacency / membership | genuinely_novel |
| 131 | Tuza ν=4 external-triangles share apex | disproven | 10-vertex graph + explicit M_cex packing | decide; manual packing-number | genuinely_novel |
| 250/267 | Tuza middle/apex bridges | disproven | Explicit graph counterexamples + structural definitions | decide + Finset | genuinely_novel |
| 578 | OEIS A67720 (φ(k²+1)=k·φ(k+1)), k<3200 | disproven | Bounded universal → Finset.range; totient via primeFactors | native_decide after revert | mechanical_extension |
| 615 | Erdős 137 k=3 (powerful consecutive) | disproven | Bounded native_decide + parity case-split | native_decide + manual divisibility | mechanical_extension |
| 618 | Casas-Alvero in char p | disproven | Explicit polynomial X^(p+1) - X^p over ZMod p | Polynomial.hasseDeriv + Mathlib | formalization_of_solved |
| 633 | FT p=3 q=71 synthesis | disproven | Derived k mod A formula + numeric check at q=71 | poly identity + Nat.ModEq | mechanical_extension |
| 693 | Erdős 850 (same primeFactors triple) | disproven | Bounded search + structural negative bounds (rad_lcm, parity) | native_decide + manual lemmas | formalization_of_solved |
| 695 | Lehmer totient (shape of counterexample) | disproven | Manual structural: odd ∧ squarefree | Nat.totient_even + Squarefree | formalization_of_solved |
| 712 | Erdős 672 k=3 l=2 | disproven | Single AP witness (1,24): product = 1225 = 35² | use 1, 24; native_decide | genuinely_novel |
| 720 | FT p=3 q≡71 mod 72, q≤1000 (iter2) | compiled_advance | Residue-subfamily + Fermat-divisor reduction | interval_cases + per-q (q,p) Fermat lemma | mechanical_extension |
| 722 | Brocard n∈[2,500] | compiled_advance | Computable nthPrimeComp bridged via Nat.nth_count | native_decide on Finset.Icc | mechanical_extension |
| 736 | FT q≤1500 (iter3) | submitted/advance | Bound → Finset.range cast + single native_decide | native_decide | mechanical_extension |
| 737 | Erdős 647 Sophie-subclass | submitted/advance | Case-split on Cunningham disjunction + σ₀ multiplicativity lower bounds | manual σ₀ lemmas, no native_decide on main | genuinely_novel |
| 738 | Brocard n∈[501,1000] | submitted/advance | 10×50 chunked witness table + checkEntryB + nth_count bridge | native_decide per chunk | mechanical_extension |
| 739 | Nonabelian Leinster D₃×C₅ | submitted/advance | Coprime-product decomposition of normal subgroups + σ multiplicativity | structural theorems + enumeration | formalization_of_solved |
| 740 | Erdős 203 8×8 index-1 covering (the disproof that opens E203) | submitted/disproof | Greedy set cover on partition structure + CRT realization, explicit m=1.58e42 | native_decide on Fin 8 × Fin 8 | genuinely_novel |

## The 8 snipe signatures

### S1 — Bounded native_decide on a universal statement
`∀ n ≤ N, P(n)` where `P` is expressible by Mathlib-decidable predicates. Reduce `∀ ℕ` to `∀ n ∈ Finset.range (N+1)` and `native_decide`.
- Slots: 736, 578, 615, 693
- Sketch must supply: explicit numeric bound `N`; predicate must use only `Nat.Prime`, `totient`, `Nat.divisors`, modular arithmetic, etc.
- Failure mode: modular exponent / search blows the native_decide budget.

### S2 — Witness table + Nat.nth_count bridge
For universal claims over indices `0..N` involving the noncomputable `Nat.nth Nat.Prime`. Precompute the witness table externally, chunk it (10 chunks of ~50), define a `checkEntryB : Bool` checker, `native_decide` per chunk, and bridge via `Nat.nth_count`.
- Slots: 722, 738
- Sketch must supply: numeric range, target property (e.g. ≥4 primes in interval), parametrization in `Nat.nth Nat.Prime`.
- This is the **scalable** version of Brocard-style claims.

### S3 — Residue-class subfamily + small-prime Fermat reduction
For FT-style claims about `q ≡ r mod M`: enumerate the bounded family by `interval_cases`, then for each `q_i` supply a small prime `p_i | A(q_i)` and reduce `3^q mod p_i` via Fermat's little theorem.
- Slots: 720, 633
- Sketch must supply: residue class `q ≡ r mod M`, bound `q ≤ N`, prior context with candidate small primes per family member.
- Failure mode: when `A(q)` is itself prime (slot720 iter3 predicted to fail at q=1583).

### S4 — Greedy cover + CRT witness embedding
For 2D / finite-grid coverage problems: run greedy set-cover externally, realize the choices via CRT, embed the resulting (very large) integer as a `def`, then `native_decide` over the finite grid.
- Slots: 740 (also implicit in the slot724 covering analysis)
- Sketch must supply: finite grid bounds, prime set, divisibility predicate, and licence to compute the witness externally.
- Limit: produces only finite-grid coverage — the lift to infinite covering is a separate algebraic problem.

### S5 — Case-split with explicit small-offset witnesses + σ₀ multiplicativity
For `∃ m < n, f(m) > bound` style existence: split on a hypothesis (e.g. Cunningham disjunction), choose witness `m ∈ {n-1, n-2, n-3, n-4}` per case, supply manual `σ₀(k·composite) ≥ K` lower bounds via prime-power decomposition.
- Slots: 737, 723
- Sketch must supply: the existence target, the bound, the disjunctive structural hypothesis.
- This is the most "structural" pattern — Aristotle synthesized the multiplicativity proofs.

### S6 — Explicit small graph counterexample
For combinatorial conjectures: build an explicit `Fintype` graph (8–12 vertices), define adjacency by enumeration, verify all hypotheses by `decide`, and exhibit the witness triangle / packing / coloring.
- Slots: 114, 131, 250, 267 (the Tuza ν=4 arc)
- Sketch must supply: precise hypothesis, structural definitions (Cycle4, isMaxPacking, ...).
- This is the dominant pattern for falsifying combinatorial bridging lemmas.

### S7 — Explicit algebraic witness + standard verification
For algebraic existence problems: supply an explicit polynomial / group element / coprime pair, then verify standard properties using Mathlib's algebra library.
- Slots: 618 (poly X^(p+1) - X^p), 739 (D₃ × C₅), 712 ((n,d)=(1,24))
- Sketch must supply: the explicit witness (this is the novelty; Aristotle verifies, doesn't search).
- Limit: Aristotle reliably verifies a supplied witness but rarely discovers novel ones from a bare gap.

### S8 — Structural constraints on counterexample shape (negative-only)
For currently-open existence problems: produce necessary conditions on any counterexample (odd, squarefree, divisible by 6, gap ≥ 30) without resolving existence.
- Slots: 695 (Lehmer), 693 (E850), 615 (E137)
- Sketch must supply: counterexample definition; permission to bound the search.
- **The user has flagged these as not gap-resolutions** — they compile clean but don't close the gap.

## Top 3 by reproducibility evidence

1. **S1 Bounded native_decide** (4 slots: 736/578/615/693). Bound + decidable predicate = win.
2. **S6 Explicit finite graph counterexample** (4 slots: 114/131/250/267). Combinatorial falsification specialty.
3. **S5 Case-split + σ₀ multiplicativity** (2 slots same arc: 737/723) — fewer slots but a tightly-reproduced structural template within the E647 family.

## Notes for the next sweep

- **S2 (witness-table chunking) is the highest-value reusable scaffold** — slot738 explicitly reused slot722's encoding. Any problem that reduces to "verify a property at every index 0..N involving noncomputable Mathlib defs" should use this.
- **S4 (greedy + CRT)** is generalizable to all 2D covering / Sierpiński-Riesel-style problems. The slot740 disproof is the proof of concept.
- **S7 only works when the witness is supplied** (sketch or context). Bare `∃ m` gaps without a candidate witness will not be cracked by Aristotle — slot724 confirms this for the lifted E203.
- **The S1+S2 combination** explains the bulk of the 5/5 batch: the new pipeline is sniping problems that already have computable cores. Tuza / structural-open problems still lack S-class signatures.
