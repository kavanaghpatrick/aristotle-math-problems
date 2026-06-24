# Top-30 Snipe List — June 1-28, 2026

**Author:** Agent #10 of 10 (synthesis)
**Date:** 2026-05-30
**Inputs:** Inventory A1 (3207 problems), Advance DNA A2 (17 successes, 8 signatures S1-S8), Failure DNA A3 (10 traps F1-F10), Capability Profile A4, Taxonomies A5/A7 (Gemini A6 rate-limited), Merged Taxonomy A8, Labeled CSVs A8/A9, Feasibility Filter Rubric.

**Re-scoring method:** A8's snipe_score column is generous to "structural-open + S6-graph-cex" entries (e.g. Erdős 61 Erdős-Hajnal scored 9, but the underlying conjecture is full-structural and famous-hard). I down-weight every problem whose `feasibility=structural-open + quantifier_geom=full-structural + theorem_uses cardinals/Tendsto/ncard ≤ asymptotic`. I up-weight problems with `S1+S2+S4+S5` matches AND a citable computable subclaim (Brocard/FT/E647 lineage). The single most reliable A4 finding: *the only template with ~100% advance probability is bounded native_decide over a precomputed witness table.* I score against that.

**Probabilities below are calibrated to slot738 (Brocard [501,1000]) = 8/10, slot737 (E647 Sophie) = 6/10 ex-ante.** A 9 means "if the sketch is bare-gap with no strategy guidance and prior context is auto-attached, Aristotle has > 70% chance of producing a compiled_advance within 1-2 retries"; a 5 means "plausible but expect 1-2 cycles of refinement"; below 4 = don't waste compute.

---

## The Five Snipe Clusters

| Cluster | Pattern | Members (rank #) | Total slots |
|---|---|---|---|
| **C1 — Bounded-range bump** | S1+S2 on Brocard-style native_decide | 1, 4, 11, 18 | 4 |
| **C2 — E647/E137/E647 residue narrowing** | S5 case-split + σ₀ multiplicativity | 2, 5, 22, 26 | 4 |
| **C3 — E203 / Sierpiński covering family** | S4 greedy-CRT covering witness | 3, 9, 12, 17 | 4 |
| **C4 — Greedy-CRT existence (Erdős's covering / Egyptian / fractal cover)** | S4-adjacent, novel | 6, 7, 8, 14, 21, 25 | 6 |
| **C5 — FT diagnostic / barrier analysis** | S3 + new modular obstruction | 10, 16, 20 | 3 |

Cross-cluster solo targets (8): ranks 13, 15, 19, 23, 24, 27, 28, 29, 30.

---

## Top 30 Ranked Snipes

### Rank 1 — Brocard `[1001, 2000]` iter4 *(C1)*
**Problem ID:** `brocard / Wikipedia_brocard_conjecture`
**Source:** `formal-conjectures/FormalConjectures/Wikipedia/BrocardConjecture.lean` (already inflight as slot745)
**Statement:** ≥ 4 primes in (pₙ², pₙ₊₁²) for n ∈ [1001, 2000].
**Taxonomy:** `mechanical-extension / finite-reducible-infinite / small-table / S2-table-bridge / low / attempted-medium`
**Advance match:** S2 (witness table + Nat.nth_count bridge) — directly inherits slot738's 10×50 encoding. Confirmed reusable.
**Risk:** F9 compute-explosion if the table fan-out exceeds slot738's per-chunk budget; pre-scan budget before draft.
**Sketch outline:** `theorem brocard_extended : ∀ n ∈ Finset.Icc 1001 2000, 4 ≤ ((Finset.Ioo (Nat.nth Prime n)² ...).filter Prime).card`. Attach slot722, slot738 as context. Tell Aristotle to chunk 20 × 50 and reuse `checkEntryB`.
**Snipe probability:** **9/10** — slot738 already validates the encoding; 1001-2000 is the natural next bump.
**Cost:** low (≈ slot738 baseline).

### Rank 2 — Erdős 647 Cunningham residual 35-case closure *(C2)*
**Problem ID:** `erdos_647`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/647.lean` (inflight as slot741)
**Statement:** Close the 35 Cunningham-chain residue cases in [3000, 10⁶] left open by slot737.
**Taxonomy:** `constructive-search / bounded-finite / small-table / S5-case-split + S1-decide / low / attempted-low`
**Advance match:** Direct sequel to slot737. Witness data (`erdos647_cunningham_extended_table.json`, 47KB; `erdos647_cunningham_witnesses.json`, 6KB) already precomputed.
**Risk:** F4 axiomatize-the-hard if Aristotle invents a σ₀-multiplicativity sub-lemma it cannot prove. Mitigation: pre-list the σ₀ ≥ 6/7 inequalities from slot737.
**Sketch outline:** Bare existence: for each of the 35 listed (q, n=q+1) pairs, exhibit divisor witness m < n with σ₀(m) + m ≤ n + 2. Attach slot737 + `erdos647_cunningham_witnesses.json` as context.
**Snipe probability:** **9/10** — bounded, decidable, witness table ready.
**Cost:** low (witness table fits in one native_decide cascade).

### Rank 3 — Erdős 203 periodic-quotient lift *(C3)*
**Problem ID:** `erdos_203`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/203.lean`
**Statement:** ∃ m coprime to 6 such that for ALL k, l ≥ 0, 2^k · 3^l · m + 1 composite (infinite covering, NOT the 8×8 finite grid).
**Taxonomy:** `constructive-search / infinite-parametric / greedy-CRT / S4-greedy-CRT / low / attempted-medium`
**Advance match:** Sequel to slot740 disproof. The `erdos203_quotient_lift_may30` analysis (158KB JSON, 4KB summary) shows slot740's 22 primes cover ~70% of the full Z² quotient lattice — STILL needs structural lift but is far past 0% baseline.
**Risk:** F1 iff-rfl if Aristotle restates and waves at infinity. F3 side-lemma bloat if it tries to extend the 8×8 to 12×12 instead of going periodic.
**Sketch outline:** State as bare existence `∃ m, ∀ k l, ¬ (2^k · 3^l · m + 1).Prime`. Attach slot740 m=1.58e42, the 22-prime cover, and the `erdos203_quotient_lift_may30.json` showing 70% partial cover. Let Aristotle find primes to fill the missing 30%.
**Snipe probability:** **6/10** — high upside (genuine novel math), real risk of partial result. If it works, this is publishable.
**Cost:** medium.

### Rank 4 — Pollock tetrahedral conjecture finite verification *(C1)*
**Problem ID:** `Wikipedia_pollock_tetrahedral`
**Source:** `formal-conjectures/FormalConjectures/Wikipedia/PollocksConjecture.lean`
**Statement:** Every integer ≥ 343,867 is the sum of ≤ 5 tetrahedral numbers (Pollock 1850).
**Taxonomy:** `finite-verification / fixed-finite-object / explicit-witness / S1-decide / low / untouched`
**Advance match:** Pure S1 — bounded native_decide on a table of representations.
**Risk:** F9 compute-explosion. Pre-scan: 343,867 entries × 5 nested choose-tetrahedral search ≈ 10⁸ cells per chunk. Chunk into 50 × 6877.
**Sketch outline:** Bare existence: for each n ≤ 343,867, exhibit a representation as ≤ 5 tetrahedral numbers. Attach OEIS A104246 if helpful; embed witness table as `def`.
**Snipe probability:** **8/10** — A7's labeling rated 4/10 because of fan-out, but if chunked correctly per slot738's pattern, it works.
**Cost:** high (table is 343k entries; need external precompute).

### Rank 5 — Erdős 647 sequel: σ₀ ≥ 8 lower-bound generalization *(C2)*
**Problem ID:** `erdos_647` (variant beyond slot741)
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/647.lean`
**Statement:** Extend slot737's σ₀(3c) ≥ 6 lower bound to σ₀(5c) ≥ 8 for composite c ≥ N₀.
**Taxonomy:** `constructive-search / infinite-parametric / explicit-witness / S5-case-split / low / attempted-low`
**Advance match:** Pure S5 reuse — Aristotle synthesized the σ₀ multiplicativity machinery in slot737 and can reapply.
**Risk:** F8 vacuous-iff if Aristotle states the strengthened bound and proves it with the same case structure (no real progress).
**Sketch outline:** `theorem σ₀_5c_ge_8 : ∀ c, Composite c → c ≥ N₀ → 8 ≤ σ₀(5 * c) ∨ Prime c`. State the σ₀-multiplicativity claim bare. Attach slot737 directly.
**Snipe probability:** **7/10** — strong reuse of proven advance signature.
**Cost:** low.

### Rank 6 — Erdős 10 (Granville-Soundararajan odd variant) *(C4)*
**Problem ID:** `erdos_10.variants.granville_soundararajan_odd`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/10.lean`
**Statement:** Every odd integer > 1 is a prime + ≤ 3 powers of 2 (Granville-Soundararajan conjecture).
**Taxonomy:** `constructive-search / infinite-parametric / explicit-witness / S7-algebraic-witness / low / untouched`
**Advance match:** A8 SUBMIT_NOW with 7/10. Bounded-N variant exists: for n ≤ 10⁸, exhibit the (prime, 2^k₁ + … + 2^k₃) decomposition. The Grechuk counterexample at n=1117175146 is a known witness for *failure of k=3*.
**Risk:** F7 bounded-leak. Bound below the 10⁹ range or Aristotle will answer with a partial range.
**Sketch outline:** Bounded version: ∀ n odd, n ≤ 10⁷, ∃ p prime, k₁ k₂ k₃, n = p + 2^k₁ + 2^k₂ + 2^k₃. State as a Finset.range claim, embed witness table externally.
**Snipe probability:** **7/10** — strong S1 candidate if bound is right.
**Cost:** medium.

### Rank 7 — Erdős 44 Sidon bounded-N existence *(C4)*
**Problem ID:** `erdos_44.empty_start`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/44.lean`
**Statement:** For large M, ∃ Sidon set A ⊆ [1, M] with |A| ≥ (1 − ε)√M.
**Taxonomy:** `constructive-search / finite-reducible-infinite / explicit-witness / S1-decide / low / untouched`
**Advance match:** Singer difference set construction is well known and gives √p Sidon sets for prime p — Aristotle can verify the explicit construction.
**Risk:** F1 iff-rfl if Aristotle defines a structure rather than constructing the set.
**Sketch outline:** Bare existence: ∃ A ⊆ Finset.Icc 1 1009, IsSidon A ∧ A.card ≥ 32. Use Singer set for p=31. Attach the explicit set as data.
**Snipe probability:** **7/10** — explicit Singer construction is Mathlib-native (`Sidon`, `Finset.Icc`).
**Cost:** low.

### Rank 8 — Erdős 686 Egyptian-fraction representation *(C4)*
**Problem ID:** `erdos_686`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/686.lean`
**Statement:** Every N ≥ 2 is ∏(m+i) / ∏(n+i) for some k ≥ 2, n, m ≥ n+k.
**Taxonomy:** `constructive-search / infinite-parametric / explicit-witness / S7-algebraic-witness / low / untouched`
**Advance match:** Bounded N version — for N ≤ 10⁴, exhibit explicit (k, n, m) triples. Mathlib has `Finset.Icc` product API.
**Risk:** F7 bounded-leak.
**Sketch outline:** Bounded: ∀ N ∈ Finset.Icc 2 100, ∃ k ≥ 2, n, m ≥ n+k, (N:ℚ) = ∏(m+i)/∏(n+i). Embed witness table.
**Snipe probability:** **7/10**.
**Cost:** low.

### Rank 9 — Erdős 938 powerful 3-term AP finite *(C3)*
**Problem ID:** `erdos_938`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/938.lean`
**Statement:** Only finitely many 3-term APs of consecutive powerful numbers.
**Taxonomy:** `constructive-search / fixed-finite-object / explicit-witness / S4-greedy-CRT / low / untouched`
**Advance match:** S4 covering / S1 native_decide on Mathlib's `Powerful` predicate. Disproof shape: exhibit a 3-term AP {(2·3·5·…)²} bag.
**Risk:** F1 iff-rfl. The conjecture asks "finite" which is hard to bound; restate as "no AP exists with first term ≤ N" for explicit N.
**Sketch outline:** Bounded: ∀ APs in Powerful ∩ [1, 10⁸], at most one is a consecutive-triple. Attach Powerful predicate definition.
**Snipe probability:** **6/10** — risk of partial range answer.
**Cost:** medium.

### Rank 10 — FT q=1583 alternate-witness diagnostic *(C5)*
**Problem ID:** `feit_thompson`
**Source:** `formal-conjectures/FormalConjectures/...` (inflight as slot744)
**Statement:** Prove ¬ A(1583) ∣ (3^1583 − 1)/2 where A(1583)=2,507,473 is prime — requires direct modular exponentiation, NOT the slot720 small-prime Fermat reduction (no r < 200 divides A(1583); see `ft_q1583_diagnostic.md`).
**Taxonomy:** `finite-verification / fixed-finite-object / explicit-witness / S1-decide / medium / attempted-low`
**Advance match:** S1 direct native_decide on a single modular exponentiation. The diagnostic confirms 3^1583 ≡ 1702700 ≠ 1 (mod 2507473). Aristotle just needs to verify the one number.
**Risk:** F9 if the kernel can't handle `3^1583 % 2507473`. Fast modpow via interval_cases may be needed.
**Sketch outline:** `theorem ft_q1583 : ¬ 2507473 ∣ (3^1583 - 1) / 2 := by native_decide`. One line. Attach `ft_q1583_diagnostic.md`.
**Snipe probability:** **8/10** — single point check; should compile.
**Cost:** low.

### Rank 11 — Brocard `[1, 1000000]` mega-chunk *(C1)*
**Problem ID:** `brocard`
**Source:** `formal-conjectures/FormalConjectures/Wikipedia/BrocardConjecture.lean`
**Statement:** ≥ 4 primes in (pₙ², pₙ₊₁²) for n ∈ [2, 10⁶], the asymptotic threshold by Ferreira 2023.
**Taxonomy:** `mechanical-extension / bounded-finite / large-table / S2-table-bridge / medium / attempted-medium`
**Advance match:** S2 at scale. 1000-chunk × 1000-entry table.
**Risk:** F9 kernel timeout on 10⁶ scale. Must be split across multiple submissions.
**Sketch outline:** Stage as [2001, 5000] first (one slot); if that compiles, [5001, 10⁴]; eventually saturate.
**Snipe probability:** **6/10** (per chunk; 1/2 for the full range).
**Cost:** high (cumulative).

### Rank 12 — Erdős 203 12×12 grid disproof scale-up *(C3)*
**Problem ID:** `erdos_203` (extension)
**Source:** Already inflight as slot743.
**Statement:** ∃ m, ∀ k,l ∈ Fin 12, ∃ index-1 prime p ≤ 1000 dividing 2^k · 3^l · m + 1.
**Taxonomy:** `constructive-search / fixed-finite-object / greedy-CRT / S4-greedy-CRT / low / attempted-medium`
**Advance match:** Pure S4 extension of slot740.
**Risk:** F7 bounded-leak (Aristotle settling at 10×10 instead of 12×12).
**Sketch outline:** Already submitted (slot743); evaluate after fetch.
**Snipe probability:** **7/10**.
**Cost:** medium.

### Rank 13 — Erdős 137 k=4,5,6 powerful product bounds *(solo)*
**Problem ID:** `erdos_137`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/137.lean`
**Statement:** Product of k consecutive integers is never powerful (for fixed k ∈ {4,5,6}, bounded n).
**Taxonomy:** `finite-verification / bounded-finite / small-table / S1-decide + S8-structural / low / attempted-low (1 disproof @ k=3)`
**Advance match:** slot615 already disproved-style succeeded for k=3 with structural lemmas. Same template for k=4, 5, 6.
**Risk:** F7 bounded-leak.
**Sketch outline:** `theorem erdos137_k4 : ∀ k = 4, ∀ n ≤ 10⁵, ¬ (∏ i ∈ Finset.range k, (n+i)).Powerful`. Attach slot615.
**Snipe probability:** **7/10**.
**Cost:** low.

### Rank 14 — Erdős 488 multiplicative density bound *(C4)*
**Problem ID:** `erdos_488`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/488.lean`
**Statement:** For finite A ⊆ ℕ, B = {n : ∃ a ∈ A, a∣n}; for all m > n ≥ max(A), |B ∩ [1,m]|/m < 2·|B ∩ [1,n]|/n.
**Taxonomy:** `constructive-search / infinite-parametric / explicit-witness / S1-decide / low / untouched`
**Advance match:** Bounded version: |A| ≤ 4, max(A) ≤ 50, m ≤ 1000, n ≤ 1000. S1 over a 4D Finset.
**Risk:** F9 compute-explosion.
**Sketch outline:** `theorem erdos488_bounded : ∀ A ⊆ Finset.Icc 1 50, A.card ≤ 4 → ∀ n m ∈ Finset.Icc 50 1000, n < m → ...`. Use native_decide.
**Snipe probability:** **6/10**.
**Cost:** medium.

### Rank 15 — Erdős 389 consecutive divisibility bounded *(solo)*
**Problem ID:** `erdos_389`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/389.lean`
**Statement:** ∀ n ≥ 1, ∃ k ≥ 1, ∏(n+i) ∣ ∏(n+k+i) (Mehta verified up to n=18, min k=207 for n=4).
**Taxonomy:** `constructive-search / finite-reducible-infinite / explicit-witness / S7-algebraic-witness / low / attempted-low`
**Advance match:** A8 SUBMIT_NOW score 8 (one of the highest legit signals).
**Risk:** F7 bounded-leak; F4 axiomatize.
**Sketch outline:** `theorem erdos389_to_50 : ∀ n ∈ Finset.Icc 1 50, ∃ k ∈ Finset.range 500, ∏(n+i) ∣ ∏(n+k+i)`. Embed the Mehta table {k(1)=1, k(2)=2, k(3)=8, k(4)=207, …}.
**Snipe probability:** **8/10** — Mehta data is precomputed and bounded.
**Cost:** low.

### Rank 16 — FT q=2999 / q=3023 break-point map *(C5)*
**Problem ID:** `feit_thompson`
**Source:** `analysis/ft_family_break_scan.json` (≈ 3.5KB)
**Statement:** For each q ∈ family ≡ 71 mod 72 with q ≤ 3000 where A(q) is composite, prove FT_p3_q via direct A(q)-mod-3 computation (extends slot720 past the q=1583 barrier).
**Taxonomy:** `mechanical-extension / bounded-finite / small-table / S3-residue-fermat + S1-decide / medium / attempted-medium`
**Advance match:** S3 generalization; bypasses the small-prime witness gap by using full A(q) modular exponentiation.
**Risk:** F9 compute (3^q mod A(q) for q ~ 2000+ is expensive).
**Sketch outline:** `theorem ft_q_le_3000_ex_1583_and_2861 : ∀ q ≡ 71 mod 72, q ≤ 3000 → q ≠ 1583 → q ≠ 2861 (or whatever) → ¬ A(q) ∣ (3^q − 1)/2`. Use the break-scan json to enumerate exceptions.
**Snipe probability:** **6/10**.
**Cost:** medium.

### Rank 17 — Erdős 203 odd-only m variant *(C3)*
**Problem ID:** `erdos_203` (variant: Sierpiński)
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/203.lean`
**Statement:** ∃ odd m such that ∀ k, 2^k · m + 1 composite (the classical 1D Sierpiński problem, slot742 is the 1D benchmark).
**Taxonomy:** `constructive-search / infinite-parametric / explicit-witness / S4-greedy-CRT / low / attempted-low`
**Advance match:** S4. The smallest known Sierpiński number is 78557 (conjectured); 5 candidates < 78557 remain unsolved.
**Risk:** F7. Bound below 78557 by submitting "for m = 78557, the 8-prime cover from {3, 5, 7, 13, 17, 241} gives composite always" — this is the classical Sierpiński witness.
**Sketch outline:** `theorem sierpinski_78557 : ∀ k ≥ 1, ¬ (2^k · 78557 + 1).Prime := by ...`. Attach the 8-prime covering set.
**Snipe probability:** **8/10** — classical witness, just needs Lean encoding.
**Cost:** low.

### Rank 18 — Brocard variant: ≥ 6 primes for n ∈ [2, 200] *(C1)*
**Problem ID:** `brocard.strengthening`
**Source:** Project-derived from slot722/738; Wikipedia BrocardConjecture.
**Statement:** Strengthen Brocard: ≥ 6 primes in (pₙ², pₙ₊₁²) for n ∈ [2, 200].
**Taxonomy:** `constructive-search / bounded-finite / small-table / S2-table-bridge / low / untouched`
**Advance match:** S2. Verify a stronger numeric inequality on the existing table.
**Risk:** Low. May fail for small n (n=2: gap (4,9) has primes {5,7} — only 2). Pre-scan needed.
**Sketch outline:** First identify n₀ where ≥ 6 primes holds. Then submit `theorem brocard_strong : ∀ n ∈ [n₀, 200], 6 ≤ ((Finset.Ioo (Nat.nth Prime n)² ...).filter Prime).card`. Attach slot722.
**Snipe probability:** **6/10** — depends on what the actual data says.
**Cost:** low.

### Rank 19 — Erdős 612/613 Wieferich extended *(solo)*
**Problem ID:** `erdos_612` (or sibling)
**Source:** project-internal slot 612/613.
**Statement:** For larger range of p ≤ N (N > 10⁹), every Wieferich-prime case is decidable.
**Taxonomy:** `mechanical-extension / bounded-finite / large-table / S1-decide / medium / attempted-medium`
**Advance match:** Mechanical S1 extension of slot612/613.
**Risk:** F9 compute.
**Sketch outline:** Chunked native_decide over the next prime range. Attach slot613.
**Snipe probability:** **6/10** — known to scale only if chunks stay small.
**Cost:** medium.

### Rank 20 — FT residue class q ≡ 23 mod 72 *(C5)*
**Problem ID:** `feit_thompson` (new residue)
**Source:** Project-derived from slot720.
**Statement:** Test slot720's mechanism on a different residue class mod 72 (one where A(q) factorization is empirically composite for the first 10 primes in the class).
**Taxonomy:** `mechanical-extension / bounded-finite / small-table / S3-residue-fermat / medium / untouched`
**Advance match:** S3. Direct re-application of slot720's interval_cases + Fermat reduction.
**Risk:** F5 if the residue class has its own break point at a small q.
**Sketch outline:** Pre-scan: find a residue class r mod 72 where A(q) is composite for q ∈ {r, r+72, ..., r+72·10}; submit the family theorem.
**Snipe probability:** **5/10** — needs pre-scan to be fair; only includes if pre-scan succeeds.
**Cost:** medium.

### Rank 21 — Erdős 312 inverse-sum density bound *(C4)*
**Problem ID:** `erdos_312`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/312.lean`
**Statement:** ∃ c > 0, ∀ K > 1, ∀ sufficiently large multisets A with Σ 1/n > K, ∃ S ⊆ A with sum in (1 − e^{−cK}, 1].
**Taxonomy:** `constructive-search / infinite-parametric / explicit-witness / S7-algebraic-witness / medium / untouched`
**Advance match:** Bounded ranges of K give partial S1 wins.
**Risk:** F1 iff-rfl, F3 side-lemma bloat.
**Sketch outline:** Bounded K=2, |A|=10, integers in {1, ..., 50}. Existence of suitable S as a Finset claim.
**Snipe probability:** **4/10** — hard quantifier nesting.
**Cost:** medium.

### Rank 22 — Erdős 647 lim variant (Erdős "doubt" direction) *(C2)*
**Problem ID:** `erdos_647.variants.lim`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/647.lean`
**Statement:** Disprove (or constrain) max_{m<n}(σ₀(m) + m − n) → ∞, the lim direction Erdős said is "extremely doubtful".
**Taxonomy:** `constructive-search / full-structural / pure-existence / S5-case-split / medium / attempted-low`
**Advance match:** Use slot737's σ₀ lower bounds to bound the lim from below.
**Risk:** F3 side-lemma bloat. F1 if Aristotle restates "lim → ∞" without a bound.
**Sketch outline:** `theorem erdos647_lim_le : ∃ c, ∀ n, max_{m<n}(σ₀(m)+m-n) ≤ c · log n`. Restrict to bounded n for native_decide.
**Snipe probability:** **5/10**.
**Cost:** medium.

### Rank 23 — Erdős 1003 totient equation bounded *(solo)*
**Problem ID:** `erdos_1003`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/1003.lean`
**Statement:** {n : φ(n) = φ(n+1)} is infinite. Bounded variant: produce witnesses up to N.
**Taxonomy:** `constructive-search / infinite-parametric / small-table / S1-decide / low / attempted-low`
**Advance match:** S1 bounded enumeration. Sage has tables of these.
**Risk:** F1 if Aristotle states `Set.Infinite` directly.
**Sketch outline:** `theorem erdos1003_bounded : ∀ N ≤ 10⁶, ∃ n ∈ Finset.Icc 1 N, φ(n) = φ(n+1)`. Attach OEIS table.
**Snipe probability:** **6/10**.
**Cost:** medium.

### Rank 24 — Erdős 11 Sárközy diff-of-squarefree bounded *(solo)*
**Problem ID:** `erdos_11`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/11.lean`
**Statement:** Differences of squarefree numbers have density 1 (Sárközy 1978). Variant: bounded density estimate.
**Taxonomy:** `constructive-search / finite-reducible-infinite / small-table / S1-decide / low / attempted-medium`
**Advance match:** S1 if reduced to bounded range.
**Risk:** F3.
**Sketch outline:** `theorem erdos11_bounded_density : ∀ N ∈ [10, 10⁵], (Finset.range N).filter is_squarefree_diff |> card ≥ ⌊0.8 · N⌋`. Pre-compute density table.
**Snipe probability:** **5/10**.
**Cost:** medium.

### Rank 25 — Erdős 172 Rado-style bounded multiplicative Schur *(C4)*
**Problem ID:** `erdos_172`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/172.lean`
**Statement:** Any finite coloring of ℕ admits monochromatic finite A with all sums and products distinct elements same color.
**Taxonomy:** `constructive-search / infinite-parametric / explicit-witness / S6-graph-cex / low / untouched`
**Advance match:** Bounded version with 2 colors, |A|=3, on [1, 20]: explicit witness. Disproof template via S6.
**Risk:** F3, F1.
**Sketch outline:** `theorem erdos172_bounded_2color_size3 : ∀ color : Fin 20 → Fin 2, ∃ A : Finset (Fin 20), A.card = 3 ∧ ∀ S nonempty subset, color (S.sum) = color (S.prod)`. Use native_decide.
**Snipe probability:** **5/10**.
**Cost:** medium.

### Rank 26 — Erdős 825 ratio σ/n bounded *(solo)*
**Problem ID:** `erdos_825`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/825.lean`
**Statement:** {n : ω(n) = ω(n+1)} infinite (related to E1003).
**Taxonomy:** `constructive-search / infinite-parametric / small-table / S1-decide / low / untouched`
**Advance match:** S1.
**Risk:** F1.
**Sketch outline:** Same template as E1003.
**Snipe probability:** **5/10**.
**Cost:** low.

### Rank 27 — Erdős 251 Pell-like bounded *(solo)*
**Problem ID:** `erdos_251`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/251.lean` (attempted-low, 2 disproofs)
**Statement:** Variant with bounded range; reuse Pell sequence structure.
**Taxonomy:** `constructive-search / bounded-finite / small-table / S1-decide / low / attempted-low (2 disp)`
**Advance match:** S1 if Pell sequence is short enough.
**Risk:** F3 — Aristotle previously produced 1148-line Pell infrastructure.
**Sketch outline:** Bound to first 50 Pell terms with `Nat.divisors`.
**Snipe probability:** **4/10** — known-failure mode.
**Cost:** medium.

### Rank 28 — Erdős 100 Reuschle / Cunningham extension *(solo)*
**Problem ID:** `erdos_100`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/100.lean`
**Statement:** Geometric variant; bounded.
**Taxonomy:** `constructive-search / finite-reducible-infinite / explicit-witness / none / low / untouched`
**Advance match:** Open shape — needs sketch attention.
**Snipe probability:** **4/10**.
**Cost:** medium.

### Rank 29 — Erdős 233 Romanoff bounded *(solo)*
**Problem ID:** `erdos_233`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/233.lean` (Math/Erdos233.lean exists)
**Statement:** Density of {n : n = p + 2^k} positive.
**Taxonomy:** `finite-verification / bounded-finite / small-table / S1-decide / low / untouched`
**Advance match:** S1. Same template as E10.
**Risk:** F7.
**Sketch outline:** Bounded enumeration on [1, 10⁵] showing density > 0.4.
**Snipe probability:** **5/10**.
**Cost:** medium.

### Rank 30 — Erdős 952 Gaussian-prime moat bounded *(solo)*
**Problem ID:** `erdos_952`
**Source:** `formal-conjectures/FormalConjectures/ErdosProblems/952.lean`
**Statement:** ∃ infinite sequence of Gaussian primes with bounded gaps.
**Taxonomy:** `constructive-search / infinite-parametric / explicit-witness / S7-algebraic-witness / low / untouched`
**Advance match:** Bounded: exhibit a chain of length 50.
**Risk:** F1, F3.
**Sketch outline:** `theorem gaussian_chain_50 : ∃ x : Fin 50 → GaussianInt, ∀ n, Prime (x n) ∧ |x(n+1)−x(n)|² ≤ C`. Use known Tsang-style data.
**Snipe probability:** **4/10**.
**Cost:** medium.

---

## Recommended June 1-30 Batch Sequence

| Week | Slots | Members | Rationale |
|---|---|---|---|
| **Week 1 (Jun 1-7)** — calibrate + exploit existing wins | slot746-750 | Ranks 1, 2, 10, 15, 17 | All S1/S2/S3 with precomputed data. Should produce 4-5/5 advances. |
| **Week 2 (Jun 8-14)** — new constructive search snipes | slot751-755 | Ranks 3, 5, 7, 8, 13 | Lift E203 + reuse σ₀ template + Sidon/E686/E137. Mixed risk. |
| **Week 3 (Jun 15-21)** — exploit cluster C4 + C5 | slot756-760 | Ranks 4, 9, 11, 12, 16 | Pollock + E203 12x12 + Brocard mega + FT residue scan. Higher compute. |
| **Week 4 (Jun 22-28)** — long-shot novelty + tier-2 cleanup | slot761-765 | Ranks 14, 18, 22, 23, 25 | Erdős 488, Brocard ≥6 strengthening, E647-lim, E1003, E172. |

Slots 766-770 (overflow): ranks 6, 19, 20 for one-off probes.

### Expected outcomes
- Week 1: 4-5 compiled_advance (replicates May 30 rate).
- Week 2: 2-3 compiled_advance + 1-2 strategically valuable disproofs.
- Week 3: 2-3 compiled_advance; some F9 timeouts likely on Pollock/Brocard mega.
- Week 4: 1-2 compiled_advance + most useful as research/HOLD signal.

**Target: 10-13 compiled_advance + 2-4 strategic disproofs across 30 slots over 4 weeks.** Status quo at 0.17% would predict ~0 advances from 30 cold submissions; rubric+depth/breadth selection plus auto-context gives a credible ~40% advance rate.

---

## Five "Surprise" Findings From This Sweep

1. **The 2 SUBMIT_NOW erdos problems (E10, E389) are far more likely snipes than the 11 "score 9" problems (E61, E64, E108, …).** The score-9 list is dominated by Erdős–Hajnal, Erdős-Hajnal-style transfinite cardinal questions, and the well-known Brown 1992-style critical-graph problems that need actual structural mathematics. The labeling rubric weights "S6-graph-cex" too generously when the underlying conjecture is full-structural.

2. **Erdős 938 (powerful 3-term APs) is a hidden S4 / S1 hybrid.** The Powerful predicate is Mathlib-native, and the conjecture asks for finiteness of an AP-set — bounded enumeration with explicit decidability. A8 scored it 5; ex-ante it deserves 7.

3. **The Sierpiński 78557 / Erdős 203 1D classical case (rank 17) is almost a benchmark.** The 8-prime covering set is on Wikipedia; Aristotle should verify it cleanly. The risk is F7 (Aristotle proves it for the 5 unsolved candidates ≤ 78557 instead of 78557 itself).

4. **Erdős 647's lim variant (rank 22) is the highest-value "next step" inside the C2 cluster.** Erdős called it "doubtful" — disproving the lim claim would be a real result, and slot737's σ₀ machinery is the natural lever.

5. **Pollock tetrahedral (rank 4) is the largest unexploited S1-decide target.** Pollock 1850 is fully solved in the literature for n ≥ 343,867; the bounded verification has never been formalized. This is a `known-formalization` per the rubric BUT the proof scale is novel for Aristotle's tooling — straddles the line between cluster C1 and the "benchmark" lane.

---

## Convergence and Divergence Across External Models

- **Codex (A5)** and **Grok (A7)** both rated Tuza ν=4 = 1/10 — strongest convergence.
- **Codex** explicitly added D8 negative-evidence, **Grok** added Breakpoint Risk — these merged in A8 as `negative_evidence` and `failure_risk` dimensions.
- **Gemini (A6)** failed (API rate limited) — A8 noted this; the merged taxonomy used Codex+Grok+rubric only.
- **Divergence**: Codex was more pessimistic on Brocard generic (2/10), Grok was more optimistic (6/10). Resolution: ex-ante Codex correct on the unbounded version; Grok correct on the bounded range bumps slot722/738/745 are doing.
- **All three (Codex/Grok/A4 capability profile)** agreed: the only ~100% advance template is `bounded native_decide over a precomputed witness table`.

---

## Ten Problems Where Labeled CSVs AND External LLMs Agreed Are Top Snipes

(Intersection of A8 SUBMIT_NOW/DRAFT_FIRST high-confidence Erdős entries with Codex/Grok top-3 from each taxonomy)

1. Erdős 389 (consecutive product divisibility) — A8 score 8, Codex finite, Grok 7/10 on Sierpiński-adjacent.
2. Erdős 203 (periodic-lift) — A8 score 8 + Grok 7/10 explicit Sierpiński-78557 covering.
3. Brocard bounded ranges — A8 score 6, Codex top-3, Grok 6/10.
4. Erdős 10 (Granville-Soundararajan odd) — A8 score 7, Codex finite-reducible, Grok 9/10 weak-Goldbach.
5. Erdős 44 (Sidon empty-start) — A8 score 6, Codex finite-reducible, Grok 8/10 "twin primes finite-N" analogue.
6. Erdős 938 (powerful 3-term AP) — A8 score 5 but matches Codex bounded-finite + Grok S1.
7. Erdős 686 (Egyptian-fraction representation) — A8 score 6, both Codex/Grok mid.
8. Erdős 647 Cunningham closure (slot741 already inflight) — A8 score 6, Codex top-3, Grok 6/10.
9. Erdős 312 (inverse-sum density) — A8 score 5, Codex constructive, Grok S1.
10. FT q=1583 diagnostic (slot744 already inflight) — A8 score 5, all three agree it's a clean S1 single-point check.

---

## The Single Most Important Pipeline Upgrade From This Sweep

**Add a `pre-submission feasibility certificate file` requirement to `safe_aristotle_submit.py`.**

Every submission MUST include a companion `<slot>_certificate.json` that:
1. Cites the **specific advance signature** (S1-S8) the sketch invites.
2. Cites the **specific failure mode** (F1-F10) the sketch dodges.
3. Cites a **parent slot or precomputed data file** (e.g., `erdos647_cunningham_witnesses.json`).
4. Names an **explicit decidability path** (e.g., "`Finset.range 10001` + `native_decide`", or "`interval_cases q` over residue class with witness table").

This adds **~5 minutes of authoring overhead per sketch** but would have caught:
- slot717-719 (E850 EM-tautology) — no S signature, no F dodge.
- slot697 (E470 iff-rfl) — no S signature, F1 risk obvious.
- slot543-style recursive falsification — no parent slot, F5 risk.

The labeled CSVs prove that 201/293 Erdős problems labeled AVOID are exactly the ones lacking a (S, F-dodge, decidability path) triple. Enforcing the certificate would automatically gate them.

**Implementation cost:** ~2 hours to add the JSON schema + a `check_feasibility_certificate()` function called before `check_gap_targeting()` in `safe_aristotle_submit.py`. The rubric's v1.1 plan (line 152 of `feasibility_filter_rubric.md`) already anticipates this — this sweep gives the certificate fields concrete content.

---

## Authority and provenance

- Rubric authority: `docs/feasibility_filter_rubric.md` v1.0.
- Sibling agent outputs: A1 (problem inventory), A2 (advance DNA), A3 (failure DNA), A4 (capability profile), A5 (Codex taxonomy), A7 (Grok taxonomy), A8 (merged taxonomy + erdos labeled CSV), A9 (non-erdos labeled CSV).
- A6 (Gemini taxonomy): API rate-limited; recorded but not used in synthesis.
- Hard rules from `CLAUDE.md` and prime directive from `MEMORY.md` remain authoritative. This list is candidate selection, NOT submission authorization. Every entry above still passes through `check_gap_targeting()` and `mk failed`/`false_lemmas` before submission.
