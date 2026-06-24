# Codex Closure Candidates (Agent C3 External Consultation, RETRY)

**Model:** gpt-5.5 (codex-cli 0.130.0, xhigh reasoning, read-only sandbox)
**Date:** 2026-05-30
**Session id:** 019e7793-c7d3-75d2-b872-4a87fffcefde
**Tokens used:** 140,514
**Approval:** never
**Prompt:** /tmp/codex_closure_prompt.txt (closure-candidates question; same context as Grok agent #5)

Codex consulted the Erdős Problems database (erdosproblems.com) via ~20 web searches before composing its list, filtering for entries flagged "VERIFIABLE Open, but could be proved with a finite example" (or finite counterexample) with formalised statements available.

This retry supersedes the previous (rate-limited) consultation. The earlier draft is preserved only in git history.

---

## Verbatim Codex response

These are **certificate targets**, not probability claims. Each would be genuine closure only if Aristotle finds the finite witness/counterexample and verifies the source statement, not just a bounded range.

### Codex's 10 Closure Candidates

#### 1. Odd Distinct Covering System
(a) [Erdős Problem #7](https://www.erdosproblems.com/7): does there exist a distinct covering system with all moduli odd?
(b) CS = `full_closure`
(c) CM = `explicit_witness`
(d) load-bearing: `native_decide`, CRT finite cover check over `ZMod L`, `omega`, `norm_num`
(e) real closure: an explicit odd distinct cover answers the open existential problem, not a bounded variant.

#### 2. Barbeau Prime Reciprocal Product
(a) [Erdős Problem #307](https://www.erdosproblems.com/307): finite prime sets `P,Q` with `(Σ 1/p)(Σ 1/q)=1`.
(b) CS = `full_closure`
(c) CM = `explicit_witness`
(d) load-bearing: `norm_num`, `native_decide`, `ring_nf`, prime-list verification
(e) real closure: no such prime sets are known; one verified pair closes the problem.

#### 3. Three Consecutive Powerful Numbers
(a) [Erdős Problem #364](https://www.erdosproblems.com/364): do three consecutive positive integers all powerful exist?
(b) CS = `full_closure`
(c) CM = `explicit_witness`
(d) load-bearing: factor tables, `native_decide`, `norm_num`, `omega`
(e) real closure: current literature has no example; one certified triple answers the existential question.

#### 4. 2-Full Followed by 3-Full
(a) [Erdős Problem #366](https://www.erdosproblems.com/366): exists `n` 2-full with `n+1` 3-full?
(b) CS = `full_closure`
(c) CM = `explicit_witness`
(d) load-bearing: factor tables, `native_decide`, `norm_num`
(e) real closure: the known pair `8,9` is reversed; a forward witness is new closure.

#### 5. AP Product Perfect Power
(a) [Erdős Problem #672](https://www.erdosproblems.com/672): can the product of a coprime AP of length `k ≥ 4` be a perfect power?
(b) CS = `full_closure`
(c) CM = `explicit_witness`
(d) load-bearing: `norm_num`, `ring_nf`, `omega`, product equality by `native_decide`
(e) real closure: one valid `(n,d,k,a,l)` witness answers "yes" to the open problem.

#### 6. Johnson Graph Coloring
(a) [Erdős Problem #835](https://www.erdosproblems.com/835): exists `k>2` with `χ(J(2k,k)) = k+1`?
(b) CS = `full_closure`
(c) CM = `witness_table_chunked`
(d) load-bearing: coloring table, subset enumeration, `native_decide`, `fin_cases`
(e) real closure: a verified coloring for an admissible open `k` closes the existential problem.

#### 7. Erdős-Gyárfás Power-of-Two Cycle Conjecture
(a) [Erdős Problem #64](https://www.erdosproblems.com/64): every finite graph of minimum degree ≥3 has a cycle of length `2^k`, `k≥2`.
(b) CS = `disproof_closure`
(c) CM = `disproof_construction`
(d) load-bearing: explicit `Fin n` graph, cycle enumerator, `native_decide`
(e) real closure: one finite graph with min degree ≥3 and no power-of-two cycle disproves the conjecture.

#### 8. Tuza's Conjecture
(a) [Erdős Problem #167](https://www.erdosproblems.com/167): if `ν_t(G) ≤ k`, can `G` be made triangle-free by deleting ≤`2k` edges?
(b) CS = `disproof_closure`
(c) CM = `disproof_construction`
(d) load-bearing: explicit `Fin n` graph, triangle packing/cover Boolean verifiers, `native_decide`
(e) real closure: one graph with triangle cover number `τ_t(G) > 2ν_t(G)` disproves Tuza.

#### 9. Erdős-Straus Counterexample
(a) [Erdős Problem #242](https://www.erdosproblems.com/242): for every `n>2`, distinct `x<y<z` solve `4/n = 1/x+1/y+1/z`.
(b) CS = `disproof_closure`
(c) CM = `structural_finite_reduction`
(d) load-bearing: denominator bounds, modular/finite certificate, `omega`, `linarith`, `native_decide`
(e) real closure: one certified `n` with no representation disproves the universal conjecture.

#### 10. Triangle-Free Graph Far From Bipartite
(a) [Erdős Problem #23](https://www.erdosproblems.com/23): every triangle-free graph on `5n` vertices can be made bipartite by deleting ≤`n²` edges.
(b) CS = `disproof_closure`
(c) CM = `disproof_construction`
(d) load-bearing: explicit graph, triangle-free check, all-bipartitions MaxCut verifier, `native_decide`
(e) real closure: one triangle-free graph requiring `> n²` deletions disproves the conjecture.

---

### Endorsement / Contest of Grok's 10

#### Grok #1 (Erdős 137 k=4): CONTEST
The cited problem asks about products of consecutive integers being powerful. "No 4 consecutive powerful" is a different and trivial statement. A `k=4` bounded theorem is not full closure unless it gives the open direction with an unbounded proof; a positive witness would be closure, but none is specified.

#### Grok #2 (Goormaghtigh (5,3)): CONTEST
At best `sub_claim_closure`. The real Goormaghtigh conjecture is not closed by one exponent pair unless the problem is explicitly re-scoped to that named subproblem.

#### Grok #3 (sqfree odd covering moduli >40): CONTEST
Squarefree odd covering systems are already ruled out in the literature; this is formalization or a bounded/variant claim, not new closure of #7.

#### Grok #4 (Casas-Alvero degree 12 over Q): CONTEST
Degree 12 over characteristic 0 was already verified in the literature. Formalizing it is not real closure; a rational counterexample would contradict the known result.

#### Grok #5 (Lehmer totient ω=7): CONTEST
Fixed-`ω` nonexistence is `sub_claim_closure`, not full Lehmer. It fails the real-closure rule.

#### Grok #6 (primitive weird ω=6): CONTEST
Also a fixed-parameter subclaim. Unless it disproves or proves the full named conjecture, it is `journal_subclaim`, not `journal_clean`.

#### Grok #7 (Tuza ν=5 Fin 13): ENDORSE, conditional
A single graph with `τ_t > 2ν_t` would genuinely disprove Tuza. This matches Aristotle's graph-witness profile. The caveat: without the actual graph certificate, CM is only a target mechanism.

#### Grok #8 (Erdős 672 k=4 l=3): CONTEST
Problem #672 is about perfect powers, and length `4` perfect-power AP products are already covered by known impossibility results. "3-powerful" is a definition mismatch.

#### Grok #9 (Pillai exponents <2000): CONTEST
Bounded ceiling = F7. It is `bounded_version_closure`, not closure of Pillai-type exponential Diophantine claims.

#### Grok #10 (odd multiperfect σ₀=11): CONTEST
Fixed divisor-count nonexistence is a subclaim. It may be publishable progress, but fails `CS ∈ {full,direction,disproof}`.

---

### EXCLUDED candidates (with KnownCliff codes)

- Brocard range bumps like `n ≤ 1000`: F7 bounded verification, not closure.
- Casas-Alvero positive-characteristic witnesses: F10 definition mismatch for characteristic-0 conjecture; often formalization only.
- Leinster `D₃ × C₅`: formalization only; also group-theory cliff.
- Erdős #5 prime-gap limit points: F1/F7, `limsup`/density behavior, not finite closure.
- Pillai or Erdős-Straus "verified up to N": F7 unless converted into a true infinite reduction or counterexample.

---

## Net signal (annotation by Agent C3)

Codex's net signal is **far stricter than Grok's**. Codex contests 9 of 10 Grok candidates (endorses only #7 Tuza ν=5 conditionally), classifying most as `sub_claim_closure`, `bounded_version_closure` (F7), or `formalization_only`. Its own 10 are dominated by **finite existential witness** problems (positive certificates for #7, #307, #364, #366, #672, #835) and **finite counterexample** problems (#23, #64, #167 Tuza, #242 Erdős-Straus).

The key methodological move: Codex used the erdosproblems.com "VERIFIABLE Open" flag as a hard filter, only proposing problems where the source explicitly states a finite witness/counterexample would resolve it. Every Codex candidate has a clean CS = `full_closure` or `disproof_closure` because the open problem is itself existential or admits a counterexample.

The cost: Codex's witness-existence claims are real long-shots. E#7 (odd distinct cover) has resisted ~75 years of search; E#23 / E#64 / E#167 disproofs may not exist. Aristotle would only verify witnesses — discovery is upstream.

**Cross-list with Grok (overlap):** Only Tuza appears in both — Codex names the full Tuza Erdős #167 (CS=disproof_closure), Grok names the specific ν=5 Fin 13 instantiation. Codex's framing is cleaner mathematically; Grok's is more tactically operational. No other overlap.
