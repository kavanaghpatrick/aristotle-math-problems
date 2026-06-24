# Closure-First Top-20 List (Agent C10 Synthesis)

**Author:** Agent #10 of 10 (closure-focused investigation)
**Date:** 2026-05-30
**Mission:** Rank the problems where success = real math closure (not bounded extension, not formalization).
**Inputs synthesized:** C1 registry, C2 taxonomy, C3 Codex candidates, C5 Grok candidates, C8 Erdős closure labels, C9 non-Erdős closure labels. C4 (Gemini closure candidates), C6 (literature freshness), C7 (closure mechanism analysis) not yet on disk — synthesis proceeds on the 6 available inputs plus tracking DB.

**Decision rule (from C2):**
```
REAL closure ⇔ CS ∈ {full_closure, direction_closure, disproof_closure}
              ∧ CM ≠ none_known
              ∧ CR ∈ {clean_decidable, witness_search_explosion (mitigated)}
              ∧ HM = journal_clean
```

Anything weaker (bounded_version_closure, sub_claim, formalization_only) is STRATEGIC at best and must not be celebrated as closure.

---

## Top-20 closure candidates

Ranking weights:
- Closure-axis score from C8/C9 (max 10).
- Endorsement count from {Codex C3, Grok C5, Gemini taxonomy-worked C2}.
- Aristotle history: prior submissions, no-advance count, disproven count.
- Honest closure probability (1–10), conditioned on Aristotle capability profile.

| # | problem_id | statement (1-line) | CS | CM | CR | HM | load-bearing creative step | endorsers | closure prob | REAL closure? |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | **erdos_203** | `∃ m, m.Coprime 6 ∧ ∀ k l, ¬(2^k·3^l·m+1).Prime` (Erdős variant of Sierpiński) | full_closure | explicit_witness | clean_decidable | journal_clean | search for `m` then `decide` covering | Codex (E#7 sibling), Grok-implicit (covering family), C8=8 | **6/10** | YES |
| 2 | **wikipedia_lemoine_conjecture (disproof direction)** | counterexample odd `n>6` not expressible as `p+2q` | disproof_closure | disproof_construction | witness_search_explosion | journal_clean | external search → `decide` non-existence over `p,q < n/2` | C9=10, Codex Sierpiński-analogue | **3/10** | YES if cex exists |
| 3 | **wikipedia_grimm_conjecture (disproof direction)** | counterexample `n,k` with consecutive composites lacking distinct prime divisors | disproof_closure | disproof_construction | witness_search_explosion | journal_clean | external SAT/CP search → `decide` over `Fin k → primes` injection | C9=10 | **3/10** | YES if cex exists |
| 4 | **wikipedia_conway99Graph (disproof or existence)** | `∃ G : SimpleGraph (Fin 99), LocallyLinear ∧ NonEdgesAreDiagonals` | full_closure (existence) or disproof_closure (non-existence) | explicit_witness or exhaustive search | iff_rfl_trap (mitigable by reformulating) | journal_clean | construct adjacency matrix; `decide` Strongly-regular SRG(99,14,1,2) | C9=10, Codex graph-cex DNA | **2/10** but transformative if hit | YES (Conway's $1000 prize) |
| 5 | **wikipedia_exists_magic_square_squares** | `∃ 3×3` magic square of distinct squares (Sallows-Bremner) | full_closure | explicit_witness | iff_rfl_trap (mitigable) | journal_clean | small-integer search over `Fin 9` perms, `decide` magic constants | C9=10 | **3/10** | YES if exists |
| 6 | **erdos_952** | `∃` infinite sequence of distinct Gaussian primes with bounded step (Gaussian moat) | full_closure | explicit_witness | clean_decidable | journal_clean | construct injection `ℕ → GaussianInt` with `(x_{n+1}-x_n).norm < C` — known OPEN whether such exists | C8=7, Codex graph-existence DNA | **2/10** (true infinite witness is the literal open) | YES if hit (Mathematica-class result) |
| 7 | **erdos_617** | `r≥3, |V|=r²+1, r-colored K_n ⇒ ∃ r+1 vertices with missing colour` | full_closure (or disproof) | explicit_witness (disproof side) | clean_decidable | journal_clean | small `r=4` cex on `Fin 17` via SAT, verify `Sym2 V → Fin r` violates clause | C8=6, Codex Erdős-Gyárfás DNA | **3/10** for `r=4` cex | YES if hit |
| 8 | **erdos_938** | `∃` AP of length 3 of primes of form 2^k... (specific Erdős AP problem) | full_closure | explicit_witness | iff_rfl_trap | journal_clean | construct AP triple via `decide` after small search | C8=5 | **4/10** | YES |
| 9 | **wikipedia_fermat_number_are_composite (`∀ n>4`)** | "all Fermat F_n with n>4 are composite" — open | full_closure | disproof_construction (find prime F_n) | iff_rfl_trap | journal_clean | extreme long-shot, but unique `n` with `Prime F_n` ends it | C9=10, Codex implicit | **1/10** (search past PrimeGrid is beyond reach) | YES, but vanishing probability |
| 10 | **goormaghtigh (5,3) closure** | only solutions to `(x^5-1)/(x-1)=(y^3-1)/(y-1)` are the two known | direction_closure (specific exponent pair) | witness_table_chunked | clean_decidable | journal_clean | chunked `native_decide` to elementary bound ≈10^9 + modular sieve | Grok-1 endorsement, Codex Brocard-DNA | **6/10** | YES (named exponent-pair closure) |
| 11 | **erdos_137 k=4 powerful tuple disproof** | `¬∀ k ≥ 3 ...` strengthened to `∃ k=4` witness of 4 consecutive powerful integers | disproof_closure | disproof_construction | recursive_falsification (low; k=3 solved 1980s) | journal_clean | σ₀ multiplicativity case-split + `interval_cases` + `native_decide` on prime-signature families | Grok-1, C8=4 | **3/10** | YES |
| 12 | **odd multiperfect σ₀(n)=11 non-existence** | extend Cunningham-Pomerance shape constraints from σ₀≤9 to σ₀=11 | direction_closure (specific divisor count) | structural_finite_reduction (σ multiplicativity case-split) | clean_decidable | journal_clean | full case-split on `p^10`, `p^4 q^2`, `p^2 q r` factor shapes + `native_decide` per family | Grok-10, C8 implicit | **5/10** | YES |
| 13 | **primitive weird ω=6 non-existence** | extend Melfi 2015 shape constraint to 6 prime factors | direction_closure | structural_finite_reduction | clean_decidable | journal_clean | σ multiplicativity + case-split on smallest prime + `Finset` enumeration | Grok-6 | **5/10** | YES |
| 14 | **Lehmer totient ω(n)=7 odd sqfree** | extend `φ(n)∣(n−1) ⇒ n prime` from ω≤6 to ω=7 | direction_closure | structural_finite_reduction | witness_search_explosion (mitigated by chunking) | journal_clean | `interval_cases` + boolean verifier via chunked `native_decide` | Grok-5 | **4/10** | YES |
| 15 | **distinct odd covering system (E#7)** | does any covering system of ℤ exist with all-odd distinct moduli? | disproof_closure (positive existence ≡ disproof of folklore conjecture) | explicit_witness | clean_decidable | journal_clean | greedy-CRT + `decide` over `Fin lcm` residue classes — verification is easy, search is the bottleneck | Codex-2, Grok-3 (sqfree variant) | **2/10** (search is the hard part) | YES, $1000 prize |
| 16 | **erdos_64 Erdős-Gyárfás 2^k cycles disproof** | min-deg-3 graph with no cycle of any `2^k`, `k≥2` length | disproof_closure | disproof_construction | clean_decidable | journal_clean | SAT-search for finite graph (no cycle of length 4,8,16,…), `decide` adjacency + cycle absence | Codex-5 | **3/10** | YES |
| 17 | **erdos_307 finite prime sets with reciprocal-product = 1** | `∃ P,Q ⊆ primes, finite, with (Σ 1/p)·(Σ 1/q) = 1` | full_closure (existence) | explicit_witness | clean_decidable | journal_clean | small-prime exhaustive `decide` over rational arithmetic | Codex-7 | **3/10** | YES |
| 18 | **erdos_835 (k+1)-subset coloring** | `∃ k>2` with a coloring of `k`-subsets of `[2k]` by `k+1` colors such that every `(k+1)`-subset sees all colors | full_closure | explicit_witness | clean_decidable | journal_clean | enumerate colorings of `Finset.powersetCard k (Finset.range (2k))`, `decide` per `(k+1)`-subset | Codex-6 | **3/10** | YES |
| 19 | **Tuza ν=5 counterexample on Fin 13** | finite 13-vertex graph violating `τ ≤ 2ν` for triangle-packing/covering at ν=5 | disproof_closure | disproof_construction | recursive_falsification (HIGH — see MEMORY.md falsified list for Tuza apex/bridge/6-packing/LP-duality/universal-apex) | journal_clean | adjacency Fin 13 graph + brute force `native_decide` on `(ν,τ)` | Grok-7 | **2/10** (Aristotle has 200+ Tuza no-advance — repeating-same-DNA risk) | YES, but the highest "looks-like-S6 but is recursive_falsification" trap |
| 20 | **erdos_672 k=4 l=3 AP-of-powerful witness** | 4-term AP of 3-powerful integers (open at k=4 after slot712 closed k=3) | disproof_closure (counterexample to AP-free conjecture) | greedy-CRT explicit_witness | clean_decidable | journal_clean | direct extension of slot712 mechanism — single `native_decide` over the AP | Grok-8, Codex-8 (positive direction k≥35) | **5/10** | YES (named open subcase) |

---

## Cross-LLM convergence (3-5 problems all 3 / ≥2 LLMs endorse)

Strict (≥2 of {Codex, Grok, Gemini-taxonomy worked-examples}):

1. **Erdős 672 family** — Codex (positive k≥35) + Grok (k=4,l=3 disproof). Different directions, same problem. Direct DNA match to compiled slot712.
2. **Covering systems** — Codex (E#7 distinct odd) + Grok (sqfree odd >40). Same combinatorial machinery (greedy-CRT + `decide`).
3. **Erdős 647 existential** — Codex (find `n>24` for `max(m+τ) ≤ n+2`) + Gemini-worked (σ₀ Sophie sub-claim, slot737-sequel). Both flag σ₀-multiplicativity as Aristotle's strongest tool. **But:** C8 labels E#647 as `score=1 AVOID` because the lim direction is `Tendsto` (iff_rfl_trap) and the existential is empty up to 10^9. Use ONLY the explicit-witness framing.
4. **Tuza-style disproofs on small graphs** — Grok ν=5 Fin 13 + Codex Erdős-Gyárfás (E#64) graph counterexample. Same S6 explicit-finite-graph mechanism. **But:** Tuza-specific falls in `recursive_falsification` per MEMORY.md.
5. **Disproof of "smallest" conjectures** — Codex (Sierpiński, Riesel smallest claims) + C9 (Lemoine, Grimm, Fermat-composite, Wolstenholme infinite — all score=10 disproof targets). Same DNA: external search supplies a candidate, Aristotle verifies.

True triple-LLM convergence:
- **No problem has explicit endorsement from all three LLMs.** Gemini's role here is the taxonomy/mechanism analysis (C2), not a candidate list. Convergence is *between mechanisms*, not on the same exact problem-ID.
- The closest 3-way mechanism convergence is **σ multiplicativity case-splits on shape-constrained number-theoretic objects** (E#647, primitive weird ω=6, odd multiperfect σ₀=11, Lehmer ω=7) — all four problems share the same closure mechanism and all three of {Codex, Grok, Gemini-taxonomy-S5} endorse the mechanism.

---

## "Don't Confuse These With Closure" (high prior-snipe rank → bounded-only / formalization)

These appear high on `snipe_list_may30.md` but FAIL the C2 decision rule:

1. **Brocard's problem (slot 738 sequel, `[1001, 2000]` or higher)** — `bounded_version_closure` + `witness_table_chunked` + HM = `journal_partial`. CLAUDE.md rule 12 applies: compiled clean ≠ resolved the gap. Brocard infinite case remains untouched. Counts as a research note, not closure. Wikipedia_brocard_conjecture C9 score=9 is CLOSURE_PROBE, not CLOSURE_CANDIDATE.
2. **Pollock tetrahedral up to 343,867** — `formalization_only` per C2 worked-example 7. Pollock 1850 solved beyond the threshold; the Aristotle work is a Lean port of a published result. Wikipedia_pollock_tetrahedral C9 score=9 is CLOSURE_PROBE only when measured as bounded; as full Pollock closure it is formalization.
3. **Fermat-Torricelli p=3 q≡71 mod 72, q ≤ 1000 (slot 720)** — `bounded_version_closure` per C2 worked-example 4. FT closure requires `q → ∞`; q-bumps are publishable as residue-class extensions, NOT as FT closure. Sub-claim still valuable but must be labeled `journal_partial`.

Honorable mention: **slot739 Leinster D₃×C₅** (formalization_only — known math, Lean port; per C2 worked-example 5 explicitly).

---

## 4-week closure-first batch sequence

Total: 11 slots / 4 weeks (≤3 per week). Lower volume than `snipe_list_may30.md` because closure has lower base rate. Mix: high-probability strategic sub-claims (anchor) + 1 long-shot per week.

### Week 1 — Multiplicativity Sub-claim Sweep (highest closure-mechanism reliability)

Three problems sharing σ multiplicativity case-split DNA; the technique is Aristotle's most reliable per C2 (S5/S7) + Grok's repeated recommendation.

- **Slot W1-A:** Odd multiperfect σ₀(n)=11 non-existence (top-12, prob 5/10)
- **Slot W1-B:** Primitive weird ω(n)=6 non-existence (top-13, prob 5/10)
- **Slot W1-C:** Lehmer totient ω(n)=7 odd sqfree non-existence (top-14, prob 4/10)

### Week 2 — Erdős AP-of-Powerful + Goormaghtigh

Highest-probability single-direction closures.

- **Slot W2-A:** Erdős 672 k=4 l=3 (top-20, direct slot712 extension, prob 5/10)
- **Slot W2-B:** Goormaghtigh (5,3) closure (top-10, prob 6/10 — named exponent-pair closure)
- **Slot W2-C:** Erdős 137 k=4 powerful disproof (top-11, prob 3/10)

### Week 3 — Pure-existence small-witness closures (Erdős prize-class)

- **Slot W3-A:** Erdős 203 explicit witness `m` Coprime 6 (top-1, prob 6/10 — already 1 honest_partial)
- **Slot W3-B:** Erdős 307 finite prime sets reciprocal-product = 1 (top-17, prob 3/10)
- **Slot W3-C:** Erdős 835 (k+1)-subset coloring (top-18, prob 3/10)

### Week 4 — Disproof long-shots

Lower probability, higher impact. One slot only because expected closure rate is low.

- **Slot W4-A:** Erdős 64 Erdős-Gyárfás 2^k cycle disproof (top-16, prob 3/10) — best of the long-shots; SAT-search precedent in C3.
- **Slot W4-B (HOLD until search ready):** Conway 99-graph (top-4) — only submit if external search yields a candidate adjacency. Pure verification, not search.

Total: **11 slots over 4 weeks.**

### Excluded from queue

- Tuza ν=5 (top-19): MEMORY.md flags recursive_falsification — Aristotle has 200+ Tuza no-advance with all listed approaches already tried (apex, bridge, 6-packing, LP duality, universal apex).
- Gaussian moat E#952 (top-6): infinite-witness construction; closure mechanism is genuinely missing.
- Fermat-composite F_n>4 (top-9): search beyond PrimeGrid, no realistic witness search.
- Distinct odd covering E#7 (top-15): closure mechanism is verification, the open problem is search itself.
- All `bounded_version_closure` targets (Brocard bumps, FT q-bumps, Pollock formalization, slot618 Casas-Alvero already disproven): submit on the engineering lane, do not celebrate as closure.

---

## Honest expected closure rate

- **Closure-rate prior (this slate):** 1–3 of 11 submissions produce REAL closure (HM = journal_clean and contribution_statement ≠ null and target_resolved = 1).
- **Engineering-rate prior (this slate):** 5–7 of 11 compile cleanly (some as `compiled_no_advance`, some as `compiled_partial`).
- **Versus prior snipe_list_may30 rate:** snipe-list claimed 60–80% advance rate, but C2 redefines the bar — that 60–80% was mostly bounded_version_closure / formalization_only, not real closure. The closure-first slate's honest expected REAL closure rate is **~15–25%** versus snipe-list's true closure rate of **<10%** under the C2 rubric.
- **Key risk:** the multiplicativity-shape-extension closures (top 12–14) read as REAL closure to a journal *only if* the prior literature explicitly leaves the next-divisor-count case open. Need a freshness sweep (C6 — currently missing) before submitting Week 1.

---

## Single most-important closure-lane upgrade

**Stop letting `compiled_advance` from `bounded_version_closure` count as closure in the snipe_list.** The C2 `real_closure_candidate` boolean in `<slot>_certificate.json` (per C2 §"Integration with the feasibility certificate") needs to gate any "closure" claim. Specifically: integrate the closure-axis fields (CS, CM, CR, HM) into the gap-targeting gate so that submissions targeting `bounded_version_closure` or `formalization_only` get a *visible* `STRATEGIC_SUBCLAIM` or `INFRASTRUCTURE_ONLY` tag in the DB. Without this, the snipe-list rubric will continue to reward bounded extensions and the closure-lane rate will remain hidden behind a 60–80% "advance rate" that is mostly journal_partial / journal_subclaim.

Concretely: add a `closure_axis_json` column to `submissions` (CS/CM/CR/HM/real_closure_candidate) and require it before `mk submit`. This is a one-day engineering change that unlocks every downstream closure-rate calculation.
