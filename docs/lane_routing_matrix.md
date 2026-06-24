# Lane Routing Matrix

**Author:** Agent S1 of 10
**Date:** 2026-05-30
**Mission:** Given the 4 lanes (BARE, CLOSURE, FUSION, INFORMAL), assign each problem CLASS its correct lane.

**Source citations:**
- Closure list — `/Users/patrickkavanagh/math/analysis/closure_list_may30.md` (C2 decision rule, top-20 ranks, fusion-amenability table)
- F-team synthesis — `/Users/patrickkavanagh/math/analysis/math_research_audit_synthesis.md` (F1, F2, F4, F5, F6, F8, F10 findings)
- W-team synthesis — `/Users/patrickkavanagh/math/analysis/web_research_synthesis.md` (W1, W2, W3, W5, W6, W8 findings; canonical Aristotle architecture per arXiv:2510.01346)
- Failure DNA — `/Users/patrickkavanagh/math/analysis/failure_dna_may30.md` (F1–F10 failure modes)

---

## The 5-Question Flowchart: "Got a problem? Find your lane."

```
                       ┌────────────────────────────────────────┐
                       │  Q1. Is the problem famous-deep?       │
                       │  (RH, BSD, P≠NP, Twin Primes,          │
                       │  Goldbach, abc, infinite-witness)      │
                       └────────────────────────────────────────┘
                         YES → AVOID (W3/W6: hit rate 0%, see Class 7)
                         NO ↓
                       ┌────────────────────────────────────────┐
                       │  Q2. Has it been SOLVED in literature  │
                       │  since the Erdős/formal-conjectures    │
                       │  database last refreshed?              │
                       │  (Mandatory I4 freshness sweep)        │
                       └────────────────────────────────────────┘
                         YES → HARD-BLOCK (Class 5; see Leinster, Pollock)
                         NO ↓
                       ┌────────────────────────────────────────┐
                       │  Q3. Does success = an explicit finite │
                       │  witness or finite-bound verification? │
                       │  (graph, integer, modular witness,     │
                       │  σ₀ case-split, q-bump, n-bump)        │
                       └────────────────────────────────────────┘
                         YES ↓                                    NO ↓
                  ┌──────────────────┐                  ┌─────────────────────────┐
                  │ Q4a. Is the      │                  │ Q4b. Is there a cross-   │
                  │ witness already  │                  │ domain technique import  │
                  │ found (off-Lean) │                  │ that produces a bridge   │
                  │ and we just need │                  │ lemma? (Frey, Chabauty,  │
                  │ Aristotle to     │                  │ Ribet, percolation,     │
                  │ verify?          │                  │ Cayley group theory…)    │
                  └──────────────────┘                  └─────────────────────────┘
                    YES ↓        NO ↓                     YES ↓             NO ↓
                  CLOSURE      BARE                     FUSION+         BARE or
                  lane         lane                     INFORMAL        AVOID
                  (Class 1)    (Class 3)                (Class 6)       (Class 4 or 8)
                                                                          │
                                                                          ▼
                                                              ┌────────────────────────┐
                                                              │ Q5. Long-tail Erdős    │
                                                              │ that no human cared    │
                                                              │ to solve? (Tao "lowest │
                                                              │ hanging fruit" regime) │
                                                              └────────────────────────┘
                                                                YES → BARE (Class 8)
                                                                NO  → AVOID
```

**Cite for flowchart:** Q1 from W3/W6 (no public AI has ever resolved a Millennium-class problem; W8 §5 "the realistic autonomous-research ceiling is ~20%"). Q2 from W2 / closure_list "Don't confuse with closure" + F10 §6 fusion-amenability (Leinster D₃×C₅ is "formalization_only"). Q3 from closure_list C2 decision rule (CS ∈ {full_closure, direction_closure, disproof_closure} requires explicit_witness or disproof_construction). Q4a vs Q4b from F1 (CLOSURE = "structural-external + compute-internal"; FUSION = cross-domain bridge import). Q5 from W2 Tao "lowest hanging fruit" + W3 (Erdős #1026 was rectangle-packing reduction).

---

## Lane Decision Matrix — 8 Problem Classes

### Class 1 — Finite verification with computable bridge

**Examples:** Brocard `[1001, 2000]`; FT p=3 q≡71 mod 72 q-bumps; Pollock tetrahedral verification bumps; Goormaghtigh (5,3) elementary bound to 10⁹.

**Recommended lane:** `CLOSURE`
**Companion file:** `.closure.json` with `real_closure_candidate=false` (these are bounded extensions, not real closure) UNLESS the bound is the published threshold (Goormaghtigh (5,3) elementary bound IS journal-publishable as "named exponent-pair closure" — closure_list top-10, 6/10 closure prob).
**LLM pairing:** Codex (proof loop on Lean 4 chunks) + ensemble check.
**Pre-submission checks:** Literature-check REQUIRED (Y) — must confirm next-bound is genuinely the current research frontier (closure_list "Don't Confuse §1" — Brocard infinite case still open; FT q-bumps are residue-class extensions, NOT FT closure). I4 hard-block on Pollock 1850 (formalization_only per closure_list §"Don't Confuse §2").
**Expected hit rate:** Engineering rate ~60–80% compile-clean; REAL closure rate <10% (F10 §3 Upgrade #5; closure_list §"Honest expected closure rate"). Bounded extensions tagged `compiled_no_advance_mechanical`.
**Failure modes to watch:** F7 (bounded leak — Aristotle proves `for n ≤ 1000` while sketch asked unbounded; slot650 Lemoine), F9 (compute explosion; slot684 Hadamard k=2).

---

### Class 2 — Bounded narrowing of an unbounded conjecture

**Examples:** E647 Sophie sub-claims with σ₀-multiplicativity; E938 powerful 3-AP narrowing; odd multiperfect σ₀(n)=11 non-existence; primitive weird ω(n)=6; Lehmer totient ω(n)=7 odd sqfree.

**Recommended lane:** `FUSION` (closure_list Week 1 batch: multiplicativity-shape-extension family is the closest 3-way mechanism convergence per closure_list §"True triple-LLM convergence").
**Companion file:** `.fusion.json` with `informal_proof_outline` (σ-multiplicativity case-split + `interval_cases` + `native_decide` per family), 3–5 `candidate_lemmas` (per closure_list top-12, 13, 14 prob 4–5/10).
**LLM pairing:** Grok (closure_list §endorsers: Grok 5, 6, 10) + Codex for Lean glue. Add Gemini for taxonomy QA (closure_list C2 worked-example 5/7 mechanism analysis).
**Pre-submission checks:** Literature-check MANDATORY (Y) — closure_list §"Key risk": "REAL closure to a journal *only if* the prior literature explicitly leaves the next-divisor-count case open. Need a freshness sweep (C6) before submitting Week 1."
**Expected hit rate:** ~4–5/10 honest closure probability per slot (closure_list ranks 12–14). Highest reliability mechanism per F1 slot737 evidence.
**Failure modes to watch:** F3 (side-lemma proliferation without closing main; slot691 conj 4.3), F4 (axiomatize-the-hard with `exact?` stubs), F1 (Iff.rfl trap if the σ₀ shape is left undecidable).

---

### Class 3 — Explicit witness construction

**Examples:** E203 (Erdős-Sierpiński, m Coprime 6, top-1 closure_list, 6/10 prob); E672 k=4 ℓ=3 AP-of-powerful witness (top-20, 5/10); Sierpinski covering / E#7 distinct odd covering; E307 finite prime sets reciprocal-product=1; E835 (k+1)-subset coloring; Conway 99-graph adjacency.

**Recommended lane:** `CLOSURE` if witness has been pre-computed off-Lean (greedy-CRT, SAT, external search). `BARE` if Aristotle's MCGS proof search is the witness-finder (rare — only for very small enumeration).
**Companion file:** `.closure.json` with `real_closure_candidate=true`, `closure_mechanism=explicit_witness`, witness literal embedded.
**LLM pairing:** Codex pre-computes witness (greedy-CRT, SAT, external solver) BEFORE submission — closure_list §"load-bearing creative step" explicitly says "search for `m` then `decide` covering". Then Aristotle verifies via `native_decide`. This is the slot740 / slot712 / slot738 winning DNA per F1.
**Pre-submission checks:** Literature-check (Y) — confirm no public witness already exists (e.g., E203: check whether m has been found). I4 must run.
**Expected hit rate:** 3–6/10 honest closure prob (closure_list top-1, 7, 8, 11, 16, 17, 18, 20). E203 at 6/10 is highest.
**Failure modes to watch:** F9 (compute explosion if search space too large), F4 (axiomatize-the-hard if witness construction left as `exact?`), F6 (restate-with-sorry if witness not pre-computed — Tuza ν=4 pattern, F5/F6 combined per failure_dna §"Tuza ν=4 Dominant Mode").

---

### Class 4 — Disproof via small counterexample

**Examples:** E64 Erdős-Gyárfás 2^k cycles min-deg-3 disproof (top-16, 3/10); E617 r=4 cex on Fin 17 (top-7, 3/10); E137 k=4 powerful tuple disproof (top-11, 3/10); Lemoine / Grimm odd n>6 counterexample; Wikipedia Fermat-composite (vanishing prob).

**Recommended lane:** `CLOSURE` (counterexample is an explicit witness — same DNA as Class 3, just disproving instead of proving).
**Companion file:** `.closure.json` with `closure_mechanism=disproof_construction`, witness graph/integer embedded literally.
**LLM pairing:** Codex SAT-search precedent (closure_list §"Failure modes" entry 16 cites "SAT-search precedent in C3"). Grok for combinatorial intuition (E#617 Grok-implicit per closure_list). Ensemble for the rare cases where the search space is large (Conway 99-graph).
**Pre-submission checks:** Literature-check (Y) — confirm no public counterexample (Lemoine: verified up to ~10⁹; Grimm: open).
**Expected hit rate:** 2–3/10 (closure_list top-2, 3, 4, 5, 11, 16). Conway 99-graph at 2/10 but transformative if hit (Conway's $1000 prize).
**Failure modes to watch:** F5 (recursive falsification — counterexample disproves its own scaffolding; documented heavy on Tuza ν=4 slot543), F6 (restate-with-sorry if SAT didn't return a witness yet).

---

### Class 5 — Solved-upstream formalization

**Examples:** Leinster D₃×C₅ classification (formalization_only per closure_list §"Don't Confuse §"Honorable mention"); Pollock tetrahedral 1850 (formalization_only per closure_list §"Don't Confuse §2"); any problem identified as solved in literature post-Erdős-database refresh.

**Recommended lane:** **HARD-BLOCK at I4 literature check.** No lane.
**Companion file:** N/A.
**LLM pairing:** Literature search agent only (verify it really is solved upstream).
**Pre-submission checks:** I4 literature-check MUST run BEFORE the gate. If `solved_upstream=true`, refuse with `INFRASTRUCTURE_ONLY` label per closure_list §"Single most-important closure-lane upgrade".
**Expected hit rate:** Engineering rate 80%+ (compiles fine — it's a known proof). REAL closure rate: 0% (W2 wiki §1a tracks these as "Section 2(b) Formalization" — secondary contribution, not novel math).
**Failure modes to watch:** F10 (definition mismatch with formal-conjectures), AND the meta-failure: counting formalization as closure (CLAUDE.md Rule 12, F10 §3 Upgrade #5).

---

### Class 6 — Structural-open with cross-domain potential

**Examples:** E938 Frey-Hellegouarch curve + Ribet level-lowering on consecutive powerful triple; E672 k=4 ℓ=3 Frey curve + Chabauty on rank-1 Jacobian; E64 Cayley graphs of small-cancellation groups (Magnus/Lyndon); E267 Pisot beta-expansion structure; E850 S-unit Baker bounds.

**Recommended lane:** `FUSION` + `INFORMAL` (both required — these are the ONLY problems where rich proof-outline submission to Aristotle's informal-reasoning subsystem is the winning move per W8 §"single most surprising finding").
**Companion file:** `.fusion.json` with full `informal_proof_outline` (150–400 words per F10 §3 Upgrade #3), 3–5 `candidate_lemmas`, and 1 bridge-lemma citation. Routes through `aristotle_informal.py` with `--informal-mode` set.
**LLM pairing:** ENSEMBLE REQUIRED. GPT-5.2 Pro as strategist (W8 §"reconciliation": canonical workflow is "GPT-5.2 Pro generates informal proof → Aristotle formalizes"); Codex for Lean glue; Gemini for cross-domain technique scouting (F4 §4 LLM technique-transfer is the most leverageable AI capability); Grok for adjacent-analog discovery; Aristotle informal mode as formalizer.
**Pre-submission checks:** Literature-check (Y) — F10 §6 caveat on E#672: "GHP 2009 may already cover it — must do literature delta first". I4 + targeted ArXiv/MathSciNet sweep for Frey/Ribet/Chabauty precedents on the specific exponent pair.
**Expected hit rate:** F10 §6: only **2 of top-20** are actually fusion-amenable (E#672 k=4 ℓ=3 and E#938). F10 §4 day-31–60 honest estimate: ~1–3% on well-chosen dossier-backed targets. W8 §3 Experiment 3 information value: even partial credit (Aristotle cites Bennett-Skinner OR reaches for `EllipticCurve.Jacobian`) flips the H2 hypothesis.
**Failure modes to watch:** F1 (Iff.rfl trap if the conjecture is left undecidable — many cross-domain conjectures ARE undecidable predicates), F3 (infrastructure overgrowth — Aristotle builds Pell/sieve scaffolding without closing main; slot703 E#672 already exemplified at 1148 lines), F4 (axiomatize-the-hard — `apply pell_valuation_mul_prime'` defined recursively as `exact?` per slot687).

---

### Class 7 — Famous deep conjectures

**Examples:** Riemann Hypothesis, BSD, P≠NP, Twin Primes, Goldbach, abc conjecture, Erdős discrepancy infinite case, Erdős-Szekeres exact bound, infinite-witness Gaussian moat (E952), Fermat F_n>4 composite for all n.

**Recommended lane:** **AVOID. No lane. Hard-skip at screen step.**
**Companion file:** N/A.
**LLM pairing:** N/A.
**Pre-submission checks:** Screen step (`/screen`) must classify as `SKIP` automatically.
**Expected hit rate:** **0%** per W3 (no AI has resolved a Millennium / famous-deep). W6 community consensus: Buzzard "no killer app yet"; Matchett Wood "had assembled human experts spent the same time"; W8 §5 ceiling ~20% even for partial credit. closure_list excludes Gaussian moat (top-6) and Fermat-composite (top-9) explicitly: "infinite-witness construction; closure mechanism is genuinely missing" / "search beyond PrimeGrid, no realistic witness search".
**Failure modes to watch:** F3 (infrastructure overgrowth — Aristotle will produce 1000-line scaffolding because the surface looks tractable), F1 (Iff.rfl trap — RH, BSD have undecidable predicates), and the META-failure: confusing the operator's morale-cost with the project's signal value.

---

### Class 8 — Long-tail neglected Erdős (the Tao "lowest hanging fruit" sweet spot)

**Examples:** Erdős #124 (Aristotle-solved Nov 2025 per W8 §1); #1026 (Aristotle rectangle-packing autonomous solve per W8 §2); #728 (Pomerance technique per W8 §2); the entire long-tail of obscure Erdős problems with elementary structure, never written up because the bound or simplification is unsurprising.

**Recommended lane:** `BARE` (≤30-line conjecture statement → Aristotle MCGS) UNLESS the problem has an identified informal lemma decomposition, in which case `INFORMAL` (route through `aristotle_informal.py`).
**Companion file:** None for BARE; `.fusion.json` with minimal `informal_proof_outline` if informal mode preferred.
**LLM pairing:** Aristotle alone for BARE (this is the slot737 / slot739 successful pattern per F1: zero `native_decide` calls, slot737 used σ₀-multiplicativity AUTONOMOUSLY). Pair with GPT-5.2 Pro for informal-mode replication of the #728 canonical workflow (W8 §3 Experiment 2).
**Pre-submission checks:** Literature-check (Y, lightweight) — confirm no recent paper claims the result. I4 freshness sweep.
**Expected hit rate:** **Highest expected hit rate of any class** — W8: Boris Alexeev got "12 Erdős problems in 90 days" via informal mode. Tao's "lowest hanging fruit" framing (W2/W8): "amenable to simple proofs using fairly standard techniques." closure_list pure-existence small-witness Week-3 cluster (E#203, E#307, E#835) targets exactly this regime.
**Failure modes to watch:** F1 (Iff.rfl trap — even long-tail problems with `Tendsto` / `Irrational` / `IsEquivalent` predicates will produce definitional tautologies per failure_dna §F1 11/25 frequency), F2 (excluded middle if framed as `P ∨ ¬P` — gate blocks but worth a second look), F8 (vacuous iff — `answer ↔ ⟨verbatim definition⟩`).

---

## The Single Most Important "Do Not Confuse" Warning

> **DO NOT CONFUSE CLASS 1 (FINITE VERIFICATION WITH COMPUTABLE BRIDGE) WITH CLASS 6 (STRUCTURAL-OPEN WITH CROSS-DOMAIN POTENTIAL).**

These two classes look superficially similar (both involve a number-theoretic Diophantine question; both can be sketched in ≤30 lines; both have a Lean target involving primes, divisibility, or exponents) — but they have **opposite** success criteria and **opposite** lane assignments.

| | Class 1 (Finite verification) | Class 6 (Cross-domain) |
|---|---|---|
| **Lane** | `CLOSURE` (bounded extension) | `FUSION` + `INFORMAL` |
| **Companion** | `.closure.json` (`real_closure_candidate=false` for bumps) | `.fusion.json` (`informal_proof_outline` mandatory) |
| **LLM pairing** | Codex + ensemble check | GPT-5.2 Pro strategist + Aristotle informal mode |
| **Success def** | Verified bound, journal_partial | Bridge lemma works, journal_clean novel math |
| **Hit rate** | 60–80% compile, <10% real closure | <5% hit rate but transformative on hit |

**Why this is the most important warning:** closure_list §"Don't Confuse These With Closure" lists FT p=3 q≡71 mod 72 q-bumps (slot 720) and Brocard `[1001, 2000]` bumps (slot 738 sequel) — both look like "we extended FT" or "we extended Brocard" but **they are bounded_version_closure**. Meanwhile **E#672 k=4 ℓ=3** (closure_list top-20) is **the SAME problem as the Brocard bumps in shape** (small Diophantine with prime structure) — but it is **fusion-amenable** because Frey curve + Chabauty produces a bridge lemma. Submitting E#672 k=4 ℓ=3 to the CLOSURE lane with a bare witness sketch is the dominant historical failure mode: F1 found slot703_erdos672 produced 1148 lines of Pell/SeqA/SeqB infrastructure (F3 failure mode) and slot698_erdos672 left `exact?` stubs (F4 failure mode). Routing the same problem to FUSION+INFORMAL with GPT-5.2 Pro as Frey-curve strategist is the only path with non-zero probability of real closure on that DNA — and we have never tried it.

**Operational rule:** If the problem has a known cross-domain bridge (Frey, Chabauty, Ribet, Bennett-Skinner, percolation, Cayley group theory, Aurifeuillean factorization), it is Class 6 — route to FUSION+INFORMAL. If the only path is "find a witness and `decide`", it is Class 3 — route to CLOSURE. If the only path is "extend the bound by 1", it is Class 1 — route to CLOSURE but DO NOT call it closure.

---

## Documentation Path

`/Users/patrickkavanagh/math/docs/lane_routing_matrix.md`
