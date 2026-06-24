# Aristotle Behavioral Ceiling Audit — May 30, 2026 (A3)

**Scope.** ~33 Aristotle submissions submitted/completed today (DB ids 1258..1290). Deep-read 14 representative result `.lean` files in `submissions/nu4_final/*_extracted/`. Cross-referenced with existing `aristotle_capability_profile_may30.md` and `closure_list_may30.md`.

This is a *ceiling* audit, not an inventory. The question: when given a bare conjecture and prior context, **what does Aristotle actually do, and what does it never do?**

---

## 1. Eight Output Patterns Observed Today

| # | Pattern | Today's instances | Trigger | Problem shape |
|---|---|---|---|---|
| P1 | **Pure `native_decide`** (single tactic closes everything) | R3 (FT q≤2000), R10 (Cunningham 35), slot 744 (FT q=1583 BARE), slot 746 odd multiperfect *bounded chunk* | BARE sketch, bounded universally-quantified statement | finite decidable verification |
| P2 | **Witness-table + `native_decide`** | E373 Surányi (bound `n < 2a`), slot 738 Brocard (50 witness entries), slot 743 (E203 12×12 with 63-digit CRT witness, 178 `native_decide` invocations across 213 lemmas), slot 745 (Brocard n∈[1001,2000], chunked) | BARE, range-shaped statement | bounded chunked verification |
| P3 | **Multi-step structural proof (≥3 helper lemmas, sorry-free main)** | E1052 (8+ helper theorems incl. `wall_k2`, `unitarySigma_mul_coprime`, `unitarySigma_eq_prod_one_add_pow`, *but* main `erdos_1052` still `sorry`); R9/E1003 (3 lemmas: `totient_mul_rad_eq`, `totient_ratio_of_primeFactors_eq`, `primeFactors_eq_filter_of_support_subset`, sorry-free 76-line main); E373/Hickerson L8 (4 sorry-free `mem_S_*` lemmas, main `sorry`); slot 746 OddMultiperfect (3 helpers + sorry-free main, σ₀=11 only) | INFORMAL-MODE on fusion lane, structural-finite-reduction closure | reduces unbounded goal to structural identity |
| P4 | **Strategy critique / falsification of sketch** | E938 v1/v2 (Chan/abc conditional), E1003 v1 (Subspace fixed-support), R7/E324 Asiryan (file explicitly flags "Asiryan 2026 reference appears to be fabricated") | INFORMAL fusion with conjectured paper reference | unverifiable cited machinery |
| P5 | **Autonomous proof substitution** (Aristotle ignores the sketched route and writes its own) | E267 (replaces Pisot-Yu route with elementary "decreasing-numerator" tail argument, 319 lines); R9 (replaces Schmidt Subspace Theorem with simple φ/n injection); R7 h=0 slice (replaces genus-one fibration with discriminant-of-residual-quadratic) | INFORMAL fusion sketch citing heavy machinery | conjecture has known elementary proof Aristotle finds |
| P6 | **Engineered algorithm design** | R4 (E324 quintic n=200): defines `quinticPairSums n : List` and `quinticSumsNodup` Bool, proves an injection lemma `quinticSumsNodup_imp`, closes the entire 200-case sweep via `native_decide` — this is custom data-structure design, not just witness extraction | BARE / verification-extended | bounded but with naive `Fin 51^4` blowup; Aristotle invented a `Nodup` reformulation that avoids it |
| P7 | **Honest failure (`sorry` + scholarly comment)** | L1/E944 (Dirac k=4), L7/E477 (Sekanina cubic), E100 Piepmeyer (Harborth construction), E938 main, E1052 main, E373 Surányi/Hickerson main, R7 main, R9 main | INFORMAL fusion, "OPEN" conjecture | genuine open problem with no elementary route |
| P8 | **Single-line `native_decide` for a numeric divisibility** | FT q=1583 v2 ("`norm_num; native_decide`"), L3/E324 n=50, slot 744 | BARE, single mod-arithmetic claim | trivial number-theoretic verification |

**Frequencies across today's deep reads (n=14):** P1=4, P2=4, P3=4, P4=3, P5=3, P6=1, P7=8 (overlaps), P8=3.

---

## 2. The Ceiling — What Aristotle Did NOT Attempt

Across 33 submissions today, Aristotle never:
- Invoked **modular forms, Galois representations, L-functions, motives, or étale cohomology**.
- Used **sieve methods** (large sieve, Selberg sieve, parity barrier discussion).
- Constructed a **non-trivial algebraic-geometric object** (elliptic curve point, modular curve, fibration).
- Wrote **>3 chained nontrivial lemmas** without leaning on `native_decide` somewhere down the call tree.
- Produced **any unconditional new bound on an unbounded conjecture** (every "advance" is sub-claim closure: bounded n, single σ₀ shape, single q value, single k value).
- **Adapted a strategy from a cited paper it could not verify** — when the sketch cites Subspace Theorem / Asiryan / Chan-abc, Aristotle either substitutes an elementary argument (P5) or comments "this reference appears fabricated" (P4) — it does *not* try to import the cited machinery.
- Proved a result that wasn't either (a) decidable-finite, (b) a known classical reformulation, or (c) a structural lemma reducing to (a) or (b).

---

## 3. The Hardest Thing Aristotle Did Today

**Two candidates, tied:**

**(a) R9 / E1003 fixed-support finiteness** (`/Users/patrickkavanagh/math/submissions/nu4_final/r9_subspace_extracted/.../Erdos1003.lean`). The submitted sketch invoked Evertse-Schlickewei-Schmidt Subspace Theorem + Tao 2016 entropy decrement, a Fields-medal-grade two-pillar attack. Aristotle silently discarded both and proved finite-support finiteness of φ(n)=φ(n+1) solutions via an injection `n ↦ (S.filter(·|n), S.filter(·|n+1))`, with a clean ratio lemma `φ(n) · rad(n) = n · ∏(p-1)` and `primeFactors_eq_filter_of_support_subset`. The proof is correct, sorry-free in the 3 helpers, and the main theorem closes the finiteness statement. The math content is elementary (a competent grad student gets it in an afternoon), but the *autonomy* — ignoring the sketch's heavy artillery and finding the right elementary path — is the strongest behavior.

**(b) R4 / E324 n=200** (`/Users/patrickkavanagh/math/submissions/nu4_final/r4_e324_n200_extracted/.../Main.lean`). Naive `native_decide` on `Fin 201^4` is ~1.6 billion cases — infeasible. Aristotle's response was to invent the `quinticPairSums` / `quinticSumsNodup` data structure: enumerate pairs once, then verify list-`Nodup` on the projection. This reduces the verification to ~20k entries. The bridging lemma `quinticSumsNodup_imp` is a genuine logical reformulation, not a witness table. *Algorithmic creativity* on top of `native_decide`.

Honorable mention: **E1052** writes a sorry-free product formula `σ*(n) = ∏(1 + p^{v_p(n)})` and a sorry-free `wall_k2` (2-prime-factor case). The σ*(p^10) prime-power formula and Wall's k=2 reduction are competent classical algebra — better than a beginner, on par with Mathlib contributors.

---

## 4. The Gap to "Novel Research Math"

| Dimension | Today's ceiling | Novel research math |
|---|---|---|
| New theorem | None — every advance is `bounded_version_closure`, `sub_claim_closure`, or `journal_subclaim` per `closure_list_may30.md` | A statement not previously in literature |
| Non-obvious lemma chain | ~3-helper chains in P3 | 10+ interlocking lemmas with novel intermediate concepts |
| Machinery depth | Mathlib level: factorials, totient identities, prime factor sets, polynomial discriminant of cubics | Modular forms, p-adic methods, ergodic theory, additive combinatorics |
| Strategic autonomy | High: rewrites sketches (P5) when an elementary path exists | Necessary for novel work: but Aristotle has no path when no elementary path exists |
| Unbounded result | Zero today | The point of research |

The gap is **categorical**, not quantitative. Aristotle operates inside a closed elementary universe defined by (Mathlib lemmas) ∪ (`native_decide` for finite checks) ∪ (interval-cases + omega + linarith). When a problem's natural proof lives in that universe, Aristotle finds it — and the autonomy to *find* it (P5) is non-trivial. When the natural proof requires anything outside (modular forms, sieve, geometric machinery), Aristotle either (P4) flags it and stops, or (P7) writes `sorry` with a citation. It never *imports* novel machinery. The R9 case is the strongest evidence: confronted with Subspace Theorem, it elected to prove the *easier* fixed-support finiteness rather than instantiate Subspace.

---

## 5. Verdict — Can Aristotle Produce Novel Math Under Any Input Shape We Have?

**No.** Under the input shapes available today (BARE, INFORMAL fusion, BARE+context, witness-table-stub):
- It produces **competent formalization** of known elementary math (P3 helpers, P6 algorithmic reductions).
- It produces **autonomous elementary proofs when one exists** (P5 — R9 injection, E267 tail argument, R7 discriminant).
- It produces **honest negative signals** when the sketched route is unverifiable (P4 — R7 Asiryan flag is genuine quality work).
- It does NOT produce **non-elementary novel theorems**. The ceiling is roughly: "what a sharp Mathlib contributor could do in a day, formalized."

The closure axis confirms this: today's `compiled_no_advance` results are all `bounded_version_closure` or `sub_claim_closure`. Zero results moved an *unbounded* open conjecture forward by a non-elementary step. Aristotle's strongest output is P5 (autonomous substitution) — and even there, the substitute is always elementary.

**Implication for our pipeline.** The 0.8% hit rate is structural, not tactical. Submitting BARE + context to an unbounded open conjecture where the literature shows only non-elementary attacks have ever made progress (E944 Dirac, E477 Sekanina cubic, E100 Piepmeyer construction, E1052 main, E373 main) will yield P7 — honest `sorry` — every time. The pipeline should concentrate on: (a) finding conjectures whose natural proof *might* be elementary but hasn't been found, (b) bounded sub-claims of famous conjectures, and (c) falsification probes.
