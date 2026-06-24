# Sketch Context Audit — F2/10

Date: 2026-05-30
Auditor: Agent F2
Sample: 20 sketches from `submissions/sketches/` (303 files total, 220 non-ID `.txt`).

---

## 1. The Six Categories

1. **GAP_ONLY** — Bare conjecture statement, nothing else.
2. **GAP + COMPUTABLE_BRIDGE** — Gap + a specific Lean function/definition to introduce (e.g., `unitarySigma`, `tetrahedral`).
3. **GAP + WITNESS_DATA** — Gap + explicit candidate number/set/group (e.g., `S₃ × ℤ/5ℤ`, `(p,q)=(5,11)`, "primes 2,3,5,7,11,13,17,19").
4. **GAP + PRIOR_ARISTOTLE_CONTEXT** — Gap + references our own prior `slotXXX` results / "prior result proved" handed back as input.
5. **GAP + CROSS_DOMAIN_LITERATURE** — Gap + references to papers in OTHER mathematical areas (algebraic geometry technique applied to NT, ergodic theory imported to combinatorics, etc.).
6. **GAP + RESEARCH_SYNTHESIS** — Gap + curated multi-subfield summary identifying potential novel connections.

---

## 2. Sample Distribution (n=20)

| Sketch | Lines | Category | Notes |
|---|---|---|---|
| `erdos850_informal_proof.txt` | 45 | 1+2+4(weak) | Restates known names (Evertse, Tijdeman, Pillai, Catalan, abc) — historical attribution only, no synthesis |
| `erdos203_covering_bare.txt` | 13 | 1 | Pure GAP_ONLY |
| `erdos1003_totient.txt` | 11 | 1 | One sentence about EPS87 bound |
| `erdos1052_unitary_even.txt` | 22 | 1+2 | Defines `unitarySigma` |
| `brocard_conjecture.txt` | 18 | 1 | One sentence about Berndt-Galway computational bound |
| `agoh_giuga_primality.txt` | 16 | 1 | Borwein-Maitland-Skerritt bound, single line |
| `slot679_hardy_littlewood_second.txt` | 10 | 1 | GAP_ONLY |
| `slot668_agoh_giuga_v2.txt` | 69 | 4 | Heavy prior-result re-statement (re-prove violation per gate) |
| `slot683_jacobian.txt` | 13 | 1 | GAP_ONLY |
| `slot681_bunyakovsky.txt` | 13 | 1 | GAP_ONLY |
| `slot685_casas_alvero.txt` | 11 | 1 | GAP_ONLY |
| `slot689_lemoine_v2.txt` | 10 | 1 | GAP_ONLY |
| `slot688_gilbreath_v2.txt` | 10 | 1 | GAP_ONLY |
| `slot687_pell_primes_resub.txt` | 9 | 1 | GAP_ONLY |
| `euler_powers_k6.txt` | 19 | 1 | Historical counterexample data |
| `leinster_nonabelian_S3xC5.txt` | 18 | 3 | Explicit witness candidate (S₃ × C₅) |
| `slot720_erdos247_lacunary_transcendence.txt` | 10 | 1 | GAP_ONLY |
| `slot721_erdos258_divisor_irrationality.txt` | 10 | 1 | GAP_ONLY |
| `erdos389_consecutive_products.txt` | 43 | 1+2+4(weak) | Proof outline (violates gate) — Legendre, CRT outline |
| `erdos273_covering.txt` | 14 | 1 | GAP_ONLY |
| `slot651_pollock_tetrahedral.txt` | 46 | 2+3 | Explicit `tetrahedral` def + witnesses for N ≤ 10 |
| `oppermann_conjecture.txt` | 19 | 1 | Baker-Harman-Pintz mentioned (single sentence) |
| `slot728_ft_p5_q11.txt` | 14 | 3 | Concrete (p=5, q=11) witness |
| `erdos1052_unitary_perfect_finite.txt` | 17 | 1+2 | Mentions slot635 prior + Wall 1972 |
| `erdos364_powerful_triples.txt` | 17 | 1 | Chan/She 2025 mentioned single line |
| `erdos617_disproof.txt` | 25 | 3 | Combinatorial witness search (K_26, r=5) |
| `erdos931_smooth.txt` | 24 | 4 | Explicit prior-result enumeration ("PRIOR RESULTS: ...") |
| `odd_multiperfect_sigma0_11.txt` | 21 | 2+3 | σ₀ structural reduction p^10 |
| `erdos647_density_extension.txt` | 23 | 1+4 | Self-references slot723, slot737 |
| `erdos672_descent_v3.txt` | 22 | 1+4 | Lists own prior lemmas |
| `slot652_sierpinski_5n_mod60_1.txt` | 63 | 1+4 (heavy strategy) | Violates gate (APPROACH 1/2/3, "GOAL", "DELIVERABLES") |
| `erdos364_n3mod4.txt` | 23 | 1 | Chan, She 2025 — one line each |

### Distribution Summary

| Category | Count | % |
|---|---|---|
| 1. GAP_ONLY (or with single-line historical citation) | **17/30 sampled** | **57%** |
| 2. + COMPUTABLE_BRIDGE | 6 | 20% |
| 3. + WITNESS_DATA | 6 | 20% |
| 4. + PRIOR_ARISTOTLE_CONTEXT (in-sketch) | 7 | 23% |
| 5. + CROSS_DOMAIN_LITERATURE | **0** | **0%** |
| 6. + RESEARCH_SYNTHESIS | **0** | **0%** |

Categories overlap (a sketch can hit 1+2+3). The dominant pattern is bare GAP_ONLY or with our own prior bookkeeping.

---

## 3. Cross-Domain Content — None Detected

- Greppped all 303 sketches for `arxiv`, `http`, `preprint`, `MathSciNet`, `Google Scholar`, `Annals`, `j. math.`, `techniques from`, `analogous to`, `borrow from`, `cross-domain`. **Zero hits** (one false positive in `erdos203_sierpinski_1d_benchmark.txt` matching "analogous to" in our own framing — not external).
- Citations that DO appear are always historical attribution (Evertse, Tijdeman, Wall 1972, Baker-Harman-Pintz, Berndt-Galway, Elkies, Borwein-Maitland-Skerritt). These are one-line references identifying the open problem's pedigree, NOT a synthesis describing what techniques those papers contain, how they could transfer, or which adjacent subfields hold candidate methods.
- No sketch contains a phrase resembling "an analogous result in [other domain] suggests trying [technique]". Zero.
- No sketch mentions web research, scraping, or downloaded literature.

---

## 4. The Auto-Context Implementation (`safe_aristotle_submit.py`)

### What `gather_context()` actually does

```python
# Lines 504-551 of safe_aristotle_submit.py
def gather_context(problem_id: str) -> list[Path]:
    """Find all prior _result.lean files for this problem from tracking.db."""
    cursor = conn.execute(
        "SELECT output_file FROM submissions "
        "WHERE (problem_id LIKE ? OR filename LIKE ?) "
        "AND output_file IS NOT NULL "
        "AND status IN ('compiled_clean', 'near_miss', 'completed') "
        "ORDER BY submitted_at DESC",
        (f'%{problem_id}%', f'%{problem_id}%')
    )
```

### Critical finding: STATUS FILTER IS BROKEN

The query looks for `status IN ('compiled_clean', 'near_miss', 'completed')`. The actual distinct statuses in `submissions/tracking.db` (1166 rows) are:

| Status | Count |
|---|---|
| `compile_failed` | 262 |
| `compiled_no_advance` | 742 |
| `compiled_partial` | 107 |
| `compiled_advance` | **2** |
| `disproven` | 14 |
| `submitted` | 39 |

**`SELECT COUNT(*) FROM submissions WHERE status IN ('compiled_clean','near_miss','completed')` returns `0`.**

The expected statuses don't exist in the schema (post-rename per CLAUDE.md "compiled_advance is opt-in"). So `gather_context()` returns the empty list for every problem_id, every submission. The "auto-context" feature has been silently no-op for an unknown stretch.

### Even if the filter were fixed

The function would only ever return **our own prior `output_file` paths** — never anything from:
- arxiv (no API call, no scraper)
- MathSciNet
- Google Scholar
- The `literature_lemmas` table (despite existing in `scripts/import_all_to_sqlite.py` — never read in submission flow)
- `analysis/literature_freshness_may30.csv` (manually curated; never auto-attached)
- The math-forge knowledge base
- Cross-domain Mathlib results

The only data source is `submissions.output_file` — the `_result.lean` files Aristotle itself previously produced. By construction, this is pure self-referential context.

---

## 5. Tension with CLAUDE.md Prime Directive

CLAUDE.md is unambiguous (the entire mission section):

> **Solve open mathematical problems** by submitting bare conjecture statements to Aristotle and letting it find novel proofs.
> We do NOT develop proof strategies. We do NOT write step-by-step proof outlines. We state the open gap, attach prior Aristotle results as context, and submit. Aristotle constructs the proof.

And hard rule #2:

> **Sketches are bare conjecture statements** — no proof strategy, no lemmas, no guidance

This directive is enforced mechanically by `check_gap_targeting()`:
- ≤30 non-blank lines (gate rejects more)
- ≤5 lines of Lean code
- Rejects regex matches for `proof strategy`, `proposed approach`, `key lemma`, `approach \d`, `fallback \d`, `proof outline`
- Rejects em-tautology shape `(P) ∨ ¬ (P)`

### Does this PREVENT cross-domain research synthesis?

**Yes, structurally.** Consider a hypothetical sketch fragment:

> Brocard's `n! + 1 = m²` is structurally analogous to Catalan-type Diophantine equations. Bilu-Tichy (2000, J. Reine Angew. Math.) classify polynomial decompositions of `f(x) = g(y)`; their separable-variable theorem reduces consecutive-integer factorial equations to Runge's method on a finite list of curves. This technique was used by Schinzel-Tijdeman (1976) for `y² = P(x)` and could plausibly transfer to factorial-shifted forms.

Such a paragraph would:
- Add ~6-8 lines (still under 30 — line gate passes)
- Match no STRATEGY_PATTERN regex (no "Proof Strategy" heading, no "Approach 1", no "Lemma")
- Be RICH cross-domain synthesis — exactly category 5/6

So the **letter of the gate** would permit it. But the **spirit of CLAUDE.md** ("no proof strategy, let Aristotle find the path") + the user directive ("zero proof guidance, bare conjecture only") would still classify it as proof guidance. The prime directive is enforced by *cultural norm* + *line gate* + *strategy regex* + *operator habit*, in that order — and the operator habit treats "literature synthesis" as falling under "guidance," even though it's mechanically permitted.

### Where the bottleneck actually lives

It is NOT primarily the regex gate. It is:
1. **The prime directive interpreted maximally.** "Bare conjecture, zero guidance" is read as forbidding any external context beyond historical attribution.
2. **The auto-context plumbing has no path for external literature.** Even if a human wanted to attach a relevant arxiv preprint, the flow is bespoke (manual `--context <file>`) — no automated fetch.
3. **The status-filter bug** (point 4 above) means even self-attached prior results aren't reaching Aristotle for ANY submission going through `safe_submit`. The "GAP + PRIOR_ARISTOTLE_CONTEXT" we claim to provide is, on the wire, GAP_ONLY for everything since the status rename.

---

## 6. Quantifying the Limitation

- **0/20 sketches** include any cross-domain research synthesis (category 5 or 6).
- **0/220 total non-ID sketches** contain external URLs (no `http`, no `arxiv`).
- **0 rows** match the `gather_context` SQL filter in the current production database.
- **2 rows** in `submissions` have status `compiled_advance` (genuine novel contributions) — and even those would not be auto-attached because they aren't in the (legacy) status set the function queries.
- The "auto-context" feature, on inspection, attaches **nothing** to current submissions unless the operator passes `--context` manually.

So when a sketch lands on Aristotle's prompt, it is almost certainly:
- The .txt file content (≤30 lines, mostly the bare gap + 1-3 sentences of historical color)
- + no auto-attached prior results (filter bug)
- + occasionally a manually attached `_result.lean` via `--context` or `--codex-context`

There is no path by which Aristotle ever sees: an arxiv abstract, a Mathematical Reviews entry, a textbook chapter, a recent preprint, a cross-domain technique catalog, or even a survey article on the problem's history.

---

## 7. Verdict

We are NOT doing research synthesis. We are doing **bare gap submission**.

- The CLAUDE.md prime directive ("bare conjecture, prior Aristotle context only") is the *philosophical* bottleneck.
- The status-filter bug in `gather_context()` is the *operational* bottleneck — it makes "prior Aristotle context" itself broken.
- No code path anywhere in the submission pipeline reaches outside `submissions/tracking.db`. There is no arxiv/MathSciNet/Scholar adapter, drafted or planned.

If we want to test whether cross-domain research synthesis improves Aristotle's hit rate, we would need BOTH:
- A relaxation (or carve-out) in the prime directive permitting external technique-transfer paragraphs as "context, not guidance."
- A new context source (e.g., `--literature <problem_id>` flag pulling pre-curated technique cards from a literature database, OR a `gather_external_context(problem_id)` helper that hits arxiv/Mathlib).

Without both, we are stuck delivering bare statements + (currently broken) self-context to Aristotle for every one of our 1166 submissions.
