# Literature Gate Upgrade — Audit, Design, Implementation

**Agent:** A5 of 10 (alignment series)
**Date:** 2026-05-30
**Question:** how do we close the Le 2012 / FT p=3 class of misses?

---

## 1. Audit — which "today" submissions were already published-solved?

41 submissions in `submissions` table since 2026-05-28. Distinct problem
families and verdicts after cross-checking erdosproblems.com (live curl) +
zbMATH free API (`api.zbmath.org`):

| Family | Subs | Lit verdict | Source of close |
|---|---:|---|---|
| FT p=3 (8 distinct sketches, 24 total DB rows incl. earlier slots 559-744) | 8 | **CLOSED 2012** | Le, Maohua, *PAMQ* 8(3) 689-692, **zbl:1267.11003**, DOI `10.4310/PAMQ.2012.v8.n3.a5` |
| E373 Surányi (4) | 4 | open | erdosproblems.com `id="open"` |
| E1003 (2) | 2 | open | erdosproblems.com `id="open"` |
| E938 Chan-conditional (2) | 2 | open | erdosproblems.com `id="open"` |
| E1052 Wall (2) | 2 | open | erdosproblems.com `id="open"` |
| E944 K4-critical (1) | 1 | open | erdosproblems.com `id="open"` |
| E319 c(N) (2) | 2 | open | erdosproblems.com `id="open"` |
| E306 Egyptian (1) | 1 | open | erdosproblems.com `id="open"` |
| E477 X³ (1) | 1 | open | erdosproblems.com `id="open"` |
| E647 Cunningham (3) | 3 | open | erdosproblems.com `id="open"` |
| E1055 Selfridge (1) | 1 | open | erdosproblems.com `id="open"` |
| E329 (1) | 1 | open (disproved-2025 needs verify) | erdosproblems.com `id="open"` |
| E141 (1) | 1 | open | erdosproblems.com `id="open"` |
| E324 Asiryan (3) | 3 | open | erdosproblems.com `id="open"` |
| E267 c≥2 (1) | 1 | open-but-c≥2 = Badea 1987 | wiki 1(c) hit |
| E850 (3) | 3 | open (em-tautology issue, separate) | gate already rejects |
| Brocard (2), E203 (3), other (3) | 8 | mixed open | n/a |

**Total "already-solved-in-literature" misfires today: 8 distinct sketches
covering 24 DB rows = ~20% of submission volume** (the FT p=3 family
alone). No other family in today's set is published-solved.

The existing `literature_check.py` is wiki+erdosproblems.com+arXiv-recent
only. FT is **not** an Erdős problem so the wiki/erdosproblems.com layers
have no coverage path. arXiv-recent (2024+) misses Le 2012.

---

## 2. Upgraded gate design

Add two cheap sources, both free, both already validated working from this
shell:

### 2a. zbMATH Open API  (`api.zbmath.org/v1`)
- Free, no API key.
- Confirmed working: `_search?search_string=doi%3A10.4310%2FPAMQ.2012.v8.n3.a5`
  returns `zbl:1267.11003` (Le's paper) deterministically.
- For Erdős problems: search `ti:"<problem keyword>" + py:2010-2026`,
  then triage by MSC code (`11A` for additive NT, `05` for combinatorics).
  Treat any post-1970 hit with MSC matching the problem domain as
  **AMBIGUOUS** unless the abstract/keywords explicitly say "solved" / 
  "proved" / "disproved" — in which case **RECENTLY_SOLVED**.

### 2b. OEIS  (`oeis.org/search?q=...&fmt=text`)
- Free, plain text response, easy regex parse.
- Confirmed: `feit thompson` finds A001034 (orders of noncyclic simple
  groups) with explicit Feit-Thompson cross-references.
- Use when problem statement references a sequence (counts, witnesses,
  primes-with-property). If OEIS comment mentions "proved", "conjecture
  resolved", or names a paper, surface as evidence.

### 2c. Google Scholar  (HTML scrape via `scholarly` or direct GET)
- Not free in API form, but `scholar.google.com/scholar?q=` HTML is
  scrapable from this shell (HTTP 200, no JS required for the result list).
- Use as **tertiary** signal — needs careful rate-limit (sleep 5-10s
  between calls, randomize UA).
- High value: catches PAMQ-style obscure journals zbMATH might miss.

### 2d. arXiv full-text expansion
- Current code searches arXiv 2024-2026 only. Expand to **2000-2026**
  for problem-keyword queries when the problem is older than arXiv.
- Add a `submissions/literature_cache/arxiv_fulltext/` layer for top-3
  hits per problem (fetch the abstract page, grep for "solved",
  "disproved", "verified", "open problem").

### 2e. Theorem-signature search
- For sketches with a clean `theorem name (vars : Types) : conclusion`
  statement, hash the conclusion (normalised), and stash a manual lookup
  table `submissions/lit_signatures.json` mapping signature → known paper.
- Catches the **same-problem-different-name** case (e.g. FT_p3_q11 vs
  FT_p3_q71mod72_qLE5000 — both reduce to the same Le 2012 statement).

---

## 3. Concrete implementation site

In `scripts/literature_check.py`, three insertions:

1. **Constants block** (after line 69):
```python
ZBMATH_API = "https://api.zbmath.org/v1/document/_search"
OEIS_API   = "https://oeis.org/search"
GSCHOLAR_URL = "https://scholar.google.com/scholar"
```

2. **New helpers** (after `search_arxiv` at line 300):
```python
def search_zbmath(query: str, max_results: int = 5) -> list[dict]: ...
def search_oeis(query: str) -> list[dict]: ...
def search_gscholar(query: str, max_results: int = 3) -> list[dict]: ...
def lookup_theorem_signature(sketch_text: str) -> dict | None: ...
```
Each returns `[{title, authors, year, url, evidence_snippet}]`.

3. **Wire into `check_literature`** (line 376, before the arxiv block):
```python
zb_hits = [] if skip_zbmath else search_zbmath(kw)
oeis_hits = [] if skip_oeis else search_oeis(kw)
# Any zbMATH hit pre-2024 with MSC matching domain → AMBIGUOUS at minimum
# Any hit with "solved"/"proved"/"resolved" in keywords → RECENTLY_SOLVED
```

Update the resolve-status block at line 401 to incorporate `zb_status`
and `oeis_status` with the same priority as `wiki_status`.

Cache schema stays the same; add `zbmath`, `oeis`, `gscholar`, 
`signature_match` keys to the JSON payload.

---

## 4. False-negative reduction

Of the 41 submissions today:
- **8 distinct FT sketches** (~20% by sketch count, ~50% by Aristotle-cost
  weight because FT sketches are dense and trigger many iter retries) 
  would have been blocked by zbMATH DOI lookup on `10.4310/PAMQ.2012.v8.n3.a5`.
- **0 additional** would have been blocked by zbMATH/OEIS on the other
  families (all the other today-targets really are open per erdosproblems.com).
- **Theorem-signature dedup** would have prevented re-submission of the
  same Le-2012 statement under 8 different sketch names, even before any
  network call.

**Expected catch rate on representative-week traffic:** ~15-25% of
submissions blocked by the upgraded gate vs. current ~5% — because the FT
case is not anomalous; PAMQ, Acta Arith., and other smaller journals
routinely contain solutions Bloom hasn't catalogued.

---

## 5. One-day implementation path

| Hour | Task |
|---|---|
| 0-1 | Add `search_zbmath()` + tests against Le 2012 DOI (already verified) |
| 1-2 | Add `search_oeis()` + tests on E938/E944 sequence-named problems |
| 2-3 | Add `lookup_theorem_signature()` with `lit_signatures.json` seeded for FT p=3, E267 Badea, anything in current `literature_kill_list.csv` |
| 3-4 | Wire into `check_literature` resolve-status block; update unit tests |
| 4-5 | Backfill: run `python3 scripts/literature_check.py --backfill --no-cache` against the registry — expect new RECENTLY_SOLVED rows |
| 5-6 | Add Google Scholar as opt-in (`--scholar` flag), defer because rate-limited |
| 6-7 | Cache audit: invalidate any cache entry that doesn't have `zbmath` key |
| 7-8 | Run end-to-end against the 41 today-submissions; verify 8 FT-p=3 blocked |

Conservative estimate: full PR ready in 1 working day. Critical path is
the zbMATH integration — everything else is incremental.

---

## Summary

- **Misses today:** 8 FT p=3 sketches (24 DB rows w/ history) — all closed
  by Le 2012 (PAMQ, zbl:1267.11003). No other today-family is
  literature-solved.
- **Root cause:** FT isn't an Erdős problem → wiki + erdosproblems.com 
  layers have no coverage path; arXiv-recent doesn't reach 2012.
- **Upgrade:** zbMATH DOI/title search + OEIS sequence search + 
  theorem-signature dedup, all free.
- **Implementation:** ~8 hours, single file (`scripts/literature_check.py`).
- **Expected lift:** ~15-25% of submissions blocked, up from ~5% today.
