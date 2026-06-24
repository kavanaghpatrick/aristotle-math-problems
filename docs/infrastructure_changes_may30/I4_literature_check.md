# I4 — Literature Freshness Check

**Status:** shipped 2026-05-30
**Owners:** I4 (infrastructure)
**Related work:** C1 audit (`analysis/open_problems_registry_may30.csv`), W6
Bloom-debunker note, C6 erdos_672 review.

## Why this exists

C1's audit found 38 registry rows (28 distinct problems) flagged
`POSSIBLY_SOLVED_SINCE` — problems where another AI team or the recent
literature has closed the problem since we last looked. Without an
automated check, the existing pipeline (`/sweep` → `/sketch` → `/submit`)
will happily burn compute resubmitting closed problems.

W6 confirmed that Bloom-style debunking — checking the wiki and
`erdosproblems.com` before claiming novelty — is the implicit community
standard. I4 turns that discipline into a gate that runs before every
submission.

## Script: `scripts/literature_check.py`

### CLI

```text
literature_check.py [-h] [--backfill] [--no-cache] [--skip-arxiv] [--json] [target]
```

- `target` — either a problem_id (`erdos_728`, `pollock_tetrahedral`) or a
  sketch file path. If a path is given, the problem_id is inferred from the
  filename or from the `OPEN GAP:` header.
- `--backfill` — process every `POSSIBLY_SOLVED_SINCE` row in
  `analysis/open_problems_registry_may30.csv` and emit
  `analysis/literature_kill_list.csv`.
- `--no-cache` — ignore the cache, hit the network.
- `--skip-arxiv` — skip the arxiv recent-papers search (faster; recommended
  for batch / backfill use).
- `--json` — emit the raw JSON report instead of a human summary.

Exit code carries the decision for shell pipelines:
- `0` → CLEAR / UNKNOWN
- `1` → AMBIGUOUS / POSSIBLY_SOLVED
- `2` → AI_CLOSED / RECENTLY_SOLVED

### Importable API

```python
from literature_check import check_literature, status_for_sketch

report = check_literature("erdos_728")            # by problem_id
report = status_for_sketch(Path("slot999.txt"))   # by sketch file
```

Both return a dict with:

```python
{
    "problem_id": "erdos_728",
    "erdos_n": 728,
    "status": "AI_CLOSED",            # see status taxonomy below
    "wiki_status": "AI_CLOSED",
    "wiki_evidence": ["wiki 1(b): AI alongside literature"],
    "wiki_snapshot_date": "2026-05-30",
    "erdosproblems_status": "solved",
    "erdosproblems_url": "https://www.erdosproblems.com/728",
    "arxiv_recent": [...],
    "mk_failed": {"present": False, "lines": []},
    "citations": [{"source": ..., "url": ..., "evidence": ...}, ...],
    "checked_at": "...",
    "cache_age_days": 0.0,
}
```

### Status taxonomy

| Status            | Meaning                                                                        | Gate action       |
|-------------------|--------------------------------------------------------------------------------|-------------------|
| `AI_CLOSED`       | Wiki lists a full AI solution (sections 1(a)/1(b)/1(c)/2(c))                   | REJECT submission |
| `RECENTLY_SOLVED` | `erdosproblems.com` returns `id="solved"` or `id="disproved"`                  | REJECT submission |
| `AMBIGUOUS`       | Partial AI progress (1(a) Partial) or human+AI collaboration (1(d))            | WARN, ack required |
| `POSSIBLY_SOLVED` | Section 2(a) only — AI used literature search, partial result may exist        | WARN, ack required |
| `CLEAR`           | None of the above; submission proceeds silently                                | pass              |
| `UNKNOWN`         | Could not infer a problem_id from the input                                    | pass (soft notice) |

### Sources consulted, in priority order

1. **teorth AI-contributions wiki** —
   `https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdős-problems`
   Snapshot lives in `WIKI_AI_*` sets inside the script (snapshot date in
   `WIKI_SNAPSHOT_DATE`).
2. **erdosproblems.com** — Per-problem page parsed for `id="solved"`,
   `id="open"`, `id="partial"`, `id="disproved"` markers (Bloom-curated).
3. **arxiv** — recent papers (2024-2026) matching `Erdős problem <N>`.
4. **Local `mk failed <keyword>`** — surfaces prior failed approaches from
   `knowledge.db` so we don't repeat them.

## Integration with `safe_aristotle_submit.py`

A new function `check_literature_freshness(input_file, *, force_stale,
literature_ack)` runs as a new gate inserted between the gap-targeting and
closure-axis checks (look for `LITERATURE FRESHNESS GATE` in
`safe_aristotle_submit.py`).

Gate decisions match the table above. The error class
`LiteratureStaleError` is a subclass of `SubmissionError`.

### New CLI flags on `safe_aristotle_submit.py`

- `--force-literature-stale` — submit anyway when the gate finds
  `AI_CLOSED` / `RECENTLY_SOLVED`. Logged via `LITERATURE_STALE_BYPASS`
  transaction.
- `--literature-ack "<note>"` — acknowledge an `AMBIGUOUS` /
  `POSSIBLY_SOLVED` warning. Required to proceed past those states.
  Logged via `LITERATURE_ACK_RECORDED`.

The existing `--force` flag bypasses every gate including this one (as it
already did for gap-targeting and closure-axis).

## Cache design

- Location: `submissions/literature_cache/<problem_id>.json`
- TTL: 7 days (`CACHE_TTL_SECONDS = 7 * 24 * 3600`)
- Storage: one JSON file per problem_id, named with characters
  sanitised to `[A-Za-z0-9_.-]`.
- Cache misses or expirations re-hit the network; failures degrade
  gracefully (the gate returns `UNKNOWN` rather than blocking).
- To bust the cache for a specific problem, delete its file or pass
  `--no-cache` on the CLI.

## Backfill kill-list

Running `python3 scripts/literature_check.py --backfill --skip-arxiv`
produces `analysis/literature_kill_list.csv`:

- **Input:** 38 `POSSIBLY_SOLVED_SINCE` rows in
  `analysis/open_problems_registry_may30.csv`
- **Distinct problem_ids:** 28
- **Confirmed kill (`AI_CLOSED` or `RECENTLY_SOLVED`):** 26
- **Ambiguous (warn, ack required):** 2 (`erdos_326`, `erdos_996`)
- **Clear:** 0

The 26 confirmed-kill problems should not be submitted under the standard
sketch pipeline. The 2 ambiguous problems need a manual review before
submission and must pass `--literature-ack "<note>"` if a submitter
decides to proceed.

## How to update for new AI teams entering the field

The wiki updates roughly weekly. When new closures arrive:

1. Open the live wiki:
   `https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdős-problems`
2. Update the corresponding set inside `scripts/literature_check.py`:
   - `WIKI_AI_SOLVED_STANDALONE` — Section 1(a) green
   - `WIKI_AI_PARTIAL_STANDALONE` — Section 1(a) yellow/white/red
   - `WIKI_AI_ALONGSIDE_LIT` — Section 1(b)
   - `WIKI_AI_BUILD_LIT` — Section 1(c)
   - `WIKI_AI_HUMAN` — Section 1(d)
   - `WIKI_LIT_SEARCH` — Section 2(a)
   - `WIKI_REWRITING` — Section 2(c)
3. Bump `WIKI_SNAPSHOT_DATE` to the wiki's "Last updated" timestamp.
4. Bust the cache directory once so existing rows re-resolve:
   `rm -rf submissions/literature_cache/erdos_*.json`
5. Re-run `python3 scripts/literature_check.py --backfill --skip-arxiv`
   and review the diff on `analysis/literature_kill_list.csv`.

Non-Erdős sources (other competitions, arXiv preprints, Mathematica's
problem index, etc.) can be added as additional `_http_get` callers in
`check_literature()`. The status-resolution cascade only needs an extra
`elif` branch reading the new signal.

## Verification

Tested 2026-05-30 against four known cases:

| Problem        | Expected behavior         | Actual                          |
|----------------|---------------------------|---------------------------------|
| `erdos_728`    | AI-closed (Aristotle+GPT5)| `AI_CLOSED` (wiki 1b, ep solved)|
| `erdos_124`    | Partial AI work flagged   | `AMBIGUOUS` (wiki 1a Partial)   |
| `erdos_672`    | Still open per C6         | `POSSIBLY_SOLVED` (wiki 2a partial-in-lit) |
| `erdos_64`     | No AI work, fully open    | `CLEAR`                         |

Note on `erdos_124`: The wiki actually classifies 124 as a 🟡 partial
result by Aristotle (29 Nov 2025), not a full closure. `AMBIGUOUS` is
therefore the correct discipline — the submitter must acknowledge the
partial work before proceeding.

Note on `erdos_672`: GPT performed a literature search 7 Jan 2026 and
found a partial result. The problem itself is still open per C6, so
`POSSIBLY_SOLVED` (a soft warn, not a reject) is the right behavior — we
preserve the signal without blocking.
