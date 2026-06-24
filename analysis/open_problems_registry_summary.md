# Open Problems Registry — Summary (2026-05-30)

**Generated from:** `formal-conjectures/FormalConjectures/` sweep

**Tag basis:** `@[category research open]`. Note: no `@[category research disproved]` tag exists in this codebase. Only three variants are used: `research open` (805), `research solved` (602), `research formally solved` (5).

## Counts

- **Total open-tagged statements:** 805
- **Distinct theorem names:** 794
- **Distinct root problem_ids:** 595
- **With >=1 prior Aristotle submission:** 65

## Freshness flag distribution

- `AMBIGUOUS`: 2
- `POSSIBLY_SOLVED_SINCE`: 38
- `VERIFIED_OPEN`: 765

## Domain distribution

- `nt`: 525
- `combinatorics`: 152
- `geometry`: 36
- `algebra`: 29
- `analysis`: 26
- `topology`: 8
- `dynamical`: 6
- `cs`: 4
- `measure`: 3
- `varied`: 3
- `linear`: 3
- `fourier`: 2
- `general_algebra`: 2
- `unknown`: 2
- `probability`: 1
- `logic`: 1
- `category`: 1
- `operator`: 1

## Stale-tag findings (top 10)

These are tagged `@[category research open]` in the repo snapshot but flagged `POSSIBLY_SOLVED_SINCE` or `AMBIGUOUS` based on the [teorth/erdosproblems AI-contributions wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems) (snapshot 2026-05-30). DO NOT submit these without checking the wiki / Bloom's page first.

| theorem_name | ams_class | attempts | flag |
|---|---|---|---|
| `erdos_1051` | 11 | 0 | POSSIBLY_SOLVED_SINCE |
| `erdos_1105_cycles` | 05 | 0 | POSSIBLY_SOLVED_SINCE |
| `erdos_1105_paths` | 05 | 0 | POSSIBLY_SOLVED_SINCE |
| `erdos_1148` | 11 | 0 | POSSIBLY_SOLVED_SINCE |
| `erdos_125` | 11 | 0 | POSSIBLY_SOLVED_SINCE |
| `erdos_152` | 5 | 0 | POSSIBLY_SOLVED_SINCE |
| `erdos_152.square` | 5 | 0 | POSSIBLY_SOLVED_SINCE |
| `erdos_258` | 11 | 0 | POSSIBLY_SOLVED_SINCE |
| `erdos_26` | 11 | 0 | POSSIBLY_SOLVED_SINCE |
| `erdos_26.variants.tenenbaum` | 11 | 0 | POSSIBLY_SOLVED_SINCE |

## Erdős open statements — top 10 by prior_attempts_count

(Root statements only, no `.variants.*`)

| theorem_name | ams_class | attempts | flag |
|---|---|---|---|
| `erdos_850` | 11 | 10 | VERIFIED_OPEN |
| `erdos_1` | 5 11 | 9 | VERIFIED_OPEN |
| `erdos_647` | 11 | 9 | VERIFIED_OPEN |
| `erdos_97` | 52 | 9 | VERIFIED_OPEN |
| `erdos_1052` | 11 | 7 | VERIFIED_OPEN |
| `erdos_123` | 11 | 6 | VERIFIED_OPEN |
| `erdos_138` | 11 | 6 | VERIFIED_OPEN |
| `erdos_11` | 11 | 4 | VERIFIED_OPEN |
| `erdos_203` | 5 | 4 | VERIFIED_OPEN |
| `erdos_672` | 11 | 4 | VERIFIED_OPEN |

## Notes on spot checks

- **Erdős 1 (`erdos_1`)**: sum-distinct sets (Conway-Guy 1969). VERIFIED_OPEN. Not to be confused with the covering-systems problem resolved by Hough 2015 (Annals); that is filed elsewhere in the FC corpus.
- **Erdős 250**: in this repo `erdos_250` is tagged `research solved` (Nesterenko 1996 transcendence) and is NOT in the open set. Correct.
- **Erdős 850 (`erdos_850`)**: status open per 2025 surveys; verified open.
- **Pollock tetrahedral**: Watson 1952 / Salzer-Levine 1958 give partial results. Formal statement asks every N is sum of <=5 tetrahedrals — flagged AMBIGUOUS.
- **`research formally solved using lean4`** (5 statements: Erdős 848, 659, BoxdotConjecture, OEIS 87719, plus one more): these are NOT in our open set (they use a separate tag).
- **Hough 2015** (Annals): minimum modulus covering systems disproved Erdős's original conjecture — but the corresponding FC entry, if any, would already be tagged `research solved`.
- **Bloom caveat**: per the TechCrunch / LeCun-Bubeck Oct-2025 exchange, `erdosproblems.com` 'open' status means 'Bloom is unaware of a paper resolving it' — NOT absence of literature solution. This is the source of our `POSSIBLY_SOLVED_SINCE` flags.
