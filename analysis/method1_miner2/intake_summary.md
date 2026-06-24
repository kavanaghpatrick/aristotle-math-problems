# Miner-2 ready-queue + intake summary (Method-1 selection)

source_screen_run --dirs ErdosProblems --limit 40: 45 statements screened, 22 lit-CLEAR non-terminal
in v_method1_ready. After applying the HARD rubric:

## Filter 1 — answer(sorry) placeholders are ILL-POSED (excluded)
30 of 45 screened statements are `theorem X : answer(sorry) ↔ <P>`. These are NOT provable targets:
Aristotle closes them trivially by instantiating `answer := P` and proving `P ↔ P`. EXCLUDED:
erdos_10, 1056(main), 1059(main), 1065a/b, 1068, 1071b, 1073, 1074(main), 1080, 1093.parts.i, 1097,
1052, 107, noll_simmons, etc.

## Filter 2 — known-formalization (excluded)
erdos_100_piepmeyer ("From [Piepmeyer]: 9 points with diameter < 5", named construction). Already at
compiled_partial (id 1261) and re-grabbed as method1 submission (id 1345) — the exact trap. EXCLUDED.

## Survivors (real, non-placeholder, lit-CLEAR): 8 statements
erdos_1041, erdos_1094, erdos_1093.parts.ii, erdos_1055, erdos_1095_lower_conjecture,
erdos_1095_upper_conjecture, erdos_1094, erdos_1 (+ erdos_100_strong, deep distinct-distances).

## Filter 3 — deep-structural class (debate-adjudicated, Gemini+Codex)
Transcript: /tmp/method1_miner2_debate.md. UNANIMOUS "Finiteness Fallacy" verdict:
- erdos_1094  (lpf finitely-many-exceptions): DEEP-STRUCTURAL, ~0%, SKIP (needs effective g(k) bounds)
- erdos_1093.ii (deficiency>1 finite): DEEP-STRUCTURAL, ~0%, SKIP (smooth-number distribution)
- erdos_1055  (infinitely many primes per class): DEEP-STRUCTURAL, 0%, SKIP (Dirichlet/Chen-level)
- erdos_1095 (both, smooth-binomial asymptotics): DEEP-STRUCTURAL estimate, SKIP
- erdos_1 (distinct subset sums N≫2^n): famous $-prize conjecture, deep-structural, SKIP
- erdos_1041 (short-path): genuinely-open, marginal #1 but a universal metric estimate; Tao+AlphaEvolve
  already failed -> frontier, expect ~0-1%.

## C5 (tuza_nu4) — legit debate subject (falsified-approaches HELD)
Residual is NOT one sorry: ~20+ scattered sorries across lemma04-09 mixing trivial bookkeeping
("extract vDA≠vAB", "x=y from cardinality") with the genuine hard core ("5-packing contradiction when
apex=vBC"). The hard-core sorries are exactly what 70 prior attempts + 5 named approaches failed on.
Finite-structural in shape but residual = the theorem's hard core, NOT cleanly closeable. HELD.

## BOTTOM LINE (honest)
The ready-queue contains NO clean Method-1 candidate. 30/45 are ill-posed answer-placeholders; the real
statements are deep-structural finiteness/infinitude/extremal traps or an exhausted hard-core scaffold.
Reporting all with honest open_status + tractability rather than dressing traps as tractable.
