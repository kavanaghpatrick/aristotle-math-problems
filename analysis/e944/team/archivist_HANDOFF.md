# ARCHIVIST HANDOFF — E944 (Dirac k=4) literature command

Status: literature command COMPLETE. k=4, r=1 CONFIRMED open as of June 2026 (three independent sources). Successor: read this + the 7 deliverable files; do NOT re-fetch the papers (text cached, see below).

## (1) COMPLETED DELIVERABLES (all in analysis/e944/team/)
- **archivist_definitions.md** — exact Lean semantics. IsCritical = VERTEX-critical (NOT edge-critical). Lean stmt forces a FINITE-edge witness (via skeptic's ncard proof, integrated). START HERE for what the target actually is.
- **archivist_known_walls.md** — CANONICAL list of all 7 published obstructions (W1 Lattanzio prime; W2 circulant→χ=3 + witness-symmetry table; W3 M-S arithmetic; W4 density Prop 5.1; W5 small-n exhaustion; W6 J–S connected/spanning-E* conjecture; W7 k=3 degeneracy). Best single reference.
- **archivist_constructions_why_k4_fails.md** — all 5 constructions + EXACT reason each dies at k=4.
- **archivist_jensen_siggers_2012.md** — FULL extract of the CLOSEST-EVER k=4 result. The construction lever.
- **archivist_master_toolkit.md** — every usable theorem precisely cited (§A necessary conds, §C positive tools incl. gluing Lemma 2.1).
- **archivist_martinsson_steiner_2025.md** — full extract of arXiv:2310.12891.
- **archivist_computational_baseline.md** — prior-search baseline (NONE exists); validates hunter's counts (n=7→7 matches MathOverflow); Brown=17 vtx scale anchor.

## CACHED PAPER TEXT (pdftotext, on disk — DO NOT re-download)
- /tmp/skottova.txt — Skottová–Steiner 2025 (arXiv:2508.08703), THE freshest source. NOTE: /tmp may not survive restart; if gone, re-fetch via `curl -sL https://arxiv.org/pdf/2508.08703 | pdftotext`.
- /tmp/ms2310.txt — Martinsson–Steiner (arXiv:2310.12891).
- /tmp/jensen_siggers.txt — Jensen–Siggers 2012 (http://semr.math.nsc.ru/v9/p156-160.pdf, open access).

## (2) IN FLIGHT — nothing. Command fully complete. All squad asks answered (forge, count, hunter, gallai, team-lead messaged).

## (3) NEXT STEPS for a successor archivist (only if asked)
- If a witness/refutation is claimed by forge/hunter/count, cross-check it against W1–W7 and the necessary conditions (Prop 5.1) before anyone celebrates.
- Untapped: Jensen 2002 [Je02] and Lattanzio 2002 [La02] original PDFs are PAYWALLED (Discrete Math). I reconstructed mechanisms from the two Steiner papers + J–S. If a successor gets library access, the verbatim Lattanzio primality step is the one thing still second-hand.
- Jensen–Toft "Graph Coloring Problems" (Wiley 1995) Problem 5.14 = canonical textbook statement; not retrieved (book).

## (4) TRAPS (read before trusting anything)
- **VOCAB TRAP (gallai's, load-bearing):** IsCritical = VERTEX-critical. Kostochka–Yancey density + Gallai low-vertex theorems are EDGE-critical theorems for a DIFFERENT object — do NOT apply them directly to the target. Track transfer carefully.
- **ABSTRACTS ≠ PROOFS:** Grok's mechanism summaries (Lattanzio tensor-product story, etc.) are paraphrased/inferential, flagged "second-hand" in the files. The three Steiner/J–S extracts are from FULL pdftotext and are trustworthy. Don't promote a Grok paraphrase to a cited fact.
- **ncard-infinite trap (skeptic's):** Set.ncard of infinite = 0, so the Lean stmt only admits a finite-edge witness — necessary AND sufficient to treat as finite combinatorial question. Don't waste effort on infinite V.
- **Circulant is a DEAD END (W2):** known symmetric witnesses (Jensen) are circulants, but circulants provably give χ=3 at k=4. A k=4 witness is more likely ASYMMETRIC (Brown-style, 17 vtx) or a J–S gadget. Don't over-invest in circulant search.
