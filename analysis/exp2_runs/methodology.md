# EXP2: Adversarial Counter-Conjecture Prompting — Methodology Spec

**Hypothesis.** Inversion-style prompting ("First argue the conjecture is FALSE; find the weakest spot; defend a counterexample; then refute your own counterexample; finally synthesize") surfaces structural insights that direct-prove prompting misses. The mechanism: forcing the model into adversarial mode obligates it to engage with the structural barriers that a direct-prove prompt allows it to elide via fluent restatement.

**Problem under test.** Erdős 938 — "Are there only finitely many 3-term arithmetic progressions of *consecutive* powerful numbers?" Open conjecture (likely TRUE per Erdős, but van Doorn 2026 arXiv:2605.06697 Conj 5 asserts FALSE via Pell family). Picked because (a) we have ~20 prior MEGA/W-team dossiers to compare against, (b) recent literature (van Doorn 2026) gives an inversion lane (the conjecture *might* be false), so adversarial prompting is not vacuous, (c) all prior direct-prove dossiers cluster around the same 4-5 angles (Frey curves, Pell parametrization, abc-conditional, Selberg sieve, ternary Mordell-Siegel).

**Models tested.**
1. **Grok-4** (`grok-4-0709`) via xAI API direct (live web search enabled).
2. **Codex CLI** `codex exec` (default model `gpt-5.5-codex-mini` / `gpt-5-codex`) in read-only sandbox mode.
3. ~~Gemini-2.5-pro~~ — SKIPPED. Quota exhausted in prior deep-iteration run (per `analysis/e938_deep_synthesis.md`); switching to 2-model run as authorized fallback.

**Three-round protocol.**

| Round | Frame | Prompt | Word target |
|---|---|---|---|
| **A — falsify** | "The conjecture is FALSE" | "Construct an explicit counterexample family for E938. Defend it. Find the weakest structural point of the conjecture. 1000 words." | 1000 |
| **B — refute self** | "Your falsification is wrong" | "Now find the structural reason your counterexample doesn't actually falsify the conjecture. What invariant blocks it?" | 800 |
| **C — synthesize** | "What does the failed attack reveal?" | "Synthesize: what does the failed counterexample reveal about the conjecture's *structure*? Name a load-bearing invariant the conjecture asserts implicitly." | 600 |

**Comparison set.** Prior direct-prove dossiers analyzed in side-by-side:
- `submissions/sketches/yolo_mega7_e938_pell_classification.fusion.json` (MEGA-7, R1-R8 Grok+Codex)
- `submissions/sketches/yolo_w2_e938_lll.ID.txt` (LLL angle)
- `submissions/sketches/yolo_e938_deep_heath_brown.fusion.json` (ternary Mordell-Siegel)
- `submissions/sketches/yolo_e938_deep_stark.ID.txt` (Stark-Heegner CM)
- `analysis/e938_deep_synthesis.md` (DEEP-6 meta-synthesis)
- `analysis/research_fusion_erdos938.md` (F5 fusion: Frey+Ribet)

**Verdict criteria.** A "novel mathematical insight" counts only if BOTH:
1. It is *not present* in any of the 6 prior dossiers above (verified by literal-text search).
2. It is *mathematically substantive* — i.e., names a specific invariant, lemma, computational artifact, or structural reason; not a meta-statement about difficulty/sociology.

**Falsification of EXP2.** If Round-C synthesis from both models contains only material already present in MEGA-7 / DEEP-6 / F5, EXP2 reports NEGATIVE (counter-conjecture prompting adds no new content). If it produces a structural invariant absent from prior dossiers, EXP2 reports POSITIVE.

**Implementation.** Grok via `curl https://api.x.ai/v1/chat/completions` (model `grok-4-0709`, no system prompt, three sequential user messages, full context accumulated). Codex via `codex exec --skip-git-repo-check -s read-only -m gpt-5.5-codex` (one invocation per round with full prior transcript). Outputs saved verbatim to `analysis/exp2_runs/{grok,codex}_round_{A,B,C}.md`.

**Run date.** 2026-05-31.
