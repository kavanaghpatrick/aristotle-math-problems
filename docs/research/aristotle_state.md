# Aristotle State of the Art — May 2026

Research compiled 2026-05-28 for math-process-improvement Task #1. Every load-bearing claim cites a URL.

## 1. Latest features

**Aristotle Agent (launched 2026-03-17)** — Harmonic's "autonomous mathematician" announced by Vlad Tenev. Operates up to 24 hours unattended; ingests plain-English problems, converts to Lean 4, edits files inside a Lean project, and produces what Harmonic calls "repo-quality" code. Shipped with web UI, CLI, and API ([Benzinga](https://www.benzinga.com/markets/tech/26/03/51317862/robinhood-ceo-vlad-tenev-touts-autonomous-mathematician-as-harmonic-unveils-aristotle-agent), [Sahm Capital](https://www.sahmcapital.com/news/content/robinhood-ceo-vlad-tenev-touts-autonomous-mathematician-as-harmonic-unveils-aristotle-agent-2026-03-18)).

The Python SDK (`aristotlelib` on PyPI, currently 0.7 → 2.0) exposes two main entry points: `aristotle submit "Fill in all sorries" --project-dir ./my-lean-project --wait` and `aristotle formalize paper.tex` ([PyPI aristotlelib](https://pypi.org/project/aristotlelib/)). Notable add-ons in the 2026 upgrade: plain-English input alongside Lean 4, automated lemma generation, and a streamlined terminal interface.

**Architecture — NO "5-agent team."** The arXiv paper [2510.01346](https://arxiv.org/html/2510.01346v1) is explicit: Aristotle has **three** components — (i) a parallel Monte Carlo Graph Search over Lean states, (ii) an informal-reasoning system that drafts a natural-language proof, decomposes it into lemmas, autoformalizes each lemma, and iterates, and (iii) a dedicated geometry solver (Yuclid). The MCGS uses a 200B+ parameter transformer as both policy and value function, with test-time training on inference traces ([EmergentMind summary](https://www.emergentmind.com/topics/aristotle-imo-level-automated-theorem-proving)). The "5 agents" claim in our docs appears unsupported in any public source.

## 2. Benchmarks

**ProofBench (Vals AI)** — Aristotle ranks #1 on formal math; ~15-point gap over GPT-5.4 (the runner-up). Models get a NL theorem statement plus a vetted Lean 4 formalization, up to 40 interaction turns, no informal proof. Aristotle runs through its own internal harness rather than the shared one ([Vals ProofBench](https://www.vals.ai/benchmarks/proof_bench)). Per-domain breakdown is not exposed in the public leaderboard text I could retrieve.

**VERINA** — 96.8% success: 183/189 specs resolved (160 proven correct, 23 proven false) ([Harmonic Verina post](https://harmonic.fun/news/verina-benchmark/)).

**IMO 2025** — solved 5/6 with fully verified Lean. The miss was **Problem 6 (combinatorics)** — the 2025×2025 tile-placement problem ([nor's blog](https://nor-blog.pages.dev/posts/2025-07-19-imo-2025/)). Every other AI gold-medal system (Gemini Deep Think, OpenAI's reasoning model, ByteDance Seed-Prover) also missed P6. As of 2026-05, no AI has published a verified formal P6 solution — it is still the open marker for combinatorial-search SOTA.

## 3. Workflow comparison vs ours

Aristotle's intended workflow ([arxiv 2510.01346 §3](https://arxiv.org/html/2510.01346v1)):

1. Researcher prompts informal model (often GPT-5.2 Pro) with the problem.
2. Informal model drafts NL proof and a lemma list.
3. Lemmas autoformalized in Lean; Lean REPL errors fed back to revise.
4. Aristotle's MCGS attempts each lemma, then the target, **initialized with a Lean code block that may contain proven background results.**
5. Iterate on failures.

The Erdős #728 resolution followed exactly this — GPT-5.2 Pro produced the strategy, Aristotle formalized it ([Erdős #728 writeup](https://arxiv.org/pdf/2601.07421v1), [aiHola summary](https://aihola.com/article/gpt-5-2-erdos-problem-728-ai-math)).

**Our workflow** (CLAUDE.md): bare conjecture, ≤30 lines, INFORMAL .txt, **no proof strategy, no lemmas, no guidance.** We rely entirely on Aristotle's internal informal-reasoning module to invent the strategy from scratch.

This is provably **the harder mode of operation** by Aristotle's own design: the paper explicitly says external Lean code blocks containing "already proven background results or lemmas tailored to the target theorem … boost the model's performance using higher-level informal reasoning." Our gate forbids exactly this.

## 4. Open-problem track record

- **Erdős #124** (Nov 2025) — Aristotle alone, working from formal statement. Asterisk: Erdős omitted a hypothesis, so the version Aristotle solved is weaker than intended. Solution was "Olympiad-level" simple ([Mindplex](https://magazine.mindplex.ai/post/harmonics-ai-aristotle-claims-solution-to-historic-math-puzzle)).
- **Erdős #728** (Jan 2026) — first **fully autonomous** AI resolution of an open Erdős problem with no prior literature. Hybrid: GPT-5.2 Pro strategy + Aristotle formalization ([writeup](https://arxiv.org/pdf/2601.07421v1)).
- **Erdős #729 and #401** — fell within a week via adaptations of the #728 argument ([Medium recap](https://medium.com/@cognidownunder/three-erd%C5%91s-problems-fell-in-seven-days-and-terence-tao-verified-every-proof-himself-1a1ff4399bc6)).
- **#645** — auto-formalized through Alexeev's pipeline (ChatGPT explains, Aristotle formalizes, Lean verifies, GitHub post) ([Xena Project](https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/)).

erdosproblems.com lists ~1,133 total problems, 279 proved, **22 formally verified in Lean** as of Jan 2026 ([erdosproblems forum](https://www.erdosproblems.com/forum/thread/blog:2)). Tao verifies submissions personally.

**Pattern:** every confirmed open-problem win paired a strong informal strategy (Erdős expert *or* a frontier LLM like GPT-5.2 Pro) with Aristotle as the Lean formalizer. None of the cracked Erdős problems came from a bare-statement-only workflow like ours.

## 5. Recommendation

Our 0/1,157 hit rate is consistent with the public evidence. **The "bare conjecture, zero guidance, ≤30 lines" doctrine fights Aristotle's design.** Both the paper and every cracked Erdős win argue for the opposite: supply an informal proof sketch and a candidate lemma list, even an imperfect one, and let Aristotle's MCGS chase the gaps.

Concrete proposals for Task #4:

1. **Drop the strategy-keyword gate** for problems where we have a Codex/GPT-5.2 draft. Submit *with* the informal sketch; track hit rate vs bare.
2. **Add a lemma-decomposition phase**: have Codex/Grok produce 3–5 candidate lemmas; submit those as a Lean code block alongside the target, mirroring Aristotle's documented input shape.
3. **Reserve "bare submission" for falsification probes only** (where the question genuinely is "is this gap real?").
4. **Triage by domain**: Aristotle is strongest on algebra/NT/geometry, weak on hard combinatorics (still hasn't cracked IMO P6). Down-weight combinatorics in `/sweep`.
5. **Correct CLAUDE.md & memory**: the "5-agent" framing has no public basis; Aristotle is a 3-component system (MCGS + informal-reasoning loop + geometry solver).

Cited sources: 14 distinct URLs across Harmonic news, Vals AI, arXiv, erdosproblems.com, EmergentMind, Xena Project, financial press, and PyPI.
