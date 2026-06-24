# LLM Math Landscape — Late 2025 / Mid 2026

*Survey for the math-process-improvement effort. Goal: identify systems that outperform Aristotle on OPEN research problems (not textbook math).*

---

## Headline findings

1. **Only two systems have publicly resolved OPEN Erdős problems autonomously**: Harmonic Aristotle (≈3 problems, late 2025–early 2026) and DeepMind's **AlphaProof Nexus** (9/353 Erdős + 44/492 OEIS conjectures, May 2026). Both fuse an LLM with Lean. ([AlphaProof Nexus arxiv 2605.22763](https://arxiv.org/abs/2605.22763), [Tao on #728](https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/), [Aristotle #124](https://www.erdosproblems.com/forum/thread/124))
2. **AlphaProof Nexus uses essentially a Ralph loop** — Gemini 3.1 Pro inside parallel subagents that edit a Lean sketch via search-and-replace and consume Lean error output as feedback. Cost: a few hundred USD per problem. Our pipeline is architecturally similar but uses Aristotle as both the LLM brain and the verifier. ([cryptobriefing](https://cryptobriefing.com/deepmind-alphaproof-nexus-erdos-problems/), [arxiv 2605.22763](https://arxiv.org/abs/2605.22763))
3. **ByteDance Seed-Prover 1.5** (Dec 2025) is the strongest OPEN-SOURCE Lean prover: 88% Putnam, 80% Fate-H, 33% Fate-X, gold at IMO 2025. Agentic with Mathlib search + Python + lemma decomposition. ([seed.bytedance.com](https://seed.bytedance.com/en/blog/seed-prover-1-5-advanced-mathematical-reasoning-through-a-novel-agentic-architecture), [arxiv 2512.17260](https://arxiv.org/html/2512.17260v1))
4. **GPT-5.2 Pro + Aristotle** solved Erdős #728 (Jan 2026) — informal proof from GPT-5.2 Pro, Aristotle formalized. This is essentially **the workflow our codex_proof_loop is set up for, but with GPT instead of Codex**. ([officechai](https://officechai.com/ai/gpt-5-2-and-harmonic-appear-to-have-autonomously-solved-an-erdos-problem-that-had-been-unsolved-by-humans-thus-far/), [Tao's writeup](https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/))

---

## Benchmark ranking (cited)

| System | MiniF2F | PutnamBench | FrontierMath T1-3 | FrontierMath T4 | Notes |
|---|---|---|---|---|---|
| GPT-5.5 Pro | – | – | **52.4%** | **39.6%** | Best on FrontierMath; not native Lean. ([LM Council](https://lmcouncil.ai/benchmarks), [ofox.ai](https://ofox.ai/blog/gpt-5-5-api-vs-claude-opus-gemini-3-1-flagship-2026/)) |
| Claude Opus 4.7 Thinking | – | – | – | 22.9% | Strong general reasoning; ([Vellum](https://www.vellum.ai/blog/claude-opus-4-7-benchmarks-explained)) |
| Claude Opus 4.5 (Thinking) | – | – | – | – | **33.5% on FormalProofBench** (grad-level Lean) — best on that bench. ([arxiv 2603.26996](https://arxiv.org/pdf/2603.26996)) |
| Claude Opus 4.6 + Rocq-MCP | 81% miniF2F-Rocq | – | – | – | 244 theorems; 14 used Admitted (hallucinated). ([arxiv 2603.20405](https://arxiv.org/pdf/2603.20405)) |
| Seed-Prover 1.5 | – | **88%** | – | – | Gold at IMO 2025; agentic; open-source-friendly. ([seed.bytedance.com](https://seed.bytedance.com/en/blog/seed-prover-1-5-advanced-mathematical-reasoning-through-a-novel-agentic-architecture)) |
| OProver-32B | 93.3% | 11.3% | – | – | 5 benchmarks SOTA on MiniF2F. ([arxiv 2605.17283](https://arxiv.org/abs/2605.17283)) |
| Goedel-Prover-V2-32B | 90.4% (self-correct) | 86 problems pass@184 | – | – | Open-source, Princeton; 80x smaller than DeepSeek-Prover-V2-671B. ([blog.goedel-prover.com](https://blog.goedel-prover.com/), [Princeton AI](https://ai.princeton.edu/news/2025/princeton-researchers-unveil-improved-mathematical-theorem-prover-powered-ai)) |
| DeepSeek-Prover-V2-671B | 82.4% | 47 problems pass@1024 | – | – | Powered by DeepSeek-V3; open. ([arxiv 2504.21801](https://arxiv.org/pdf/2504.21801)) |
| Kimina-Prover-72B | 92.2% (TTRL) | – | – | – | Moonshot+Numina; open weights. ([huggingface](https://huggingface.co/AI-MO/Kimina-Prover-72B)) |
| Gemini 3.1 Pro | – | Putnam 2025: 91/120 (solved A5 uniquely) | – | – | Best informal reasoner; powers AlphaProof Nexus. ([matharena.ai/putnam](https://matharena.ai/putnam/)) |
| DeepSeek-v3.2-Speciale (Agent) | – | **Putnam 2025: 103/120** | – | – | Top agentic informal system. ([matharena.ai/putnam](https://matharena.ai/putnam/)) |
| Grok 4.3 | – | – | – | – | ~90% GPQA Diamond; no published Lean scores. ([artificialanalysis.ai](https://artificialanalysis.ai/models/grok-4-3)) |
| Logical Intelligence Aleph | – | **76% Putnam** (energy-based, not LLM) | – | – | Different paradigm; closed. ([businesswire](https://www.businesswire.com/news/home/20251202089385/)) |

---

## OPEN-problem track record (what actually matters)

| System | Open problems autonomously resolved |
|---|---|
| AlphaProof Nexus (Gemini 3.1 Pro + Lean, Ralph loop) | 9 Erdős + 44 OEIS conjectures, May 2026, few-hundred-USD each ([arxiv 2605.22763](https://arxiv.org/abs/2605.22763)) |
| Aristotle (Harmonic) | Erdős #124 (Nov 2025), #1026 (Dec 2025), #728 (Jan 2026, with GPT-5.2 Pro input) ([Erdős #124 thread](https://www.erdosproblems.com/forum/thread/124), [Tao on #126/#728](https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/)) |
| Gemini Deep Think "Aletheia" | 212/700 candidate answers, then human-filtered. Semi-autonomous. ([arxiv 2601.22401](https://arxiv.org/html/2601.22401v3)) |
| Math Inc. Gauss | Formalized strong PNT (3 weeks) and 24-D sphere-packing proof; **autoformalization, not autonomous discovery**. ([math.inc/gauss](https://www.math.inc/gauss)) |
| Seed-Prover 1.5 | Strong on IMO/Putnam but **no public OPEN-problem resolutions yet**. ([arxiv 2512.17260](https://arxiv.org/html/2512.17260v1)) |

**Our position:** 1,157 submissions, 0 confirmed open-gap resolutions. Aristotle's public open-problem wins all came from Harmonic's own team using their internal stack — not via the public API in the way we're using it.

---

## Best fit for our pipeline

**Immediate (highest leverage):**

1. **Add a Gemini 3.1 Pro / GPT-5.2 Pro informal-reasoner stage** before the Aristotle submission. The pattern that resolved Erdős #728 was: GPT-5.2 Pro produces an informal proof sketch → Aristotle formalizes. Our `/sketch` step submits the bare gap directly to Aristotle, asking it to do both jobs. Splitting the cognitive load (informal reasoner generates a candidate strategy → Aristotle formalizes/verifies) matches every confirmed open-gap win in the public record. We already have grok/gemini/codex skills — add a `gemini-prove-informal` stage that produces a multi-paragraph informal argument, then ship to Aristotle as auto-context. This is essentially what `codex_proof_loop.py` does, but Codex is weaker than GPT-5.2 Pro / Gemini 3.1 Pro on FrontierMath. ([officechai](https://officechai.com/ai/gpt-5-2-and-harmonic-appear-to-have-autonomously-solved-an-erdos-problem-that-had-been-unsolved-by-humans-thus-far/))
2. **Mirror the AlphaProof Nexus Ralph-loop structure** — parallel subagents, each editing a Lean sketch via search-and-replace using Lean compiler errors as feedback. The arxiv 2605.22763 paper describes the architecture explicitly. We already have ralph-parallel; the missing piece is the search-and-replace edit primitive against an evolving Lean sketch. ([arxiv 2605.22763](https://arxiv.org/abs/2605.22763))
3. **Restrict targets to the [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) Erdős set** (353 problems already formalized). AlphaProof Nexus pulled from this exact corpus. We avoid both ambiguity and formalization overhead. Our gap-targeting gate should prefer problems with an existing FormalConjectures Lean statement.

**Medium term:**

4. **Self-host Seed-Prover 1.5 or Goedel-Prover-V2-32B** as a second formalizer alongside Aristotle. Both are open weights, Goedel-Prover-V2-32B is small enough to run on a single 80GB GPU and beats DeepSeek-Prover-V2-671B by 80x compute reduction. Use as a cheap pre-filter or parallel attempt. ([github.com/Goedel-LM/Goedel-Prover-V2](https://github.com/Goedel-LM/Goedel-Prover-V2), [seed-prover-1-5](https://seed.bytedance.com/en/blog/seed-prover-1-5-advanced-mathematical-reasoning-through-a-novel-agentic-architecture))
5. **Switch the debate/sketch generator to Claude Opus 4.5 Thinking** for graduate-level formal work — it leads FormalProofBench (33.5%) and is what's already running in our /debate skill. Pair with GPT-5.5 Pro for FrontierMath-style abstract steps. ([arxiv 2603.26996](https://arxiv.org/pdf/2603.26996))

**Skip:** Grok 4.3 (no published Lean scores), pure energy-based systems like Aleph (closed, different paradigm), Math Inc. Gauss (autoformalization of known proofs, not autonomous discovery).

---

## Bottom line

Aristotle alone is competitive with AlphaProof Nexus on architecture, but Nexus's published 9/353 hit rate vastly outpaces our 0/1,157. The difference is almost entirely **informal-reasoning quality**: Nexus drives Lean with Gemini 3.1 Pro; we drive it with Aristotle's internal LLM. Adding GPT-5.2 Pro or Gemini 3.1 Pro as the informal sketch generator before Aristotle submission is the single highest-leverage change and is supported by every confirmed public open-gap resolution in 2026.
