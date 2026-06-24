# Web Research: The Aristotle Theorem-Proving System

**Date**: 2026-05-30
**Agent**: W1 (web-search)
**Subject**: Identification and capability assessment of "Aristotle" as accessed via `aristotlelib` Python SDK at `https://aristotle.harmonic.fun`.

---

## 1. Who built Aristotle?

**Aristotle is built by Harmonic AI** (Harmonic Inc.), NOT by Anthropic, not by Bates, not by UC Berkeley.

- **Company**: Harmonic AI (a math-AI startup co-founded by **Vlad Tenev**, who is also CEO of Robinhood).
- **Funding context**: Harmonic raised ~$120M; the company brands Aristotle as a path to "mathematical superintelligence."
- **SDK metadata confirmation** (from local wheel file `/Users/patrickkavanagh/math/aristotlelib-0.7.0-py3-none-any.whl`, file `METADATA`):
  - `Name: aristotlelib`
  - `Author: Harmonic`
  - `Project-URL: Homepage, https://aristotle.harmonic.fun`
  - Description: "Aristotle SDK - Python library for automated theorem proving with Lean … capable of proving and formally verifying graduate and research level problems in math, software, and more."
  - Tagline in README inside wheel: **"The Era of Vibe Proving is Here"**
- **The team paper** (arXiv:2510.01346, Oct 2025): authored by "The Harmonic Team" — 23 named authors including **Tudor Achim**, **Alex Best** (Mathlib contributor), **Sergei Gukov** (Caltech mathematical physicist), **Daniel Halpern-Leistner**, **Yury Kudryashov** (Mathlib maintainer), **Vlad Tenev**, **Harold Williams**, and others. The roster is a mix of ex-research-mathematicians and ML engineers.
- **Lean Together 2026 talk**: "Aristotle, an AI theorem prover using Lean" — presented by Alex Best at Cambridge.

Sources:
- arXiv paper: https://arxiv.org/abs/2510.01346 ; https://arxiv.org/html/2510.01346v1
- Harmonic PDF: https://harmonic.fun/pdf/Aristotle_IMO_Level_Automated_Theorem_Proving.pdf
- Cambridge seminar listing: https://www.cst.cam.ac.uk/seminars/list/243277
- Wheel METADATA in `aristotlelib-0.7.0.dist-info/METADATA`
- HuggingFace paper page: https://huggingface.co/papers/2510.01346

---

## 2. Stated capabilities: formalize vs solve

Aristotle claims BOTH formalization and end-to-end proof discovery. The architecture has three subsystems:

1. **Lean proof-search engine** — Monte Carlo Graph Search (MCGS) with a large transformer (paper claims "200B+ parameter" backbone) acting as policy and value network.
2. **Informal reasoning model** — drafts proofs / lemma decompositions in natural language, then formalizes them as Lean sketches with sorries.
3. **Geometry solver** — AlphaGeometry-style system for plane geometry (used for IMO 2025 problem 2).

The pitch (per Harmonic, paper §1, and SDK README): take an informal statement OR a Lean sketch with `sorry`, return a fully verified Lean 4 / Mathlib proof — no `sorry`, no unsound axioms (no `sorryAx`). The SDK CLI exposes both `aristotle submit` (Lean project with sketches) and `aristotle formalize` (informal text/PDF → Lean).

A correctness floor is enforced by the Lean kernel: "a problem is only considered solved if the system produces a complete proof using the Lean 4 proof language and its mathematical library Mathlib, without gaps or unsound axioms like sorryAx" (paper, §2).

---

## 3. Public benchmarks

| Benchmark | Aristotle's reported result | Source |
|---|---|---|
| **IMO 2025** | 5/6 problems with verified Lean proofs (gold-medal-equivalent) | arXiv 2510.01346; same level as Google DeepMind Deep Think and OpenAI reasoning model in 2025, but Aristotle's are fully formal in Lean — the others were natural-language solutions human-judged. |
| **ProofBench (Vals AI)** | **#1 overall at 71%**. GPT-5.4 next at 56%, Claude Opus 4.7 at 54%. ~15-point gap between Aristotle and best general LLM. | https://www.vals.ai/benchmarks/proof_bench |
| **Polya–Szegő formalization** | 100% verified on 80 submitted formalizations (informal→formal). | Igor Rivin write-up — https://igorrivin.github.io/research/polya-szego-aristotle/ |
| **miniF2F / ProofNet / PutnamBench** | Standard suite; specific Aristotle numbers not extracted from abstract (paper claims SOTA). HILBERT (separate system) recently hit 99.2% miniF2F and 70% PutnamBench, putting Aristotle in a tight pack of frontier provers. | arXiv 2510.01346 ; arXiv 2511.03108 |

---

## 4. Comparison to peer systems (2025-2026)

- **AlphaProof (DeepMind, 2024)** — also Lean-based, IMO 2024 silver. Aristotle one generation later, claims to surpass on IMO 2025.
- **DeepSeek-Prover (V1/V1.5/V2)** — open-weights Lean prover; strong on miniF2F/Putnam but no comparable IMO claim.
- **Seed-Prover (Bytedance)** — also achieved IMO 2025 gold (Chen et al., 2025b); explicitly listed alongside Aristotle as the two systems that hit gold at IMO 2025.
- **HILBERT** — recent frontier on miniF2F/PutnamBench (99.2% / 70%).
- **AlphaGeometry / AlphaGeometry 2** — geometry only; Aristotle has its own geometry solver "based on AlphaGeometry."
- **Lean-STaR / COPRA / ReProver / LeanDojo** — earlier-generation retrieval / step-prediction systems; not in same tier.
- **General-purpose LLMs (GPT-5.x, Claude Opus 4.x, Gemini)** — strong informal math (~95% on informal problems) but cratered at ~2.8% on producing verified Lean proofs — the "30x gap" Harmonic markets against.

---

## 5. THE CRITICAL QUESTION: Has Aristotle solved any OPEN problem (vs formalized known proofs)?

### Strongest piece of evidence FOR novel mathematical discovery

**Erdős Problem #124** (Nov 2025): Harmonic announced that Aristotle, running autonomously on its beta with a natural-language interface, solved Erdős Problem #124 ("Complete sequences of sets of integer powers," Burr–Erdős–Graham–Li, *Acta Arithmetica*, 1996) in ~6 hours and formalized it in Lean in ~1 minute. The problem had been open ~30 years. Boris Alexeev (Harmonic) executed the run; no human supplied the proof outline. **Terence Tao publicly accepted the result** and engaged on Mathstodon.

A follow-up paper, "Resolution of Erdős Problem #728: a writeup of Aristotle's Lean proof" (arXiv:2601.07421, Jan 2026), describes this as "the first Erdős problem (collected on the Erdős Problems website) regarded as fully resolved autonomously by an AI system." Erdős #729 and #401 fell to derivative arguments; Erdős #397 was solved by GPT-5.2 + Aristotle (formalize role). New Scientist (Jan 2026) covered the cluster.

Sources:
- arXiv:2601.07421 — https://arxiv.org/pdf/2601.07421
- Tao on Mathstodon: https://mathstodon.xyz/@tao/115639984077620023
- TechCrunch (Jan 14 2026): https://techcrunch.com/2026/01/14/ai-models-are-starting-to-crack-high-level-math-problems/
- Office Chai: https://officechai.com/ai/robinhood-ceo-vlad-tenevs-math-ai-startup-claims-to-have-solved-an-erdos-problem-that-was-open-for-30-years/
- The Rundown AI: https://www.therundown.ai/p/ai-cracks-30-year-math-problem
- Stacker News thread: https://stacker.news/items/1296227
- 36kr / Tao reporting: https://eu.36kr.com/en/p/3576638922980231

### Strongest piece of evidence AGAINST (i.e., that Aristotle has not done deep novel math)

**Terence Tao's "lowest hanging fruit" caveat.** Tao explicitly framed the recent batch of Aristotle/GPT-5.2 Erdős resolutions as resolutions of the easy tail of a long-tail distribution: "automated sweeps are now beginning to resolve the lowest hanging fruit in this set of problems." He noted that ~12 problems flipped from "open" to "resolved" in late 2025 *not* via novel discovery but via AI-assisted literature search turning up existing proofs.

Specific tells in the Erdős #124 case:
- There exist **two versions** of E124. The version Aristotle solved is acknowledged as the **easier** of the two.
- Community discussion on the Erdős Problems forum (#124 thread): "The final proof is quite simple and elementary — indeed, if one was given this problem in a maths competition (so therefore expected a short simple solution existed) something like this would be produced. … if something like this worked, then surely the combined talents of Burr, Erdős, Graham, and Li would have spotted it. Normally, this would make one suspicious …" The community concluded the proof is valid (Lean checked) but its existence in elementary form suggests the problem was open largely due to neglect, not depth.
- Tao's framing: "open-ended research requiring genuine insight" — current AI scores ~25%. The IMO-gold and ProofBench results live in domains with *known* solutions / well-defined competition statements.
- Aristotle's marquee non-Erdős successes (IMO, ProofBench, Polya–Szegő, Mathlib contributions) are all **formalize-known-math** or **solve-by-design-has-short-proof** — not "discover a new theorem of genuine research interest."

Sources:
- Mathstodon thread by Tao: https://mathstodon.xyz/@tao/115639984077620023
- The Neuron Daily commentary: https://www.theneurondaily.com/p/ai-cracks-legendary-erdos-problems
- 36kr: https://eu.36kr.com/en/p/3576638922980231

---

## 6. Bottom line for this project

Aristotle is real, externally validated (IMO 2025 gold via 5/6 in Lean; #1 on ProofBench; arXiv paper with 23 authors including known Mathlib maintainers; Tao engagement; Lean Together 2026 talk; published Erdős resolutions). It genuinely produces machine-verified Lean 4 + Mathlib proofs and has *autonomously* closed a small set of Erdős problems (#124, #728, #729, #401) — verifiable as Lean files, not just press claims.

But the case for Aristotle resolving *novel hard* open problems is **circumscribed**: the Erdős cluster is the long-tail-low-attention regime. There is currently NO public demonstration of Aristotle producing a deep, surprising proof on a problem of broad research interest. Tao himself, the loudest mathematician endorser, frames the wins as low-hanging fruit. This is consistent with our project's empirical 0.8% gap-resolution hit rate on harder Erdős problems.

The realistic use mode implied by the public evidence: **state a bare open gap that lives in the long tail**, hand Aristotle the prior-Aristotle context it likes, and accept that the hits will come from problems whose proofs are short-but-overlooked, not from breakthroughs on famous conjectures.

---

## Appendix: Local SDK shape

From `/tmp/aristotle_wheel` extraction of `aristotlelib-0.7.0`:

- `aristotlelib.Project.create_from_directory(prompt, project_dir)` — submit a Lean project (a `.tar.gz` of `lakefile.toml` + `lean-toolchain` + `Math/*.lean`) with a natural-language prompt.
- `aristotlelib.Project.create(prompt, tar_file_path=None)` — generic submission.
- CLI: `aristotle submit "<prompt>" --project-dir ./proj --wait --destination out.tar.gz` ; `aristotle formalize file.txt`.
- ProjectStatus FSM: QUEUED → IN_PROGRESS → {COMPLETE, COMPLETE_WITH_ERRORS, OUT_OF_BUDGET, FAILED, CANCELED}.
- License is included but not redistributable; the wheel itself is 22 KB — all heavy lifting is server-side at `aristotle.harmonic.fun`.
