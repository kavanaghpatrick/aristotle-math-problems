# Web Research: teorth/erdosproblems AI-contributions Wiki

**Source**: https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems
**Wiki last edited**: natsothanaphan, May 29, 2026
**Research date**: 2026-05-30
**Agent**: W2

---

## Wiki structure

The wiki separates contributions into two top-level categories:

- **Section 1 — Primary contributions** (novel mathematics)
  - 1(a) AI standalone
  - 1(b) AI alongside literature (independently re-derived)
  - 1(c) AI building on literature
  - 1(d) AI + human collaboration
- **Section 2 — Secondary contributions**
  - 2(a) Literature search
  - 2(b) **Formalization** (column heading: "Proof to formalize")
  - 2(c) Rewriting

Aristotle appears across all of these. The shape of its role differs per section.

---

## Aristotle entry inventory

### 1(a) — Aristotle "standalone" (novel solving claim)

| Erdős# | Date | Co-AIs | Outcome | Notes |
|---|---|---|---|---|
| 11 | 24 Jan 2026 | GPT | INCORRECT | FALSE_CLAIM |
| 124 | 29 Nov 2025 | — | 🟡 Partial (Lean) | Aristotle solo |
| 205 | 10 Jan 2026 | GPT-5.2 Thinking | 🟢 Full (Lean) | Joint with GPT-5.2 |
| 263 | 9 May 2026 | Claude Opus 4.7, GPT-5.5 Pro | 🟡 Partial second part | Multi-AI |
| 457 | 2 Mar 2026 | GPT-5.2 Pro | 🟢 Full (Lean) | Joint with GPT-5.2 |

Aristotle is the **only AI named** on just two 1(a) entries: #124 (partial) and the #11 failed attempt. The full-solution standalone entries (#205, #457) all co-cite GPT-5.2 Pro/Thinking as collaborator.

### 1(b) — Aristotle alongside literature (re-derived independently)

| Erdős# | Date | Co-AIs | Lit. comparison | Outcome |
|---|---|---|---|---|
| 397 | 10 Jan 2026 | GPT-5.2 Pro | China TST 2012 | Full (Lean) |
| 635 | 30 Jan 2026 | GPT-5.2 Pro | Elliott (1979) | Partial (Lean) |
| 728 | 6 Jan 2026 | GPT-5.2 Pro | Pomerance (2014) | Full (Lean) |
| 897 | 26 Dec 2025 | Archivara | Wirsing (1981); "Similar? Yes" | Full (Lean) |
| 1026 | 7 Dec 2025 | — | Tidor, Wang, Yang (2016); "Similar only after Seidenberg (1959)" | Full (Lean) |
| 1077 | 24 Dec 2025 | — | Jiang, Longbrake (2025); "Similar? No" | Counterexample to earlier formulation |

Aristotle solo full-solution in 1(b): **#1026, #1077** (and #1077 is a counterexample to a formulation, not a solving of the problem). Everything else here has a GPT-5.2 Pro or Archivara co-author.

### 1(c) — Aristotle building on existing literature (new proof of known result)

| Erdős# | Date | Co-AIs | Literature | Verdict |
|---|---|---|---|---|
| 43 | 4 Dec 2025 | — | Barreto (2025) | New proof of partial (Lean) |
| 264 | 18 Dec 2025 | — | Kovač–Tao (2024) | New proof of partial |
| 488 | 27 Nov 2025 | — | Cambie (2025) | New variant solution |
| 493 | 2025 | GPT, Seed Prover | Seamans (2025) | "New or existing" |
| 679 | 12 Jan 2026 | — | DottedCalculator (2025) | Improved proof, less PNT dependence |
| 729 | 8-10 Jan 2026 | GPT-5.2 Pro | #728 result | Full (Lean) |
| 958 | 27 Dec 2025 | — | Clemen, Dumitrescu, Liu (2025) | New proof |
| 966 | 25 Feb 2026 | — | Spencer (unpublished) | Full (Lean) |
| 1007 | 19 Jan 2026 | — | House (2013), Chaffee–Noble (2016) | New proof |
| 1043 | 28 Dec 2025 | — | Pommerenke (1961) | New proof |
| 1047 | 21 Jan 2026 | — | Goodman (1966) | New proof |
| 1048 | 28 Jan 2026 | — | Pommerenke (1961) | "Specific case of Pommerenke" |
| 1090 | 27 Feb 2026 | Gemini 3 Flash | Graham–Selfridge (~1975) | Proof found |
| 1095 | 30 Dec 2025 | — | Ecklund, Erdős, Selfridge (1975) | New proof, slightly weaker |

**Critical: every 1(c) entry has known literature.** The "new proof" label means *new proof of a known result*, not novel mathematics. #1048 is explicitly "a specific case of Pommerenke."

### 1(d) — Aristotle in AI+human collaborations

| Erdős# | Date | Humans | AIs | Outcome |
|---|---|---|---|---|
| 347 | 25 Oct 2025 – 4 Feb 2026 | Barschkis, van Doorn, jbbaehr22, Naskrecki, Tao | Aristotle, Claude Opus, Codex, GPT | Full (Lean) |
| 367 | 20-22 Nov 2025 | Alexeev, van Doorn, Tao | Aristotle, Gemini Deep Think | Partial |
| 401 | 10-11 Jan 2026 | Alexeev, Barreto, Price, Sothanaphan | Aristotle, GPT-5.2 Pro | Counterexample + Lean |
| 1026 | 8 Dec 2025 | Alexeev, Cambie, Tao, Wu | AlphaEvolve, Aristotle, Gemini, GPT | Full (Lean) |

These are human-led teams using Aristotle (and other tools) as instruments. Wiki does not attribute proof ideas to Aristotle here.

### 2(b) — Formalization (column heading: "Proof to formalize")

The dominant Aristotle use case. ~170 Aristotle entries — porting existing published proofs into Lean. Examples (representative):

| Erdős# | Date | Proof being formalized |
|---|---|---|
| 16 | 25 Feb 2026 | Chen (2023) |
| 24 | 23 Apr-26 May 2026 | Grzesik (2012) |
| 26 | 28 Dec 2025 | Ruzsa |
| 31 | 24 Nov 2025 | Lorentz (1954), van Doorn (2025) |
| 34 | 5 Feb 2026 | Konieczny (2015) |
| 38 | 1 May 2026 | GPT-5.5 Pro (2026) |
| 56 | 25 Nov 2025 – 27 May 2026 | Ahlswede–Khachatrian (1995) |
| 71 | 24 May 2026 | Bollobás (1977) |
| 93 | 17 Feb 2026 | Altman (1963) |
| 134 | 7 Feb 2026 | Alon |
| 154 | 6 Feb 2026 | Lindström (1998) |
| 178 | 21 Apr 2026 | Beck (1981) |
| 192 | 9-10 May 2026 | Keränen (1992) |
| 198 | 24 Nov 2025 | Baumgartner (1975) |
| 199 | 24 Feb 2026 | Baumgartner (1975) |
| 204 | 15 Mar 2026 | Adenwalla (2025) |
| 206 | 28 Apr 2026 | Kovač (2024) |
| 214 | 2 Mar 2026 | Juhász (1979) |

Section heading explicitly: "Formalization", with column "Proof to formalize". Aristotle ports human-authored proofs to Lean.

### 2(c) — Rewriting

Aristotle is cited on rewrites of arguments for #281, #392, #457, #543, #728, #783, #846, #1196 (all 2(c) is stylistic FORMALIZATION/rewriting). Co-credit with GPT-5.2 Pro/Thinking.

---

## Totals

| Category | Aristotle entries |
|---|---|
| 1(a) standalone full-solution **solo** (Aristotle only AI) | **0** |
| 1(a) standalone full-solution with co-AI (GPT-5.2 Pro/etc.) | 2 (#205, #457) |
| 1(a) partial result solo | 1 (#124) |
| 1(a) partial result multi-AI | 1 (#263) |
| 1(a) FALSE_CLAIM (Aristotle+GPT) | 1 (#11) |
| 1(b) re-derived match-with-literature, solo | 2 (#1026, #1077) |
| 1(b) re-derived, with co-AI | 4 (#397, #635, #728, #897) |
| 1(c) new proof of known result, solo | 11 |
| 1(c) new proof of known result, with co-AI | 3 (#493, #729, #1090) |
| 1(d) AI+human team, Aristotle as instrument | 4 |
| 2(b) FORMALIZATION (porting human proofs to Lean) | **~170** |
| 2(c) Rewriting | 8 |

**Aristotle is the only AI named on a successful primary contribution exactly twice: #124 (partial) and the disputed #1077 (counterexample to a formulation, not the open conjecture itself).** Every other "Aristotle full solution" co-cites GPT-5.2 Pro, Claude Opus, Gemini, GPT, Archivara, or Seed Prover.

---

## Question: Originator vs Formalizer?

The wiki provides table entries only — it does **not** describe per-entry "who proposed the proof idea". However, the structural evidence is decisive:

1. **Section 2(b) explicitly labels Aristotle's role as formalization** with a column literally titled "Proof to formalize." This is the majority of Aristotle's wiki footprint.
2. **Section 1(c) entries are all framed as "new proof of [literature-known result]"** — Aristotle re-derives, it does not originate the conjecture-resolving idea (Pommerenke, Goodman, Spencer, etc. did).
3. **Section 1(a) entries where Aristotle is the only AI** number just one (partial: #124) and one disputed counterexample (#1077). No standalone full novel solving by Aristotle alone.
4. **Co-citation patterns**: when Aristotle is cited with GPT-5.2 Pro/Claude/Gemini on full solutions, the wiki does not credit one over the other, but the timing (GPT-5.2 Pro alone solves many problems standalone in 1(a); Aristotle does not) suggests the LLM partner is the prover and Aristotle is the Lean back-end.
5. **No language of origination**: the wiki never uses words like "originated", "discovered", "first proof", "novel". Standard phrases are "New proof found (Lean)" or "Proof found (Lean)" — both consistent with re-proof in a formal system.

### Entries where Aristotle is plausibly an ORIGINATOR (Aristotle-only AI, no prior literature mentioned)

Strict reading — the wiki's 1(a) "AI standalone" section, Aristotle solo:

- **#124** (29 Nov 2025): Partial result, no co-AI, no literature reference. **Most plausible Aristotle-originated mathematics**, though only partial.
- **#1077** (24 Dec 2025): Counterexample to an earlier formulation — Aristotle's contribution is to disprove a formulation, not to resolve the open question. Subsequent Jiang-Longbrake (2025) work is "Similar? No", suggesting Aristotle's path was independent.

No other Aristotle-only entry in 1(a) full-solves a problem without an LLM co-author or prior literature.

---

## Citations

All wiki entries link only to `erdosproblems.com/[number]` pages. **No arxiv or paper citations appear directly on the wiki for AI contributions.** The wiki itself states: "This wiki is only a superficial reference and is not definitive verdict or assessment."

---

## Verdict

**Per the wiki evidence, Aristotle is overwhelmingly a FORMALIZER, not a discoverer.**

- ~170 formalization entries vs ~30 primary-contribution entries.
- Of those ~30 primary contributions, the strict "Aristotle alone, novel mathematics, no prior literature" count is **1 partial (#124)** and **1 disputed counterexample (#1077)**.
- All other "Aristotle full solutions" are either (a) co-authored with another LLM that did the mathematical proposing (GPT-5.2 Pro pattern), (b) re-derivations of literature-known results (Pommerenke, Goodman, Spencer, etc.), or (c) human-led teams using Aristotle as a Lean assistant.

Aristotle's value, per wiki framing, is the Lean back-end: taking proofs proposed by GPT-5.2 Pro, Claude, Gemini, or humans and producing machine-checked formalizations. The "novel discoverer" role on Erdős problems sits with **GPT-5.2 Pro** (most independent solves in 1(a)), **AlphaProof** (#477, #949), **Aletheia** (#1051), and **Claude Mythos** (#90).
