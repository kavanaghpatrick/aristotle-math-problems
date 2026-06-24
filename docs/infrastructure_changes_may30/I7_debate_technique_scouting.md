# I7 — Cross-Domain Technique Scouting via `debate.py`

**Agent:** I7 (agent 7 of 10) | **Date:** 2026-05-30
**Status:** LANDED
**Motivation:** F3 found 87% of 107 LLM consultations were meta-process (which problem next, taxonomy design) rather than math content. The `scripts/debate.py` infrastructure is fully general — `--topic` is free-form, the strategy-debate format is just a convention. I7 repurposes it for cross-domain *math-content* scouting.

---

## TL;DR

Six prompt templates in `research_fusion/prompts/debate_templates/` turn the existing `scripts/debate.py` orchestrator into a cross-domain technique-scouting tool. A wrapper script `scripts/debate_fusion.py` auto-pulls Stage-1 literature dossiers and routes output to `research_fusion/runs/<problem>/debates/<template>.md`. A new `mk debate` subcommand makes the whole thing one-line. `debate.py` itself is untouched.

Smoke tested on Erdős 938 (powerful 3-APs) with `technique_scout.md` and 3 full rounds: all 3 AIs (Grok-4, Gemini, Codex/GPT-5.2) successfully produced cross-domain technique proposals including Frey-Hellegouarch + Ribet level-lowering, Bombieri-Lang/Vojta, Pila-Wilkie, l^p decoupling, Furstenberg correspondence, Schmidt subspace theorem, and Bombieri-Pila determinant method.

---

## The 6 templates

All live in `/Users/patrickkavanagh/math/research_fusion/prompts/debate_templates/`. Each is a self-contained `.md` file with usage instructions, when-to-use guidance, and a `## Sample prompt body` section containing the actual prompt body (extracted by the wrapper, with `{PROBLEM}` substituted at call time).

| Template | Purpose | When to use |
|----------|---------|-------------|
| `technique_scout.md` | 5 specific techniques from OTHER mathematical areas, each with technique name, seminal paper, structural analog, diagnosis of why bare-gap attempts failed, and Mathlib feasibility. Hard constraint: at least 3 of 5 must come from outside the problem's native domain. | Stage-2 escalation; 3+ failed bare-gap attempts; need to break out of iter1->iter2 default |
| `adjacent_analog.md` | 3-5 STRUCTURALLY ISOMORPHIC closed problems in adjacent domains, with the technique that closed each. Goal: technique transfer by analogy. | Need prior art before novel attack; want to falsify "this problem is totally new" |
| `tao_simulator.md` | Roleplay Tao's first 3 moves with citations to his actual blog posts and papers. At least 1 computation, 1 literature pull, 1 structural decomposition. | LLM outputs too generic; want working-mathematician heuristic prioritization |
| `bias_flush.md` | Adversarial critique of our 4 default techniques (bounded `native_decide`, σ-multiplicativity, Fermat reduction, residue parametrization) against the target problem, plus enumeration of techniques we are MISSING. | Strategic pivot decision; before abandoning a problem; check whether iter1->iter2 even applies |
| `bridge_lemma.md` | Factor the problem into KNOWN theorems + ONE specific unproven lemma. Lemma must be precisely statable, currently unproven, strictly weaker than the conjecture, and ideally submittable as a bare gap to Aristotle. | Want to scope a 1-week attack, not a 1-year program; suspect "almost closed" |
| `obstruction_diagnosis.md` | Identify the structural obstructions that have prevented closure for N years. Concrete vocabulary (parity barrier, sieve dimension, height bound, transcendence gap, Selmer parity, etc.) with historical citations. | Set realistic expectations; classify failures; honest cost estimates for multi-month attack |

---

## Wrapper script — `scripts/debate_fusion.py`

**CLI:**

```bash
python3 scripts/debate_fusion.py <problem_id> --template <name> [--rounds N] [--models grok,gemini,codex] [--timeout 300] [--context PATH] [--output PATH] [--dry-run]
```

**Behavior:**

1. Resolves the template at `research_fusion/prompts/debate_templates/<name>.md` and extracts the prompt body from its `## Sample prompt body` fenced block.
2. Substitutes `{PROBLEM}` with the supplied problem ID.
3. Auto-pulls a Stage-1 literature context if available, trying these locations and naming variants in order:
   - `analysis/research_fusion_<problem>.md`
   - `docs/research/<problem>.md`
   - `docs/debate_context_<problem>.md`
   - Variants tried: as-given, underscored (`erdos-938` -> `erdos_938`), compact (`erdos938`)
4. If no context exists, writes a minimal stub and warns.
5. Invokes `scripts/debate.py` with `--context`, `--topic` (the substituted prompt), `--rounds`, `--output`, `--models`, `--timeout`.
6. Output lands at `research_fusion/runs/<problem>/debates/<template>.md`.

**Examples:**

```bash
python3 scripts/debate_fusion.py erdos_938 --template technique_scout --rounds 3
python3 scripts/debate_fusion.py erdos_938 --template bridge_lemma --rounds 2
python3 scripts/debate_fusion.py erdos_938 --template tao_simulator --models gemini,codex
python3 scripts/debate_fusion.py erdos_938 --template bias_flush --dry-run   # preview
```

**`mk debate` convenience wrapper** (added in `math-forge/scripts/mk`):

```bash
mk debate erdos_938 technique_scout
mk debate erdos_938 bridge_lemma --rounds 2
mk debate erdos_938 bias_flush --models gemini,codex
```

`mk debate` with fewer than 2 args prints the template list and example invocations.

---

## E938 smoke test — `technique_scout.md`, 3 rounds, all 3 AIs

**Command:** `python3 scripts/debate_fusion.py erdos_938 --template technique_scout --rounds 3`
**Context pulled:** `analysis/research_fusion_erdos938.md` (Frey-Hellegouarch dossier prepared by F5)
**Wall time:** ~6 minutes for 3 rounds × 3 AIs in parallel
**Output:** `research_fusion/runs/erdos_938/debates/technique_scout.md` (~14600 tokens total)

### Cross-domain techniques surfaced

All three AIs successfully obeyed the template constraint (at least 3 of 5 techniques from outside number theory) and surfaced concrete cross-domain proposals. Highlights of the union across AIs:

1. **Frey-Hellegouarch curve + Ribet level-lowering** (Codex Round 1, Gemini Round 1)
   - Cited Bennett-Skinner 2004 on ternary Diophantine equations
   - Mapped powerful AP `n_k + n_{k+2} = 2 n_{k+1}` to Frey discriminant
   - Identified moving-conductor obstruction (conductor grows with radical)
2. **Bombieri-Lang / Vojta height inequalities** (Grok Round 1, Codex Round 1)
   - Surface of general type for fixed cubefree kernels
   - Vojta's height inequality as the missing tool
3. **Pila-Wilkie counting in o-minimal structures** (Grok Round 3)
   - André-Oort analogy
   - Bounds rational points of height H by H^ε
4. **l^p decoupling for polynomial curves** (Grok Round 3, Codex Round 2)
   - Bourgain-Demeter 2015
   - L^6 norm along the curve y ≈ x^(3/2) in the √N short-interval regime
5. **Furstenberg correspondence principle** (Grok Round 1, Gemini Round 1)
   - Multiple recurrence for zero-density sequences
   - Diagnosed sieve barrier as the failure mode of bare-gap attempts
6. **Gowers U^3 norms / inverse theorem** (Grok Round 1; revised to U^2 for 3-APs in Round 3 after Codex's correction)
7. **Schmidt subspace theorem / Evertse S-unit equations** (Codex Round 1)
   - Moving-S barrier identified
8. **Bombieri-Pila / Heath-Brown determinant method** (Gemini Round 3)
   - Counting integral points in thin boxes
9. **Effective equidistribution on nilmanifolds** (Grok Round 3, Codex Round 2)
   - Green-Tao 2012 quantitative inverse theorem
   - Polynomial sequences on nilmanifolds

### Round-3 closing positions

All three AIs converged on a similar diagnosis: the verified obstructions for E938 are (a) the moving conductor for Frey curves, (b) the √N short-interval emptiness condition from the consecutive constraint, and (c) the moving-S barrier for S-unit methods. Their consensus top-3 cross-domain tools were:

- Pila-Wilkie / Bombieri-Pila determinant method (highest fit to the √N window)
- Bombieri-Lang via Vojta on the fiber-product surface
- Frey-Ribet with kernel control (still viable but needs uniform conductor bound)

This is *exactly* the cross-domain content F3 was hoping to extract — concrete techniques, named papers, structural analogs, and diagnostic vocabulary for failure modes. No meta-process talk ("which problem next"), no taxonomy debate. Pure math content.

### Honest caveats

- One AI's claim that "Catalan was proved by Frey-Ribet" was caught and corrected by another AI in Round 2 (Mihăilescu used cyclotomic fields). The 3-AI debate format catches its own hallucinations.
- The Tao blog citations in `tao_simulator.md` will need verification on first real use — we ship the template with the `[citation needs verification]` disclaimer.

---

## How this differs from the May 29/30 strategy-debate format

| Dimension | May 29/30 strategy debate | I7 cross-domain debate |
|---|---|---|
| Topic shape | "Where should the project concentrate effort over the next month?" | "What 5 cross-domain techniques could unlock {PROBLEM}?" |
| Output type | Meta-process: rank problems, allocate effort, choose pipeline patterns | Math content: name techniques, cite papers, identify structural analogs |
| Granularity | Whole-project strategic | Per-problem tactical |
| Cadence | Monthly | On-demand per problem (stage-2 escalation) |
| Reusability | Single-shot | One template can be applied to dozens of problems |
| Storage | `docs/debate_*.md` (ad hoc) | `research_fusion/runs/<problem>/debates/<template>.md` (structured) |
| Triggers | Quarterly review, major pivots | Bare-gap stall, mk failed shows repeat failure, before abandoning |
| Hallucination risk | Low (process talk is robust) | Higher (technique citations needed) → mitigated by 3-AI cross-check |

The May 29/30 debate IS the right pattern for strategic questions — F3's finding was that 87% of LLM use was strategic when it should have been content-side. I7 doesn't replace the strategy debate; it adds the *missing* content-side debate.

---

## Files added / modified

**Added:**
- `research_fusion/prompts/debate_templates/technique_scout.md`
- `research_fusion/prompts/debate_templates/adjacent_analog.md`
- `research_fusion/prompts/debate_templates/tao_simulator.md`
- `research_fusion/prompts/debate_templates/bias_flush.md`
- `research_fusion/prompts/debate_templates/bridge_lemma.md`
- `research_fusion/prompts/debate_templates/obstruction_diagnosis.md`
- `scripts/debate_fusion.py` (executable wrapper)
- `research_fusion/runs/erdos_938/debates/technique_scout.md` (smoke test output, ~14600 tokens)
- `docs/infrastructure_changes_may30/I7_debate_technique_scouting.md` (this file)

**Modified:**
- `math-forge/scripts/mk` — added `debate` subcommand and help line

**Untouched:** `scripts/debate.py` (per scope — wrappers + templates only).

---

## Known gaps / follow-ups

1. **Grok env var mismatch:** `debate.py` reads `GROK_API_KEY`, but the user keeps the secret in `XAI_API_KEY` (per global CLAUDE.md). The smoke test required `export GROK_API_KEY="$XAI_API_KEY"` as a one-shot. A follow-up (I8+ scope) could either patch `debate.py` to accept `XAI_API_KEY` as a fallback, or add the export to a shared `scripts/env.sh`.
2. **Citation verification:** `tao_simulator.md` invites blog-post citations that an LLM may fabricate. The 3-AI cross-check helps, but a follow-up could pipe citations through `WebFetch` for automatic verification.
3. **Template versioning:** Each template is a single `.md` file with no version field. If a template is materially revised, prior debates' provenance will be ambiguous. Consider adding a YAML frontmatter `version:` field.
4. **No automatic Stage-3 hand-off:** The output is a markdown file. A future hook could parse the top-ranked technique and auto-draft a bare-gap sketch that name-drops the technique in the prior-results context. Out of scope for I7.
