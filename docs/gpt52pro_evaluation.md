# GPT-5.2 Pro Evaluation as Class 6 FUSION Strategist

**Status**: PROVISIONAL — gating on developer-tier OPENAI_API_KEY
**Date**: 2026-05-30
**Investigator**: E10
**Resolves**: S9 vs S10 conflict on adopting `gpt-5.2-pro` as paired strategist LLM

---

## 1. API Availability Verdict — gpt-5.2-pro IS real

**S10 was correct on existence; S9 was wrong on that point.** Updated facts:

| Claim | Status |
|---|---|
| S9: "OpenAI folded 5.2 Pro into 5.5" | **False.** 5.2-pro is a live, distinct SKU. |
| S9: "Codex CLI = gpt-5.5 is the substitute" | **Partially true.** Codex defaults to 5.5; 5.2-pro is NOT reachable through Codex CLI under ChatGPT-account auth. |
| S10: "gpt-5.2-pro is available" | **True.** Live as a developer-API model. |

### Evidence

1. **OpenAI announcement** (`https://openai.com/index/introducing-gpt-5-2/`):
   GPT-5.2 Pro available in **Responses API only**, model id `gpt-5.2-pro`.
   Supports the new `xhigh` reasoning effort tier.

2. **Codex CLI direct test** (`codex exec -m gpt-5.2-pro "..."`):
   ```
   ERROR 400 invalid_request_error:
   "The 'gpt-5.2-pro' model is not supported when using Codex
    with a ChatGPT account."
   ```
   So Codex CLI under ChatGPT-Plus OAuth cannot route to 5.2-pro. A
   developer-tier `OPENAI_API_KEY` (sk-…) bound to a paid developer
   account is required, hitting the Responses API directly.

3. **Codex models cache** (`~/.codex/models_cache.json`): lists `gpt-5.2`
   (base) as `supported_in_api: true`, with explicit `upgrade → gpt-5.5`
   migration metadata. The Pro snapshot is omitted from Codex's list
   because Codex itself can't access it; this is the source of S9's
   confusion.

### Pricing (per 1M tokens, base GPT-5.2 SKU)

| Tier | $/1M input | $/1M output | Cached input |
|---|---|---|---|
| gpt-5.2 (base) | $1.75 | $14.00 | $0.18 (90% off) |
| gpt-5.2-pro | not separately disclosed; same Responses-API rate card; reasoning tokens billed at output rate | | |

Reasoning tokens (the "Thinking" trace) are **invisible but billed at
output rate**. A single `xhigh` Stage 4 outline call could easily consume
~10-30k reasoning tokens (= $0.14-$0.42 each).

Sources: [Introducing GPT-5.2](https://openai.com/index/introducing-gpt-5-2/),
[OpenAI API Pricing](https://openai.com/api/pricing/).

---

## 2. Smoke Test Results

### Path A — Direct Responses API
**BLOCKED.** No developer-tier `OPENAI_API_KEY` is provisioned in the
environment. `~/.zshrc` shows the variable commented out, and
`~/.codex/auth.json` contains only OAuth tokens (not a usable sk-
key). Smoke script is written and ready to run.

Run when key is provisioned:
```
export OPENAI_API_KEY=sk-…
python3 scripts/gpt52pro_smoke.py \
    --gap submissions/sketches/erdos938_fusion.txt \
    --compare-codex
```
Script: `scripts/gpt52pro_smoke.py` (already in place).

### Path B — Codex CLI model override
**BLOCKED at the model layer.** `codex exec -m gpt-5.2-pro` returns
HTTP 400 — Codex with ChatGPT-Plus auth refuses to route to 5.2-pro.
`codex exec -m gpt-5.2` (no Pro) works but `models_cache.json` marks
gpt-5.2 with an explicit upgrade arrow → gpt-5.5. Using base 5.2 over
5.5 is a downgrade with no upside.

---

## 3. Decision

**HYBRID, conditional on API-key provisioning.**

1. **Default strategist remains Codex CLI / gpt-5.5** (zero extra setup,
   already wired through `research_fusion/stage3_techniques.py`).
2. **Add `--paired-llm gpt-5.2-pro` actually-callable path** only after
   the user exports a developer-tier `OPENAI_API_KEY`. Until then the
   existing `--paired-llm gpt-5.2-pro` flag in
   `safe_aristotle_submit.py` and `aristotle_informal.py` remains an
   **audit-trail label only** (sets `DB.paired_llm`, does NOT route the
   actual outline call).
3. **When key is available**: run the smoke test on E938, compare
   outputs side-by-side. If the 5.2-pro outline differs qualitatively
   (different named technique, materially different candidate lemmas)
   from the gpt-5.5 outline, wire 5.2-pro into Stage 3 as an optional
   provider via `research_fusion/stage3_techniques.py`. If outputs are
   comparable, keep Codex.

### Why not unconditional adoption

- W4's claim that gpt-5.2-pro is the documented author for 5 successful
  Aristotle-paired Erdős solves comes from a period when the
  ChatGPT-Plus UI labelled 5.2-pro as the underlying model. Those
  outlines were produced through the **ChatGPT interface**, not the
  Responses API — meaning we don't yet have direct evidence that
  Responses-API 5.2-pro produces the same quality as the ChatGPT-UI
  version, only that they share an underlying weight checkpoint.
- Without an actual smoke comparison on E938 we cannot quantify
  qualitative gain over gpt-5.5.

---

## 4. Single Most Important Finding

**The blocker is auth provisioning, not engineering.** GPT-5.2 Pro
exists and works, but only through `api.openai.com/v1/responses` with a
developer-account API key. The user has only a ChatGPT-Plus OAuth token
in `~/.codex/auth.json`. ~10 lines of integration shell + a smoke
comparison is all that stands between us and using it — once an
`sk-…` key is exported.

---

## 5. Action Items for Wiring (when key is provisioned)

1. Set `OPENAI_API_KEY=sk-…` in `~/.zshrc` (uncomment + replace).
2. Run `python3 scripts/gpt52pro_smoke.py --gap
   submissions/sketches/erdos938_fusion.txt --compare-codex`.
3. Read both outputs from `docs/gpt52pro_smoke_runs/`.
4. If qualitative difference confirmed:
   - Add `call_gpt52pro()` to `research_fusion/stage3_techniques.py`
     mirroring `call_codex()` but hitting Responses API.
   - Add `--strategist {codex,gpt-5.2-pro}` flag to Stage 3 entrypoint.
   - Optional prompt template:
     `research_fusion/prompts/stage3_techniques_gpt52pro.md`
     (currently no provider-specific prompt is needed; the existing
     `stage3_techniques.md` is provider-agnostic).
5. Update `safe_aristotle_submit.py` docstring to clarify
   `--paired-llm gpt-5.2-pro` is the audit-trail label and routing
   happens at Stage 3 invocation time.

### Estimated Cost per Stage 4 Outline

Assume ~2k prompt tokens (gap + system instruction) + ~3k visible output
+ ~20k reasoning tokens at `xhigh`.
- input: 2k × $1.75/1M = $0.0035
- visible output: 3k × $14/1M = $0.042
- reasoning (billed as output): 20k × $14/1M = $0.28
- **Total per outline: ~$0.33**, dominated by reasoning tokens.

At ~5 fusion submissions/week → ~$1.65/wk, ~$85/yr. Budget non-issue
once activated.

---

## References

- [Introducing GPT-5.2 — OpenAI](https://openai.com/index/introducing-gpt-5-2/)
- [OpenAI API Pricing](https://openai.com/api/pricing/)
- [GPT-5.2 API Pricing 2026 — PricePerToken](https://pricepertoken.com/pricing-page/model/openai-gpt-5.2)
- Codex CLI 0.130.0 `~/.codex/models_cache.json` (snapshot 2026-05-30)
- `scripts/gpt52pro_smoke.py` — smoke harness
- `scripts/safe_aristotle_submit.py:1472` — `--paired-llm` audit-trail flag
- `scripts/aristotle_informal.py:324` — same
