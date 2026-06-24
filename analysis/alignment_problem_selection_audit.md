# Alignment Audit: Problem-Selection Methods (A1 of 10)

**Date:** 2026-05-30
**Auditor:** Claude (A1)
**Scope:** Every problem-selection method this session, scored against the V-team finding "0/6 truly novel results."
**Smoking gun:** R3 (FT p=3, q≡71 mod 72, q ≤ 2000) was strictly subsumed by **Le, M.-H. (2012), Pure Appl. Math. Quart. 8(3), 689-692** — which proves the p=3 case of Feit-Thompson **unconditionally for ALL primes q**. R3's q ≤ 2000 is ~5×10^10 smaller than the computational frontier already in Guy/Motose (2009), and the theoretical case is closed since 2012. Our pipeline cited Le 2012 in `FT_p3_q71mod72_qLE2000_iter5.fusion.json` and `bridge_lemma.md`, but only as a parenthetical attribution — every gate proceeded to submit.

---

## 1. Method catalog with hit rates

| Method | Candidates | Submitted | Already-solved | Folklore/elementary | Truly open AND new | Novelty hit |
|---|---:|---:|---:|---:|---:|---:|
| **S5 long-tail Erdős mining** (CSV from 805-statement registry → 50 ranked) | 50 | 9 (E373, E944, E141, E477, E306, E1055, E319, E329, E100) | 0 verified solved | 6+ (E477 cubic = AlphaProof analog, E373 = 60-yr untouched but folklore; E100 Piepmeyer = **published witness from 1990s** — *known result, just unformalized*) | ~3 (E944 Dirac k=4, E373 Surányi, E1055 Selfridge) | 0/9 returned novel math |
| **S6 cross-domain technique scouting** (E672, E1003, E1052, E267, E64) | 5 | 5 fusion submissions | **1 outright (E672 (k=4, ℓ=3) closed by Bajpai-Bennett-Chan 2023)** + **E672 general by GHP 2009** per Codex's own R2 finding | 4 (E1003 rad-injection is folklore; E267 Fermat descent predates Brun 1910; E1052 = Wall 1972 case-split; E64 = same DNA as prior fails) | 0 | 0/5 |
| **S2 portfolio sequencing** (Jun 30-day plan) | 19 slots planned | 5 inflight by May 30 (slot747+E647, E938, E64, weird ω=6, Goormaghtigh) | E672 (k=4, ℓ=3) already SOLVED per S6's own debate; primitive weird ω=6 = SOLVED by Amato-Hasler-Melfi-Parton 2019; Lehmer ω=7 = SOLVED by Cohen-Hagis 1980 | Brocard, FT-p3 q-bumps = bounded-version-closure only | 0 confirmed | 0 of inflight |
| **C3 Codex closure candidates** (gpt-5.5 via codex-cli + ~20 web searches on erdosproblems.com) | 10 | 4 routed via S2 (E647, E64, E672, E835) | **E307 unit-fraction sums SOLVED in 2024** (Steinerberger, Liu-Sawhney); E672 family already covered by GHP 2009 | E7 distinct odd cover = verification-not-discovery; Sierpinski/Riesel = upstream search needed | 1-2 (E647 σ₀ existential, E64 cubic SAT) | uncertain |
| **C4 Gemini closure candidates** | Not on disk at synthesis time | 0 | n/a | n/a | n/a | n/a |
| **C5 Grok closure candidates** | 10 | 0 directly (some bled into S2) | **5 of 10 fail freshness**: Casas-Alvero deg 12 (solved 2012/2025), Lehmer ω=7 (1980), Primitive weird ω=6 (2019), sqfree-odd covers (BBMST 2022), E137 k=4 = k=3 (trivially equivalent) | 2 (Goormaghtigh (5,3), Pillai 5x-3y=2 = bound-bumping) | 2 (Tuza ν=5 small-graph, E672 k=4,ℓ=3) | 0 — both unproductive |
| **C6 literature freshness check** | retrospective audit on C3+C5+E1-bonus = 22 distinct candidates | 0 (kill-list only, not a generative method) | Caught 4/22 = **18% of LLM picks were SOLVED-SINCE**; missed Le 2012 entirely | n/a | n/a | n/a |

**Total session:** ~22 distinct LLM-generated candidates + 50 S5 long-tail + 5 S6 fusion. Of these, **~33 made it into submissions or active inflight** as of May 30. **0 produced novel math per V-team verdict.**

---

## 2. The Le 2012 failure path (which gates missed it)

The chain of gates that should have caught it:

1. **C6 literature_freshness** — Audited 22 Codex/Grok closure candidates. **Did NOT audit S2 inflight (R3 was already in S2)**. Le 2012 was outside scope.
2. **scripts/literature_check.py** — Hits only (a) teorth wiki AI-contributions snapshot, (b) erdosproblems.com page, (c) arxiv 2024-present, (d) `mk failed`. The teorth wiki only covers AI-resolved Erdős problems; Feit-Thompson is not on it. erdosproblems.com does not list FT. arxiv 2024-present does not contain Le 2012 (it's in *Pure Appl. Math. Quart.*, paywalled, MathSciNet only). **Zero of the 4 sources reach MathSciNet, zbMATH, Mathematical Reviews, or any pre-2024 journal database.**
3. **The fusion.json itself cites Le 2012** in `seminal_paper_arxiv` — but as a parenthetical "cf. Le 2012 for the p=3 elementary cases." No gate parses this as "the entire p=3 column is already solved unconditionally."
4. **`bridge_lemma.md` debate (May 30)** contains the line `-- p = 3 known by Le 2012` — but Grok/Gemini/Codex did not flag this as "STOP, the bound is trivial." Treated as context, not as a gate.
5. **R3 sketch** writes `Status: OPEN in full generality` — technically true (p ≥ 5 is open), but the *bounded p=3 q≤2000 claim* the sketch actually submits is the trivially-subsumed range.
6. **V-team `ft_family_publishability.md`** (post-hoc) catches it for the first time — but only after the result returned and a sibling agent went specifically to verify publishability.

**No gate cross-checks against MathSciNet/zbMATH.** Every selection method used: AI-contributions wiki + erdosproblems.com + arxiv (2024+) + internal DB. The pre-2024 paywalled-journal literature is invisible to the pipeline.

---

## 3. The single most important upgrade

**Add a mandatory MathSciNet/zbMATH cross-check to `literature_check.py` for every submission whose problem_id contains a named conjecture (FT, Brocard, Goormaghtigh, Lehmer, Pillai, Casas-Alvero, etc.).** This pre-2024 literature window is where 4 of the 5 confirmed misfires live (Le 2012, Cohen-Hagis 1980, Amato-Hasler-Melfi-Parton 2019, Castryck-Laterveer-Ounaïes 2012). The current gate's "arxiv 2024-present" window leaves a 40-year hole.

Implementation: query `https://mathscinet.ams.org/mathscinet/api/...` with the conjecture name OR pull a curated card per famous-named-conjecture into a local JSON (one-time annotation effort, ~60 named conjectures, < 1 day). The kill-list CSV already has the right schema — just needs a NAMED_CONJECTURE_STATUS column populated from MathSciNet.

Second-order: **`mk failed <keyword>` is local-only** and does not catch external literature. Without MathSciNet integration, every "is this open?" claim by an LLM scout is unverified.

---

## 4. Honest verdict: with perfect selection, what fraction would have changed?

**~25-40% of recent submissions would not have been submitted, but the novelty count would still be ~0/6.**

Breakdown:
- **R3 FT q≤2000 + R3-iter5 + R3-iter6 + slot744 + slot720 lineage:** ~5-6 slots that should never have been submitted. Le 2012 closes the entire p=3 column.
- **Primitive weird ω=6, Lehmer ω=7, sqfree-odd covers, Casas-Alvero d=12** (if S2 had pulled them from Grok's list): ~3-4 slots avoided.
- **E672 k=4 ℓ=3 (S6 candidate):** likely already covered by GHP 2009 per Codex's R2 finding — but R3 of S6 debate's specific framing as "AP of 3-powerful numbers" may genuinely be open. Ambiguous.
- **Folklore-elementary results (E1003 rad-injection, E267 Fermat descent, R7 E324 h=0 slice, slot 746 σ₀=11):** these would still have been submitted — they're not in the literature as published theorems, just as one-line exercises. Submitting them is defensible; counting them as novel is not.

**Net:** perfect selection saves ~6-8 slots of compute (~$15-25) but does **not** convert a single submission into novel math. The V-team's 0/6 verdict is a **pipeline ceiling**, not a selection failure. Even if every submission targeted a verified-open problem, the bare-gap-only architecture cannot produce novel mathematics — it produces bounded verifications and elementary substitutions of folklore proofs. Per A2's audit: 0/6 PUBLISHED PARTIAL strategies executed; 5/6 were replaced by Aristotle with elementary folklore.

**Better problem selection is necessary but not sufficient.** The architecture, not the selection, is the rate-limiting step.

---

## 5. Sources

- `analysis/literature_freshness_summary.md` — the C6 freshness audit (22 candidates, 18% LLM-solved-since rate)
- `analysis/literature_freshness_may30.csv` — per-candidate status table
- `scripts/literature_check.py` — the production gate (lines 9-13 list the 4 sources; no MathSciNet)
- `analysis/long_tail_erdos_summary.md` — S5 long-tail mining (50 candidates)
- `analysis/technique_scouting_round1.md` — S6 cross-domain scouting (5 fusion candidates)
- `analysis/closure_list_may30.md` — C10 closure-first synthesis (20 candidates, 11-slot batch)
- `analysis/codex_closure_candidates.md`, `analysis/grok_closure_candidates.md` — C3, C5 raw LLM outputs
- `docs/strategy_synthesis_may30.md` — S10 final 30/60/90 synthesis (S2 portfolio)
- `docs/research/ft_family_publishability.md` — V-FT post-hoc Le 2012 detection
- `docs/research/today_results_research_impact_synthesis.md` — V-team 0/6 verdict
- `submissions/sketches/FT_p3_q71mod72_qLE2000_iter5.fusion.json` — fusion.json that cited Le 2012 parenthetically while submitting anyway
- `research_fusion/runs/feit_thompson/debates/bridge_lemma.md` — debate transcript containing `-- p = 3 known by Le 2012`
