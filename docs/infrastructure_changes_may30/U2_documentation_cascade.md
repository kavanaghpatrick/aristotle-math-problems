# U2 — Documentation Cascade (Informal Mode Operational Confirmation)

**Author:** U2 (May 30 2026 wave, agent 2 of 5)
**Status:** Documentation cascade complete.
**Trigger:** I9 smoke test (Euclid infinitude, UUID `8d500201-0786-4bb2-8489-2f6aad91be91`) returned an `ARISTOTLE_SUMMARY.md` with explicit "Informal proof:" + "Formalization:" sections, empirically confirming subsystem #2 engagement via the informal-mode prompt-assembly pathway.

---

## Single Message

**"Strategy lives in the companion, not the sketch; informal mode is now operational and confirmed."**

The `.txt` sketch stays bare (≤30 lines, no proof guidance). Strategy material — informal proof outlines, candidate lemmas, cross-domain literature, paired-LLM dossiers — lives in the airlocked `.fusion.json` companion. When `aristotle_informal.py` sees a companion present, it assembles an informal-mode prompt that routes Aristotle through its lemma-based reasoner subsystem (#2) before the MCGS formalizer (#1) runs. The I9 Euclid smoke test is the canonical "this is what the output looks like" reference.

---

## Per-File Change Log

### 1. `CLAUDE.md` (modified)

- **Section:** Mission
- **Change:** After the existing Mission paragraph ("We do NOT develop proof strategies..."), inserted a blockquote clarifying that strategy belongs in the `.fusion.json` companion (NOT the `.txt` sketch), citing arXiv:2510.01346 §3 (the documented Harmonic pattern) and the I9 smoke test (UUID `8d500201`) as empirical confirmation.
- **Preserved:** All user-authored content. Hard Rules untouched. Lane decision tree untouched. Status enum untouched.
- **Lines added:** 1 blockquote (~4 lines effective text).

### 2. `~/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md` (modified)

- **Section:** USER DIRECTIVES, item #5
- **Change:** Appended an "Empirical confirmation May 30 2026" line stating the I9 smoke test produced an `ARISTOTLE_SUMMARY.md` with explicit "Informal proof:" + "Formalization:" sections using `Nat.exists_infinite_primes`. Subsystem #2 confirmed engaged. Reference to canonical doc at `docs/research/aristotle_smoke_test_euclid_may30.md`.
- **Preserved:** All other directives, FALSIFIED APPROACHES, FACTS, TOOLING, FEEDBACK sections untouched.
- **Lines added:** ~5 sentences appended to directive #5.

### 3. `docs/research/aristotle_smoke_test_euclid_may30.md` (NEW — canonical reference)

- **Purpose:** Promote the I9 smoke-test artifact to a canonical location so any future audit ambiguity about whether subsystem #2 was engaged on a submission can be resolved by comparison.
- **Contents:**
  - Preamble: provenance (UUID `8d500201`, endpoint, SDK version), canonical-reference status declaration.
  - "What This Demonstrates": explicit statement that bare-Lean submissions only invoke MCGS; informal-mode prompts engage the lemma-based informal reasoner. Two-channel response signature.
  - Provenance chain: sketch → companion → adapter → SDK call → result tarball, including both UUIDs (project `8d500201` vs result-bundle `f9e23cf2`).
  - Verbatim `ARISTOTLE_SUMMARY.md` content (Theorem, Informal proof, Formalization sections).
  - Verbatim `Main.lean` content.
  - "What This Output Format Tells Us": 5-point breakdown of subsystem-#2 signatures.
  - "How to Use This Reference": audit instructions.
  - Cross-references to I9 infrastructure doc, W8 finding, Harmonic paper, S10 four-criteria rule, lane routing matrix, Aristotle usage guide, E938 watch.
- **Size:** ~120 lines.

### 4. `docs/aristotle_usage_guide.md` (modified — new Section 7.5)

- **Section:** Inserted Section 7.5 "BARE vs INFORMAL Mode Output: Empirical Comparison" between existing §7 ("How to Invoke Each Lane") and §8 ("Sanity Checks Before Submitting").
- **Contents:**
  - Side-by-side BARE vs INFORMAL output comparison table (tarball contents, ARISTOTLE_SUMMARY.md presence, NL narrative, Lean body, subsystem invoked, two-channel response, canonical reference).
  - The 4 validation criteria (S10 pivot rule): named-technique citation, Mathlib cross-domain import, separate NL reasoning trace, non-trivial candidate-lemma partial. Decision rule table (0/4 → shelve, 1/4 → validated, 2-3/4 → scale, 4/4 → pivot).
  - When to use each lane: consolidating S1's lane-routing matrix (`docs/lane_routing_matrix.md`) into the 8-class table.
  - Operational sequence for new structural-open problems (BARE → FUSION → INFORMAL fallback).
  - Pointer to the canonical reference (`docs/research/aristotle_smoke_test_euclid_may30.md`).
- **Preserved:** All existing sections 1-7 and 8+ untouched.
- **Size:** ~90 lines added.

### 5. `docs/infrastructure_changes_may30/U2_documentation_cascade.md` (this file — NEW)

- **Purpose:** This documentation-change manifest. Single landing page for the U2 cascade.

---

## Cross-References

### To U1's routing changes

U1's task in this wave was the parallel update to **routing logic** in `safe_aristotle_submit.py` / `aristotle_informal.py` (sibling agent). U1's changes may not have landed at the moment U2 wrote this doc. When U1's documentation lands, U2's cross-references to:

- "the I9 informal-mode prompt-assembly pathway"
- "`aristotle_informal.py` assembles an informal-mode prompt at submission time"
- "When a `.fusion.json` companion is present"

should be auditable against U1's per-file routing changes. If U1 renamed `aristotle_informal.py` or changed the trigger condition (e.g. from "companion present" to "explicit `--informal-mode` flag"), the CLAUDE.md blockquote and the Section 7.5 prose in `aristotle_usage_guide.md` may need a small adjustment to reflect the final invocation surface. The Euclid smoke-test artifact (`docs/research/aristotle_smoke_test_euclid_may30.md`) is invariant — UUID `8d500201` is the live witness.

### To prior agent outputs

- **W8** (analysis/web_research_synthesis.md): Hypothesis that bare-Lean submissions only invoke MCGS, informal mode invokes subsystem #2. Confirmed empirically.
- **I9** (docs/infrastructure_changes_may30/I9_informal_mode.md): Adapter spec, prompt assembly, smoke-test command, smoke-test transaction log. U2's canonical doc draws from I9 §5 (Smoke test — Live run).
- **S10** (docs/strategy_synthesis_may30.md + docs/e938_fusion_validation_watch.md): Four-criteria pivot rule. U2's Section 7.5 in the usage guide consolidates this rule.
- **S1** (docs/lane_routing_matrix.md): 5-question flowchart + 8 problem classes. U2's Section 7.5 "When to use each lane" condenses S1's matrix.
- **F1 / F2 / F3** (F-team audits): The motivation for FUSION lane existence. Referenced through CLAUDE.md Hard Rules.

---

## Verification Pointers

For a future auditor checking this cascade landed correctly:

```bash
# 1. CLAUDE.md has the blockquote
grep -n "Strategy belongs in the airlock companion" /Users/patrickkavanagh/math/CLAUDE.md

# 2. MEMORY.md has the empirical-confirmation line
grep -n "Empirical confirmation May 30 2026" /Users/patrickkavanagh/.claude/projects/-Users-patrickkavanagh-math/memory/MEMORY.md

# 3. Canonical doc exists with the UUID
test -f /Users/patrickkavanagh/math/docs/research/aristotle_smoke_test_euclid_may30.md && \
    grep -c "8d500201-0786-4bb2-8489-2f6aad91be91" /Users/patrickkavanagh/math/docs/research/aristotle_smoke_test_euclid_may30.md

# 4. Usage guide has new section 7.5
grep -n "## 7.5 BARE vs INFORMAL" /Users/patrickkavanagh/math/docs/aristotle_usage_guide.md

# 5. Original I9 smoke-test artifact still in place
test -f /Users/patrickkavanagh/math/submissions/nu4_final/i9_extracted/f9e23cf2-55f2-4eab-940c-6c06e79f54e5_aristotle/ARISTOTLE_SUMMARY.md
```

---

## What Did NOT Change

- Hard Rules in CLAUDE.md — preserved verbatim per directive.
- Pipeline gate (`check_gap_targeting()`) — unchanged.
- Lane decision tree in CLAUDE.md — unchanged.
- Status enum — unchanged.
- DB schema — unchanged.
- User-authored sections of MEMORY.md (FALSIFIED APPROACHES, ARISTOTLE FACTS, LITERATURE-CHECK REQUIREMENT, TOOLING, FEEDBACK) — preserved verbatim.
- Existing sections 1-7 and 8-10 of `aristotle_usage_guide.md` — preserved verbatim.

---

## Authority

- Smoke-test source: `submissions/nu4_final/i9_extracted/f9e23cf2-55f2-4eab-940c-6c06e79f54e5_aristotle/`
- Project UUID: `8d500201-0786-4bb2-8489-2f6aad91be91`
- Endpoint: `https://aristotle.harmonic.fun`
- SDK: `aristotlelib 0.7.0`
- Submission timestamp: 2026-05-30 (per I9 §5 transaction log)
- I9 adapter: `scripts/aristotle_informal.py`
