# 4-Round Multi-Model Debate Summary (Round 2)
## Tuza ν=4 Proof Strategy - Post Database Analysis
## February 7, 2026

---

## Participants

| Model | Focus Area | Rounds |
|-------|------------|--------|
| **Grok (xAI)** | LP formalization, Lean tactics | 4/4 |
| **Gemini (Google)** | Strategy, "Bird in Hand" | 4/4 |
| **Codex (OpenAI)** | File analysis, proof structure | 4/4 |

---

## Context: 10-Agent Database Analysis

Before this debate, 10 agents analyzed our entire database:
- **713 submissions**, 155 with 0 sorry
- **39 false lemmas** documented with evidence levels
- **56 failed approaches** (84% conceptual errors)
- **Only `scattered` has a truly GENERAL theorem** (SimpleGraph V)

---

## Round-by-Round Summary

### Round 1: Initial Positions

| Question | Grok | Gemini | Codex |
|----------|------|--------|-------|
| Q1 Priority | LP first | slot331 first | slot331 first |
| Q2 LP | Top priority | Parallel track | Defer |
| Q4 Cycle_4 | LP relaxation | τ ≤ 12 MVP | τ ≤ 12 MVP |

**Core tension**: Grok wanted LP upfront for leverage; Gemini/Codex wanted to secure near-wins.

### Round 2: Cross-Responses

**Key Finding by Codex**: Located the exact sorry in `slot331_tau_le_8_direct.lean`:
- Line 385: `tau_le_8` main theorem
- 18 proven lemmas, 1 sorry
- Key blocker: "Bad Bridge" problem

**Gemini's Proposal**: 48-hour timebox for slot331, then LP fallback

**Grok's Concession**: Agreed to slot331 first with LP as parallel prep

### Round 3: Synthesis

**Unanimous Agreement on**:
1. slot331 first (48-hour timebox)
2. LP as parallel backup
3. τ ≤ 12 as MVP baseline for cycle_4

**"Bad Bridge" Proof Strategy**:
1. Hypothesis: B missed → both X and Y have apex AWAY from shared edge
2. Exchange: Replace X/Y with externals → add B → 5-packing
3. Contradiction: ν ≥ 5 contradicts ν = 4

### Round 4: Final Consensus

**UNANIMOUS VOTE: YES - Execute the plan**

| Model | Vote | Amendment |
|-------|------|-----------|
| Grok | ✅ YES | None |
| Gemini | ✅ YES | Add counterexample search in parallel |
| Codex | ✅ YES | Lock 5-packing lemma statement first |

---

## Final Action Plan

### Phase 0-6h: Formalize "Bad Bridge" Hypothesis
- **Owner**: Codex
- **File**: `submissions/nu4_final/slot331_tau_le_8_direct.lean`
- **Deliverable**: `BadBridge` definition + `bad_bridge_implies_packing_5` stub

### Phase 6-24h: Prove 5-Packing Lemma
- **Owner**: Codex + Gemini
- **Approach**: Exchange argument using existing scaffolding
- **Scaffolding**: `two_edges_cover_X_and_externals`, `triangle_shares_edge_with_packing`

### Phase 24-36h: Lean Feasibility Review
- **Owner**: Grok
- **Deliverable**: Risk list + syntax pitfalls

### Phase 36-48h: Integration
- **Owner**: All
- **Deliverable**: Close the sorry in `tau_le_8`

### 48h Decision Point
- **Owner**: Patrick
- **Trigger**: If slot331 still blocked → start LP formalization

---

## LP Fallback Trigger Criteria

Any of:
- No viable proof sketch after 24h
- Requires >3 new helper lemmas
- Counterexample discovered
- High Lean feasibility risk at 36h

---

## Definition of Done

### Minimal (Victory)
```lean
theorem tau_le_8_of_nu_le_4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 8
```
With 0 sorry, 0 axiom.

### MVP Fallback
τ ≤ 12 for cycle_4 (already proven in slot139)

---

## Monday First Action

**EXACT COMMAND**:
```bash
# Open the file and locate the sorry
rg -n "sorry" submissions/nu4_final/slot331_tau_le_8_direct.lean
# Line 385 - tau_le_8 main theorem

# Add BadBridge hypothesis stub before the sorry
```

**EXACT FILE**: `submissions/nu4_final/slot331_tau_le_8_direct.lean`

**EXACT TASK**: Insert `BadBridge` definition + 4-step proof sketch at line 385

---

## T+24h Success Metric

At T+24h, we are ON TRACK if:
1. `bad_bridge_implies_packing_5` lemma statement compiles
2. At least 2 helper lemmas fully proved (0 sorry)
3. Exchange argument has concrete Lean structure
4. No blocking type mismatches

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Exchange argument fails (disjointness) | MEDIUM | HIGH | Add explicit disjointness lemma first |
| Hidden geometric constraints | LOW | HIGH | Parallel counterexample search |
| Lean type mismatches | MEDIUM | MEDIUM | Grok feasibility review at 36h |
| LP formalization too heavy | LOW | MEDIUM | Defer to v2 if needed |

---

## Key Files

| File | Purpose | Status |
|------|---------|--------|
| `slot331_tau_le_8_direct.lean` | Main target | 18 proven, 1 sorry |
| `slot12_lp_rounding.lean` | LP backup | Skeleton only |
| `literature_lemmas.lean` | LP duality sketch | Reference |
| `slot56_scattered_general_aristotle.lean` | Only GENERAL theorem | ✅ PROVEN |

---

## Debate Statistics

| Metric | Value |
|--------|-------|
| Total rounds | 4 |
| Models consulted | 3 |
| API calls | 12 |
| Consensus reached | ✅ UNANIMOUS |
| Key decision | slot331 first, 48h timebox, LP fallback |

---

*Debate conducted February 7, 2026*
*Models: Grok-4 (xAI), Gemini-3-Pro (Google), GPT-5.2-Codex (OpenAI)*
*Context: Post 10-agent database analysis*
