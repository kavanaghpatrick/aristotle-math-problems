# CLAUDE.md - Math Project

## Mission
Prove Tuza's conjecture for ν=4 using Aristotle as a **discovery engine**. Falsify false conjectures fast. Prove true ones with scaffolding.

---

## Aristotle Capability Taxonomy

**Aristotle is a DISCOVERY ENGINE on finite domains, not just a verifier.**

| Tier | Success Rate | Capabilities | Key Tactics |
|------|--------------|--------------|-------------|
| **1** | 70-90% | Counterexamples (Fin 5-7), cardinality bounds, decidable predicates | `native_decide`, `fin_cases`, `decide` |
| **2** | 30-50% | Subadditivity, simple induction, LP witnesses (needs 10+ scaffolding) | `simp_all`, `aesop`, `omega` |
| **3** | 10-20% | Deep combinatorics (human must outline proof structure) | `grind`, `linarith` |
| **4** | <5% | Asymptotics, optimal selection, global coordination | **AVOID** |

**Falsification-first**: Submit uncertain conjectures on `Fin 6-7`. Aristotle finds counterexamples in minutes if false.

---

## Optimal Submission Pattern

| Metric | Target | Impact |
|--------|--------|--------|
| **Lines** | 100-200 | Under 100 = insufficient context; over 200 = diluted signal |
| **Lemmas** | 3-7 | Chain of dependencies, not monolith |
| **Sorries** | 0-1 | More sorries = diffuse effort |
| **Proven helpers** | 10+ | **4x success rate** (40% vs 10%) |
| **Vertex type** | `Fin n` (n ≤ 7) | Enables `native_decide`, `fin_cases` |

**Winning patterns** (by success rate):
- `safe_discard`: 100% - verify already-proven work
- `multi_agent_optimized`: 100% - parallel AI review before submit
- `scaffolded`: 10% - **needs more helpers or smaller scope**

---

## Hard Rules

1. **Never run `aristotle` directly** → always `./scripts/submit.sh`
2. **Never submit without problem_id** → track everything
3. **Near-misses (1-2 sorry) get worked FIRST** → before new submissions
4. **Check `failed_approaches` before submitting** → don't repeat mistakes
5. **Include proven scaffolding** → full proofs, never sorry placeholders
6. **Process every result** → `./scripts/process_result.sh` extracts learnings
7. **NEVER replace existing proof code with sorry** → if it compiled before, fix it, don't delete it

### File & Database Integrity

8. **PROVEN means 0 sorry AND 0 axiom** → `rg "sorry|^axiom" file.lean` must return nothing
9. **`proven/` directory = verified clean files only** → incomplete work goes in `partial/`
10. **Database follows files, not the other way around** → always verify .lean before updating status
11. **Axioms are not proofs** → any file using `axiom` is incomplete
12. **No self-loops in covers** → `s(v,v)` is not a graph edge; cover definitions MUST have `E ⊆ G.edgeFinset`
13. **Falsification-first for uncertain lemmas** → submit on `Fin 6-7`; Aristotle finds counterexamples fast if false
14. **10+ proven helpers minimum** → scaffolding increases success rate 4x

---

## FALSE LEMMAS (Query Database Before Submitting!)

All false lemmas are tracked in `false_lemmas` table with evidence levels:
- 🔴 `aristotle_verified` - Actual Aristotle counterexample (highest confidence)
- 🟠 `ai_verified` - AI agents verified the math (high confidence)
- 🟡 `reasoning_based` - Sound reasoning, no formal verification
- ⚪ `trivially_false` - Obvious logical error

**CRITICAL: Before submitting, check for false lemmas:**
```sql
-- Quick summary of all false lemmas
SELECT * FROM v_false_lemmas_summary;

-- Full details for a specific pattern
SELECT lemma_name, false_statement_english, counterexample,
       why_false, correct_approach
FROM false_lemmas WHERE lemma_name LIKE '%cover%';

-- Check if your lemma is false
SELECT * FROM false_lemmas WHERE lemma_name = 'local_cover_le_2';
```

**Key false lemmas to remember:**
| # | Lemma | Evidence | Impact |
|---|-------|----------|--------|
| 1 | `local_cover_le_2` | 🟠 AI | 2 M-edges at v insufficient |
| 6 | `external_share_common_vertex` | 🟠 AI | Externals don't share common x |
| 8 | `link_graph_bipartite` | 🟠 AI | König approach INVALID |
| 11 | `self_loop_cover` | ⚪ trivial | `s(v,v)` not a valid edge |

**Also check failed_approaches:**
```sql
SELECT approach_name, why_failed, avoid_pattern FROM failed_approaches
WHERE frontier_id='nu_4' AND failure_category='wrong_direction';
```

---

## The Correct T_pair Approach

For e = {v,a,b} and f = {v,c,d} sharing exactly vertex v:

| Set | Cover | Bound | Why |
|-----|-------|-------|-----|
| trianglesContaining(v) | Spokes {va,vb,vc,vd} | ≤ 4 | All contain v, so all contain a spoke |
| trianglesAvoiding(v) | Base edges {ab,cd} | ≤ 2 | If t avoids v but shares edge with e, t MUST share base {a,b} |
| **Total T_pair** | Spokes + Bases | **≤ 6** | NOT 4! The 4-bound is FALSE. |

---

## ν=4 Cases (Query database for full details)

```sql
-- Get ALL knowledge for a case in one query
SELECT case_name, status, notes, correct_approach, false_lemmas,
       proven_lemmas, key_insight, next_action
FROM nu4_cases WHERE case_name = 'path_4';
```

| Case | Status | Key Insight |
|------|--------|-------------|
| star_all_4 | PARTIAL | 4 spokes from shared vertex; τ ≤ 4 straightforward |
| three_share_v | PARTIAL | 3-star + isolated triangle; τ ≤ 5 straightforward |
| scattered | PARTIAL | Each external has unique parent; τ ≤ 12 proven |
| path_4 | PARTIAL | Endpoints need bases; τ ≤ 12 proven |
| cycle_4 | PARTIAL | All approaches blocked; τ ≤ 12 proven, τ ≤ 8 open |
| two_two_vw | PARTIAL | Two independent pairs; τ ≤ 12 proven |
| matching_2 | PARTIAL | Same as two_two_vw; τ ≤ 12 proven |

**What IS proven:** τ ≤ 12 for ALL cases (slot139 - 0 sorry, 0 axiom, correct definitions)

---

## Commands

```bash
# Submit (validates, tracks, submits atomically)
./scripts/submit.sh file.lean problem_id [pattern]

# Process completed result
./scripts/process_result.sh <UUID>

# Dashboard
./scripts/dashboard.sh
```

---

## Decision Priority

1. **Falsify uncertain conjectures** (submit on Fin 6-7 for fast counterexample search)
2. **Complete near-misses** (1-2 sorry with proven_count ≥ 10) - **70% of submissions are fixable**
3. **Partial cases** (nu4_cases WHERE status='partial')
4. **New exploration** (only if 1-3 are empty)

```sql
-- Find near-misses to work
SELECT filename, sorry_count, proven_count FROM submissions
WHERE status='completed' AND sorry_count = 1 AND proven_count >= 10 ORDER BY proven_count DESC;

-- Case knowledge
SELECT case_name, status, key_insight, next_action FROM nu4_cases;

-- Failed approaches to AVOID
SELECT approach_name, avoid_pattern FROM failed_approaches WHERE frontier_id='nu_4';
```

---

## Scaffolding (10+ helpers → 4x success rate)

**Validated TRUE lemmas** (mathematically verified):
- `tau_containing_v_in_pair_le_4` - Spokes cover containing triangles
- `tau_avoiding_v_in_pair_le_2` - Base edges cover avoiding triangles
- `avoiding_contains_base_edge` - Avoiding must share base edge
- `tau_union_le_sum` - Subadditivity
- `tau_S_le_2`, `tau_X_le_2` - S and X bounds
- `triangle_shares_edge_with_packing` - Maximality

```sql
SELECT name, english FROM literature_lemmas WHERE validated_true = 1;
```

**Critical rules:**
- Include FULL PROOF CODE from Aristotle outputs, not sorry
- Local compilation errors are OK (Mathlib version mismatch) - submit anyway
- Copy exact Aristotle output, don't modify

---

## Lean Pitfalls

| Bug | Problem | Fix |
|-----|---------|-----|
| `sInf` unrestricted | Allows invalid edge sets | Require `E ⊆ G.edgeFinset` |
| `Finset.sym2` | Includes self-loops s(v,v) | Filter to actual edges |
| `Set` vs `Finset` | Missing decidability | Use `Finset V` with `DecidableEq` |

**Required instances:**
```lean
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
```

---

## Multi-Agent Strategy

| Agent | Use For | Avoid |
|-------|---------|-------|
| **Grok-4** | Lean syntax, code bugs, proof gaps | Math reasoning (times out) |
| **Gemini** | Literature, proof strategy, architecture | Detailed code |
| **Claude** | Long context, planning, synthesis | - |
| **Aristotle** | **Discovery**: counterexamples (Fin 5-7), proof search with 10+ scaffolding, bound verification | Tier 3-4 without human outline, files >200 lines |

### Grok-4 API
```bash
python3 << 'PYEOF'
import json
prompt = "Your question..."
request = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-4",
    "temperature": 0.3,
    "max_tokens": 2000
}
json.dump(request, open('/tmp/grok_request.json', 'w'))
PYEOF

curl -s -X POST https://api.x.ai/v1/chat/completions \
  -H "Authorization: Bearer $GROK_API_KEY" \
  -H "Content-Type: application/json" \
  --max-time 300 \
  -d @/tmp/grok_request.json | python3 -c "import sys,json; print(json.load(sys.stdin)['choices'][0]['message']['content'])"
```

---

## Database

All state in `submissions/tracking.db`:

| Table | Content |
|-------|---------|
| `submissions` | All Aristotle jobs + notes |
| `literature_lemmas` | Proven (70) with validated_true flag |
| `failed_approaches` | What doesn't work (38) with falsity_proof |
| `false_lemmas` | **9 patterns with counterexamples, evidence levels** |
| `nu4_cases` | Case knowledge: approach, false_lemmas, key_insight, next_action |
| `ai_consultations` | AI recommendations and outcomes |

**Key views:**
| View | Purpose |
|------|---------|
| `v_false_lemmas_summary` | Quick overview of all false lemmas with evidence |
| `v_valid_proven` | All proven theorems with valid definitions |

---

## When Stuck

1. Query `false_lemmas` - is your lemma already disproven?
2. Query `failed_approaches` - repeating a failed approach?
3. Query `nu4_cases` for case-specific knowledge
4. Check `ai_consultations` for past recommendations
5. Parallel consult: Grok (code) + Gemini (strategy)
6. Target different case

```sql
-- Check everything at once
SELECT 'false_lemma' as type, lemma_name as name, evidence_level as info
FROM false_lemmas
UNION ALL
SELECT 'failed_approach', approach_name, failure_category
FROM failed_approaches WHERE frontier_id='nu_4';
```

---

## Metrics

**North star:** Discovery Velocity = new proven theorems / month

Current: ~0.5/month → Target: 2/month
