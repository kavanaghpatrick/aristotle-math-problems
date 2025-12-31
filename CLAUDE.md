# CLAUDE.md - Math Project

## Mission
Prove Tuza's conjecture for ν=4 using Aristotle. Learn from every attempt.

---

## Hard Rules

1. **Never run `aristotle` directly** → always `./scripts/submit.sh`
2. **Never submit without problem_id** → track everything
3. **Near-misses (1-2 sorry) get worked FIRST** → before new submissions
4. **Check `failed_approaches` before submitting** → don't repeat mistakes
5. **Include proven scaffolding** → full proofs, never sorry placeholders
6. **Process every result** → `./scripts/process_result.sh` extracts learnings
7. **NEVER replace existing proof code with sorry** → if it compiled before, fix it, don't delete it

---

## FALSE LEMMA PATTERNS (Critical - Check Before Submitting!)

### Pattern 1: Spokes Cannot Cover Avoiding Triangles
```
FALSE: "If t avoids v, then ∃ spoke {v,x} ∈ t.sym2"
WHY:   If t avoids v, then v ∉ t. Spokes contain v. So spokes ∉ t.sym2.
FIX:   Use BASE EDGES {a,b},{c,d} for avoiding triangles, not spokes.
```

### Pattern 2: Bridge Coverage Errors
```
FALSE: "Cover of S_e ∪ S_f covers bridges X(e,f)"
WHY:   Bridges share vertices with e,f but may not share edges with S_e or S_f.
FIX:   Handle bridges separately with tau_X_le_2.
```

### Pattern 3: Intersection Assumptions
```
FALSE: "Non-adjacent packing elements are vertex-disjoint"
WHY:   In a cycle, opposite elements can share a vertex.
FIX:   Check actual intersection, don't assume disjointness.
```

### Pattern 4: Vertex vs Edge Cover Confusion
```
FALSE: "Hitting all vertices of e covers bridges through e"
WHY:   Edge cover needs edges IN the triangle, not just incident to vertices.
FIX:   Use edge-based covering, not vertex-based.
```

### Pattern 5: local_cover_le_2 (CRITICAL - Dec 26, 2025)
```
FALSE: "2 edges from M_edges_at suffice to cover triangles at shared vertex v"
WHY:   Codex counterexample: 4 triangles at v_ab each use DIFFERENT M-edge,
       but share {v_ab,x} so ν stays 4. Hitting set needs ALL 4 M-edges.
FIX:   Use "support clusters" approach - cover edges can be OUTSIDE M_edges_at.
SEE:   docs/FALSE_LEMMAS.md for full details
```

### Pattern 6: support_sunflower τ ≤ 2 (CRITICAL - Dec 28, 2025)
```
FALSE: "τ(trianglesSharingMEdgeAt G M v) ≤ 2"
WHY:   trianglesSharingMEdgeAt INCLUDES M-elements A, B (not just externals)!
       At v_ab: {A, B, T1, T2, T3, T4} needs 3 edges minimum.
       {v_ab, x} covers T1-T4 but NOT A, B (x ∉ A, x ∉ B).
FIX:   Separate M-coverage from external-coverage. But see Pattern 7!
SEE:   docs/FALSE_LEMMAS.md
```

### Pattern 7: external_share_common_vertex (CRITICAL - Dec 29, 2025)
```
FALSE: "All external triangles at shared vertex v share a common external vertex x"
WHY:   Aristotle counterexample (slot131_v2, UUID 7039b275):
       CounterexampleG has T1={0,1,5} using edge from A, T2={0,3,6} using edge from B.
       T1 ∩ T2 = {0} only - external vertices 5 and 6 are DIFFERENT!
       External triangles can independently use edges from DIFFERENT M-triangles.
FIX:   UNKNOWN - 4+4 cover approach is INVALID. Need new strategy.
SEE:   docs/FALSE_LEMMAS.md for full counterexample
```

**CRITICAL: Check `docs/FALSE_LEMMAS.md` before using ANY lemma from slot73!**

**Before submitting, run:**
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
| star_all_4 | PROVEN | 4 spokes from shared vertex |
| three_share_v | PROVEN | 3-share + isolated triangle |
| scattered | PROVEN | Disjoint = no bridges, each independent |
| path_4 | PARTIAL | Endpoints need base edges, middles use All-Middle |
| **cycle_4** | **BLOCKED** | **4+4 approach INVALID - slot131_v2 disproved external_share_common_vertex** |
| two_two_vw | PARTIAL | Two independent pairs, no inter-bridges |
| matching_2 | PARTIAL | Same as two_two_vw |

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

1. **Complete near-misses** (1-2 sorry with proven_count > 0)
2. **Partial cases** (nu4_cases WHERE status='partial')
3. **New exploration** (only if 1-2 are empty)

```sql
-- Near-misses
SELECT filename, sorry_count, proven_count FROM submissions
WHERE status='completed' AND sorry_count BETWEEN 1 AND 2 ORDER BY proven_count DESC;

-- Case knowledge
SELECT case_name, status, key_insight, next_action FROM nu4_cases;

-- Failed approaches to AVOID
SELECT approach_name, avoid_pattern FROM failed_approaches WHERE frontier_id='nu_4';
```

---

## Scaffolding

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
| **Aristotle** | Actual proving (6+ hrs) | Quick checks |

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
| `failed_approaches` | What doesn't work (17) with falsity_proof |
| `nu4_cases` | Case knowledge: approach, false_lemmas, key_insight, next_action |
| `ai_consultations` | AI recommendations and outcomes |

---

## When Stuck

1. Query `failed_approaches` - repeating a mistake?
2. Query `nu4_cases` for case-specific knowledge
3. Check `ai_consultations` for past recommendations
4. Parallel consult: Grok (code) + Gemini (strategy)
5. Target different case

---

## Metrics

**North star:** Discovery Velocity = new proven theorems / month

Current: ~0.5/month → Target: 2/month
