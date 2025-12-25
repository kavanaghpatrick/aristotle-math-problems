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

## Commands

```bash
# Submit (validates, tracks, submits atomically)
./scripts/submit.sh file.lean problem_id [pattern]

# Process completed result
./scripts/process_result.sh <UUID>

# What should I do next?
./scripts/next_task.sh

# Dashboard
./scripts/dashboard.sh

# Before ending session (MANDATORY after Dec 22 incident)
./scripts/session_check.sh
```

---

## Decision Priority

1. **Complete near-misses** (1-2 sorry with proven_count > 0)
2. **Open cases** (nu4_cases WHERE status='open')
3. **New exploration** (only if 1-2 are empty)

```sql
-- Near-misses
SELECT filename, sorry_count FROM submissions
WHERE status='completed' AND sorry_count BETWEEN 1 AND 2;

-- Open cases
SELECT case_name FROM nu4_cases WHERE status='open';

-- Failed approaches to AVOID
SELECT approach_name, avoid_pattern FROM failed_approaches WHERE frontier_id='nu_4';
```

---

## ν=4 Cases

| Case | Status | Notes |
|------|--------|-------|
| star_all_4 | PROVEN | slot29 |
| three_share_v | PROVEN | slot29 |
| two_two_vw | OPEN | |
| path_4 | PARTIAL | 2 sorry |
| cycle_4 | PARTIAL | 2 sorry |
| matching_2 | OPEN | |
| scattered | OPEN | hardest |

---

## Scaffolding

Key proven lemmas: `tau_S_le_2`, `tau_union_le_sum`, `tau_X_le_2`, `lemma_2_2`, `lemma_2_3`

```sql
SELECT name, statement FROM literature_lemmas WHERE proof_status='proven';
```

**Critical rules:**
- Include FULL PROOF CODE from Aristotle outputs, not sorry
- Local compilation errors are OK (Mathlib version mismatch) - submit anyway
- Copy exact Aristotle output, don't modify
- Wasting Aristotle time reproving known lemmas = bad

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
    "model": "grok-4",  # ALWAYS grok-4, never grok-3-mini
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

### Gemini CLI
```bash
gemini -p "Analyze: $(cat file.lean)"
```

---

## Counterexample Constraints

Any Tuza counterexample must satisfy (from literature):
- mad(G) ≥ 7
- χ(G) ≥ 5
- NOT tripartite, NOT threshold
- treewidth ≥ 7

---

## What Works

- **Scaffolded** (1.7 avg sorry) beats boris_minimal (2.5)
- **Specific sub-cases** beat generic attacks
- **Informal (.md)** sometimes works when formal fails
- **Concrete examples** (A4 Cayley graph) build intuition

---

## What Aristotle Does Well

- Finds counterexamples to false lemmas (found 12!)
- Proves sub-lemmas even when main fails
- Works better with scaffolding
- 6+ hour runtime is normal

---

## Database

All state in `submissions/tracking.db`:

| Table | Content |
|-------|---------|
| `submissions` | All Aristotle jobs |
| `literature_lemmas` | Proven (53) + axioms (27) |
| `failed_approaches` | What doesn't work (12) |
| `nu4_cases` | Case coverage |
| `hypotheses` | Research narrative |

---

## When Stuck

1. Check `failed_approaches` - repeating a mistake?
2. Check near-misses - almost-win to complete?
3. Try informal (.md) submission
4. Parallel consult: Grok (code) + Gemini (strategy)
5. Target different case

---

## Metrics

**North star:** Discovery Velocity = new proven theorems / month

Current: ~0.5/month → Target: 2/month
