# Solving Open Mathematical Problems with AI

Using [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) to make progress on genuinely open mathematical problems.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)

**Last Updated**: December 23, 2024

---

## Mission

**Goal**: Use AI-powered theorem proving to make genuine progress on open mathematical problems—not just re-formalize known results.

**Primary Focus**: Tuza's Conjecture frontiers
- **ν = 4 case** (genuinely OPEN - Parker's 2024 proof breaks here)
- Split graphs general case
- Counterexample search

---

## Current Status: ν = 4 Attack

### Proven Infrastructure (87 lemmas in database)

| Lemma | Description | Status |
|-------|-------------|--------|
| **tau_union_le_sum** | τ(A ∪ B) ≤ τ(A) + τ(B) | ✅ Proven |
| **tau_S_le_2** | τ(S_e) ≤ 2 for any packing element | ✅ Proven |
| **Se_pairwise_intersect** | All triangles in S_e share edges | ✅ Proven |
| **Te_eq_Se_union_bridges** | T_e = S_e ∪ bridges partition | ✅ Proven |
| **bridges_inter_card_eq_one** | Distinct bridges share exactly 1 vertex | ✅ Proven |
| **bridges_contain_v** | Bridges between e,f contain shared vertex | ✅ Proven |

### Running Submissions (12 active)

| Slot | Target | UUID |
|------|--------|------|
| slot29_v2 | Triple-apex reduction | `39778d23-...` |
| slot30_v2 | Vertex partition | `744eb623-...` |
| slot31_v2 | Link graph VC (star) | `60a910e6-...` |
| slot32_v2 | Path configuration (P4) | `5694d879-...` |
| slot33_v2 | Cycle configuration (C4) | `a6038542-...` |

### Attack Strategy

The ν=4 case requires analyzing the **sharing graph** - which pairs of packing elements share vertices:

```
Sharing Graph Configurations:
├── Connected (≥3 share a vertex)
│   ├── Star (K4) → slot29, slot31
│   ├── 3-star → slot29
│   └── Triangle+1 → slot29
├── Path (P4) → slot32 [NEW]
├── Cycle (C4) → slot33 [NEW]
└── Disconnected → slot30
```

**Key Insight**: The v2 submissions include FULL proven scaffolding (not sorry placeholders), so Aristotle focuses on the new target theorems.

---

## Verified Results

### Erdős Problems (Fully Proven)

| Problem | Result | File |
|---------|--------|------|
| **Erdős #153** | Sidon set sumset bounds | `erdos153_v4_SUCCESS.lean` |
| **Erdős #190** | Divisibility result | `erdos190_SUCCESS.lean` |
| **Erdős #593** | Partition result | `erdos593_SUCCESS.lean` |

### Tuza's Conjecture

**Conjecture (Tuza, 1981)**: For any graph G, τ(G) ≤ 2ν(G)
- τ(G) = minimum edges to hit all triangles
- ν(G) = maximum edge-disjoint triangles

| Case | Status | Notes |
|------|--------|-------|
| ν = 0 | ✅ Proven | Base case |
| ν = 1 | ✅ Proven | K4 structure |
| ν = 2 | ✅ Proven | Full proof |
| ν = 3 | ✅ Proven | Parker's approach |
| **ν = 4** | 🔄 In Progress | Active attack |

---

## Repository Structure

```
math/
├── proven/                          # Verified Aristotle outputs
│   └── tuza/
│       ├── lemmas/
│       │   ├── tau_union_le_sum.lean    # Key union bound
│       │   ├── slot6_Se_lemmas.lean     # tau_S_le_2, Se structure
│       │   └── parker_lemmas.lean       # Parker infrastructure
│       ├── nu0/, nu1/, nu2/             # Base case proofs
│
├── submissions/
│   ├── nu4_portfolio/               # Active ν=4 attack files
│   │   ├── slot*_v2.lean            # Full scaffolding versions
│   │   └── slot*.lean               # Original submissions
│   ├── erdos*_SUCCESS.lean          # Erdős successes
│   ├── CORRUPTED/                   # Archived invalid files
│   └── tracking.db                  # SQLite tracking database
│
├── scripts/                         # Validation & tracking scripts
│   ├── validate_submission.sh
│   ├── pre_submit.sh
│   └── verify_output.sh
│
├── docs/                            # Documentation
├── tests/                           # Test files
└── CLAUDE.md                        # AI workflow instructions
```

---

## Database Schema

All project state tracked in `submissions/tracking.db`:

```sql
-- Key tables
submissions          -- All Aristotle jobs (86 total)
literature_lemmas    -- 87 proven lemmas for scaffolding
lemma_dependencies   -- Dependency graph
frontiers           -- Open problems being attacked
failed_approaches   -- What didn't work (avoid repeating)
```

### Quick Queries

```bash
# Running submissions
sqlite3 submissions/tracking.db "SELECT filename FROM submissions WHERE status='running';"

# Proven lemmas for scaffolding
sqlite3 submissions/tracking.db "SELECT name FROM literature_lemmas WHERE proof_status='proven';"

# Submission stats
sqlite3 submissions/tracking.db "SELECT status, COUNT(*) FROM submissions GROUP BY status;"
```

---

## Workflow

### Pre-Submission
```bash
./scripts/pre_submit.sh submissions/file.lean    # Check prior work
./scripts/validate_submission.sh submissions/file.lean  # Syntax check
```

### Submit to Aristotle
```bash
aristotle prove-from-file submissions/file.lean --no-wait
./scripts/track_submission.sh submissions/file.lean "problem_id" "pattern"
```

### Post-Result
```bash
aristotle download <UUID>
./scripts/verify_output.sh output.lean           # Validate claims
./scripts/post_result.sh <UUID> output.lean      # Update database
```

---

## Statistics

| Metric | Count |
|--------|-------|
| Total submissions | 86 |
| Completed | 38 |
| Running | 12 |
| Proven lemmas | 87 |
| Erdős problems solved | 3 |

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Tuza's Conjecture**: Tuza (1981), "A conjecture on triangles of graphs"
- **Parker's Proof**: Parker (2024), proves ν ≤ 3 case
- **Erdős Problems**: https://erdosproblems.com
- **Lean 4**: https://lean-lang.org

---

## License

Research project - see individual files for licensing.
