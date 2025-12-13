# Unified Open Problems Database
## For Aristotle Submission Pipeline

Generated: December 13, 2025

---

## Database Overview

| Source | Total | Open | Open + Lean 4 |
|--------|-------|------|---------------|
| **Erdős Problems** (Tao repo) | 1,111 | 640 | **195** ⭐ |
| **Formal Conjectures** (DeepMind) | 448 | ~400 | **448** |
| | | | |
| **Wikipedia Conjectures** | 88 | ~80 | 88 |
| **arXiv Problems** | 11 | ~10 | 11 |
| **Green's Open Problems** | 2 | 2 | 2 |

### Key Insight

**195 Erdős problems are OPEN + have pre-formalized Lean 4 statements ready for Aristotle.**

Boris Alexeev solved Erdős #124 from this exact pool. We have 194 more to try.

---

## Database Files

| File | Contents |
|------|----------|
| `unified_problems_database.json` | Complete database (1,500+ problems) |
| `top_50_candidates.json` | Top 50 by tractability score |
| `top_candidates.csv` | Spreadsheet-friendly format |
| `erdosproblems/` | Terence Tao's YAML database |
| `formal-conjectures/` | DeepMind's Lean 4 formalizations |

---

## Top 20 Candidates (Erdős + Lean 4)

| Rank | Problem | Score | Prize | Tags |
|------|---------|-------|-------|------|
| 1 | **#1** | 100 | $500 | additive combinatorics |
| 2 | **#9** | 100 | - | additive basis, primes |
| 3 | **#10** | 100 | - | additive basis, primes |
| 4 | **#14** | 100 | - | sidon sets |
| 5 | **#20** | 100 | $1000 | combinatorics (Sunflower!) |
| 6 | **#30** | 100 | $1000 | sidon sets |
| 7 | **#33** | 100 | - | additive basis |
| 8 | **#36** | 100 | - | additive combinatorics |
| 9 | **#39** | 100 | $500 | sidon sets |
| 10 | **#41** | 100 | $500 | sidon sets |
| 11 | **#42** | 100 | - | sidon sets |
| 12 | **#44** | 100 | - | sidon sets |
| 13 | **#51** | 100 | - | number theory |
| 14 | **#61** | 100 | - | graph theory (Erdős-Hajnal!) |
| 15 | **#68** | 100 | - | irrationality |
| 16 | **#89** | 100 | $500 | geometry, distances |
| 17 | **#90** | 100 | $500 | geometry, distances |
| 18 | **#92** | 100 | $500 | geometry, distances |
| 19 | **#108** | 100 | - | graph theory, chromatic |
| 20 | **#125** | 100 | - | base representations |

---

## Problem Categories

### By Domain (Open + Lean 4)

| Domain | Count | Notes |
|--------|-------|-------|
| **Sidon sets** | ~30 | Highly tractable, bounded |
| **Additive combinatorics** | ~40 | Boris pattern territory |
| **Graph theory** | ~25 | Erdős-Hajnal, chromatic |
| **Geometry/distances** | ~15 | Unit distance problems |
| **Number theory** | ~50 | Mixed tractability |
| **Primes** | ~20 | Often intractable |

### By Prize (Open + Lean 4)

| Prize | Count | Notes |
|-------|-------|-------|
| No prize | ~120 | Often more tractable |
| $100-$500 | ~50 | Medium difficulty |
| $1000+ | ~25 | Harder problems |

---

## Submission Strategy

### Phase 1: Quick Wins (This Week)

Submit 10-15 problems with:
- Sidon set problems (#14, #39, #41, #42, #44)
- Additive basis problems (#9, #10, #33)
- Graph theory bounded cases (#61, #108)

### Phase 2: Deep Exploration

- Cross-reference with OEIS for bounded parameters
- Check recent arXiv for "almost solved" problems
- Focus on problems with recent partial progress

### Phase 3: High-Value Targets

- Erdős #20 (Sunflower) - recent progress by Alweiss et al.
- Erdős #61 (Erdős-Hajnal) - active research area
- Distance geometry problems

---

## How to Submit

Each Lean file in `formal-conjectures/FormalConjectures/ErdosProblems/` can be submitted directly:

```bash
# Example: Submit Erdős #61
python3 scripts/safe_aristotle_submit.py \
  problem-databases/formal-conjectures/FormalConjectures/ErdosProblems/61.lean \
  erdos_61_project_id.txt \
  "Erdős Problem 61 - Erdős-Hajnal Conjecture"
```

**Key**: The Lean files have `sorry` placeholders - Aristotle fills these in!

---

## Tractability Scoring

Current heuristic (v1):
- +30: Has Lean 4 file
- +10: Has OEIS sequence (bounded)
- +5: Combinatorics/graph theory tags
- -10: Prime-related (often intractable)
- -15: High prize ($5000+)

### Improvements Needed

- [ ] Check recent arXiv for partial progress
- [ ] Cross-reference with Mathlib coverage
- [ ] Add "bounded parameter" detection
- [ ] Include problem statement complexity

---

## Files Structure

```
problem-databases/
├── unified_problems_database.json    # Master database
├── top_50_candidates.json            # Best candidates
├── top_candidates.csv                # Spreadsheet view
├── build_unified_database.py         # Builder script
├── UNIFIED_DATABASE_SUMMARY.md       # This file
├── erdosproblems/                    # Tao's YAML data
│   └── data/problems.yaml
└── formal-conjectures/               # DeepMind Lean 4
    └── FormalConjectures/
        ├── ErdosProblems/            # 261 Erdős files
        ├── Wikipedia/                # 88 Wikipedia conjectures
        ├── Arxiv/                    # 11 arXiv problems
        └── ...
```

---

## Next Steps

1. **Verify open status** of top 20 candidates
2. **Submit batch** of 10 sidon set problems (most tractable)
3. **Monitor results** from current 5 submissions
4. **Iterate** based on what works

---

## Reference: Boris's Success (Erdős #124)

Boris Alexeev's approach:
1. Found Erdős #124 (open since 1979)
2. Submitted formal statement to Aristotle
3. **Went to bed** (zero intervention)
4. Woke up → **SOLVED**

We have **194 more** problems in the same format. The pipeline is ready.
