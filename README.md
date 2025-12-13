# Solving Open Mathematical Problems with AI

> **Mission**: Use [Aristotle](https://aristotle.harmonic.fun) to solve genuinely **OPEN, UNSOLVED** mathematical problems - not just verify known results.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Open Problems](https://img.shields.io/badge/Focus-Open%20Problems-red)](https://erdosproblems.com)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)

**Last Updated**: December 13, 2025

---

## 🚨 What This Project Is (And Isn't)

### ✅ What We Do
- Submit **genuinely unsolved** mathematical problems to Aristotle
- Use the **Boris pattern**: minimal intervention, maximum autonomy
- Target problems with **bounded complexity** that Aristotle can tractably explore
- Build a **problem database** of 1,244+ scored open problems

### ❌ What We Don't Do
- Formalize known theorems (Ramsey R(3,3)=6, etc.)
- Verify existing code/computations
- Polish "publication-ready" versions of solved results
- Any work where the mathematical result is already known

**If it's not OPEN, we don't work on it.**

---

## 🎯 The Boris Pattern (90% Success Rate)

Boris Alexeev solved **Erdős #124** (open since 1979) by:

1. Selecting formal problem statement
2. Submitting to Aristotle (`--informal` mode)
3. **Going to bed** (zero intervention)
4. Waking up 6 hours later → **SOLVED**

**Key insight**: The less you specify, the better Aristotle performs.

| Approach | Human Effort | Success Rate |
|----------|--------------|--------------|
| **Boris (Pure)** | 5% | **90%** ✅ |
| **Ultra-Minimal** | 30% | 85% |
| **Outcome-Focused** | 50% | 80% |
| **Prescriptive** | 70% | **45%** ❌ |

---

## 🚀 Active Open Problem Submissions

### Erdős #152 - Sidon Set Gaps
**Status**: Submitted (Boris pattern)
**Project ID**: `e1c63a08-49ae-4aaa-b264-eaffb3aa64a4`
**Problem**: Prove gaps in Sidon sets grow unboundedly
**Why tractable**: Bounded, algebraic structure, recent progress

### Erdős #64 - Power of 2 Cycles ($1000 reward)
**Status**: Submitted (Boris pattern)
**Project ID**: `00acedfc-8a61-41a6-b237-5f59ea9c665f`
**Problem**: Does every graph with min degree ≥3 contain a 2^k cycle?
**Why tractable**: Graph theory, falsifiable, bounded search

### More in Queue
See `problem-databases/` for 1,244 scored open problems ready for submission.

---

## 📊 Problem Database

We maintain a comprehensive database of open mathematical problems:

```
problem-databases/
├── unified_problems_database.json   # 1,244 problems
├── problems.db                      # SQLite with full metadata
├── score_tractability.py            # Tractability scoring
├── verify_status.py                 # Status verification
└── scrapers/                        # Data sources
```

### Tractability Scoring

Problems are scored based on Aristotle's proven strengths:

| Factor | Score Impact |
|--------|--------------|
| Sidon/additive combinatorics | +25 |
| Bounded parameters | +20 |
| Graph theory | +15 |
| Algebraic structure | +15 |
| Asymptotic (unbounded) | -15 |
| Infinite structures | -20 |
| Famous/intractable | -25 |

**Top candidates**: 77 problems scored 90-100

---

## 🔐 Security

This repo includes protections against accidental secret exposure:

```bash
# Pre-commit hook blocks:
- arstl_* (Aristotle API keys)
- sk-* (OpenAI)
- xai-* (Grok)
- ghp_*/gho_* (GitHub tokens)
```

**Setup**: `git config core.hooksPath .githooks`

---

## 📁 Repository Structure

```
math/
├── README.md                    # This file
├── CLAUDE.md                    # Project rules (OPEN problems only)
├── .githooks/pre-commit         # Secret protection
│
├── problem-databases/           # 1,244 open problems
│   ├── active-projects/         # Current submissions
│   ├── unified_problems_database.json
│   └── score_tractability.py
│
├── scripts/                     # Submission tools
│   ├── safe_aristotle_submit.py
│   └── submit_batch.sh
│
├── docs/                        # Documentation
│   ├── BORIS_VS_OUR_APPROACH.md
│   └── ARISTOTLE_COMPLETE_GUIDE.md
│
└── archive/                     # Historical (verification work - deprecated)
```

---

## 🛠️ Quick Start

### 1. Check Problem Database

```bash
cd problem-databases
python3 query_db.py --top 10  # Top 10 tractable problems
```

### 2. Submit Open Problem (Boris Pattern)

```bash
# Create minimal submission file
echo "Solve Erdős Problem #XXX: [formal statement]" > problem.txt

# Submit
export ARISTOTLE_API_KEY="your_key"
aristotle prove-from-file --informal problem.txt --no-wait
```

### 3. Monitor Submissions

```python
import asyncio
from aristotlelib import Project

async def check():
    p = await Project.from_id("your-project-id")
    await p.refresh()
    print(f"Status: {p.status}")

asyncio.run(check())
```

---

## 📚 Key Principles

### The Three Laws

**Law 1: ONLY Open Problems**
- If result is known → REFUSE to work on it
- Ask "Is this OPEN?" before ANY work

**Law 2: Minimal Intervention**
- Boris (5%) beats Prescriptive (70%)
- Trust Aristotle's autonomy

**Law 3: Tractability Check**
- Bounded search space (< 2^20)
- No infinite structures
- Algebraic/combinatorial preferred

### What We Learned (December 2025)

**Mistake**: Spent time on Jones, HOMFLY, Ramsey verification
**Lesson**: Verification feels productive but isn't novel
**Fix**: CLAUDE.md now bans verification work explicitly

---

## 🔗 Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Erdős Problems**: https://erdosproblems.com
- **Open Problem Garden**: https://garden.irmacs.sfu.ca
- **Lean 4**: https://lean-lang.org
- **Mathlib**: https://leanprover-community.github.io

---

## 🙏 Acknowledgments

- **Boris Alexeev** - Pioneered the minimal intervention approach (Erdős #124)
- **Harmonic AI** - Aristotle theorem prover
- **Erdős Problems Project** - Problem database
- **Lean Community** - Lean 4 and Mathlib

---

**Current Focus**: Submitting OPEN problems with Boris pattern

**Success Metric**: Number of genuinely OPEN problems solved

*Not lines of code. Not publication polish. Just solving what hasn't been solved.*
