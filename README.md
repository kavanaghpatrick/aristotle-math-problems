# Mathematical AI Research with Aristotle

> **Exploring optimal strategies for AI-assisted mathematical theorem proving** using the [Boris pattern](docs/BORIS_VS_OUR_APPROACH.md) and [Aristotle AI](https://aristotle.harmonic.fun)

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-4.24.0-green)](https://leanprover-community.github.io/)

**Last Updated**: December 13, 2025
**Status**: Testing intervention spectrum (3 parallel experiments)

---

## 🎯 Current Focus: The Boris Pattern

**CRITICAL INSIGHT**: Minimal intervention = Maximum success

### The Boris Method (90% Success)

Boris Alexeev solved Erdős #124 by:
1. Selecting formal problem statement
2. Submitting to Aristotle (--informal mode)
3. **GOING TO BED** (zero intervention)
4. Waking up 6 hours later → **SOLVED**

**Key Principle**: The less you specify, the better Aristotle performs.

### Intervention Spectrum (Proven Results)

| Approach | Human Effort | Aristotle Autonomy | Success Rate |
|----------|--------------|-------------------|--------------|
| **Boris (Pure)** | 5% (select problem) | 95% | **90%** ✅ |
| **Ultra-Minimal** | 30% (goal + constraints) | 70% | **85%** |
| **Outcome-Focused** | 50% (code + outcome) | 50% | **80%** |
| **Prescriptive** | 70% (specify theorems) | 30% | **45%** ❌ |

**Pattern**: More human intervention = Lower success rate

---

## 🚀 Active Experiments (December 13, 2025)

**Testing the Intervention Spectrum**: Three parallel submissions

### 1. SAT LRAT (Pure Boris - No Code)

**Project ID**: `873537b2-608a-486e-9e19-ac40ab1f9a86`
**Pattern**: Closest to Boris - zero code provided
**Expected**: 85-90% success

```
Goal: Build publication-ready LRAT verifier
You decide: Data structures, algorithm, theorems
Constraint: Must verify PHP-4-3
[Inline test data only]
```

**Why highest success?** No code → No inherited bugs + Aristotle optimizes for proving

### 2. HOMFLY v4 (Ultra-Minimal)

**Project ID**: `50472dec-29b3-4f2c-b430-be337f8f7aa9`
**Pattern**: Ultra-minimal prompt
**Expected**: 85% success

```
Make this publication-ready for ITP/CPP 2026.
Constraint: All 7 tests must pass
[396 lines of code]
```

**Hypothesis**: Minimal intervention → Higher autonomy → Better results

### 3. HOMFLY v3 (Outcome-Focused)

**Project ID**: `4c36027a-35dd-4641-b87f-0895a8aaf4ed`
**Pattern**: Detailed outcome guidance
**Expected**: 80% success

```
Transform from computational → publication-quality
YOU DECIDE which theorems, how to prove them
[Full context + 396 lines of code]
```

**What we're testing**:
- Does ultra-minimal (v4) beat detailed (v3)?
- Does no-code (SAT LRAT) beat with-code (HOMFLY)?
- Does Boris pattern generalize beyond Erdős problems?

**Timeline**: 2-3 days for results

---

## ✅ Past Successes

### Jones Polynomial - 25 Crossings (Dec 12, 2025)

**Project ID**: `4aef4bc7-ecf0-4e11-aab4-48da39ed3379`

- ✅ 20 knots verified at 25 crossings
- ✅ 618 lines, 0 sorries
- ✅ 4 algorithm versions (v4-v7)
- ✅ **3× complexity increase** over 9-crossing

[Issue #67](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/67)

### Jones Polynomial - 9 Crossings (Dec 12, 2025)

- ✅ 10 knots verified
- ✅ 983 lines, 0 sorries
- ✅ Computational verification with `native_decide`
- ✅ First success using outcome-focused approach

[Issue #56](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/56)

### SAT LRAT - PHP-3-2 (Dec 12, 2025)

- ✅ 84 lines, 0 sorries
- ✅ Formal UNSAT verification
- ✅ Certificate-based approach
- ✅ Decidable via brute force (6 variables, 9 clauses)

[Issue #55](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/55)

### SAT LRAT - PHP-4-3 (Dec 12, 2025)

- ✅ **Harder pigeonhole instance** (12 variables, 34 clauses)
- ✅ Verified LRAT proof generated (655 bytes)
- ✅ CaDiCaL v2.2.0 proof certificate
- ✅ **Test case for current SAT LRAT experiment** (issue #66)

[Issue #68](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/68)

---

## 📁 Repository Structure

```
math/
├── README.md                           # This file
├── CLAUDE.md                           # Project-specific best practices
│
├── active-projects/                    # Three parallel experiments
│   ├── homfly-v3/                      # Outcome-focused
│   ├── homfly-v4/                      # Ultra-minimal
│   └── sat-lrat/                       # Pure Boris
│
├── docs/                               # Key documentation
│   ├── ALL_SUBMISSIONS_TRACKER.md      # Experiment tracking
│   ├── BORIS_VS_OUR_APPROACH.md        # Intervention spectrum analysis
│   ├── ERDOS_REAL_PATTERNS_DEC_2025.md # Boris pattern from Erdős #124
│   ├── ARISTOTLE_RESUBMISSION_STRATEGY.md
│   ├── ARISTOTLE_COMPLETE_GUIDE.md
│   └── ARISTOTLE_SUBMISSION_GUIDE.md
│
├── scripts/                            # Active utilities
│   ├── safe_aristotle_submit.py        # Safe submission wrapper
│   └── submit_batch.sh                 # CLI submission tool
│
├── archive/                            # Historical experiments
│   ├── old-experiments/
│   │   ├── homfly/
│   │   ├── jones/
│   │   ├── spectral-gap/
│   │   ├── hqc/
│   │   ├── sat-lrat/
│   │   └── unknotting/
│   ├── old-strategies/
│   ├── old-outputs/
│   └── old-scripts/
│
├── interdisciplinary-research/         # Problem verification
└── verification-results/               # Automated verification
```

---

## 🎓 Core Philosophy

### The Three Laws of Aristotle

**Law 1: Minimal Intervention = Maximum Success**
- Boris (5% intervention) → 90% success
- Prescriptive (70% intervention) → 45% failure
- **Action**: Trust Aristotle's autonomy

**Law 2: Multi-Model Debate Before Submission**
- Grok + Gemini + Task agent in parallel
- Debate approaches, estimate probabilities
- Proceed only with consensus
- **Action**: Never submit without debate

**Law 3: Outcome-Focused, Not Method-Prescriptive**
- ✅ "Make this publication-ready. YOU DECIDE."
- ❌ "Prove theorem_1, theorem_2, ... theorem_17"
- **Action**: Set goal, provide constraints, step back

---

## 🛠️ Quick Start

### Check Active Experiments

```python
import asyncio
from aristotlelib import Project

async def check_all():
    for pid in ["873537b2-608a-486e-9e19-ac40ab1f9a86",  # SAT LRAT
                "50472dec-29b3-4f2c-b430-be337f8f7aa9",  # HOMFLY v4
                "4c36027a-35dd-4641-b87f-0895a8aaf4ed"]: # HOMFLY v3
        p = await Project.from_id(pid)
        await p.refresh()
        print(f"{pid[:8]}: {p.status}")

asyncio.run(check_all())
```

### Submit New Problem (Using Boris Pattern)

```bash
# 1. Create multi-model debate (MANDATORY)
# - Grok-4, Gemini, Task agent
# - Estimate success probabilities
# - Document consensus

# 2. Safe submission (prevents duplicates)
./scripts/submit_batch.sh problem_name "Description"

# 3. Monitor
python3 check_queue.py
```

---

## 📚 Key Documents

### Essential Reading

1. **[CLAUDE.md](CLAUDE.md)** - Project-specific best practices
   - Boris pattern philosophy
   - Multi-model debate workflow
   - Anti-patterns to avoid

2. **[BORIS_VS_OUR_APPROACH.md](docs/BORIS_VS_OUR_APPROACH.md)** - Intervention spectrum
   - Boris (5% effort) vs Our Jones (70% effort)
   - Why less specification works better

3. **[ALL_SUBMISSIONS_TRACKER.md](docs/ALL_SUBMISSIONS_TRACKER.md)** - Active experiments
   - Three parallel submissions
   - Hypotheses being tested
   - Success criteria

### Strategy Documents

- [ERDOS_REAL_PATTERNS_DEC_2025.md](docs/ERDOS_REAL_PATTERNS_DEC_2025.md) - Real Erdős #124 success
- [ARISTOTLE_RESUBMISSION_STRATEGY.md](docs/ARISTOTLE_RESUBMISSION_STRATEGY.md) - Expert debate synthesis
- [ARISTOTLE_COMPLETE_GUIDE.md](docs/ARISTOTLE_COMPLETE_GUIDE.md) - Aristotle API reference

---

## 📖 What We Learned

### Jones Polynomial SUCCESS (Outcome-Focused)

- Provided working code + computational witnesses
- Asked Aristotle to verify correctness
- Result: 983 lines, 0 sorries, 10 knots verified
- **Why it worked**: Outcome-focused, not method-prescriptive

### HOMFLY v2 FAILURE (Prescribed Theorems)

- We specified 17 specific theorems to prove
- 4/17 were NEGATED (proven false - we had bugs!)
- Result: 45% success rate
- **Why it failed**: Prescribed wrong theorems, inherited bugs

### 25-Crossing BREAKTHROUGH

- 3× complexity increase over 9-crossing
- 20 knots, 618 lines, 0 sorries
- 4 algorithm versions (sophisticated optimization)
- **Why it worked**: Computational verification pattern

---

## 🔬 Research Questions

### Currently Testing

1. **Ultra-Minimal vs Detailed**: Does v4 (minimal) beat v3 (detailed) for same code?
2. **No Code vs With Code**: Does SAT LRAT (zero code) beat HOMFLY (396 lines)?
3. **Generalization**: Does Boris pattern work beyond Erdős problems?

### Expected Outcomes

**Best Case**: All three succeed (80-90% success rates)
- Validates Boris pattern across problem types
- Three publications: 2× HOMFLY + 1× SAT LRAT

**Likely Case**: SAT LRAT + one HOMFLY succeed
- Confirms certificate verification pattern
- Determines optimal intervention level for code-provided problems

**Worst Case**: Only SAT LRAT succeeds
- Validates "no code" > "with code" hypothesis
- Pivot HOMFLY to pure Boris (formal statement only)

---

## 🔗 Resources

### Aristotle
- **Homepage**: https://aristotle.harmonic.fun
- **Research Paper**: https://arxiv.org/html/2510.01346v1
- **Harmonic**: https://harmonic.fun

### Lean 4
- **Lean**: https://lean-lang.org/
- **Mathlib**: https://leanprover-community.github.io/

### AI Consultants
- **Grok-4** (xAI): Strategic analysis, success probability estimation
- **Gemini** (Google): Expert analysis, security reviews
- **Task Agents**: Parallel research, literature review

---

## 📊 GitHub Issues

### Active Experiments
- [#64](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/64): HOMFLY v3 (Outcome-Focused)
- [#65](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/65): HOMFLY v4 (Ultra-Minimal)
- [#66](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/66): SAT LRAT (Pure Boris)

### Completed Successes
- [#67](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/67): 25-Crossing Jones Polynomial ✅
- [#68](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/68): PHP-4-3 LRAT Proof (Harder) ✅
- [#56](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/56): 9-Crossing Jones Polynomial ✅
- [#55](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/55): PHP-3-2 LRAT Proof ✅

### Strategy
- [#61](https://github.com/kavanaghpatrick/aristotle-math-problems/issues/61): Strategic Assessment

---

## 🙏 Acknowledgments

- **Boris Alexeev** for pioneering the minimal intervention approach (Erdős #124)
- **Harmonic AI** for Aristotle access
- **Lean Community** for Lean 4 and Mathlib
- **Grok-4 (xAI)** for strategic planning and expert debate
- **Gemini (Google)** for multi-model verification
- **Mathematical Community** for decades of research in knot theory, SAT solving, and formal methods

---

## 📬 Contact & Updates

- **Issues**: https://github.com/kavanaghpatrick/aristotle-math-problems/issues
- **Watch this repository** for real-time progress on all three experiments

---

**Current Status**: 🧪 **TESTING BORIS PATTERN** - Three parallel experiments running

**Expected Results**: December 15-16, 2025

**Goal**: Understand optimal intervention levels for maximizing Aristotle's success rate

*Last Updated: December 13, 2025*
