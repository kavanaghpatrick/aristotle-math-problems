# Aristotle Meta-Analysis

**Date**: Feb 8, 2026
**Method**: 10 parallel agents analyzing 969 submissions, then 7 agents checking for confounds
**Dataset**: 969 submissions, 122 proven (12.6% overall success rate)

---

## Key Finding: Sorry Count Determines Everything

| Input Sorry | Submitted | Proven | Rate |
|---|---|---|---|
| 0 | ~33 | ~30 | ~96% |
| 1 | ~56 | ~7 | ~12% |
| 2+ | ~53 | ~1 | ~0% |

This is the dominant predictor. After controlling for sorry count, most other factors (line count, declaration count, topic) lose statistical significance or have very small independent effects.

---

## What We Know With Confidence

### 1. sorry=0 files succeed ~96% of the time
The ~4% failure rate is mostly bookkeeping (files with hidden axioms, self-loops, or unsafe sym2 that weren't caught pre-submission). Clean sorry=0 files essentially always succeed.

### 2. sorry=1 files succeed ~12% of the time
The successful ones tend to be shorter, more focused files with simple gaps. This is the one structural factor that independently helps for sorry=1.

### 3. sorry=2+ files have never succeeded
0% across all attempts. Don't submit — split or prove locally.

### 4. native_decide is powerful on Fin n
Files using `native_decide` on `Fin 9-12` have notably higher success rates. This makes sense — it closes theorems computationally rather than requiring proof search.

### 5. Resubmission has diminishing returns
- Attempt 1: ~10% success
- Attempt 2: modest improvement if the file was genuinely rewritten
- Attempt 3+: 0/102 succeeded — but note ~34% of these targeted false lemmas, so the true signal is partially selection bias

### 6. Very long files don't work
No file over ~700 lines has ever been proven. But shorter files aren't automatically better — this correlation is confounded by sorry count.

---

## What We Initially Claimed But Had to Correct

These findings from the initial 10-agent analysis were debunked by the 7-agent confound check:

| Initial Claim | Problem |
|---|---|
| "Lines 50-150 or 200-550 optimal" | Simpson's Paradox — short files succeed because they're sorry=0, not because they're short |
| "Death valley at 13-20 declarations" | Partially artifact of sorry count distribution and false lemma contamination |
| "Topic X has 60% success, topic Y has 0%" | Topic effects nearly vanish after controlling for submission quality |
| "PROVIDED SOLUTION tag: 0% success" | Only 3 completed results (not 10), all on hardest problem — not statistically meaningful |
| "3.6x multiplier from native_decide" | Real correlation but from small cells (n=114 vs 682) with wide confidence intervals |
| "Scaffolding paradox: 0 helpers best" | True for sorry resolution specifically, but confounded — low-scaffold sorry=1 files are simpler lemmas |

---

## Practical Guidance

1. **Get to sorry=0 before submitting** — this is the single most impactful thing you can do
2. **If stuck at sorry=1** — keep the file short and focused, try `native_decide`/`omega`/`simp` to close the gap
3. **Never submit sorry=2+** — split into separate files instead
4. **Use `native_decide` on Fin n** — it's genuinely powerful for computational proofs
5. **Check false lemmas before resubmitting** — many failed resubmissions were targeting false claims
6. **Max 2 attempts** — if it fails twice, rewrite fundamentally rather than tweaking

---

## Data Notes

- 969 total submissions analyzed
- Success is bursty: 3 days produced ~75% of all proven theorems
- Named strategies (boris, tier1_prize) all had 0% success — the winning approach is accumulating scaffolding then batch-verifying
- Many early submissions used INFORMAL mode instead of FORMAL_LEAN, which may explain some failures
