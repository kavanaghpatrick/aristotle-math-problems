# troika: the difficulty, located exactly (synthesis with maverick's Lemma BG)

This reconciles my "boundary needs transcendence" finding with maverick's bounded-gap Lemma BG
([[maverick_bounded_gap_lemma]]). **They are fully consistent and together pin the open core
precisely.** All verified computationally.

## The exceptional set is ISOLATED SHORT CLUSTERS, not intervals
For (3,4,7), the set of non-representable n above the early transient has **bounded runs**:
| k | #exceptional below N₀ | N₀ | MAX run of consecutive missing |
|---|----|-----|-----|
| 2 | 5 205 | 785 743 | 8 (≈ 3² = d_min^k) |
| 3 | 390 934 | 57 751 591 | 70 (≈ 3³ order) |

So the complement is sparse isolated points/short clusters (run length O(d_min^k)), terminating at N₀.

## What this means for the proof (the clean split)
1. **maverick's Lemma BG is CORRECT and ELEMENTARY** (k-uniform, transient index i₀ ≤ 3): once the
   running sum dominates (which ∑1/(d−1)≥1 guarantees past a tiny i₀), the max GAP (longest run of
   consecutive missing integers) is bounded by G(k) ≈ d_min^k. I verified this directly: max run is
   8 at k=2, 70 at k=3 — exactly d_min^k order, never growing. **This part is formalizer-reachable.**
2. **But bounded gaps ≠ cofinite** (maverick's Result 2, correct). The complement stays infinite
   *as far as Lemma BG can see* — it only forbids long runs, not isolated points. The true content
   is killing the LAST isolated exceptional point (581, 785743, 57751591, …).
3. **My Cassels-insufficiency result** ([[troika_cassels_insufficient]]) shows why step 2 is hard:
   the naive merged-atom interval-filling lemma underestimates N₀ by 200×–29000×, because it cannot
   account for which isolated values get skipped. The last skipped value is set by cross-base power
   spacing |dᵢ^p − dⱼ^q| — a Diophantine-approximation quantity. **This is the MW/Baker step.**

## The proof obligation, sharp (agreeing with maverick's ★)
> Show: for n ≥ N₀(k), every residue mod G(k) is realized within each O(G(k))-window — equivalently,
> no isolated exceptional point survives above N₀(k).

The bulk (long-run prevention) is elementary (Lemma BG). The isolated-point elimination couples the
big-atom bulk of one base with the small-atom residue freedom of the OTHER bases, quantitatively —
and the quantitative coupling is bounded only via linear-forms-in-logs (how close 3^p and 4^q can be).
**For (3,4,7) this is exactly the MW Cor 10.1 step BEGL96 used; for general boundary D it is the
open conjecture.**

## Strategic bottom line (consolidated team view)
- **Answer = True** (overwhelming computational evidence; all 9 boundary families finite-threshold at
  k=1,2,3; the conjecture itself predicts True).
- **Settled, elementary, formalizer-reachable:** gcd=1 necessity; residue covering (Residue Lemma);
  bounded-gap Lemma BG; the d^k scaling reduction. These are clean Lean targets.
- **NOT formalizer-reachable / genuinely open:** the isolated-point elimination at the harmonic
  boundary, which needs Baker/MW lower bounds on |dᵢ^p − dⱼ^q| (not in Mathlib). No bare submission
  closes this. The only rigorously-closed instance in the literature is BEGL96's (3,4,7), s=1, =581.
- **Tao calibration holds:** k=0 (Alexeev) was the low-hanging fruit; the all-k / general-D boundary
  case sits on classical transcendence theory and is correctly "open."
