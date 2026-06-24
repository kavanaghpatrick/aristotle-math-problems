# E944 — Adversarial review of wall's Circulant Uniqueness Lemma (skeptic)

wall requested adversarial review of wall_uniqueness_lemma.md (3 specific attack points). All three
adjudicated with my own independent code. VERDICT: the file is HONEST and holds up; nothing to retract.

## 1. LEMMA A ({1,2}⊆S ⟹ C_n(S)−0 uniquely 3-colorable) — CONFIRMED
Independently counted proper 3-colorings of G−0 (my own backtracking counter) for every GENUINELY
4-vertex-critical circulant with {1,2}⊆S, n=13..31 (19 cases): EXACTLY 6 colorings each (= unique up
to the 3! color permutation). The triangle-chain induction is sound.
- SCOPE EXPANSION (correction in wall's favor): the forcing holds for ANY graph with {1,2}⊆S, not just
  4-vc ones — the 3-periodicity is forced whenever a proper 3-coloring of G−0 exists at all.
- Self-correction note: my FIRST test mistakenly counted colorings on χ=4-but-NOT-vertex-critical
  circulants (where vertex 0 isn't critical ⟹ G−0 not 3-colorable ⟹ 0 colorings). Those are outside
  Lemma A's scope; not counterexamples. Caught and fixed; final result clean.

## 2. MULTIPLIER-ISOMORPHISM step (v↦tv : C_n(S) ≅ C_n(t·S), gcd(t,n)=1, fixing 0) — CONFIRMED
200 random trials (varied n∈{13..31}, t coprime, random 3-element S): the explicit relabeling v↦tv
maps edge sets EXACTLY onto C_n(t·S reduced into [1,n/2]). The 68/112 multiplier coverage is sound.

## 3. AFFINE THEOREM + n≡1 mod 3 — break-test n=28..32, both HELD (no break beyond wall's n≤27)
Tried to BREAK both on cases wall didn't reach (n=28..34; n=33,34 timed out on the heavy 4-vc screen,
n≤32 decisive):
- **n≡1 mod 3 necessary condition: HOLDS.** n=28 (30 four-vc circulant distance-sets) and n=31 (120)
  are both ≡1 mod 3. The strong falsification check: n=29, 30, 32 (all ≢1 mod 3) have ZERO 4-vc
  6-regular circulants — exactly as wall's equal-class-size argument predicts. No counterexample.
- **Affine Coloring Theorem: HELD.** Every 4-vc 6-reg circulant at n=28..32 has a coprime s*∈S whose
  residue-mod-3 affine coloring is proper. No break. Extends wall's n≤27 to n≤32.

## ⚠ UPDATE (2026-06-10) — UNIQUENESS LEMMA RETRACTED BY WALL, skeptic-CONFIRMED
wall retracted the uniqueness lemma: it is FALSE. Counterexamples (dual-checker verified by skeptic):
C₃₁(1,4,6) and C₃₁(5,6,7) are 4-vc, 6-regular, triangle-free circulants whose G−0 has **12 proper
3-colorings** (>6) — NON-uniquely 3-colorable. Uniqueness held ≤ n=27, broke at n=31 (the n≥31 rule).
So "uniqueness ⟹ one critical orbit ⟹ no circulant witness" is DEAD.

SELF-CORRECTION (skeptic): my "affine theorem HELD to n≤32" (below) was IMPRECISE. I tested only
affine-EXISTENCE (a proper coprime-s* residue coloring EXISTS — true at n≤32, incl. both n=31
counterexamples, s*=4 and s*=5). I did NOT test affine-UNIQUENESS (that it is the ONLY coloring) — which
is exactly what breaks at n=31. The n≡1 mod 3 necessary condition is UNAFFECTED (separate claim, n=31≡1,
still held n≤32). SAFETY: both counterexamples have 62 critical edges (=2n), NOT 0 — uniqueness-failure
did NOT produce a witness; "no circulant witness" conclusion survives, only the proof method dies.
DURABLE SURVIVOR: Lemma A ({1,2}⊆S ⟹ uniquely 3-col), still rigorously true (skeptic-confirmed n≤31).

## VERDICT (now partly superseded — see UPDATE above)
At review time the labels looked accurate; the n=31 stress test showed the "VERIFIED" items were small-n
artifacts. Lesson: "verified to n≤27" is NOT "true." Original labels:
- PROVEN (rigorous, n-uniform): Lemma A + multiplier coverage = 68/112. Independently confirmed — STILL STANDS.
- ~~VERIFIED (not derived) n≤32: affine closed form + n≡1 mod 3~~ → affine-UNIQUENESS RETRACTED (false n=31);
  affine-EXISTENCE + n≡1 mod 3 still held n≤32.
- ~~OPEN sub-lemma (rotational unique coloring)~~ → MOOT: the uniqueness it assumed is false.

## Literature note (wall's question 3)
No published characterization of uniquely-3-colorable circulants over ℤ_n found (web tooling erroring).
Greenwell–Lovász (uniquely k-col ⟹ (k−1)-connected + two-color-class unions connected = Kempe
connectivity) is the closest general frame, which wall already uses. wall's affine closed form may be a
new structural statement in its own right.
