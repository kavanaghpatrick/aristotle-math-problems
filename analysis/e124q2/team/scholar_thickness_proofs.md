# Thickness theory: Newhouse + Astels PROOFS, and the EXACT match to ∑1/(d−1)≥1

**Author:** scholar. **Purpose:** give the three attackers (maverick/cassels/density) the actual
proof MECHANICS of continuous thickness theory to port to ℤ. **★ HEADLINE RESULT (computed,
exact): the continuous analogue of Q2 is TRUE and the BEGL admissibility condition ∑1/(d−1)≥1 is
EXACTLY the Astels thickness threshold for the real sets K_d.** This is the continuous shadow we
are trying to discretize. Confidence: [PROOF]=mechanism given; [COMP]=I computed it exactly;
[SEC]=secondary (Newhouse/Astels statements not re-derived from their papers, but the K_d
computation IS mine and exact).

---

## 0. ★ THE MATCH (do this first — it tells us the target is real) [COMP, exact]

`K_d ⊂ ℝ` := reals in [0, 1/(d−1)] whose base-d expansion uses only digits 0,1. It is the IFS
attractor of `{x ↦ x/d, x ↦ (x+1)/d}`. This is the REAL analogue of `B_d` (our integer set).

**I computed its Newhouse thickness exactly:** the first-level decomposition is
`K_d = (1/d)K_d ∪ (1/d)(K_d+1)`, giving two congruent pieces
`A = [0, 1/(d(d−1))]` and `B = [1/d, 1/(d−1)]`. The gap between them is
`G = 1/d − 1/(d(d−1)) = (d−2)/(d(d−1))`, each adjacent bridge has length `1/(d(d−1))`. Self-similarity
makes this the worst ratio, so

> **τ(K_d) = 1/(d − 2)**   for d ≥ 3.   [COMP, exact fractions]

So `τ(K_3)=1` (middle-third-like), `τ(K_4)=1/2`, `τ(K_5)=1/3`, … decreasing.

**Newhouse pairwise (τ₁τ₂ ≥ 1) is USELESS here:** only `(3,3)` satisfies it; any distinct admissible
pair fails. We need the FINITE-SUM theory (Astels), not pairwise Newhouse.

**★ Astels' finite-sum criterion `∑_i τ_i/(τ_i+1) ≥ 1 ⟹ C_1+…+C_r ⊇ interval` becomes, for K_d:**
`τ/(τ+1) = [1/(d−2)]/[1/(d−2)+1] = 1/(d−1)`. Therefore

> **Astels condition  ∑_i τ(K_{d_i})/(τ+1) ≥ 1   ⟺   ∑_i 1/(d_i − 1) ≥ 1.**   [COMP, exact]

Verified on every team example: (3,4,7)→1, (3,4,5)→13/12, (3,5,7,13)→1, (3,4)→5/6<1 — **all match
the harmonic sum exactly.** Conclusion:

> **THEOREM (continuous shadow of Q2) [SEC: Astels 2000 + COMP].** For finite D, all d≥3, if
> ∑1/(d−1) ≥ 1 then `K_{d_1}+…+K_{d_r} ⊇ a nonempty interval` (in fact = a full interval up to its
> endpoints). The harmonic admissibility condition is PRECISELY Astels' thickness threshold.

This is why Q2 should be TRUE, and it tells us the discrete proof should be a lattice port of
Astels' gap-induction. The gcd=1 condition has NO continuous counterpart — it is the purely
arithmetic obstruction (residue coverage) that the team already proved separately (R-half); the
THICKNESS is the archimedean (A) half. **So: Astels ⊕ (residue coverage) = Q2.**

---

## 1. Newhouse thickness — definition + Gap Lemma PROOF [SEC statement, PROOF mechanism]

**Thickness.** For a Cantor set `C ⊂ ℝ` built by removing open gaps from an interval: each gap `U`
has two adjacent closed "bridges" (the components of the set's hull touching U's endpoints). Let
`B(U)` be the SHORTER adjacent bridge. Then `τ(C) := inf_U |B(U)|/|U|` over all gaps in the
construction (value independent of the exhaustion).

**Newhouse Gap Lemma.** If `τ(C₁)·τ(C₂) ≥ 1` and `C₁,C₂` are *linked* (neither lies inside a single
gap of the other, and their hulls overlap), then `C₁ ∩ C₂ ≠ ∅`.

**Corollary (sumset contains interval).** If `τ(C₁)·τ(C₂) ≥ 1` then `C₁ + C₂ ⊇` an interval.
*Reason:* `t ∈ C₁ + C₂ ⟺ C₁ ∩ (t − C₂) ≠ ∅`. Reflection preserves thickness (`τ(t−C₂)=τ(C₂)`), and
for every `t` in an explicit range `C₁` and `t−C₂` are linked; apply the Gap Lemma. So the whole
range lies in `C₁+C₂`.

**PROOF of the Gap Lemma (gap-processing induction — THE mechanism to port).**
WLOG both sets in [0,1], linked, `τ(C₁)τ(C₂) ≥ 1`. Process all gaps of BOTH sets in DECREASING
length order. Invariant maintained: the two hulls always overlap with each endpoint of one set's
current bridge "covered" by the other set.
- **Key inequality:** for any gap `U` of `Cᵢ`, the adjacent bridge of the OTHER set `C_{3−i}` that
  meets `U` has length `≥ τ(C_{3−i})·(its own adjacent gap) ≥ … ≥ |U|·τ(C₁)τ(C₂) ≥ |U|`. So a
  bridge of the opposite set facing `U` is **at least as long as `U` itself**.
- **Base:** the largest gap `U` (say of `C₁`). By linking, a bridge `Bʹ` of `C₂` meets `U`'s
  interior. Since `|Bʹ| ≥ |U|`, `Bʹ` cannot fit inside `U` — it must cover one of `U`'s endpoints.
  But `U`'s endpoints ∈ `C₁`. So `Bʹ ∩ C₁ ≠ ∅` at that endpoint → intersection point.
- **Inductive step:** assume all longer gaps processed without separating the sets. Next gap `U`
  is flanked by two bridges that (by hypothesis) already meet the opposite set. Whichever opposite
  bridge faces `U` has length `≥ |U|`, so it again covers an endpoint of `U`, which lies in the
  first set ⇒ they still intersect across `U`.
The nested, ever-finer bridges keep overlapping ⇒ `⋂ ≠ ∅`. (Strict inequality ⇒ the intersection
is itself a Cantor set of positive thickness.) ∎

> **THE LOAD-BEARING STEP TO PORT:** "a gap of width w is always spanned by a bridge of the other
> set of width ≥ w, which therefore reaches an endpoint that belongs to the first set." Discretely
> this becomes: *every integer gap of one summand is covered by a block of the other summand's
> reachable set that reaches across it.* That is the discrete gap lemma (task #15).

## 2. Astels 2000 — finite sums, normalized thickness [SEC]

Astels (Trans. AMS 352 (2000) 133–170, "Cantor sets and numbers with restricted partial quotients")
replaces τ by a **normalized thickness** that is well-behaved under repeated Minkowski sums and gives
an EXACT (sharp) threshold for finitely many summands. The clean usable form:

> **Astels finite-sum criterion.** For Cantor sets `C_1,…,C_r`, if
> `∑_{i=1}^r τ(C_i)/(1+τ(C_i)) ≥ 1`, then `C_1+…+C_r` contains an interval. Sharp; attained by
> self-similar sets; any finite r. (Newhouse is the r=2 special case in disguise.)

Mechanism: an inductive refined Gap Lemma where the normalized parameter `τ/(1+τ)` is ADDITIVE
across summands (it measures the fraction of a gap one summand's bridges can "fill"); when the
fractions sum to ≥1, the gaps are collectively covered at every scale — same gap-processing
induction as §1 but the "coverage budget" is shared among r sets. **This additivity of τ/(1+τ) is
exactly why the harmonic sum ∑1/(d−1) [= ∑τ/(1+τ) for K_d] is THE invariant.**

## 3. The K_d thickness derivation in full [COMP — port this exactly]

`K_d = (1/d)K_d ∪ (1/d)(K_d + 1)`. Hull `[0, 1/(d−1)]`. Level-1 pieces and first gap:
- `A = (1/d)K_d = [0, 1/(d(d−1))]`,  `B = (1/d)(K_d+1) = [1/d, 1/(d−1)]`.
- First gap `G = (1/d) − 1/(d(d−1)) = (d−2)/(d(d−1))`; bridges `|A| = |B| = 1/(d(d−1))`.
- Ratio `|bridge|/|G| = 1/(d−2)`. Self-similarity ⇒ this is the inf ⇒ `τ(K_d)=1/(d−2)`. ∎ [COMP]

And `τ/(1+τ) = 1/(d−1)`, so Astels ⟺ `∑1/(d−1)≥1`. The DISCRETE analogue must reproduce this:
the integer set `B_d` scaled by `d^k` has the SAME self-similar gap structure (gaps of relative
size (d−2)/(d−1) at the top, recursively), only on a lattice with minimum spacing `d^k`. The
"discrete thickness" should again be `~1/(d−2)` with the SCALE (not the ratio) carrying the k.

---

## 4. WHERE THE DISCRETE PORT MUST BREAK OR SUCCEED (my analysis → attack §6)

The continuous proof uses `|bridge| ≥ |gap|` to force an endpoint cover. Discretely, `B_d`'s
reachable set is a finite point set, and `d^k·B_d` has minimum spacing `d^k`. The gap-lemma
induction needs: at every scale down to the lattice floor `d^k`, a block of one summand reaches
across a gap of the sumset of the others. This works in the continuum because there is NO smallest
scale; on ℤ the induction TERMINATES at scale `d_min^k` (the smallest atom). So the discrete port
should go through for gaps ABOVE `d_max^k`-ish and the residual is a FINITE bottom region — which
is exactly the empirical picture (N₀ ≍ d_max^k, finite exceptional set). **The conjecture is that
the Astels induction ports cleanly above the lattice floor; the only place it can fail is the
finitely many scales between `d_min^k` and the first fully-covered block — a FINITE check.** If
that is right, Q2 = Astels-port (above floor) + finite verification (below) + residue coverage
(team-proven). I attempt this port in scholar_discrete_thickness_attack.md (next).
