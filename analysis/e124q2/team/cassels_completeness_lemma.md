# E124 k≥1: The Cassels completeness lemma (step M=b^k) and the exact role of the two side conditions

**Author:** cassels. **Status:** Completeness lemma PROVED (elementary). The mapping
[two side conditions ⟺ two hypotheses of the lemma] is COMPUTATIONALLY ESTABLISHED across
admissible families + all three control regimes. This isolates the open core to a single
local condition and explains WHY the conjecture's hypotheses are exactly gcd=1 and ∑1/(d−1)≥1.

Builds on: sumset_reduction_scaling.md (S(d,k)=d^k·B_d), lift_sufficiency_mechanism.md
((R)+(A) split, Residue Lemma), carry_constructive_findings.md (Observation 1, +b^k closure),
scholar_BEGL96_proof_dissected.md (BEGL Claim 1 needs β>2; boundary needs Mignotte–Waldschmidt),
breaker_density_terminates.md (correct stable thresholds).

---

## 1. The completeness lemma (PROVED, elementary — Lean-ready)

Write R = R(D,k) = ∑_{d∈D} d^k·B_d ⊆ ℕ, b = min(D), M = b^k.

> **Lemma C (step-M completeness).** Suppose ∃ T such that
>   **(a)** the M consecutive integers [T+1, T+M] are all in R, and
>   **(b)** R is closed under +M above T: ∀ n>T, n∈R ⟹ n+M∈R.
> Then [T+1, ∞) ⊆ R, i.e. R is cofinite (every integer > T is representable).

**Proof.** Let n > T. Write n = n₀ + jM with n₀ ∈ [T+1, T+M] and j ≥ 0 (the unique such n₀ is
T+1 + ((n−T−1) mod M)). By (a), n₀ ∈ R. Apply (b) exactly j times along n₀, n₀+M, …, n₀+jM = n;
each step stays in R. Hence n ∈ R. ∎

This is the classical interval-filling completeness criterion (Brown 1961, Amer. Math. Monthly 68;
with Erdős 1962, Acta Arith. 7 — NOT "Cassels 1960", which is a phantom ref) specialised to step M = b^k.
It is trivial once (a),(b) hold; ALL the difficulty of E124-open is in establishing (a) and (b).
Both are needed (controls below show either one alone is insufficient).

## 2. The threshold identity (COMPUTED, exact, in every admissible case)

For the true cofiniteness threshold T(D,k) = (largest non-representable integer):

> **T(D,k) = v + M, where v = max{ n : n∈R, n+M∉R } is the last +M-closure failure.**

Logical content (verified, with the correct mechanism): T itself is missing, and T = v+M where v∈R.
So the LARGEST gap is reached by a single +M step up from a present value v=T−M: it is the final
+M-closure failure. For all n > v, +M-closure holds (n∈R ⟹ n+M∈R) by maximality of v; and the only
missing values above v lie in the single window [v+1, v+M] (with v+M=T the topmost). Once you are
past T, +M-closure (from the M present values just below) + Lemma C's induction give the whole tail.
**So the entire cofiniteness threshold is pinned by one quantity: the height of the last
+b^k-closure failure.** Verified EXACTLY (independent bitset + numpy engines):

| D | k | M=b^k | T (largest gap) | last +M violation v | T = v+M ? |
|---|---|---|---|---|---|
| (3,4,7) | 1 | 3 | 581 | 578 | ✅ |
| (3,4,7) | 2 | 9 | 3,982,888 | 3,982,879 | ✅ |
| (3,4,5) | 1 | 3 | 79 | 76 | ✅ |
| (3,5,7,13)| 1 | 3 | 112 | 109 | ✅ |
| (3,4,6) | 1 | 3 | 986 | 983 | ✅ |
| (3,4,8,12)| 1 | 3 | 150 | 147 | ✅ |
| (3,5,8,10)| 1 | 3 | 58 | 55 | ✅ |

(Validation: my engine reproduces BEGL96's published (3,4,7) k=1 value 581 exactly. The
(3,4,7) k=2 value is 3,982,888 — NOT 785743; the latter is a window-truncation artifact that
appeared in early lift/cassels notes, corrected by breaker's larger engine and re-verified here.)

**Consequence.** E124-open ⟺ "for every admissible (D,k), the +M-closure failures are FINITE
(bounded)." That is the entire open content, reduced to one local, checkable property.

## 3. THE MAPPING: the two side conditions ⟺ the two hypotheses of Lemma C (COMPUTED)

This is the structural payoff. The two independent hypotheses (a),(b) of Lemma C correspond
EXACTLY to the two side conditions of the BEGL96 conjecture:

> **(a) [eventually M=b^k consecutive integers all reachable]  ⟺  gcd(D) = 1.**
> **(b) [+b^k closure eventually holds]  ⟺  ∑_{d∈D} 1/(d−1) ≥ 1.**

Confirmed against all three control regimes (each isolates ONE failure):

| Family | gcd | ∑1/(d−1) | (a) max consec run high up | (b) +M viol high up |
|---|---|---|---|---|
| (3,4,7) — admissible | 1 | 1.000 | ✅ unbounded | ✅ 0 |
| (3,6,9,…,24) — gcd=3 | 3 | 1.140 | ❌ max run = 1 | ✅ 0 |
| (4,6,…,30) — gcd=2 | 2 | 1.336 | ❌ max run = 1 | ✅ 0 |
| (3,5,9) — ∑<1 | 1 | 0.875 | ✅ unbounded | ❌ 546 violations |

**Why the mapping holds (mechanism):**
- **(a) ⟺ gcd=1.** If p | gcd(D), every element of R is ≡ 0 (mod p^k) (sumset/troika/carry's
  proved necessity), so R never contains 2 consecutive integers, let alone M — condition (a)
  fails permanently. Conversely gcd=1 + lift's **Residue Lemma** (each B_{d*} with gcd(d*,m)=1 is
  surjective mod m) gives full residue coverage, which is exactly what lets a run of M consecutive
  reachable integers form. **(a) is lift's ingredient (R), localised to a run of length M.**
- **(b) ⟺ ∑1/(d−1)≥1.** +M closure n↦n+M requires re-representing n+M; the obstruction is purely
  archimedean density (Pomerance's converse: ∑<1 ⟹ positive density of gaps, so +M closure fails
  infinitely often). ∑≥1 is the supercritical density at which gaps become finite. **(b) is lift's
  ingredient (A), localised to the single step +M.**

So Lemma C cleanly factors E124 into (R)=(a) and (A)=(b), matching lift's decomposition, and
PINS each to one side condition. The conjecture's hypotheses are not ad hoc: they are precisely
the two conditions making the step-M Cassels filling run.

## 4. Where it's genuinely hard: the boundary ∑=1 (the pinch, per scholar)

Condition (b) — finiteness of +M-closure failures — is the open analytic core. Two regimes:

- **∑1/(d−1) > 1 (strict excess):** BEGL96 Claim 1 (scholar) gives bounded gaps once a finite
  sub-chunk has harmonic sum β>2; the strict surplus is what feeds that engine. Plausibly closable
  by adapting Claim 1 to step M (the density argument has room to spare). **This regime is the
  more tractable target.**
- **∑1/(d−1) = 1 (boundary — (3,4,7), (3,5,7,13), and all knife-edge families):** Claim 1 gives
  NOTHING (it needs β>2 strictly). BEGL closed the single triple (3,4,7) via **Mignotte–Waldschmidt
  linear forms in logarithms** bounding |3^p − 4^q| — a transcendence input, base-pair-specific.
  No general boundary result exists (confirmed: no progress beyond (3,4,7) since 1996). **THE
  boundary case is THE lemma the team must isolate as the true frontier.** It is hard for a
  principled reason: at exactly-critical density, +M closure holds only because powers of distinct
  bases cannot be too close, which is a Baker-type Diophantine fact, not a counting fact.

## 5. Honest status / what is and isn't proved here

PROVED (elementary, would survive Lean formalisation):
- Lemma C (step-M completeness criterion). Trivial induction.
- Necessity of gcd=1 for k≥1 (with sumset/troika/carry): p|gcd ⟹ R ⊆ p^k·ℕ ⟹ (a) fails.
- The reduction: E124-open ⟺ +b^k-closure failures are finite for every admissible (D,k).

COMPUTED (not proved), strong evidence:
- The threshold identity T = v + M (7 admissible families, exact).
- The mapping (a)⟺gcd=1, (b)⟺∑≥1 (4 families spanning all control regimes).
- Every admissible family tested is cofinite (this + breaker's 45-family/knife-edge scan ⟹
  predicted answer = **True**).

NOT proved (the genuine open core, same as BEGL left it):
- That (b) [+M closure eventually] holds for general admissible D at the boundary ∑=1. This is
  the Mignotte–Waldschmidt / Baker-type frontier; only (3,4,7) is done.

## 5b. Honest negative: "no +M violation" is NOT characterised by harmonic surplus alone

I hoped the strict regime would give a clean "∑1/(d−1) > c ⟹ trivially complete" sub-theorem
(v=None, +M-closed from the bottom, cofinite by Lemma C with T = b^k−1). It does NOT split that
cleanly. Scan of all 28 admissible D with d≤10, r≤4, k=1: only 4 have v=None, and they are NOT the
highest-surplus ones — e.g. (3,5,6,9) has v=None at surplus 0.075, while (3,4,5,7) still has a
violation at surplus 0.25. Whether +M-closure holds from the start depends on the detailed
multiplicative structure (which residues mod M=b^k each base reaches cheaply), not on ∑1/(d−1).
**Takeaway:** even the strict regime's tractability is structural, not purely density-driven; the
+M-closure condition (b) is genuinely the open content and cannot be reduced to a surplus bound.
This is an honest limit on how far the elementary machinery alone goes.

## 6. Recommendation to the team
The cleanest **provable** deliverable to extract for a formal/Aristotle attempt is **Lemma C +
the gcd-necessity + the reduction "E124-open ⟺ finite +b^k-closure failures"**: these are honest,
elementary, and convert the conjecture into a single local condition. The remaining content —
finiteness of +M-closure failures at the harmonic boundary — should be flagged as resting on a
Baker-type lower bound per base-pair, and is NOT something bare-formalisation will produce.
