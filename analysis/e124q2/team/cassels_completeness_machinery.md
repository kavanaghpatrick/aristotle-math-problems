# E124 open part: completeness machinery + computational structure

**Author:** cassels. **Status:** IN PROGRESS — solid empirical structure, partial proof skeleton.
Builds directly on `sumset_reduction_scaling.md` (the reduction `S(d,k) = d^k·B_d`).

## 0. The object (using sumset's reduction)

Open question (Q): for every k≥1 and admissible D (all d≥3, ∑1/(d−1)≥1, gcd(D)=1),
is `R(D,k) := ∑_{d∈D} d^k·B_d` cofinite in ℕ? Here B_d = {0/1-digit numbers base d}.

I built a real bitset reachability computer: `code/reach.py` (big-int bitmask DP, Minkowski
sums via shift-OR). `code/sweep.py`, `code/tight.py` drive it. All numbers below are COMPUTED,
not asserted.

## 1. The classical machinery (Birch 1959; Brown 1961) — what actually applies

> **CITATION CORRECTION (team-lead + scholar):** the interval-filling completeness criterion below
> is **Brown 1961** (J. L. Brown Jr., "A note on complete sequences of integers", Amer. Math.
> Monthly 68 (1961), 557–560), with **Erdős 1962** (Acta Arith. 7). The "Cassels 1960" attribution
> used in earlier drafts of these files is a **PHANTOM** — do not cite it for this lemma. I keep the
> informal name "interval-filling lemma" below; the citation is Brown 1961 / Erdős 1962.

**Interval-filling lemma (Brown 1961; the workhorse).** Order a multiset of positive terms
t_1 ≤ t_2 ≤ … with partial sums T_n = t_1+…+t_n. If t_{n+1} ≤ T_n + 1 for all n past some point,
then every integer in [t_1, T_n] is a subset-sum, so the sequence is complete from that point.
The induction: if [a, T_n] is filled and t_{n+1} ≤ T_n+1, then [a, T_n + t_{n+1}] is filled
(old interval ∪ (old interval + t_{n+1}) overlap because the gap t_{n+1} ≤ T_n+1).

**Birch 1959** ('Note on a problem of Erdős', Proc. Camb. Phil. Soc. 55): for coprime p,q,
the set {p^a q^b} is complete. His method survives a LOWER BOUND on exponents (a≥A₀, b≥B₀):
only finitely many small terms are dropped, the tail still satisfies the filling condition.
This is the structural reason our k≥1 shift should not change the YES/NO answer for fixed
admissible D — only the threshold N₀ moves.

**Caveat (verified by hand):** Grok's "expansion-factor ∏(1+1/(d−1))≥2 ⟺ ∑1/(d−1)≥1" heuristic
is NOT an identity — ∏(1+x_i) ≥ 1+∑x_i, so ∑1/(d−1)≥1 ⟹ ∏(1+1/(d−1))≥2 holds, but the
converse fails. So ∏≥2 is WEAKER than ∑≥1. The correct density invariant is ∑1/(d−1) (Pomerance
converse, proven in 124.lean as `erdos124.converse`), NOT the product. Do not use the product form.

## 2. The two obstructions are real and SEPARATE (COMPUTED)

### (a) gcd>1 kills it for k≥1 (confirms sumset's necessity argument with data)
D=[3,6,9,12,15,18,21,24], gcd=3, ∑1/(d−1)=1.14>1:
- k=0: FULLY COVERED [0,300000]  (gcd irrelevant: d⁰=1)
- k=1: 200000/300001 missing — every reachable value ≡ 0 mod 3 (verified: 0 reachable values
  are ≢0 mod 3). So ⅔ of residues permanently absent. NOT cofinite.
- k=2: 266671/300001 missing — reachable ⊆ 9ℕ.
Mechanism: every element of d^k·B_d is divisible by d^k; if p|gcd(D) then p^k divides EVERY
summand, so p^k | every element of R(D,k). Cofinite ⊄ p^k·ℕ. **gcd(D)=1 necessary for k≥1.**

### (b) ∑<1 kills it (Pomerance converse, already a theorem) — controls confirm
Control D with ∑<1 (e.g. [3,4] s=0.833, [3,5,9] s=0.875, [3,4,9] s=0.958) have largest-missing
≈ N at N=200000, i.e. gaps persist arbitrarily high. NOT cofinite. Matches `erdos124.converse`.

These two obstructions are independent: (a) is a congruence trap (mod p^k), (b) is a density
deficit. (Q) asks whether removing BOTH suffices.

## 3. SUFFICIENCY evidence: every admissible D tested is cofinite (COMPUTED)

For every D with gcd=1 AND ∑1/(d−1)≥1 tested, R(D,k) is cofinite with a FINITE threshold N₀(D,k)
well inside the window (k=1,2; N=200000):

| D | ∑1/(d−1) | k=1 N₀ | k=2 N₀ |
|---|---|---|---|
| [3,4,7] | 1.000 | 581 | **3,982,888** |
| [3,4,5] | 1.083 | 79 | 77613 |
| [3,4,5,7] | 1.250 | 22 | 695 |
| [3,4,6] | 1.033 | 986 | (see note) |
| [5,6,7,8,9,10,11] | 1.096 | 4 | 1033 |

No admissible counterexample found. Consistent with the conjecture being **TRUE**.

**CORRECTION (important, team-wide):** the k=2 numbers I first reported (e.g. (3,4,7) k=2 =
195353 or 785743) were WINDOW-TRUNCATION artifacts. Local coverage saturates to 1.000 long
before the true threshold, then a STRAGGLER gap appears far above (breaker's "straggler trap").
True stable (3,4,7) thresholds (breaker's numpy engine, re-verified by my bitset engine at N=5M):
k=1: 581, k=2: **3,982,888**, k=3: **57,751,591** (grows >14× per k-step). A reported threshold
is valid ONLY if the window extends FAR past it. The refined analysis is in
`cassels_completeness_lemma.md` (Lemma C + the threshold identity + the side-condition mapping).

## 4. THE PINCH: threshold N₀(D,k) scales like d_max^k (the crux)

This is the precise location of the difficulty the lead asked me to isolate.

**Floor of the pinch (PROVED, trivial):** the smallest nonzero element of d^k·B_d is d^k. So the
smallest nonzero element of R(D,k) is d_min^k. Hence EVERY n in [1, d_min^k − 1] is missing.
⟹ N₀(D,k) ≥ d_min^k − 1. For the induction to even start, n must exceed d_min^k.

**Empirical ceiling:** N₀ grows like ~d_max^k. For (3,4,7): k=1 N₀=581, k=2 N₀=195353 (ratio
~336 ≈ 7^2/... ; 581≈ between 7²·12 and ...). The threshold climbs geometrically in k with ratio
≈ d_max. So for fixed admissible D the answer is YES for every k, but the "sufficiently large"
bound N₀(k) is NOT uniform in k — it blows up like d_max^k. This is why a naive "apply k=0 and
scale" fails (sumset's point) and why BEGL96 could only prove the single triple (3,4,7).

**Where the induction needs ∑≥1, precisely:** to run Cassels' filling on the merged geometric
rays above the floor d_min^k, at each scale you need enough terms below the current partial sum to
keep t_{n+1} ≤ T_n+1. The count of base-d terms below X is ~log_d X, and the SUMMABLE density that
controls whether merged rays leave no gap is exactly ∑1/(d−1) (the per-ray contribution 1/(d−1) is
the limiting fraction of [0,X] coverable by one ray's subset-sums). ∑≥1 is the supercritical
threshold; ∑=1 (the (3,4,7)/(3,5,7,13) tight cases) is the boundary where coverage is exactly
critical — the gaps are finite but N₀ is largest relative to the bases. **The tight case ∑=1 is
where the filling self-sustains with zero slack; this is THE lemma to nail.**

## 5. NEXT (open in this file)
- Confirm second exact ∑=1 case (3,5,7,13) is cofinite for k=1,2,3 → tests whether (3,4,7) was
  special or the tight boundary is generically fine. (running: code/tight.py)
- Pin the exact N₀(k)/N₀(k−1) ratio → conjecture closed form N₀(D,k) ≍ C(D)·d_max^k.
- Formalize the floor bound N₀ ≥ d_min^k − 1 (clean, provable).
