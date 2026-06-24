# BEGL96 — full proof dissected (the template, and what it does NOT cover)

**Author:** scholar. **Source:** the actual PDF, Acta Arith. 77.2 (1996) 133–138,
`http://matwbn.icm.edu.pl/ksiazki/aa/aa77/aa7722.pdf` (free, CC-BY via ICM matwbn).
Full raw text saved at `_raw_begl96_fulltext.txt` in this dir. References: Birch [B] 1959,
Erdős–Lewin [EL] Math.Comp. 65 (1996) 837–840, Mignotte–Waldschmidt [MW] Acta Arith. 53
(1989) 251–287, Szemerédi [S] Acta Arith. 27 (1975) 199–245.

> **HEADLINE FOR THE TEAM:** BEGL96 proves a *general* theorem (Theorem 1) that resolves a
> SUPERSET-hypothesis version of our problem, but its hypothesis is `lim sup A(n)/n > 0`
> (the base set, viewed as an integer sequence, has positive upper density) — NOT the
> harmonic condition `∑ 1/(d−1) ≥ 1` on a FINITE set. **Our open Q2 is the FINITE-set,
> harmonic-boundary regime, which Theorem 1 does not touch.** The (3,4,7) result for all k
> is proved by a SEPARATE, ad hoc method (Mignotte–Waldschmidt linear forms in logs), NOT
> by Theorem 1. This is the crux: the team must not assume BEGL96's machinery applies to D.

---

## 1. The exact conjecture, in BEGL96's own words (verbatim)

BEGL define, for a sequence `A` of integers > 1, `Pow(A;s)` = the nondecreasing sequence of
all powers `a^k`, `a ∈ A`, `k ≥ s ≥ 1`. A sequence `S` is **complete** if `Σ(S)`
(all finite 0/1 subset-sums) contains all sufficiently large integers.

> **Conjecture (BEGL96).** For any `s`, `Pow(A;s)` is complete iff
> (i) `∑_{a∈A} 1/(a−1) ≥ 1`, and (ii) `gcd{a ∈ A} = 1`.

**Mapping to our Lean formalisation.** Our `k` = their `s` (the min exponent). Our `D` = their
`A` (the finite set of bases, all ≥ 3). Our `sumsOfDistinctPowers d k` = the per-base
component; `∑_{d∈D} sumsOfDistinctPowers d k` (pointwise sumset) = `Σ(Pow(D; k))`. The two
side-conditions are identical. **So our open Q2 IS exactly the "if" direction of the BEGL96
Conjecture for a finite set `A = D`.** [matches sumset's reduction: `Σ(Pow(D;k)) = ∑_d d^k·B_d`.]

NOTE on "≥3": BEGL state the bases as ">1" (i.e. ≥2). Our file restricts to `d ≥ 3`. With
`d=2`: `1/(2−1)=1` already, and base-2 0/1-digit numbers ARE all integers, so `d=2` alone is
trivially complete for `k=0` but the ≥3 restriction is the genuinely hard regime. The
formal-conjectures file uses `3 ≤ d`. (One d=2 in D would make 1/(d−1)=1 and likely trivialise;
the interesting conjecture is all d ≥ 3.)

---

## 2. Theorem 1 (the ONLY general theorem proved) — and why it is NOT our conjecture

> **Theorem 1 (BEGL96).** Suppose `A` is a sequence of integers > 1 with
> (i) `lim sup_{n→∞} A(n)/n > 0`  [A(x) = #{a∈A : a ≤ x}], and (ii) `gcd{a∈A} = 1`.
> Then for any `s`, there is a **finite subset** `A₀ = A₀(s) ⊆ A` such that `Pow(A₀; s)` is
> complete.

**This is a DIFFERENT theorem from the conjecture in two decisive ways:**

1. **Hypothesis (i) is `lim sup A(n)/n > 0`, a POSITIVE-DENSITY condition on the base set A
   as a subset of ℕ — not the harmonic sum `∑ 1/(a−1) ≥ 1`.** Positive upper density of A is
   FAR stronger. E.g. `D = {3,4,7}` is a 3-element finite set: `A(n)/n → 0`, so `lim sup = 0`.
   **Theorem 1 says NOTHING about any finite D.** It needs A to be an *infinite* set occupying
   a positive fraction of the integers.

2. **The conclusion only asserts existence of SOME finite `A₀ ⊆ A`**, not that the given
   finite set is complete. It is a "thinning down from a thick infinite set" result.

**Why Theorem 1 cannot be our lever directly:** our `D` is finite, fixed, and on the harmonic
*boundary* `∑1/(d−1) = 1` (the hardest case). `lim sup A(n)/n = 0` for every finite set, so
Theorem 1's hypothesis (i) is FALSE for every D we care about. The harmonic condition
`∑1/(d−1) ≥ 1` and the positive-upper-density condition are genuinely different sufficient
inputs; BEGL prove the conjecture only when the (much stronger) density input is available.

> **TEAM TAKEAWAY (false-trail flag):** Do not try to invoke "BEGL96 Theorem 1" to close Q2 —
> it does not apply to finite D. Q2 (finite D, harmonic boundary) is exactly the gap BEGL left
> open and explicitly say "We are still fairly far from being able to prove the conjecture."

---

## 3. The MACHINERY of Theorem 1's proof (reusable lemmas — the real gold)

The proof is a 4-Claim covering/gap-filling argument. Each Claim is an independent, reusable
tool. **These DO transfer to the k≥1 setting** (they are k=s–uniform); the obstruction is only
that the *density* input is what feeds them. Several pieces are exactly what `cassels`, `carry`,
and `modular` need.

### Claim 1 (gap bound from harmonic excess β > 2 — "Cassels-type completeness lemma")
Take a finite `B = (b₁<…<b_N) ⊆ A` with `β := ∑ b_i^{−1} > 2`. Write
`Σ(Pow(B;s)) = {0=p₀<p₁<…}`. Then **every gap is bounded: `p_{k+1} − p_k ≤ 2 b_N^{s+1}`.**

*Proof mechanism (THE completeness engine):* order `Pow(B;s) = {β₁<β₂<…}`. Two elementary
facts about subset-sum sets:
  - (a) max gap of `Σ(β₁,…,β_k)` is `≤ β_k`;
  - (b) if `∑_{i≤k} β_i ≥ β_{k+1}` then adding `β_{k+1}` does not increase the max gap.
Then a counting estimate: for `β_k ≥ 2b_N^{s+1}`,
  `∑_{i=1}^N ∑_{j: b_i^j ≤ β_k} b_i^j  =  ∑_i (b_i^{t(i)+1} − b_i^{s+1})/(b_i−1)
     ≥ (β_k − b_N^{s+1}) ∑_i 1/(b_i−1) = β(β_k − b_N^{s+1}) ≥ β_k`
(using `β > 2`, `β_k ≥ 2b_N^{s+1}`). So hypothesis (b) holds for all large terms ⇒ gap stays
`≤ 2b_N^{s+1}`. **This is the quantitative Cassels/Erdős "∑1/aₙ large ⇒ small gaps" criterion,
made explicit.** It is the heart of why `∑1/(d−1) ≥ 1` is the right invariant: `∑ b_i^{−s}`
controls density of `Pow(B;s)`, and `∑1/(b_i−1) = ∑_{j≥1} b_i^{−j}` is its geometric-series
envelope. NOTE: Claim 1 needs `β > 2`, i.e. `∑1/(b_i−1)` STRICTLY exceeds 2 (a *finite chunk*
B with harmonic sum > 2) — boundary `= 1` is NOT enough for this lemma. This is precisely why
the harmonic-*boundary* case is hard and why a single finite D with `∑=1` evades it.

### Claim 2 (combinatorial partition identity — "moment-matching split")
For each `s`, partition `{0,1,…,2^s−1} = C(s) ∪ D(s)` with matched power-sums:
  `∑_{c∈C} c^j = ∑_{d∈D} d^j` for `0 ≤ j ≤ s−1`, and
  `∑_{c∈C} c^s − ∑_{d∈D} d^s = s! · 2^{\binom{s}{2}}`.
Built by the **Prouhet–Thue–Morse recursion**: `C(1)={0}, D(1)={1}`,
`C(k+1)=C(k)∪(2^k+D(k))`, `D(k+1)=D(k)∪(2^k+C(k))`. This is the classical Prouhet–Tarry–Escott
(PTE) ideal solution. It produces two equinumerous sets agreeing on all power-sums up to order
`s−1` and differing by a controlled amount at order `s`.

### Claim 3 (manufacture an arithmetic progression of given step in the sumset)
Using Szemerédi [S] (an interval of positive-density integers contains a 2^s-term AP) +
the affine-invariance of Claim 2's identity (it survives `k ↦ a_j + k d_j`), one extracts from
each density-block `A_j` two disjoint sub-multisets `P_j, Q_j` of `Pow(A_j;s)` whose s-th
power-sums differ by exactly `D := s! 2^{\binom{s}{2}} d^s` (a FIXED step `d` recurring
infinitely often by pigeonhole). Hence **`Σ(Pow(A_1;s))+…+Σ(Pow(A_u;s))` contains an AP of
length `u+1` and step `D`** — arbitrarily long APs of fixed step.

### Claim 4 (hit every residue class mod D — where gcd=1 is USED)
**This is the lemma that consumes hypothesis (ii) gcd=1.** Let `q₁<…<q_r` be the primes
dividing `D`. By gcd{a∈A₀}=1, for each `q_i` there is `a(i)∈A₀` with `gcd(a(i),q_i)=1`. Powers
`a(i)^t mod D` are eventually periodic, so pick exponents giving a fixed residue
`a(i)^{t_i(k)} ≡ c(i) (mod D)` with `gcd(c(i),q_i)=1`. Then a CRT combination
`M ≡ ∑_i (D/q_i)·... ` with `gcd(M,D)=1` is realised, and `kM (mod D)` for `k=1..D` sweeps a
complete residue system. **⇒ `Σ(Pow(A₀;s))` contains a complete residue system mod D.**

### Assembly
Claim 3 gives long APs of step D; Claim 4 fills all residues mod D ⇒
`Σ(Pow(A₀∪A_1∪…∪A_u; s))` contains `≥ 2b_N^{s+1}` consecutive integers (for u large); Claim 1
then bootstraps from that block to ALL large integers. Done.

> **Where gcd=1 enters (definitive answer to the whole team's recurring question):** ONLY in
> Claim 4, and ONLY to hit every residue class mod `D = s!·2^{\binom{s}{2}}·d^s`. It is a
> CRT/residue-covering use, exactly as `modular` suspected. The k(=s) exponent enters Claim 4
> through `D` containing the factor `d^s` (so the modulus grows with k), and through Claim 1's
> gap bound `2 b_N^{s+1}` and the per-base density `∑ b_i^{−(s+...)}`. The structure is
> k-uniform; nothing breaks as k grows EXCEPT that you still need the density input β>2.

---

## 4. The (3,4,7)-for-all-k result is proved by a TOTALLY DIFFERENT method

BEGL §3 "Concluding remarks": the small-set results are NOT from Theorem 1. They write:
"Using fairly recent estimates in diophantine approximation, such as the inequality
`|3^p − 4^q| > exp{ln3 (p − 500 ln4 (8+ln p)^2)}` of **Mignotte–Waldschmidt [MW], Cor. 10.1**,
we can show that the largest integer not in `Σ(Pow({3,4,7};1))` is 581."

So (3,4,7) completeness is established for `s=1` by a **linear-forms-in-logarithms** bound
controlling how close `3^p` and `4^q` can be — i.e. a transcendence-theory gap estimate, then
(presumably) a finite computation up to 581. Similarly:
  - largest missing in `Σ(Pow({3,5,7,13};1))` = **111**;
  - largest missing in `Σ(Pow({3,6,7,13,21};1))` = **16**;
  - largest missing in `Σ(Pow({3,4,5};1))` = **78** (here ∑1/(d−1)=13/12 > 1, easier).

**CRITICAL CAVEAT for the team:** the PAPER's explicit (3,4,7) computation is for `s=1` only.
Our Lean file's `erdos124.ne_zero_three_four_seven` claims (3,4,7) for ALL `k ≠ 0`. BEGL's §3
says "for any s" in the conjecture but the displayed (3,4,7) bound 581 is the `s=1`
linear-forms argument. **Whether the (3,4,7)-for-all-k claim in our file is actually proven in
BEGL96 for general s, or is an extrapolation, needs checking** — the MW linear-forms method
extends to `3^p` vs `4^q` with both exponents ≥ s, so it plausibly does, but the paper only
displays s=1. troika should verify exactly which (d, k) the MW method closes.

> **TEAM LEVER (for `troika`, `lift`):** The route to (3,4,7)-for-all-k is Mignotte–Waldschmidt
> linear forms in two logs (`|3^p − 4^q|` lower bounds), NOT the density machinery. To
> generalise (3,4,7) to another harmonic-boundary triple you need a *Baker-type* lower bound on
> `|d_i^{p} − d_j^{q}|` for the relevant base pairs. This is the actual classical tool the
> conjecture's small-set instances rest on.

---

## 5. The Erdős–Lewin connection (origin of the whole problem)

BEGL close: the investigation "grew out of" the **Erdős–Lewin conjecture** [EL] (Math.Comp. 65
(1996) 837–840, "d-complete sequences of integers"): for `{a_1,…,a_k}`, `k≥2`, gcd=1, every
large integer is a sum of terms `a_1^{r_1}…a_k^{r_k}` (all `r_i ≥ 1`) with no term dividing
another. Proven for `{2,3}` (Selfridge, Lewin independently) and `{2,5,7}` (Erdős–Lewin). This
is a *cousin* problem (multiplicative-mixed powers vs our pure-power-per-base) — relevant
background but NOT the same object. **False-trail caution:** don't conflate "d-complete" (EL)
with our "complete sequence of sets of integer powers."

## 6. Open sub-question BEGL themselves pose (might be a softer target)

BEGL ask (§3): if `∑_i 1/log(a_i) > 1/log 2`, must `Σ(Pow({a_1,…,a_k}; s))` have positive
(upper) density? "For example, what about `{3,4}`?" — `{3,4}` has `∑1/(d−1)=5/6 < 1` so it is
BELOW the completeness threshold, but they ask about positive density, a weaker property. This
is a recorded open sub-problem; `density` should note it.
