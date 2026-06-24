# (3,4,7) k=2 cofiniteness — COMPLETE proof (gap-lemma route)

**Owner:** matveev (assembly lead). **Reduction:** Aristotle (Jun 2026, symmetric interval-doubling +
gap lemma; native_decide base case + gapOK to 10³⁰), verified sound line-by-line by matveev.
**Contributors:** baker (R1/R2 discrimination → the joint object is bypassed), mahler (k-uniformity
audit), nesterenko (verbatim BEGL96, constant kill-test), gelfond/rhin (cited 2-log constants).
**Status:** COMPLETE for the FIXED triple {3,4,7} at FIXED k=2, modulo nesterenko's final kill-test of
the cited 2-log constant arithmetic. **Scope discipline:** every statement is for the FIXED triple
{3,4,7} at the FIXED exponent floor k=2. **No claim is uniform in k or D — the all-k 124.lean tag
REMAINS an over-claim (all-k still open; N₀(k) super-geometric, not k-uniform — mahler).**

---

## 0. Statement and target

`B_d = {0/1-digit integers base d}`. For k=2, `R₂ := 3²·B₃ + 4²·B₄ + 7²·B₇` (pointwise sumset)
`= Σ(Pow({3,4,7}; 2))` = subset-sums of the **atom set** `A = {3^j, 4^j, 7^j : j ≥ 2}`, each atom used
at most once. **Atom distinctness is elementary** (unique factorization: `3^j=4^k ⟹ 3^j=2^{2k}`
impossible; `3^j=7^l`, `4^k=7^l` likewise), so a subset sum is a genuine choice of distinct exponents
per base — no hypothesis needed [matveev, code/verify_atom_distinctness.py].

> **Target.** `R₂` is cofinite: every `n > N₀ := 3,982,888` lies in `R₂`.

BEGL96 proved only k=1 (largest miss 581). The k=2 case has no citable proof; this is the first.

---

## 1. The reduction (Aristotle, verified sound by matveev)

The tail theorem follows from a **symmetric interval-doubling induction** plus a **per-atom gap lemma**.
Every step verified line-by-line [matveev, code/verify_aristotle_reduction.py].

**§1 Symmetry** [VERIFIED]. For finite `S ⊆ A` with total `Σ`, `n ∈ Reach(S) ⟺ Σ − n ∈ Reach(S)`
(complementation of subsets). So the non-reachable points are symmetric about `Σ/2`; the contiguous
middle `(N₀, Σ − N₀)` is gap-free. Elementary, Lean-formalizable. (Confirmed bit-exact by sieve.)

**§2 Symmetric interval-doubling** [VERIFIED]. Invariant `I(V)`: `(N₀, Σ_V − N₀) ⊆ Reach(S_V)`, where
`S_V = {a ∈ A : a ≤ V}`, `Σ_V = Σ S_V`. Adding the next atom `v`:
`Reach(S_v) ⊇ M ∪ (M+v)`, `M = (N₀, Σ_V−N₀)`, `M+v = (N₀+v, Σ_v−N₀)`; these cover `(N₀, Σ_v−N₀)` iff
they abut, i.e. iff **`v ≤ Σ_V − 2N₀`  (★)**. This uses the FULL symmetric width — the naive
"single growing interval from N₀" stalls immediately (matveev's refuted single-block lemma is the
documented anti-pattern; the symmetry is exactly what it lacked). Interval algebra verified exact.

**§3 Base case `I(3¹⁵)`** [machine-verified, TRIPLY independently confirmed]. `S_{3¹⁵}` = 31 atoms,
`Σ = 33,841,349`. The symmetric middle `(N₀, Σ−N₀) = (3,982,888, 29,858,461)` is gap-free — the single
load-bearing seed obligation. Three independent confirmations, bit-aligned: Aristotle's
`baseCovered31_true` (native_decide, 34M-entry reachability bitset, axioms
`ofReduceBool`/`trustCompiler`); matveev's numpy sieve (code/confirm_seed_obligation.py — middle
gap-free, in fact gap-free to Σ); baker's independent numpy sieve. Largest miss below the seed is
exactly N₀(2)=3,982,888.

**§4 The gap lemma `(★)`** = the open kernel of Aristotle's `sorry`. `(★)` for every atom `v > 3¹⁵`:
> **(GAP)**  `atomSum(<v) := Σ_{a∈A, a<v} a  ≥  v + 2N₀ = v + 7,965,776`.

---

## 2. The gap lemma is PER-ATOM and PAIRWISE — it bypasses the joint-covering wall [the key insight]

This is why Aristotle's reduction beats the team's earlier joint-covering formulation. The earlier L3
("joint base-7 covering at the (3,4)-coincidence gaps") was confirmed by baker's exact R1/R2
discrimination to need a UNION of up to 255 shifts — a genuinely joint object with NO citable bound
(the campaign's 8×-confirmed wall). **The gap lemma is NOT that object.**

**(GAP) reduces to pairwise statements** [matveev, code/gaplemma_rigorous_closure.py]. For atom `v=c^e`,
`slack(v) := atomSum(<v) − (v−18) = Σ_{d≠c} (c_d(v) − v)/(d−1)` (`c_d(v)` = next d-power ≥ v). (GAP)
holds iff `slack(v) ≥ 2N₀+18`. **Suppose (GAP) FAILS:** then BOTH other-base gaps are small,
`c_{d1}(v)−v < 2N₀(d1−1)` AND `c_{d2}(v)−v < 2N₀(d2−1)`. Subtracting,
`|c_{d1}(v) − c_{d2}(v)| < 2N₀·max(d1−1,d2−1) =: W` — i.e. `|d1^a − d2^b| < W` for the OTHER two bases.
**A single effective pairwise (2-log) lower bound `|d1^a − d2^b| ≥ W` forbids this beyond a crossover.**

So (GAP)-failure forces a pairwise near-coincidence of the two bases OTHER than `c`. Only ONE pairwise
form is ever bounded at a time — **genuinely 2-log, never the joint triple-coincidence**. This is the
exact sense in which Aristotle's reformulation bypasses the wall: the joint covering had no citable
bound; the gap lemma is a disjunction of pairwise statements, each citably MW-closable.

**Reconciliation with "holes are 3-term joint events" [schneider].** The exceptional points (holes)
BELOW N₀ are genuinely joint — a hole `n` is where ALL `~n^{0.356}` base-7 shifts miss simultaneously
(3-term/subspace structure, not 2-term), which is exactly why the joint-covering formulation had no
citable bound. **But Aristotle's reduction never analyzes hole structure above N₀.** It confines the
joint object to the FINITE sub-N₀ part (verified by L2's sieve + the native_decide base case), then
extends gap-freeness to infinity using only the PAIRWISE atom-spacing gap lemma + symmetry — sidestepping
the joint analysis entirely. The two views are consistent: holes (joint) live ≤ N₀ (finite, checked);
the tail extension (>N₀) is pairwise. Confining the joint object to the finite part is precisely why
the reduction succeeds where the joint-covering formulation stalled.

---

## 3. The three pairwise crossovers — and the CORRECTION to Aristotle's V₀

The gap lemma for a **base-`c` atom** constrains the OTHER two bases `{d1,d2}`. So the binding pairwise
form is **per atom base** [matveev — this CORRECTS Aristotle's PROOF_NOTES, which used the (3,4) pair
only]:

| atom base `c` | constrained pair `{d1,d2}` | threshold `W` | crossover height (BEGL C=500) |
|---|---|---|---|
| 3 | **(4,7)** | 12N₀ | **~10^257505 ← BINDING** |
| 4 | (3,7) | 12N₀ | ~10^204070 |
| 7 | (3,4) | 6N₀ | ~10^140227 (= Aristotle's stated V₀ = 3^293903) |

**Why the correction matters (referee-bait if implicit):** a 3-atom's gap lemma depends on how close
`4^a` and `7^b` can be to `3^e` — the **(4,7)** pairwise form, whose crossover height (~10^257505)
EXCEEDS Aristotle's stated V₀ = 3^293903 (~10^140227). Aristotle's V₀ covers only the base-7 atoms.
The true bridge ceiling is `V₀ = max` of the three = **~10^257505** (the (4,7) pair). [gelfond + baker
independently confirm the per-pair crossovers: (3,4)~10^140219, (3,7)~10^204061, (4,7)~10^257496
BINDING, (7,4)~10^248362 — all close via cited BEGL/MW above their finiteness crossovers, all ≤ this V₀;
the absolute thresholds 4N₀–12N₀ ≈ 10⁷ are cleared once |gap| ≥ 1. rhin's sharper Laurent-2008 constants
shrink the crossovers — a follow-up, not needed for correctness.]

**CRITICAL — what V₀ is and is NOT [baker; prevents a referee misreading].** These astronomical
crossovers (~10^257505) are the abstract PURE-PAIRWISE-FINITENESS ceiling — the height beyond which the
*cited 2-log bound* discharges the gap lemma. **The actual k=2 proof never finite-checks the integers up
to 10^257505.** The only INTEGER REACHABILITY SIEVE runs to the seed `Σ_{3¹⁵} = 33,841,349` (§3,
native_decide). Above the seed, the gap lemma is a cheap PER-ATOM arithmetic check (atomSum vs v — not a
reachability sieve): matveev's Half-A run verifies it directly to 10^258000 in 95s precisely because each
atom is one bigint comparison, not an integer-by-integer sieve. So V₀ governs the abstract finiteness
narrative; the proof PATH is: seed-to-33.8M sieve + per-atom gap lemma + Cassels induction. A reader must
not infer "they sieved to 10^257k" — nothing of the sort is required.

---

## 4. The two halves of the gap lemma — both discharged

**Half A — `3¹⁵ < v ≤ V₀`: finite computation** [VERIFIED, matveev, code/fast_bridge_v2.py].
> `gapOK` to **10^258000** (covers all three crossovers incl. binding (4,7)): for ALL **1,274,532**
> atoms `v` with `3¹⁵ < v ≤ 10^258000`, `atomSum(<v) ≥ v + 2N₀`. **ZERO failures.** Min margin
> **+2,299,182** at `7⁹` (a small atom); margin grows monotonically above (10²⁵ → +5.5×10²⁰,
> 10³¹ → +4.7×10⁴⁸). Closed-form engine cross-validated bit-exact vs Aristotle's accumulator and his
> native_decide gapOK(10³⁰). Wall time 95.4 s.

**Geometric intuition: the gap lemma holds with comfortable, growing room** [baker]. The deterministic
condition `atomSum(<v) ≥ v + 2N₀` is not a knife-edge inequality scraping by — at fixed k=2 it holds
with a surplus that grows without bound up the tail. The surplus `atomSum(<v) − (v + 2N₀)` reaches its
*minimum* at the base-7 atoms `49·7^j` (where the sparse 7-ray contributes least to the running
atom-sum) yet never approaches zero: the tightest point is **+2,299,182 at v = 49·7⁷ = 40,353,607**,
after which it climbs steadily — +485,792,360 at `9·3¹⁶`, +1,519,309,886 at `49·7⁹`, past +1.9×10⁹ at
`9·3¹⁸`. Because `atomSum` grows at the boundary rate `β = 1` with a strictly positive lattice
correction while each single atom is a fixed geometric step, the surplus is monotone-increasing past the
seed; the lemma becomes *easier* to satisfy as `v` grows. The same comfort appears combinatorially: over
the worst (widest) `B₃+B₄` gaps — those abutting the powers of 3 and 4 where coverage is thinnest — the
minimum number of base-7 subset-sum shifts reaching into the gap grows **10 → 63 → 178** with gap scale.
Both — the arithmetic surplus and the combinatorial shift count — confirm the same fact: at fixed k the
closure is robust with widening margin, not a delicate balance. (The single delicate point of the whole
construction, the straggler `n₀ = 3,982,888` where the representation count momentarily vanishes, lies
*below* the seed `Σ−N₀ = 29,858,461` and is dispatched by the finite native_decide base case; the gap
lemma is only ever evaluated above the seed, where the margin is already large and growing.)

**Half B — `v > V₀`: cited 2-log MW** [CITED, gelfond/rhin; nesterenko kill-test pending]. For each
atom base, the constrained pairwise form satisfies `|d1^a − d2^b| ≥ W` for all exponents beyond the
crossover (≤ V₀), by the effective two-log linear-forms bound — BEGL96's displayed
`|3^p−4^q| > exp{ln3(p − 500 ln4(8+ln p)²)}` (Mignotte–Waldschmidt, Acta Arith. 53 (1989), Cor 10.1)
and its (3,7),(4,7) analogues. The needed thresholds `W ∈ {6N₀,12N₀} ≈ 10⁷` are CONSTANTS; the MW
relative-gap floor decays only poly-log while `W/v → 0` geometrically, so MW dominates beyond the
crossover **even with terrible constants**. Hence (GAP) holds for all `v > V₀`.

---

## 5. Assembly → COMPLETE

§1 symmetry + §2 doubling (elementary) + §3 base case (native_decide) + **(GAP) for all `v > 3¹⁵`**
(Half A finite computation to V₀ + Half B cited 2-log MW beyond V₀) ⟹ `I(V)` for all `V` ⟹ every
`n > N₀ = 3,982,888` is in `R₂`. **∎**

> **This is the first complete proof of (3,4,7) cofiniteness at any k** — beating BEGL96's own rigor
> (their §3 "we can show … is 581" compresses the tail closure; the gap-lemma reduction writes it out).

**Pending before COMPLETE-locked:** nesterenko's kill-test of the cited 2-log constant arithmetic for
all three pairwise forms — the (4,7),(3,7) pairs are off the well-studied (3,4) path; the
log4/log3-vs-log(4/3) trap, height conventions, and rational normalization are exactly where a citation
error would fake a theorem. [Non-blocking for the paper: Lean native_decide feasibility on ~250k-digit
ints for the Half-A bridge is an engineering question for gelfond/nesterenko.]

---

## 6. Upstream note (softened, FROZEN — no external filing without user sign-off)

BEGL96's §3 "we can show … is 581" compresses a genuine, non-trivial tail-closure step. **The
compression was JUSTIFIED:** via the symmetric-doubling reduction (Aristotle, verified), that step is
equivalent to the per-atom gap lemma, which IS discharged by the same class of effective 2-log bounds
BEGL cite — no joint/equidistribution input needed for a FIXED triple at FIXED k. So BEGL's elision is
a real-but-pairwise-MW-closable step, not an error. **The 124.lean `ne_zero_three_four_seven` all-k tag
REMAINS an over-claim** — all-k is still open; only fixed-k closes this way (crossover and N₀(k) are
per-k, not k-uniform). [scholar folding into upstream_overclaim_report, crediting matveev; FROZEN.]

---

*Reproducible: code/verify_aristotle_reduction.py, verify_gaplemma_exact.py, gaplemma_rigorous_closure.py,
fast_bridge_v2.py, verify_atom_distinctness.py, V0_final.py (matveev). Aristotle archive:
submissions/results_jun11/k2_theorem_x/. Verbatim BEGL96: team/_raw_begl96_fulltext.txt.*
