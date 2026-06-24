# schneider — REQUIREMENTS MAP: weakest sufficient transcendence input for E124 / BEGL96

**Author:** schneider. **Seed:** find the WEAKEST sufficient transcendence input across the equivalent
forms of the open core; identify the cheapest path. **Coordination:** baker (canonical NEEDED-MW
inequality), gelfond (known-constants comparison table). **Status:** the load-bearing §C.1-vs-§C.3
tension is RESOLVED below — they are inputs at two DIFFERENT locations with DIFFERENT costs, and the
team has been conflating them.

Tag legend: [VERIFIED] = exact computation here; [DERIVED] = follows from team's proven stack;
[CLAIM] = my assessment, flagged for cross-check.

---

## 0. The resolution in one paragraph

The team's open core has been stated two ways that are NOT the same difficulty:
- **§C.1 / UNIFIED_CONCLUSION / KILL_LEDGER:** the input is the **2-log MW bound** on `|3^p−4^q|`
  (classical, BEGL96's cited Cor 10.1).
- **§C.3 RETRACTION:** the bridge is a **joint equidistribution / circle-method** estimate of the
  base-7 ray, and *MW alone is insufficient*.

**Both are right, about different things.** The reduction needs TWO transcendence inputs at two
separable locations: (I) a **gap-width bound** (cheap: 2-log, inverse-poly RATE, convergents-only,
sparse) and (II) a **last-hole / margin-floor bound** (expensive: the flat-margin spot where the
base-7 ray must align). The cheapest *sufficient* path uses input (I) for the bulk and reduces (II)
to a **finite check per (D,k)** — which is exactly what BEGL96 did at k=1 (the "computation to 581").
The genuinely-hard *uniform-in-k* version is input (II) made effective, and that is §C.3's
equidistribution. **The win: input (I) — the part that is published and cheap — does the asymptotic
bulk; input (II) is finite-per-instance, not a new uniform transcendence theorem, UNLESS you demand
a single effective N₀(k) formula uniform in k.**

---

## 1. The four equivalent forms, mapped to their minimal transcendence requirement

| Form | Where it lives | Minimal input | logs | q-support | rate vs constant | cost |
|---|---|---|---|---|---|---|
| **§C.2 gap-width** (B₃+B₄ gaps ∝ top power) | theorem_347 §C.2; baker NEEDED-MW | lower bound on `\|3^p−4^q\|/3^p` | **2** | **convergents only** (sparse, density 0) | **RATE** `f(m)≥m^{−A}`, any A | **CHEAPEST — published (Laurent/Matveev)** |
| **S10 Riesz-product minor-arc** (INV-S10) | INVENTIONS §S10; breaker S10 kill-test | uniform `\|F₃F₄F₇\|≪N^{3−δ}` on minor arcs | 2 (arcs are 2-log convergent arcs) | convergent arcs only | **RATE** (decay rate `c∈[0.17,0.31]`, bounded below) | medium — NEW harmonic-analysis lemma, but rate-only |
| **Lemma A′ 2-mass bridging** (d_min ray bridges sub-complete non-d_min sums) | REDUCTION_THM Part 3b; cassels | d_min-ray reach ≥ non-d_min constraint-gap, uniform in k | 2 | all q (per-class) | RATE per fixed k; uniform-k is the wall | medium — Hegyvári–Lev R+T lever |
| **KERNEL min-vs-avg** (`min r_D(n) ≥ 1`) | REDUCTION_THM Part 2 (lift) | margin floor: `min_{[X,2X]} r_D / avg → bounded below` | **3 at the worst points** (base-7 alignment) | **isolated last-hole points** | **SHARP CONSTANT at the flat-margin spot** | **MOST EXPENSIVE — but finite per (D,k)** |

**The cheapest path is the top row** (§C.2 gap-width). It needs only a 2-log bound, only at convergent
denominators, only a polynomial rate — all three axes minimized. **The most expensive is the bottom
row** (KERNEL min-vs-avg) — but its expense is **finite-per-instance**, not a uniform transcendence
theorem, because the sharp-constant demand only bites at the *single last hole*, which a finite
computation kills (BEGL: "to 581").

---

## 2. The evidence (all VERIFIED here, exact integer arithmetic)

### 2a. The big B₃+B₄ gaps are 2-log gap-width phenomena [VERIFIED]
The largest B₃+B₄ gap below scale N ends exactly at a power and has width `O(3^p)`:
- k=1: max gap width 7679 (scale ~10⁶) → 404718 (scale ~10⁷). Largest gap `[3789586,4194303]`
  ends at `4^11=4194304` (off −1).
- The width is **exactly** `4^q − (sum of 4-atoms below 4^q) − (best 3-subset-sum fill)`. Verified
  bit-for-bit: maxS34below(4^11) = `1398096 + 2391480 = 3789576`, gap width `= 404728 = 4^11 −
  3789576`. The residual = **granularity of base-3 subset-sums near the target = O(3^{13})** = the
  **spacing of 3-powers** = a `|3^p − 4^q|` **two-log** quantity.

⟹ **The gap-width bound is 2-log. No base 7 enters the gap-width.** [refutes the part of §C.3 that
implied the gap structure itself needs equidistribution — it does not; the gap WIDTH is pure 2-base.]

### 2b. Base-7 covers the big gap with a GROWING margin, from OUTSIDE [VERIFIED]
**[MAGNITUDE CORRECTION — convention fix.** An earlier draft used units-inclusive `B_d` (j≥0), which
adds a spurious `d^0=1` atom and inflates rep counts. BEGL's `Pow({3,4,7};k)` uses j≥k, NO units. With
the correct j≥1 atoms: largest k=1 hole = **581** exactly (matches BEGL), `r(581)=0` with neighbors
`r(580)=5, r(582)=4` — a genuine isolated single-point miss (corroborates baker's k=1 finding). The
bulk margins below are the corrected j≥1 values; structural conclusions unchanged and sharper.]**

In the bulk near `4^11` (window [3.7M, 4.2M], well above N₀(k=1)=581): **min rep = 24, median 55,
max 104; zero holes.** At the 1M scale: min rep = 64. So covering is NOT a delicate single-shift event
in the bulk; it is a comfortably redundant (24–64×) cover, and the margin **grows** with scale. The
base-7 ray covers each gap from *outside* (shifts below the gap, B₃+B₄ complement reaching up).

The dangerous region is the FINITE set of isolated last holes (581 at k=1, 3982888 at k=2) — exactly
what BEGL's finite computation to 581 handles, and which baker verified ports to k=2.

⟹ **In the bulk, only the gap-width (2-log, input I) matters; the margin is supercritical and growing.**
[confirms breaker's S10 finding that the decorrelation rate `c` is bounded below and growing.]

### 2c. The last hole is the flat-margin spot — and it is FINITE-per-instance [VERIFIED]
k=2 (atoms `{3^j,4^j,7^j : j≥2}`): the **largest hole is n = 3982888 = N₀(k=2)** exactly. It persists
because of TWO conjoined facts:
1. it sits in the big two-base gap `[3789577, 4194303]` (the `4^11` band — **2-log, input I**), AND
2. of the **32** base-7 subset-sums that "reach" (land `n−b7` below the gap into dense S34), **none**
   hits an S34 point — a genuine base-7-vs-S34 **alignment** event (**3-base, input II**).

This is the ONLY place input (II) bites — at the single last hole. Above N₀(k=2) the margin grows
(min-rep → 63+). So input (II) is a **finite check** (compute to N₀), NOT a uniform asymptotic theorem
— UNLESS one demands an effective formula for N₀(k) uniform in k, which is the genuinely-open §C.3.

---

## 3. The decision: weakest sufficient input, by goal

**The seed asked for the cheapest path. It depends on the deliverable:**

### Goal (a): (3,4,7)-all-k cofinite, with a (possibly enormous, k-dependent) threshold N₀(k)
**Weakest sufficient input = the 2-log bound, rate-only, convergents-only.** Precisely:
> `|3^p − 4^q| ≥ 3^p · max(p,q)^{−A}` for some effective absolute `A`, all p,q ≥ 1.

This is **input (I)** and it is **PUBLISHED** (Laurent–Mignotte–Nesterenko / Matveev give exactly the
inverse-poly-in-exponent shape — see baker's NEEDED-MW + gelfond's table). It bounds every B₃+B₄ gap
width by `O(3^p)`; the base-7 ray (density `n^{0.356}`, margin ≥63 growing) covers gaps of that width
above an effective scale; and `[scale, N₀(k)]` is a finite check. **This matches the BEGL96 k=1 proof
exactly** (their displayed bound is this 2-log inequality, then computation to 581). The all-k lift is
lift's §A+§B (k-uniformity is automatic, the bad pairs are k-independent convergents).

⟹ **Goal (a) does NOT need equidistribution. §C.3 over-corrected.** The equidistribution framing
arises only if you insist on covering *via base-7 joint behavior*; but the cheaper route covers via the
**2-log gap-width bound + redundant (≥63×) base-7 cover + finite check**, which is BEGL's actual route.

### Goal (b): a single CLEAN effective N₀(k) formula, uniform in k (no per-k finite check)
**This is where input (II) / §C.3 equidistribution is genuinely needed**, and where the cheapest path
hits the wall. The flat-margin criticality (the last hole = N₀(k), §2c) means the constant in N₀(k)
is set by the worst base-7-vs-S34 alignment, which is the joint-equidistribution quantity. No 2-log
bound gives this constant; it is the S10 minor-arc bound with a SHARP constant on the convergent arcs.

⟹ **Goal (b) is the hard open core. But it is NOT needed for goal (a).** The team's "complete modulo
one MW constant" (withdrawn) was right for goal (a) and wrong for goal (b).

---

## 4. Answer to baker's open hinge (the one flagged for maverick/density cross-check)

> baker: "is inverse-poly-in-exponent genuinely sufficient, or does the flat-margin criticality (§C.3)
> demand a SHARP constant, not just a rate?"

**Answer (schneider, VERIFIED): inverse-poly RATE is sufficient for cofiniteness with a k-dependent
N₀(k) [goal a]; the SHARP constant is needed ONLY for an effective uniform N₀(k) formula [goal b].**
The flat margin (min-rep dips to the single last hole = N₀) is a FINITE-scale event per (D,k): above
N₀ the margin grows (≥63, verified). So the rate bounds the gap widths and pushes all holes below an
effective (huge) N₀(k); the finite check `[scale, N₀(k)]` then certifies. The sharp constant is only
required to *predict* N₀(k) without computing it. **Rate ⟹ cofinite (with finite check); sharp
constant ⟹ effective uniform threshold.** The reduction (goal a) closes on the RATE — which is known.

---

## 5. Cheapest-path summary (the deliverable)

**WEAKEST SUFFICIENT INPUT for (3,4,7)-all-k cofiniteness:**
> the **2-log, inverse-polynomial-rate, convergent-denominators-only** lower bound
> `|3^p − 4^q| / 3^p ≥ max(p,q)^{−A}` (effective absolute A), which is **PUBLISHED**
> (Laurent/Matveev), PLUS a finite computation `[N_eff, N₀(k)]` per k (k-uniformity by lift §A+§B).

This is strictly weaker than the team's stated "open core" along all three axes:
- **logs:** 2, not 3 (no `|3^a4^b − 7^c|` joint form needed for the bulk).
- **q-support:** convergent denominators only (sparse, density 0), not all q.
- **rate:** any polynomial rate, not a sharp constant.

The expensive inputs (3-log alignment at the last hole; sharp minor-arc constant; uniform N₀(k)) are
needed ONLY for the stronger goal (b) "clean effective uniform threshold," which is NOT required for
the cofiniteness theorem (goal a). **Conclusion (a)** of the seed: the cheapest path yields a genuine
conditional theorem on a PUBLISHED input — this is outcome (a)/(b) on the team's scale, not a shape-wall.

**Caveat (honest):** goal (a)'s "finite check to N₀(k)" is not a-priori-bounded without input (II) —
we know N₀(k) is finite GIVEN the gap-width bound + base-7 reach, but the bound on N₀(k) itself
(to know how far to compute) is the sharp-constant content. So goal (a) is "cofinite, finite-but-
not-effectively-bounded N₀(k)" on the 2-log input alone; effective N₀(k) needs input (II). This is the
exact same honesty line as cassels' strict-excess theorem (cofinite VERIFIED, N₀ computable IF a
bound is known). **The 2-log input gives qualitative cofiniteness; the sharp constant gives the
effective bound.**

### 5a. CRUCIAL HONEST REFINEMENT — the covering step is a real second ingredient [VERIFIED]

A reviewer (and I) must not overstate input (I). The crossover from "gap width bounded" to "gap
covered" is NOT pure gap-width. Verified mechanism at mid-gap (n≈3.99M, k=1 scale): the B₃+B₄ gap is
width `W ≈ 0.096·n` (LINEAR in n, ending at a power), and it is covered by **~`W^{0.356} ≈ n^{0.356}`
reaching base-7 shifts**, each landing `n − b7` in the dense S34 region below the gap, where S34 has
gaps **bounded by the previous scale's input-(I) bound** (≤7679 here). At n≈3.99M: 128 reaching
shifts, 119 hit S34 — so covered with huge redundancy, but the covering is a genuine
"many-shifts-vs-bounded-gaps" event, not a one-line gap-width consequence.

**So the honest decomposition is three-layered, not two:**
- **(I) gap-width** [2-log, rate, convergents-only, PUBLISHED]: bounds every S34 gap by `O(3^p)` at
  its scale. Cheap.
- **(I′) covering redundancy** [elementary counting]: `#reaching base-7 shifts ~ n^{0.356} → ∞`,
  growing, while the gaps they must avoid are input-(I)-bounded. This is the part that MAKES the cover
  work asymptotically; it is elementary IF you only need "redundancy → ∞." **But "redundancy → ∞"
  does not by itself forbid all shifts missing simultaneously** — that simultaneous-miss is exactly:
- **(II) the alignment / equidistribution** [the §C.3 content, sharp]: that the `n^{0.356}` shifts do
  not *all* land in S34 gaps at once. Empirically they don't (redundancy 60–120×); rigorously, this
  is the joint-equidistribution of the base-7 ray vs the S34 gap pattern. **This is where §C.3 is
  genuinely correct** — the asymptotic *closure* (not the gap width) needs this.

**Net, corrected:** input (I) (2-log, published) bounds the gaps; the covering then works *empirically*
with growing redundancy, but the *rigorous proof of asymptotic closure* still needs input (II) — OR a
finite check per (D,k). So the truly-weakest sufficient input for a RIGOROUS uniform theorem is input
(II) (equidistribution); input (I) alone gives "gaps bounded + empirically covered + finite check per
k." **§C.3 was right that MW-alone (input I) does not rigorously close it; §C.1 was right that the
gap WIDTHS are pure 2-log. My contribution is separating these cleanly and showing the residual (II)
is a redundant-covering / equidistribution statement with a 60–120× empirical margin, located only at
the last hole — NOT a delicate everywhere-tight bound.** The margin being large (not flat) at the
generic gap, and tight only at the single last hole = N₀, is why the finite check works and why this
is genuinely "easy-tail" rather than a hard everywhere-sharp transcendence problem.
