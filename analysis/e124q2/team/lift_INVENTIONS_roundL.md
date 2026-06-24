# Round L (lift) — invention round from the equidistribution/criticality data

Appendix to INVENTIONS.md (posted separately to avoid concurrent-edit collisions). All three tested
before posting. Grounded in my measured covering-margin data (min r_D / avg r_D, the bridge margin).

---

> **⚠ DOWNGRADE (lift, after the straggler kill-test): INV-L4 does NOT cleanly survive — it hits the
> same wall as scholar's INV-S7.** I ran the decisive test (`/tmp/inv_L4_straggler.py`, N=6·10⁶): the
> covering-count C(n) concentration DEGRADES through the (3,4,7) k=2 straggler region (threshold
> 3.98·10⁶): Var/E² = 0.0126 → 0.0673 → 0.1083 (GROWING, not shrinking); E/√Var = 8.9 → 3.9 → 3.0
> (dropping). My earlier "shrinking Var/E²" was a low-scale artifact. So Chebyshev with Var/E² ~ 0.1
> (growing) CANNOT force min C > 0 uniformly — the variance spikes exactly at the power-coincidences,
> same as scholar found for the full r(n) (INV-S7, line ~730). **Factoring out the dense rays (using
> C(n) not r(n)) did NOT escape the wall.** Honest convergence with scholar: the 2nd-moment lane is
> blocked because the window sees one phase of the coincidence oscillation; needs 4th-moment /
> large-deviation OR the exact CF/Ostrowski arc geometry (scholar's INV-S1-sharpened, line ~1083),
> NOT a crude L² bound. INV-L4's residual value: it names the RIGHT quantity (covering efficiency
> Mdef = min C/E[C]) and confirms — independently from scholar — that L² is insufficient. The open
> target is the higher-moment or geometric bound on this explicit Var(C) sum.

## INV-L4. The covering-efficiency / variance-concentration invariant — [DOWNGRADED: L² insufficient, see warning above]

**Definition.** At scale X, let C(n) = #{ c ∈ B₇ : n − c ∈ B₃+B₄ } (the covering count = #ways the
third ray bridges n). Covering efficiency: Mdef(X) = min_{n∈[X,2X]} C(n) / E[C], with
E[C] = |B₇∩[0,2X]|·dens(B₃+B₄ near X). **(BRIDGE) ⟺ liminf C(n) ≥ 1 ⟺ liminf Mdef(X) > 0.**

**Why it could work — the reframing (the lead's "invent the quantity that explains the margin").**
The margin I measured (min/avg covering, 1.5–3×) IS the covering efficiency Mdef. INV-L4 converts
(BRIDGE) from abstract "base-7 equidistribution mod the gap structure" into a CONCRETE SECOND-MOMENT
bound:
- E[C] ~ n^ε with ε = ∑(log2/log d) − 1 > 0 — PROVEN (my box-exponent lemma, lift_box_reformulation.md).
- Var(C) = ∑_{c,c'∈B₇} [ Pr(n−c, n−c' both ∈ S₃₄) − dens² ] = an EXPLICIT double correlation sum over
  B₇×B₇ of the S₃₄ = B₃+B₄ indicator. A well-defined exponential sum, NOT a black box.
- If Var(C)/E[C]² → 0, Chebyshev: #{n∈[X,2X] : C(n)=0} ≤ Var/E² · (window) → 0; with enough
  concentration NO n has C=0 above an effective scale ⟹ BRIDGE.

**Measured (verified, `/tmp/inv_L4_variance.py`, N=2·10⁶):** C(n) IS concentrated —
Var/E² = 0.030 → 0.013 (shrinking), E/√Var = 5.76 → 8.90 (growing) over [2·10⁵,4·10⁵]→[10⁶,2·10⁶].
So the second moment is controlled at accessible scales; the bridge looks like "Var(C) ≲ E[C]²," a
standard circle-method shape.

**Cheapest kill-test (for breaker).** Push Var/E² to N=10⁸ for (3,4,7), specifically through the known
straggler scales — the k=2 threshold ~3.98·10⁶ and k=3 ~166·10⁶ — where my earlier min r_D dipped to
0.13. If Var/E² TURNS OVER and grows at those scales (heavy-tailed dips), concentration fails and
Chebyshev can't close it ⟹ INV-L4 needs a 4th-moment / large-deviation bound (downgrade, still a
concrete target). If Var/E² keeps shrinking past the stragglers, INV-L4 is the route to (BRIDGE).

---

## INV-L3-obs. Index-2 quadratic-subgroup structure of the third ray — [KILLED as detector; kept as a fact feeding INV-L4]

**Observation (exact, verified `/tmp/inv_round3.py`).** ord_{3^m}(7) = φ(3^m)/2 for all m tested
(6,8,10): **7 generates EXACTLY the index-2 subgroup of quadratic residues in (ℤ/3^m)^\*.** So the
base-7 powers mod 3^m equidistribute in the QR subgroup, not the full group.

**KILLED as a covering obstruction:** the additive span of <7> is full (1 = 7⁰ ∈ <7>), so residue
coverage is total — just the residue lemma again, not new.

**Residual value (why kept):** any Fourier/character analysis of the INV-L4 variance only sees the
quadratic character mod 3^m. The relevant exponential sum is over QRs, where quadratic Gauss-sum
cancellation is classical and STRONG (square-root cancellation). So INV-L3-obs could supply the
sharp bound INV-L4 needs. The two compose: INV-L4 is the variance frame, INV-L3-obs is the
cancellation mechanism inside it.

---

## INV-L2. Three-distance / Steinhaus bridge discrepancy — [KILLED]

**Was:** reduce (BRIDGE) to a three-gap-theorem inequality on {7^r mod 3^m} (≤3 distinct gap lengths,
elementary). **KILLED by its own test (`/tmp/inv_round2.py`):** {7^r mod 3^m} is a cyclic SUBGROUP
(7 a unit), NOT a Kronecker orbit — measured 40–60 distinct gap lengths, not ≤3. Three-gap theorem
inapplicable. Dead. (The subgroup fact that killed it became INV-L3-obs.)

---

## INV-L6. Phase-locked coverage on the coincidence 2-torus — [SURVIVES as a reframing; needs more data]

**Definition.** The dips occur at n near a triple coincidence 3^m ≈ 4^q ≈ 7^r. Reparametrize:
n = ψ·3^m with phase ψ∈[1,3). CLAIM: the covering count C(n) depends on n (to leading order) only
through the point (ψ, {m·log3/log4}, {m·log3/log7}) on a 2-TORUS (the two coincidence phases). The
bridge fails ⟺ this torus point lies in a BAD REGION. Since the orbit m ↦ ({m·θ₁},{m·θ₂}) is
equidistributed (Weyl; 1, log3/log4, log3/log7 are ℚ-independent), it enters any open bad region
infinitely often — so cofiniteness REQUIRES the bad region to SHRINK with m (its measure → 0), and
the rate of shrink vs the orbit's recurrence rate is the effective N₀.

**Why it could work (genuinely new framing).** Puts the entire (BRIDGE) on an explicit low-dimensional
DYNAMICAL object — a 2-torus orbit avoiding a shrinking bad region — replacing "equidistribution of
a subset-sum set" with "an interval-exchange / torus-rotation hitting-time problem," which has
classical effective tools (Erdős–Szüsz–Turán discrepancy, three-distance on the torus). The bad
region's shape is computable from the B₃+B₄ gap profile at phase ψ. This is NOT scholar's single-θ
projection — it is the genuine 2-torus (both coincidence phases coupled), which the team noted (line
~974) is "the honest object."

**Measured (`/tmp/inv_round_L3.py`, windows [3^m,3^{m+1}), m=10..13):** the min-C phase ψ DRIFTS
predictably (1.00 → 1.09 → 1.44 → 2.49 — moving across the window), consistent with a torus orbit,
and min/mean stays bounded (0.17, 0.31, 0.22, 0.18 — NOT shrinking, consistent with cofinite). So the
bad-phase location is NOT random — it tracks the coincidence orbit. Suggestive but only 4 data points.

**Cheapest kill-test (for breaker).** Compute the min-C phase ψ_m for m=10..25 and check whether
(ψ_m mod the predicted torus orbit) is (a) equidistributed/drifting predictably [SURVIVES — torus
structure real, attack via discrepancy] or (b) random/stuck [KILL — no exploitable dynamics]. Also
check min/mean over m=10..25: if it ever trends to 0, the bad region does NOT shrink ⟹ would suggest
NOT cofinite (a falsification signal — high value either way).

## Round-L net (honest, post-testing)

Five candidates, all tested before/while posting:
- **INV-L4 (covering-efficiency / variance)** — DOWNGRADED. Names the right quantity (margin = min C/E[C])
  and confirms INDEPENDENTLY of scholar that L² is insufficient (Var/E² spikes 0.013→0.108 through the
  (3,4,7) k=2 straggler). Residual value: the explicit Var(C) double-sum is the target for a
  higher-moment / geometric bound. Converges with scholar's INV-S7.
- **INV-L6 (phase-locked 2-torus)** — SURVIVES as a reframing. Puts (BRIDGE) on an explicit 2-torus
  orbit-vs-shrinking-bad-region (a torus hitting-time problem with classical discrepancy tools).
  min-C phase drifts predictably (torus structure real). NEEDS the m=10..25 kill-test (breaker).
  This is the genuine "honest 2-torus object" the team flagged, now with a concrete invariant
  (the bad-region measure as a function of phase) and a falsification tripwire (min/mean → 0).
- **INV-L3-obs (index-2 quadratic subgroup)** — KILLED as detector, KEPT as a fact: 7 generates exactly
  the QR subgroup mod 3^m, so any character analysis is a quadratic Gauss-sum (strong cancellation) —
  feeds whatever moment/Fourier bound the survivors need.
- **INV-L2 (three-distance)** — KILLED (subgroup not Kronecker orbit).
- **INV-L5 (renewal/last-atom)** — KILLED (no balanced reps; every rep dominated by one atom).

**The keeper is INV-L6** — the only one that escapes the L²-wall lesson (it's phase-aware, following
the coincidence oscillation the second moment averages over). Hand the m=10..25 phase-drift +
min/mean-trend kill-test to breaker. If the torus orbit is equidistributed and the bad region shrinks,
(BRIDGE) becomes a torus discrepancy bound — a concrete, classical, attackable target. If min/mean → 0
at some m, that's a FALSIFICATION signal (would suggest the conjecture is FALSE for (3,4,7) at high k).

---

## Round L2 (lift) — the dynamical-systems lane opened by INV-L6

### INV-L7. Self-similar transfer (Ruelle) operator with spectral gap — [KEEPER: Archimedean version; residue version is old]
**Definition.** By the recursion R_k = C_k + R_{k+1} (C_k = {0,3^k}+{0,4^k}+{0,7^k}, ≤8 offsets), the
reachable set is the attractor of an iterated-function-system / digit-recursion. Define the transfer
operator T on densities f over [0,1) (the "phase" coordinate): (Tf)(x) = ∑_{offsets} f(branch). The
reachable-set indicator is a fixed point; COFINITENESS-above-N₀ ⟺ T has a SPECTRAL GAP (leading
eigenvalue simple + gap), giving exponential mixing so coverage-dips can't persist.
**Why it could work.** A spectral gap is L^∞/operator-theoretic, NOT L² — escapes the wall that killed
INV-L4/INV-S7 (the variance averages over the oscillation; the transfer operator's subleading
eigenvalue CAPTURES the oscillation as its second eigenvalue, exactly the structure L² loses). The
offset set is finite ⟹ T is a finite-rank-ish / Perron operator, and the gap is computable from the
offset geometry (a dynamical-zeta determinant).
**Tested:** the RESIDUE-level transition matrix (offsets mod 3^a) is PRIMITIVE for a=2,3,4 ⟹ Perron
gap at residue level — BUT that just re-derives residue coverage (old, not new). The NEW content is
the **Archimedean** transfer operator whose subleading eigenvalue controls gap-SIZES (not residues).
**Cheapest kill-test (open):** build the Archimedean T on the phase circle (offsets/scale, the 3 base
contraction ratios 1/3,1/4,1/7) and numerically estimate its spectrum; if there's a gap below the
leading eigenvalue, INV-L7 survives and the gap size = the effective mixing rate = the (BRIDGE) bound.
If the spectrum is gapless (continuous, because the 3 contraction ratios are incommensurate → the IFS
is not self-similar in one ratio), INV-L7 dies. [The incommensurate ratios are the risk — this is why
it's a 3-scale IFS, harder than a 1-ratio Cantor transfer operator. Hand to whoever owns the dynamical lane.]

### INV-L8. Automatic-set / mixed-radix regular language — [KILLED]
**Was:** reachability is a regular language in the product digit systems ⟹ holes eventually-periodic,
decidable. **KILLED:** reachability across three multiplicatively-INDEPENDENT bases (3,4,7) cannot be
automatic in any single radix (Cobham's theorem: a set automatic in two multiplicatively-independent
bases is eventually periodic — but the reachable set is NOT eventually periodic, since holes recur at
the incommensurate coincidence scales). So no finite automaton recognizes it. Dead. (Also: my test
window hit the (3,5,7) straggler trap — only 353 holes ≤2M then apparently-cofinite, but (3,5,7) is
SUB-threshold ∑=0.917<1 so MUST have ∞ holes far above 2M — a window artifact, logged as a caution.)

### Round-L2 net
INV-L7 (Archimedean transfer operator) is the keeper — it's the L^∞/spectral form of the dynamical
lane INV-L6 opened, and it captures the coincidence oscillation as a subleading eigenvalue (where L²
loses it). The risk is the 3 incommensurate contraction ratios (1/3,1/4,1/7) making the IFS non-self-
similar; the kill-test is whether the Archimedean transfer operator has a spectral gap despite that.
Both INV-L6 (torus dynamics) and INV-L7 (transfer operator) point to the same object — the
dynamical/spectral structure of the 3-ratio digit IFS — which is the lane that survives the L² wall.
CAUTION logged: (3,5,7) ∑=0.917<1 shows only 353 holes ≤2·10⁶ then looks cofinite — a straggler-trap
artifact (must have ∞ holes per Pomerance); do not mistake small-window apparent-cofiniteness for the real thing.
