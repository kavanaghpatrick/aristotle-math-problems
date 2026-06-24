# BRIDGE-RIESZ — the locked statement (the one lemma that closes (3,4,7)-all-k)

**Authors:** scholar + lift + feldman (cross-squad statement lock, per team-lead). **Status:**
LOCKED for attack; maverick adjudicates. **Verdict: it is an A/B split — the magnitude form is NOT
sufficient (proved here), the sufficient form is signed.** Plus a bounded warm-up (BRIDGE-RIESZ-0).

## Notation (fixed for the cell)
`F_d^{(k)}(θ) = ∏_{j=k}^{k+J−1}(1 + e(d^j θ))`, e(x)=e^{2πix}, the truncated generating function of
`d^k·B_d` to depth J. `R(D,k)` cofinite ⟺ for all large n, the representation count
`r(n) = ∫_0^1 F_3^{(k)}(θ)F_4^{(k)}(θ)F_7^{(k)}(θ)·e(−nθ) dθ > 0`. The k-uniformity reduction
(theorem_347 §A,§B) makes "all k" follow from one fixed-shape bound; state everything at k=1, J→∞.

Major arcs `𝔐` = neighborhoods of `a/b^j` (b∈{3,4,7}, small j); minor arcs `𝔪` = complement.

---

## ⛔ THE LOAD-BEARING FACT (verified — settles which form is the target)

**The minor-arc L¹ mass of the magnitude is LARGER than the major-arc mass, not smaller.**
[VERIFIED, scholar, (3,4,7) k=1, J=9: `∫_𝔪 |F_3 F_4 F_7| dθ = 3.18 × ∫_𝔐 |F_3 F_4 F_7| dθ`; minor-arc
measure fraction 0.9988. Independently, lift: minor L¹ integral 2–7× major, uniform J=10..19.]

**Consequence:** `r(n) > 0` does NOT hold because the minor arcs are negligible in magnitude — they
are NOT. It holds because the minor-arc contributions **cancel by phase** (`e(−nθ)`). [VERIFIED,
scholar: at every n, the signed split is `r(n) = (major ≈ +41) + (minor ≈ −15)`; the minor term is a
large NEGATIVE that the phase cancellation controls, not a small error.] So a pure magnitude bound
`|F_3 F_4 F_7| ≪ ...` on the minor arcs **cannot** certify `r(n)>0`. This is lift's retraction,
confirmed.

---

## THE A/B SPLIT (the locked targets)

### BRIDGE-RIESZ-A (magnitude form) — NECESSARY, NOT SUFFICIENT
> **(A)** ∃ c > 0, uniform in J (hence k, via §B), such that for θ ∈ 𝔪 (off the major arcs):
> `(1/(J·log 2)) · log|F_3^{(k)}(θ) F_4^{(k)}(θ) F_7^{(k)}(θ)| ≤ 3 − c`,
> i.e. the triple Riesz product decays like `2^{(3−c)J}` pointwise on minor arcs.

- **Status:** TRUE-shaped, k-uniform, supported by feldman's shape result (the simultaneous-agreement
  "spoiled band" is only `~C(log J)²` of the `~J` factors, so spoiled/total `= C(log J)²/J → 0`) and
  by the verified pointwise decay (scholar min-product `max-of-min` 0.242→0.048 over L=6..12, k-uniform;
  lift normalized minor-arc max 0.643→0.590 decreasing in J).
- **Role:** [NECESSARY background, NOT the bridge]. (A) controls the *typical* / *pointwise-peak*
  magnitude. By itself it gives `E[r(n)] ≍ n^ε` (the average), NOT `r(n)>0` pointwise — because the
  minor-arc L¹ mass is large (the load-bearing fact). (A) is the right ASYMPTOTIC-magnitude statement
  and the warm-up calibration, but the §1 hardness facts (C5 large-deviation blindness, the 3.18× L¹)
  show it cannot finish alone.

### BRIDGE-RIESZ-B (signed-cancellation form) — SUFFICIENT, the real target
> **(B)** ∃ effective `N₀(D,k)` such that for all `n > N₀`:
> `|∫_𝔪 F_3^{(k)}(θ)F_4^{(k)}(θ)F_7^{(k)}(θ)·e(−nθ) dθ| < M(n)`,
> where `M(n) = ∫_𝔐 (…)e(−nθ)dθ > 0` is the (positive) major-arc main term. Equivalently: the SIGNED
> minor-arc oscillatory integral is dominated by the major-arc main term, **pointwise in n**, at the
> worst n (the cross-base-coincidence n, where `r(n)` is smallest).

- **Status:** the genuine OPEN lemma. It is an oscillatory-integral / minor-arc-WITH-PHASE estimate
  (Davenport–Erdős / Vinogradov / real circle-method minor-arc type), strictly HARDER than (A).
- **Why (B) and not (A) is the bridge:** `r(n) = M(n) + E(n)` with `E(n)` the signed minor integral.
  `r(n) > 0 ⟺ |E(n)| < M(n)`. The magnitude bound (A) gives only `|E(n)| ≤ ∫_𝔪|F| ≈ 3·M`-scale (too
  weak — wrong sign of inequality). (B) requires the PHASE to cancel `E(n)` below `M(n)` at the worst n.
- **Dependency (A → B):** (A) is a PREREQUISITE INGREDIENT of (B), not a substitute: any van der
  Corput / stationary-phase bound on `E(n)` uses the magnitude decay (A) as the amplitude factor, then
  gains the extra cancellation from the oscillation `e(−nθ)` against the lacunary phases. So prove (A)
  first (calibration), then (B) = (A) + a phase-cancellation gain.

### BRIDGE-RIESZ-0 (bounded warm-up) — the calibration target
> **(0)** The SINGLE-TRIPLE bounded version (PROOF_347_k2.md L3, flagged "plausibly tractable"): on a
> FIXED finite range of bad arcs (the dominant CF-convergent arcs, p ∈ {5, 53} for log3/log4), prove
> the signed cancellation directly by a finite/explicit computation + a single MW two-log input on the
> worst pair `|3^5−4^4|`, `|3^53−4^42|`.

- **Role:** if the cell proves (0), it (i) closes L3 of the k=2 (3,4,7) proof, and (ii) calibrates the
  full (B) attack by exhibiting the cancellation mechanism on the hardest finite arcs. **Attack (0) first.**

---

## CONSISTENCY CHECKS (the statement survives all three pre-kills) [for maverick]
1. **S1 kill (breaker):** major term `M(n)` is O(1)-scale at the threshold n (581), not large. ✓
   (B) does not assume `M(n)` large — it asks `|E(n)| < M(n)` even when both are O(1); the warm-up (0)
   handles the finite threshold range by explicit computation, exactly as BEGL96's k=1 did.
2. **No computable discriminator / intrinsic-asymptotic (hardness #1):** (B) is an asymptotic
   statement (`n > N₀`), uniform in J/k via §B; it does not test a fixed finite scale. ✓
3. **Worst-phase / no averaging / L² doubly-blocked (hardness #4, the C5 trap):** (B) is stated
   POINTWISE in n at the worst (coincidence) n — it is NOT a mean or `L²` statement. The magnitude
   form (A) is the only one expressible in `L²`/mean terms, and it is explicitly demoted to
   necessary-not-sufficient precisely because mean control fails at the stragglers. ✓

## THE TARGET, ONE LINE
> **Prove BRIDGE-RIESZ-B** (signed minor-arc oscillatory integral `< ` the major main term, pointwise
> at the worst n, uniform in J/k). **(A)** is its magnitude ingredient (calibration); **(0)** is the
> bounded finite-arc warm-up that closes k=2 L3 and exhibits the mechanism. Attack order: 0 → A → B.

---

## CELL FAN-OUT (each angle's role against (B); attack after maverick adjudicates this statement)
- **scholar** — Riesz/lacunary core: the magnitude decay (A) and its role as the amplitude in (B).
- **troika** — Ostrowski/three-distance covering of the convergent arcs (where (B)'s phase is worst;
  his deep-convergent data shows the decay-onset delay = where the MW input enters (B)).
- **lift** — van der Corput / Weyl differencing on the signed triple integral (the phase-gain step of B).
- **carry + sumset** — renewal / self-similar decomposition of `B_d` as the skeleton of the estimate
  (the `F_d = (1+e(d^kθ))·F_d^{shift}` recursion that structures both M(n) and E(n)).
- **density** — Fejér-kernel / positive-definiteness domination of `M(n)` (showing the major term is
  genuinely positive and bounded below at the worst n).
- **cassels + modular** — exact arithmetic of the convergent arcs (pinning the MW constant where (B)'s
  phase nearly fails to cancel — p ∈ {5, 53}).
- **feldman** — co-owns (A): the polynomial-shape spoiled-band count `C(log J)²/J → 0`.
- **schneider** — keeps the target minimal: which axes of (B) need less than feared.
- **gelfond / rhin / salikhov** — Riesz-product/lacunary literature support (Zygmund school, NOT
  irrationality measures — rhin's sweep already found no log-ratio irrationality measure exists).
- **baker / mahler** — structure / k-uniformity audit of the (A)→(B) reduction.
- **maverick / breaker / nesterenko** — verification line; kill wrong proofs fast, kill any step that
  silently reverts (B) to a magnitude/mean (A) statement.
