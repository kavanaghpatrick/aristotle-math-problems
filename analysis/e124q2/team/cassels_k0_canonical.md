# E124 k=0 base case — CANONICAL [KNOWN, base case] (cassels + maverick, merged)

**STATUS: [KNOWN] — not novel.** This is the k=0 instance of Erdős #124 (the `erdos124.zero`
statement). It is a corollary of Brown 1961 / Erdős 1962 interval-filling, and has a PUBLIC proof:
Alexeev 2025 (Erdos124b.lean, 407 lines, plby/lean-proofs, Dec 2025; described on Bloom's Xena blog).
We record a clean self-contained re-derivation as the base case of the REDUCTION_THEOREM stack.
DO NOT publish as new; DO NOT submit as open. Citations: Brown 1961 ("complete sequences"), Erdős
1962; the often-cited "Cassels 1960" is a PHANTOM reference (team-confirmed) — do not use it.

Authorship: cassels (statement + exposition, §1–2) + maverick (boundary-tightness §3, k≥1
lift-obstruction §4). Two fully independent derivations agree; numerics cross-verified both ways.

## §1. Statement + attribution
> **Theorem (k=0).** Let D = {d_1<…<d_r}, all d_i ≥ 3, with ∑_{d∈D} 1/(d−1) ≥ 1. Then
> ∑_{d∈D} B_d = ℕ — EVERY nonnegative integer is a sum ∑_d a_d with a_d ∈ B_d (0/1-digit base d).
> (Stronger than cofinite: no exceptional set; contiguous from 0. No gcd condition needed at k=0.)

= Erdős [Er97] conjecture, k=0 / `erdos124.zero`. KNOWN: Alexeev 2025 public Lean proof; Brown 1961
interval-filling corollary. gcd not needed because d^0=1 ∈ B_d makes every residue free.

## §2. Proof (Brown/Erdős interval-filling; cassels' m = min(d·x_d) exposition)
The pointwise sumset ∑_d B_d = subset sums of the atom multiset A = {d^j : d∈D, j≥0} (bijection:
subsets of A indexed by (d,j) ↔ tuples (a_d); value collisions kept by index). Sort A ascending.

**Gap-condition (the engine).** For any X≥1, let S(X) = ∑ of atoms ≤ X = ∑_d (d·x_d − 1)/(d−1)
(geometric series; x_d = largest d-power ≤ X). Let m = smallest atom > X = min_d (d·x_d). Since
d·x_d ≥ m for every d:
> S(X) = ∑_d (d·x_d − 1)/(d−1) ≥ ∑_d (m−1)/(d−1) = (m−1)·∑_d 1/(d−1) ≥ (m−1)·1 = m−1.
So m ≤ S(X)+1, the Brown/Erdős interval-filling gap-condition, at EVERY threshold X. With a_1 = 1
(= d^0 ∈ B_d) seeding [0,1], interval-filling gives [0, S(X)] ⊆ ∑_d B_d for all X ⟹ ∑_d B_d = ℕ. ∎
[VERIFIED: closed-form S(X)=∑(d·x_d−1)/(d−1) and m=min(d·x_d) exact vs direct atom-sum, 4 families,
X≤10⁵, 0 mismatches (maverick); 0/8000 gap-condition violations to 10¹⁵ (cassels).]

**The diameter metric = the renormalization budget (cassels).** The estimate above is the discrete
shadow of a covering/thickness fact. Each base d contributes the self-similar Cantor set
C_d = {∑_{j≥1} e_j d^{−j} : e_j∈{0,1}} of DIAMETER τ_d := ∑_{j≥1} d^{−j} = **1/(d−1)** in its unit
cell, anchored at every integer. So ∑_{d∈D} 1/(d−1) ≥ 1 is exactly "∑ of diameters ≥ the unit gap (=1)
between integer anchors" — a covering condition (NOT a Newhouse gap-ratio, which gives the wrong
1/(d−2); validated: 2-set threshold B_a+B_b cofinite ⟺ 1/(a−1)+1/(b−1)≥1, 8/8). In maverick's
renormalization framing T_k=C_k+T_{k+1}, τ_d=1/(d−1) IS the per-cell renormalization budget and the
fixed-point "cell covered ⟺ ∑ diameters ≥ 1" is exactly Brown's interval-filling — same proof, three
languages (Brown gap-condition / renormalization fixed-point / diameter-covering). The k=0 seed is
C_0={∑e_d·d^0}=[0,r] (contiguous, r=|D|) — the unit atoms give the seed for free; ∑1/(d−1)≥1 propagates it.

## §3. Boundary tightness (∑1/(d−1)=1, e.g. (3,4,7)) — maverick
At the harmonic boundary the estimate is TIGHT but holds. Margin := S(X) − (m−1) ≥ 0 is the
gap-condition. Computed for (3,4,7) k=0 over all atoms: margin = 1 (X=1), 3 (X=3), 4, 9, 11, …
> **The minimum margin = 1, attained at the smallest atoms** (the three unit atoms 3^0=4^0=7^0=1
> give S(1)=3, m=3, margin 3−2=1). The gap-condition holds THROUGHOUT (margin ≥ 1 at every atom for
> k=0). (The single-base-power "tightness at d_max^J" is a single-ray artifact — the MERGED predecessor
> sum stays ≥ the atom.) **REFINEMENT (maverick, k=1 merged predecessor sum to 10^1300):** the earlier
> "ratio S(X)/X ∈ [1.25, 2.4]" was only checked at d_max-powers; the TRUE infimum over ALL atoms is
> ~1.006 and DEEPENING (no positive floor established), at atoms just above the closest cross-base
> coincidences (|3^p−4^q|, |3^p−7^r| near-equalities). The gap-condition (margin ≥ 0, i.e. atomSum ≥ v)
> still HOLDS — that's what k=0 needs — but the thin/deepening margin atomSum/v−1 → ~0.0056 is itself
> the δ>0 open MW core (a STRICTLY STRONGER question than ≥v). Do NOT quote [1.25,2.4] as the margin.
Why it holds even at ∑=1: a value a is a power of at most ONE base in an admissible D (two
common-power bases would force ∑1/(d−1)<1), so at least one base contributes a STRICT d^{m+1}>a,
giving the +1 slack. [VERIFIED (3,4,7): min margin over power-atoms = 1, no failure.]

## §4. Why k≥1 is harder — the lift-obstruction (maverick) [bridge to the OPEN part]
The k=0 proof rests entirely on **a_1 = 1** (the d^0 unit atom) seeding the interval from 0. At k≥1
the atoms are {d^j : j≥k}, so the smallest atom is d_min^k > 1 — **the unit seed is GONE.** Two
consequences:
- Brown/Erdős interval-filling REQUIRES a_1=1 to start [0,S_i] from 0; with a_1=d_min^k>1 the small
  integers 1..d_min^k−1 are unreachable and the induction has no base — the seed must be MANUFACTURED.
- The merged reciprocal mass degrades: ∑_d d^{1−k}/(d−1) < ∑_d 1/(d−1) for k≥1 (decays in k).
So the entire k≥1 difficulty = **"regain the seed without the unit atom"** — which forces the gaps
below n₀(k) to be closed by cross-base RESIDUE coverage + power-spacing, i.e. Mignotte–Waldschmidt /
Baker territory. This is the precise bridge from the [KNOWN] k=0 base case to the OPEN k≥1/Q2 core.
(NB: gcd(D)=1 is needed only for k≥1 — exactly because the unit atom that made residues free at k=0
is gone.)

**Why no finite-state/renormalization shortcut at k≥1 (cassels, the rigorous form of "V2 dies").**
A finite transfer-matrix / renormalization fixed-point would need the reachable-residue cell-state mod
d_min^s to STABILIZE to a bounded set as s grows. It does NOT: for (3,4,7) k=1, R(D,k) hits ALL of
ℤ/3^s for every s (VERIFIED s=1..8: residues-hit = 3,9,27,81,243,729,2187,6561 = 3^s, full each time).
So the cell-state is MAXIMAL/unbounded ⟹ no finite transfer matrix ⟹ the renormalization fixed-point
has no finite cell at k≥1 (= sumset's M5 non-automaticity, maverick's V2 death, confirmed from the
renormalization side). The precise tension: full-ℤ/3^s coverage is the gcd=1 residue lemma working FOR
cofiniteness, but AGAINST a bounded transfer matrix — the cell-state the renormalization must track is
exactly the thing the residue lemma makes unbounded. At k=0 this doesn't bite (the C_0=[0,r] unit-seed
is a finite contiguous block, no unbounded carry); at k≥1 the seed is gone and the state blows up. This
is the clean structural "why the k=0 renormalization/Brown proof does NOT lift."

## Slot
[KNOWN, base case] → REDUCTION_THEOREM §base-case. Open part (k≥1) is the rest of the stack; §4 is the hinge.

## cassels VERIFICATION PASS — SIGNED OFF (all checks pass)
- §2 proof + estimate S(X)=∑(d·x_d−1)/(d−1) ≥ (m−1)·∑1/(d−1) ≥ m−1: re-verified, correct and exact.
  Merged-atom = sumset bijection (incl. the |D|-fold multiplicity of the value 1): re-confirmed (my
  earlier 0-diff test on [0,300000]). The "value collisions kept by index" phrasing is right.
- §3 boundary-tightness (margin := S(X)−(m−1), min = 1 at smallest atoms for (3,4,7) k=0): VERIFIED
  exactly — margins 1,3,4,9,11,16,… (X=1,3,4,7,9,16,…), min = 1 at X=1 (S(1)=3, m=3). Holds, never
  fails at large scale. **Convention reconciliation NOTED:** the earlier cassels "margin = 0" was for
  k=1 (smallest atom 3, no unit seed: S(3)=3, m=4, margin 0); maverick's "margin = 1" is k=0 (unit
  atoms present: S(1)=3, m=3, margin 1). Different k — both correct, no contradiction.
- §4 lift-obstruction (a_1=1 seed gone at k≥1; reciprocal mass ∑d^{1−k}/(d−1)<∑1/(d−1); gcd=1 needed
  only k≥1): correct, and it is the precise hinge to the open core. ✓
**Sign-off: this canonical k=0 file is correct, faithfully attributed [KNOWN, Brown/Erdős/Alexeev,
phantom Cassels excluded], and ready to slot into REDUCTION_THEOREM §base-case. — cassels.**
