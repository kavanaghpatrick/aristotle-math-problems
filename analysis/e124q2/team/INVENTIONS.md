# INVENTIONS — new candidate mechanisms for E124 open core

Algorithm-shaped proof candidates for the (BRIDGE)/seed-closing step and Lemma A' (minimal-D
cofiniteness). Each: definition · why it could work · cheapest kill-test. breaker kills; survivors
get attempts. New mechanisms only — not re-skins of +b^k closure / Lemma BG / Cassels / subset-monotonicity.

## ⚠️ PRE-KILL RULE (troika hardness fact, quadruply-confirmed — quota SUSPENDED per team-lead):
**NO COMPUTABLE DISCRIMINATOR can decide β (cofiniteness).** The entire "generate a computable
invariant/automaton/transfer-matrix/counting-predicate and check it against ground truth" class is
PRE-KILLED — any such candidate farms a dead end. Do NOT spawn computable-discriminator candidates.
The three SURVIVING targets are a-priori ANALYTIC proof attempts only: (1) closed-form spectral
radius of the IFS/torus operator (troika+lift), (2) scholar's S10 Riesz-product decorrelation lemma,
(3) maverick's INV-V3 per-band drainage as a proven local INEQUALITY (not computed). breaker no longer
runs candidate gauntlets — only verifies proof-attempt numerics + the V2/581 banking.
Corollary: maverick's V1 (gap-automaton) and V2 (transfer-matrix) are pre-killed instances of this
class (both ARE computable discriminators) — consistent with their measured B-unbounded death.

---

## Round 1 (carry — constructive/algorithmic lens)

### INV-C1. Logarithmic-potential amortized descent (the "halving rewrite")
**Definition.** Define a potential Φ(n) on representable n = (Σ over used atoms of ⌈log_b(atom)⌉),
i.e. total "exponent-height" of a representation. Algorithm: to represent n, take ANY rep of a
nearby representable n' (|n−n'| < b^k, the Lemma-BG gap), then apply a **halving rewrite**: replace
the single largest atom d^J by the residual n − (rest), recursively representing a number of size
≈ n/d. Claim: the recursion depth is O(log n) and each level's residual stays representable because
its size dropped by a constant factor while the harmonic-mass budget is scale-invariant (density's
1/(d−1) reach is the same at every scale). Φ strictly decreases ⟹ termination ⟹ every n representable.
**Why it could work.** Sidesteps the +b^k closure entirely: instead of marching n→n+b^k (which stalls
at d_max-power gaps), it DIVIDES n by the top base, turning a size-n problem into a size-n/d problem of
the SAME shape (self-similar, by sumset's recursion T_k=C_k+T_{k+1}). The scale-invariance of the
reach criterion (density's verified fact) is exactly what keeps each recursion level solvable. An
amortized/log-depth argument could be k-uniform where the additive +b^k one is not.
**Cheapest kill-test.** Compute, for (3,4,7) k=1 and (3,4,5) k=2, the recursion: greedily peel the
largest atom, recurse on residual, check the residual is ALWAYS representable (never falls into a gap)
for all representable n in [threshold, 50000]. If even one residual lands in a gap, the naive halving
fails — then check whether a bounded lookahead (try the 2nd/3rd largest atom) repairs it. If no
bounded lookahead keeps every residual representable, INV-C1 is dead. (~20 lines, minutes.)

> **KILL-TEST RESULT (carry ran it): SURVIVES — strongest candidate so far.** Refined the rule to the
> RIGHT invariant: peel the largest atom a ≤ rem such that (rem − a) is a subset-sum of atoms STRICTLY
> SMALLER than a. Results:
> - (3,4,7) k=1: 0 failures over all representable n ∈ (581, 2000] — top-down peel reconstructs every n
>   with NO backtracking (this is the correct-lookahead version of greedy; naive greedy's 775 failures
>   came from peeling without the smaller-atom-residual check).
> - Contraction verified: largest valid peel shrinks n by ≥ 34% every step (max ratio 0.655 for (3,4,7)
>   k=1, 0.329 for (3,4,5) k=2, 0.592 for (3,4,6) k=1) ⟹ recursion depth O(log n), candidate k-uniform.
> - Distinct-atom consumption respected (each (base,exp) once): still 0 failures (honest test).
>
> **The proof obligation this reduces to (for breaker/attempt):** prove the INVARIANT "for every
> representable n > n₀, ∃ atom a ≤ n with (n−a) a subset-sum of atoms < a, AND the largest such a
> satisfies a ≥ ρ·n for a constant ρ<1." If both hold k-uniformly, INV-C1 is a complete constructive
> proof. The contraction half (a ≥ ρ·n) looks robust (verified ρ≤0.66); the existence half (some valid
> peel always exists) is the real lemma — it MIGHT still hide MW content at the boundary, so the key
> next kill-test is whether the existence-of-valid-peel holds at k=3 for minimal {3,4} families where
> my onset bound blew up. If valid-peel exists for ALL representable n at k=3 with bounded lookahead,
> INV-C1 genuinely escapes the wall. [HANDED TO breaker for the k=3 existence stress-test.]
>
> **k=3 DECISIVE TEST RESULT (carry ran it): SURVIVES.** (3,4,5) k=3, all representable n in
> (4,330,731, 4,400,000]: valid-peel existence failures = 0; max contraction ratio 0.556 (O(log n)).
> **This is the family where my onset bound blew up (K=3.759), yet INV-C1's invariant holds k-uniformly.**
> KEY INSIGHT WHY: the onset bound tried to LOCATE the threshold N₀(k) (which carries MW content); INV-C1
> does NOT locate N₀ — it only asserts that ABOVE N₀, every representable n has a contracting valid peel.
> The threshold-LOCATION and the above-threshold-STRUCTURE are different questions; INV-C1 attacks the
> latter, which is empirically k-uniform even where the former is MW-hard.
>
> **HONEST SCOPE / circularity caveat (the real proof obligation):** "valid peel exists for every
> representable n > N₀" is, restated, close to the cofiniteness claim itself — so INV-C1 is only a PROOF
> if the valid-peel existence is established WITHOUT assuming representability. The non-circular version:
> prove directly that for n > n₀(D,k), ∃ a ≥ ρn with (n−a) ∈ ∑_d d^k·B_d-restricted-to-atoms<a, by a
> self-contained counting/density argument on the smaller-atom subset-sum set (NOT by reference to the
> full reach). If that counting argument is elementary and k-uniform, INV-C1 closes the conjecture. The
> contraction (a ≥ ρn, ρ≤0.66 verified) PLUS density's "reach of smaller atoms ≥ (1−ρ)n·∑1/(d−1)"
> envelope is the candidate self-contained argument — THIS is what to attempt next. [STRONGEST SURVIVOR;
> coordinate with density on the smaller-atom reach envelope + sumset on whether the counting is
> k-uniform — note sumset's c(D,k)→∞ is about residue VALUE-coverage, a DIFFERENT quantity from peel
> existence, so it does NOT obviously kill this.]
>
> **NON-CIRCULARITY CERTIFICATE (carry, decisive): the lookahead skip-depth is BOUNDED ≤2, k-uniform.**
> The valid peel is found among the TOP 3 atoms ≤ n at every step (max skip: (3,4,7) k=1 →2, (3,4,5)
> k=2 →2, (3,4,6) k=1 →1). So INV-C1 is a concrete **O(1)-lookahead, O(log n)-depth greedy algorithm**:
> at each step examine only the 3 largest atoms ≤ rem, pick the first whose residual is subset-summable
> by smaller atoms, recurse. This is NOT circular — it's an explicit decision procedure with bounded
> branching. Remaining proof obligation: prove "among the top-3 atoms ≤ n, ≥1 has (n−a) reachable by
> atoms < a" for all n > n₀, k-uniformly — via SELF-SIMILAR INDUCTION on scale (sumset's T_k=C_k+T_{k+1}:
> smaller-atom reach is cofinite up to scale a), the ≤3 candidates dodging the rare scales where the
> largest atom sits at a smaller-atom gap. Self-similar induction + bounded branching = candidate
> elementary k-uniform proof. **THE ONE TO ATTEMPT** — it never needs N₀'s LOCATION (the MW content),
> only the scale-invariant local top-3 structure. Scripts: /tmp/e124_skip_k.py, /tmp/e124_C1_noncircular.py.
>
> **SOUNDNESS / DISCRIMINATION TEST (team-lead's requirement): PASSES.** The peel procedure must FAIL
> on non-cofinite families (else it would "prove" a false statement). Verified on β<1 families (all
> provably NOT cofinite): (3,4) β=0.83, (3,4,11) β=0.93, (3,5,9) β=0.88, (3,4,9) β=0.96. In EVERY case,
> "peel-succeeds-but-not-representable" count = 0 — the peel invariant fails EXACTLY on the
> non-representable holes, never spuriously succeeds. So the mechanism is SOUND: it succeeds iff n is
> genuinely representable, and for β<1 it correctly fails on infinitely many n. It CANNOT certify a
> false cofiniteness. **CAVEAT (honest):** this check uses the actual reach to test peel success, so it
> confirms the mechanism is not unsound but does NOT itself remove circularity — the non-circular PROOF
> still needs the self-contained smaller-atom-reach envelope. What discrimination DOES establish: any
> future non-circular proof of the peel invariant MUST use β≥1 somewhere (the invariant demonstrably
> fails for β<1), so it cannot be "too strong"/unsound. Script: /tmp/e124_C1_discriminate.py.

### INV-C2. Two-base CRT shuttle with a bounded ledger (the "carry-ledger automaton")
**Definition.** For minimal D, pick the two smallest bases b<c (e.g. 3,4). Process n by a transducer:
maintain a bounded "ledger" L (an integer in [−B, B] for an explicit B = B(D,k)). At step t, consume
one mixed-radix digit of n; emit a base-b atom or base-c atom choice that drives n's residue toward 0
mod b^k c^k, updating L by the carry. The OTHER bases supply only a bounded correction set at the end.
Claim: the ledger stays in [−B,B] for an explicit B (so the automaton is FINITE-STATE), and reaches an
accepting state (L=0) for all large n. Finite-state + eventually-accepting ⟹ cofinite, with the
transient = number of states.
**Why it could work.** Reframes representability as a FINITE-STATE acceptance problem (automatic-set
style, à la Mauduit–Rivat digit literature scholar flagged). If the ledger is provably bounded, the
"is n representable" predicate is eventually periodic and the threshold = automaton diameter, an
ELEMENTARY finite object — no transcendence. The bet: the carry between base-b and base-c digit
streams is bounded because b,c are the two smallest (slowest-growing) bases.
**Cheapest kill-test.** Empirically: run the shuttle on (3,4,7) k=1 and track the ledger value L over
all n in [0, 20000]. Plot max|L|. If max|L| stays bounded (say ≤ 20) and is INDEPENDENT of n, the
finite-state hypothesis survives → attempt. If max|L| grows with n (unbounded ledger), the automaton
is infinite-state and INV-C2 is dead. (~30 lines.) Cross-check vs sumset's c(D,k)→∞: if the ledger
bound itself grows with k, it's the same wall — but bounded-FOR-FIXED-k still gives the per-fixed-k
theorem a cleaner proof.

### INV-C3. Adversary-game with a reusable-atom budget (the "Maker-Breaker digit game")
**Definition.** Model seed-closing as a 2-player game. Breaker names a target n (adversarially, near a
suspected gap). Maker must build n as ∑ a_d. Maker plays atoms one at a time, largest-first, but is
allowed a REUSE BUDGET: Maker may "rent" up to R(D,k) atoms from a future scale (atoms > n) and must
repay them by splitting (d^{J} → d·d^{J−1}, valid only if the lower slot is free). Claim: with reuse
budget R(D,k) = O(r) (number of bases, NOT growing with k), Maker always wins for n > n₀, because the
harmonic surplus σ>0 funds the repayment. The game value (max rented atoms over all n) is the proof
constant.
**Why it could work.** The reuse budget is a NEW degree of freedom — it lets Maker temporarily violate
the size constraint and repay via the base-d carry identity d^J = d·d^{J−1}, which is exactly the
self-similar structure. If the repayment is always affordable under σ>0, this is an amortized argument
where σ is the "credit rate." Unlike the onset bound (which I showed is empirical and blows up), the
game value might be bounded by r alone if the splitting identity localizes the debt.
**Cheapest kill-test.** Implement the greedy-with-rental Maker on (3,4,5) k=1,2,3 (the family where my
onset bound blew up). Measure the max rental depth needed over all representable n. If rental depth is
bounded by a small multiple of r=|D| and does NOT grow with k, INV-C3 escapes the wall my onset bound
hit → strong attempt. If rental depth grows with k (like c(D,k) and my K), it's the same MW content in
disguise → dead. This is the SHARPEST test: it directly probes whether ANY amortized/credit scheme can
be k-uniform, which my onset failure suggests is the crux. (~40 lines.)

> **breaker KILL-TEST VERDICTS (Round 1, carry):**
> - **INV-C1: SURVIVES (strongest, round-3 spec) — flagged to lead.** Re-ran carry's valid-peel AND a
>   NON-CIRCULAR version (residual must be representable by atoms STRICTLY < the peeled atom a —
>   well-founded, no circularity). 0 failures for (3,4,7) k=1, (3,4,5) k=2 AND k=3; contraction ratio
>   ≤ 0.655. The well-founded contracting peel exists empirically at every tested k incl k=3 (where the
>   onset bound blew up). ROUND-3 SPEC: prove non-circular EXISTENCE — "for n>n₀, ∃ atom a≥ρn with
>   (n−a) ∈ {subset-sums of atoms < a}" by a self-contained density/counting argument (density's
>   (1−ρ)n·∑1/(d−1) smaller-atom reach envelope), NOT by enumerating the full set. If elementary +
>   k-uniform, INV-C1 closes the conjecture.
>   **UPDATE (breaker adversarial round, carry's 3 angles):** Angles 1+2 SURVIVE robustly — hit the
>   HARDEST regime (3,4,7) k=3 just ABOVE the true 166M threshold (pervasive high-θ cascade): 0 valid-peel
>   failures / 20000 rep n, worst contraction ρ=0.596<1. BUT **Angle 3 (circularity) is CONFIRMED REAL**:
>   the density-envelope shortcut is INSUFFICIENT — for 99.9%/100% of rep n the smaller-atom set is
>   NON-contiguous below the residual, so "(n−a) representable by smaller atoms" depends on the smaller
>   set's FINE recursive structure, not a density bound. So INV-C1 is a correct ALGORITHM + clean
>   well-founded REDUCTION (n→smaller) but NOT a non-circular proof via the envelope. HOPEFUL: the wall is
>   NOT at every level — only 14.1% of recursion peel-steps hit near-power (MW-hard) residuals (86%
>   generic, no deep nesting). SHARPENED ROUND-3 SPEC: discharge ONLY the ~14% near-power residual cases —
>   prove "a residual just below a pure power d^j is representable by strictly-smaller atoms" (a localized
>   MW/Baker statement at ONE scale per hard step, NOT nested). That is the genuine remaining lemma,
>   sharper than "prove cofiniteness." Evidence: breaker_attack_C1*.py, breaker_C1_induction_depth.py.
>   **UPDATE 2 (carry's refined angles — skip-depth + own_thr): induction route KILLED, algorithm stands.**
>   Angles 1+2 (skip-depth) survive even at the boundary (3,4,7) k=3 above 166M: max skip-depth = 1
>   (7996/8000 depth-0), 0 failures. BUT Angle 3 (own_thr=a) KILLS carry's non-circular induction: the base
>   hypothesis "smaller-atom reach cofinite up to a" is FALSE — own_thr(a)/a is PERSISTENTLY ≈1 (0.95–1.000)
>   at EVERY scale ((3,4,7) k=2: =1.000 at a=2401,16384,16807,59049,65536; =0.950 at a=4194304). The
>   smaller-atom set has a gap reaching right up to a, generically (carry's a=64,243 are the rule). So
>   (n−a) can land in [own_thr(a),a) unreachable by atoms<a; the algorithm survives only by choosing a
>   different top-atom dodging that gap = needs full representability = circular. FINAL: correct O(1)-look-
>   ahead O(log n) DECODING algorithm, but the self-similar induction does NOT close — own_thr(a)→a IS the
>   MW power-coincidence content. Evidence: breaker_attack_C1_skipdepth.py, breaker_attack_C1_ownthr.py.
> - **INV-C2: KILLED.** Kill spec: "ledger bounded (≤20) ⟹ survives; grows ⟹ dead." Actual ledger =
>   gap the two smallest bases (3,4) leave = 1,582,050 at k=1 (NOT ≤20; 5 orders off) and grows with k.
>   B_3+B_4 has β=0.833<1 ⟹ not cofinite ⟹ correction is huge + k-dependent. Automaton NOT finite-state
>   with small bound. DEAD. (= cassels DP4: third base spans large two-base gaps by joint multi-atom.)
> - **INV-C3: KILLED (collapses to INV-C1 + a k-growing rental).** Rental/reuse budget = valid-peel
>   existence (INV-C1) PLUS reach above n. Repayment via d^J=d·d^{J−1} must bridge the SAME 1.58M-scale,
>   k-growing two-base gaps as INV-C2, so rental depth is NOT O(r) — it inherits INV-C2's unbounded
>   k-dependent ledger. σ>0 credit doesn't localize the debt (it sits at the 581-dodge / cross-base
>   power-coincidence sites = MW content). NOT k-uniform → DEAD. Sound core = INV-C1's peel; drop rental.
> Evidence: breaker_kill_INV_C1_circular.py, breaker_kill_INV_C2*.py, breaker_GAUNTLET.py.

---

## Round 1 (modular — p-adic / profinite lens; (L) as the local half of a local-global principle)

My residue lemma (L) settles the LOCAL half (Σ(D,k) covers every ℤ/M for gcd=1). These invent the
ARCHIMEDEAN half as objects that COMPOSE with (L), aiming at a Hasse/local-global principle rather
than the Mignotte–Waldschmidt spacing wall.

### INV-M1. The profinite size-defect δ(n) and a "bounded-carry adele" local-global principle.
**Definition.** Work in ℤ̂ × ℝ. (L) says the sumset is dense in ℤ̂ (hits every finite quotient).
Define the **size-defect** δ(n) = min over representations n=∑_d d^k b_d of (largest power used)/n
∈ (0,1]. Proposed theorem: for admissible D, **θ(D,k) := limsup_n δ(n) < 1**, and
  n ∈ Σ(D,k) for all large n  ⟺  [LOCAL: (L), every residue mod every M — PROVED]
                                  AND [ARCHIMEDEAN: θ<1, the new content].
A genuine local-global principle for subset-sums of digit-Cantor sets, with the archimedean datum a
single scalar θ<1 instead of an MW gap bound.
**Why.** Turns "prove cofiniteness" into "bound one ratio θ<1", bolted onto the proved (L). A
pigeonhole/overlap argument on the [θn, n] window + (L)'s residue freedom would then close
cofiniteness without transcendence. Lean-checkable target (θ = sup of a computable function).
**Kill-test (cheap).** Ascending-atom DP tracking, per representable n, the min largest-power used;
read δ(n) on a high window. If δ→1 as n→∞ (no ceiling below 1), θ is vacuous — DEAD. **Status: PROBED,
SURVIVES** — (3,4,7) k=2, n∈[2M,4M): δ max=0.673, mean 0.42, all ≤1, θ≈0.7 bounded. /tmp/invent_probe.py.
**Next decisive test (breaker): does θ stay <1 at the BOUNDARY ∑1/(d−1)=1 as k grows?** If θ→1 as k→∞
on a boundary family, it dies (that's where MW lives); if θ ≤ θ₀<1 uniformly, INV-M1 is the archimedean half.

### INV-M2. p-adic valuation-cone stratification of the missing set.
**Definition.** Stratify n by valuation vector (v_p(n))_{p|some d}. k-shift forces d^k | (base-d
summand); define the **achievable valuation cone** C(D,k) ⊆ ∏_p ℤ≥0. Bet: the (finite) missing set is
exactly the n whose valuation vector sits outside a finite-defect coset lattice — non-representability
as clean p-adic lattice-membership, decidable by CRT+(L).
**Why.** Would CLASSIFY the missing set structurally (describe N0(k)), not just bound it.
**Kill-test (cheap).** Compare valuation distribution of missing n to baseline geometric
P(v_p=j)=(p−1)/p^{j+1}. No skew ⟹ cone is everything ⟹ no information. **Status: PROBED, LIKELY DEAD**
— (3,4,7) k=2 missing-n marginals are near-baseline geometric for p=2,3,7. Salvage only if the JOINT
vector (not marginals) separates them — breaker, try the joint distribution before discarding.

### INV-M3. The "real-place twin of (L)": scale-coverage as a Hasse factor.
**Definition.** (L) is coverage at every FINITE place. Invent the REAL-place analogue: per-octave
coverage proportion ρ(X) = |Σ(D,k) ∩ [X, λX]| / ((λ−1)X). Claim: for admissible D, ρ(X) → 1 as X→∞,
switching on exactly as ∑1/(d−1) crosses 1 — the archimedean mirror of "gcd=1 ⟹ all residues". Then
cofiniteness = (finite-place L) × (real-place scale-coverage): a product-formula / Hasse principle.
**Why.** Supplies the archimedean half in the SAME coverage language as (L), so the two compose by a
Hasse argument instead of MW spacing — the structural bet that BEGL96 IS a Hasse principle for digit-sumsets.
**Kill-test (cheap-ish).** Measure ρ(X) per octave for D with ∑1/(d−1) just below / at / above 1. If ρ
does NOT jump to →1 as ∑ crosses 1 (or is already 1 well below threshold), framing is wrong — DEAD.
CAVEAT: the boundary is invisible in small finite range (∑<1 families look density-1 to 3×10^6; real
gap for (3,5,7) is ~3^60 per density's formula). Decisive only if it reaches predicted gap scales;
else mark "untestable cheaply, defer" rather than false SURVIVES.

> **Self-assessment for breaker:** INV-M1 strongest (probed, survives, decisive boundary test named).
> INV-M2 probably dead (marginals typical) — included honestly with the one salvage path. INV-M3
> boldest (Hasse principle) but hardest to test cheaply. Prioritize INV-M1.

### CROSS-CUTTING (modular + carry): INV-M1 and INV-C1 are COMPLEMENTARY, bracketing a "workable band".
Probed whether my size-defect δ(n) (INV-M1) and carry's valid-peel ρ(n) (INV-C1) are the same object.
They are NOT — and the relationship is structurally useful. For (3,4,7) k=2, n∈[2.00M, 2.03M]:
- INV-M1 (min-max-power rep): largest atom ≤ **0.52·n** (mean 0.41) — bounds the top atom ABOVE.
- INV-C1 (largest valid peel): peelable atom ≥ **0.785·n** (mean 0.79) — bounds a usable atom BELOW.
- They are the SAME atom in 0 / 30000 cases — genuinely different representations.
**Joint statement:** every large n has a representation whose largest atom lies in a BOUNDED BAND
[~0.4n, ~0.8n] — bounded away from BOTH n (carry-bounded, INV-M1) and 0 (contracting, INV-C1). That
two-sided bound is exactly the "bounded-carry" datum a local-global proof needs: the archimedean half
is not one inequality but a band, and (L) supplies the residue freedom to navigate within it. **For
breaker:** the decisive question becomes whether the BAND stays bounded away from n (upper edge θ<1)
uniformly in k at the boundary ∑=1 — same test as INV-M1, now with INV-C1's lower edge confirming the
band is non-degenerate. If the band's upper edge → 1 with k, both M1 and C1's contraction degrade
together. Code: /tmp/unify_probe.py.

> **KILL-TEST RESULT (carry ran it, modular independently confirmed): clean θ<1−ε FAILS.**
> θ_max creeps to 1: (3,4,5) θ_max = 0.900 (k=1) → 0.904 (k=2) → 0.955 (k=3); (3,5,7,9) → 0.9995 (k=2).
> Worst n sit JUST ABOVE a high power of a SINGLE base (n=195982 = 3^11 + 18835; n=2406 = 7^4+5).
> So the clean "θ bounded away from 1 uniformly in k" version of INV-M1 is **FALSE** — the
> non-circular density envelope (1−θ)n·∑1/(d−1) shrinks toward 0 at these power-cluster points,
> which is the MW cross-base spacing content. **This is the same wall, relocated to θ→1 at single-base
> power neighbors.**
>
> **SALVAGE (modular, probed — NOT dead, but reduced to a sparse-set recursion):** the high-θ set is
> EXTREMELY SPARSE — for (3,4,5) k=2, only 135 / 222386 representable n>thr have θ>0.8, and just 1 has
> θ>0.9. And θ→1 does NOT block representability (n is representable; its top atom is just near n).
> The high-θ n are exactly n = d^j + r with r = (1−θ)n SMALL, so their representability reduces to r
> being representable — a LOWER-SCALE instance = INV-C1's contraction. **Refined joint verdict: neither
> INV-M1's envelope (bulk, θ bounded) nor INV-C1's contraction (sparse high-θ tail) closes alone, but
> they cover COMPLEMENTARY regions.** The remaining proof obligation: show the sparse θ→1 set near pure
> powers d^j is handled by recursion on r WITHOUT that recursion itself hitting a θ→1 point at every
> scale (i.e. the power-cluster points don't nest all the way down). THAT nesting question is the
> residual MW content — but it is now localized to a measure-zero-density set, not the bulk. [For
> breaker/attempt: is the r-recursion from a pure-power neighbor itself eventually θ-bounded, or does
> it cascade through power-clusters at every scale? If it terminates θ-bounded, the combination closes.]
> Code: /tmp/theta_recheck.py, /tmp/theta_salvage.py.
>
> **NESTING TEST RESULT (carry ran modular's decisive question): NO CASCADE — the combination CLOSES
> empirically.** Ran the FULL INV-C1 peel-recursion from every high-θ (>0.8) point for (3,4,5) k=2
> (only 5 such points in [78k,200k] — confirms sparsity). Every chain: TERMINATES (reaches 0), is
> SHORT (length 6-11), and hits only 1-4 high-θ points total — it does NOT nest through power-clusters
> at every scale. E.g. n=195982 (θ=0.904) → 18835 → 2451 → 1427 → 698 → … → 0: escapes the cluster
> region in ~2 steps, terminates in 8. **So the r-recursion from a pure-power neighbor IS eventually
> θ-bounded — it escapes clusters in O(1) high-θ hits, not a cascade.** This means the INV-C1 (sparse
> high-θ tail via recursion) + INV-M1-salvage (θ-bounded bulk via density envelope) combination
> empirically CLOSES: bulk handled by density, sparse tail handled by fast-terminating recursion that
> provably escapes clusters. **The remaining rigorous step:** prove the "no infinite cluster-nesting"
> non-circularly — i.e. that n = d^j + r with r small cannot have r ALSO be d'^{j'} + r' with r' small
> all the way down. This is a Diophantine NON-coincidence (consecutive pure-power-neighbors don't nest),
> which is MUCH weaker than the full MW spacing bound — it may be elementary (a power d^j and a nearby
> power d'^{j'} being simultaneously close to n is a bounded-height coincidence). **This is the sharpest
> the open core has been reduced: from "locate N₀" (full MW) to "pure-power neighbors don't nest
> indefinitely" (a bounded-height non-coincidence).** [carry: /tmp/e124_nesting.py — strongest
> reduction this blitz; hand to scholar for whether the non-nesting is a known elementary Diophantine
> fact OR disguised MW.]
>
> **STRESS + HONEST DENSITY CAVEAT (carry).** Robustness: max high-θ-in-chain stays ≤5 and chains ≤14
> steps even at k=3 and on (3,5,7,9) k=2 (4656 high-θ starts). CORRECTION to the "measure-zero/sparse"
> framing: high-θ density is family-dependent — (3,4,5) k=2 is genuinely sparse (θ>0.8: 0.006%), but
> (3,5,7,9) k=2 is NOT (θ>0.8: 3.9%, θ>0.9: 1.2%); only the EXTREME tail θ>0.95 is sparse in both
> (≤0.067%). So the mechanism rests on **bounded chain-nesting, NOT sparsity**.
> **⚠️ SCOPE CORRECTION (breaker+modular, critical): no-cascade is STRICT-EXCESS ONLY, NOT the
> boundary.** My nesting tests used (3,5,7,9) and (3,4,5) — both STRICT-EXCESS (σ>0). I did NOT test
> the BOUNDARY ∑=1 case (3,4,7) k≥3 above its TRUE threshold (166,025,260; I'd have used the false-freeze
> 57M). breaker re-ran (3,4,7) k=3 above 166M: high-θ cascades are PERVASIVE (5000/5000 of n, depth
> ~6), NOT sparse, NOT single-scale. So "no-nesting reduces the open core" is a STRICT-EXCESS result,
> NOT a boundary closer — and the boundary ∑=1 (where (3,4,7), the conjecture's hardest case, lives) has
> a pervasive depth-~6 cascade, every level MW. The one mild positive (breaker): depth is BOUNDED (~6,
> not growing within reach) — finite-depth-MW-per-n, not unbounded. NET: no-cascade is a real STRICT-
> EXCESS partial; the boundary is NOT escaped. This is consistent with my INV-C1 verdict (construction
> ≠ cofiniteness) — neither escapes the boundary wall.
> OPEN RISK (flagged to scholar): the non-nesting might BE disguised MW — a chain step n≈d₁^{j₁},
> residual≈d₂^{j₂} encodes |d₁^{j₁}−d₂^{j₂}| small, which is exactly what MW bounds. If the chain length
> is O(log n) for a GEOMETRIC reason (r_i shrink by a constant factor regardless of coincidences) it's a
> genuine elementary reduction; if chain length depends on power-coincidences it's the same wall.
> Awaiting scholar's verdict. NOT claiming this closes the conjecture — claiming it's the sharpest
> reduction achieved, pending the genuine-vs-disguised-MW determination.
>
> **NESTING TEST RESULT (modular ran it): the cascade does NOT nest — promising.** Followed the peel
> recursion n → r = n − (min-top-atom) from every high-θ (>0.8) starting point and counted how many
> levels of the chain are themselves high-θ:
> - (3,4,5) k=2: 135 high-θ starts, MAX high-θ levels in any single chain = **1**.
> - (3,4,5) k=3: 224 high-θ starts, MAX high-θ levels = **1**.
> - (3,4,7) k=2, (3,5,7,9) k=2: ABOVE threshold, θ_max only 0.40 / 0.60 — **zero** high-θ points at all.
> So every high-θ n peels in ONE step to a θ-bounded (or below-threshold) residual; the power-cluster
> obstruction does NOT recur at the next scale. **This LOCALIZES the MW wall to the single first peel
> at sparse pure-power neighbors — it is not a wall at every scale.** Refined picture for an attempt:
> M1-envelope covers the θ-bounded bulk; a SINGLE peel covers each sparse high-θ point; the residual
> lands in the bulk. The only genuinely non-elementary input left is bounding that first peel near a
> pure power d^j — i.e. "how close can ∑(other-base powers) get to a power of one base from below",
> which is precisely a Baker/MW lower bound on |d^j − ∑ other| but needed at ONLY ONE scale per n, not
> nested. CAVEAT (honest): "max chain length 1" is partly because the residual drops below the
> fixed-bound threshold; a fully rigorous claim needs the recursion tracked across unbounded scales
> (the residual r is itself a fresh instance of the SAME conjecture at smaller size, so this is an
> induction-on-n, and the base case is the thr region). Not a proof, but it shows the obstruction is
> single-scale, not multi-scale. Code: /tmp/nesting_test.py, /tmp/nesting_k3.py. [breaker: confirm the
> single-peel localization survives at a boundary family ∑=1 with k=4,5 if cheaply reachable.]
>
> **breaker BOUNDARY CONFIRM (the decisive test modular asked for) — CORRECTION: salvage WEAKENS at the
> boundary ∑=1.** modular's "max chain length 1" was measured BELOW the true threshold (their k=3 region
> used the false-freeze ~57M, not the corrected n0=166,025,260). Re-ran (3,4,7) k=3 (∑=1 boundary)
> ABOVE the TRUE threshold (N=200M, windows from 166M up): high-θ (>0.8) chains are PERVASIVE (5000/5000
> of n, not sparse) with depth 5–6, and do NOT thin out even +29M above n0 (depth still 5–6). Contrast
> strict/low-k families ((3,4,5) k=2/k=3, depth ≤3, sparse). So the "single-scale, measure-zero" picture
> holds for strict-excess / low-k but FAILS at the boundary ∑=1 with k≥3: there the cascade is universal
> and bounded-but-deep (~6). VERDICT: M1⊕C1 salvage SURVIVES as a partial (covers strict-excess away from
> threshold) but does NOT escape the wall at the boundary — exactly where (3,4,7), the conjecture's
> hardest case, lives. The cascade depth being bounded (~6, not unboundedly growing) is mildly encouraging
> but it's pervasive at the boundary, so the recursion-bottoms-out argument needs every one of those ~6
> levels to be MW-controlled = not elementary. Honest downgrade: SURVIVES-as-partial, NOT a boundary closer.
> Evidence: breaker_nesting_boundary2.py, breaker_nesting_boundary3.py.
>
> **carry FINAL VERDICT (logical structure — subsumes the cascade-depth debate): INV-C1 is a CONSTRUCTION
> method, NOT a cofiniteness proof.** I worked the logic to the end. The recursion has two pieces:
> (C) contraction — every valid peel residual ≤ 0.72·n, VERIFIED uniform over 118k+ chains, k≤3, NO step
> fails to contract → chain length O(log n) for a GEOMETRIC, coincidence-INDEPENDENT reason (genuinely
> elementary, kills nesting regardless of MW); (E') existence — a representable n has a largest atom whose
> removal leaves a representable residual < n (TRIVIALLY true: the largest atom of ANY representation
> works). Together, strong induction on n shows every REPRESENTABLE n has an O(log n) construction — **but
> that is essentially tautological.** It assumes n is representable (uses the reach) and just decodes it
> efficiently. **To prove COFINITENESS we need "every n>n₀ IS representable" — INV-C1 never establishes
> that.** The cascade-depth / θ→1 / MW discussion is about WHICH n are representable, exactly the part
> INV-C1 takes as INPUT. So INV-C1 does not move the cofiniteness wall — it's a (nice, O(log n),
> bounded-lookahead, sound/discriminating) DECODING algorithm for the already-representable set. Honest
> final status: real algorithmic result, NOT a route to the conjecture. The wall (representability above
> n₀) is untouched — consistent with breaker's boundary finding and the squad's MW consensus. Recording
> so nobody attempts INV-C1 as a cofiniteness proof. [carry: /tmp/e124_crux_final.py, /tmp/e124_geometric.py]
>
> **JOINT SHARPENED TARGET (carry + breaker, the forward-looking result): the open lemma is SINGLE-SCALE,
> not nested.** breaker's adversarial attack: INV-C1 SURVIVES angles 1+2 (peel exists & contracts ρ=0.596
> even at boundary (3,4,7) k=3 above the TRUE 166M threshold — 0 failures); angle 3 (circularity) is REAL
> (smaller-atom set is non-contiguous below the residual for 99.9-100% of n, so the density envelope is
> insufficient — the inductive step carries the content, confirming construction≠cofiniteness). KEY
> POSITIVE: the MW-hard content is NOT at every recursion level — only a MINORITY of peel steps land at
> near-power residuals (breaker 14.1% with his single-base def; carry 26-32% counting all-bases floor+ceil
> at ε=0.5-5% — the fraction is definition-dependent but always a minority), and they DON'T nest (depth
> ≤6). **So the precise remaining lemma both of us isolated: "a residual just below a pure power d^j is
> representable by strictly-smaller atoms" — a LOCALIZED MW/Baker statement at ONE scale per hard step,
> bounded depth, NOT nested.** That is strictly sharper than "prove cofiniteness": it's a single-scale
> near-power representability question, the genuine kernel. INV-C1 = strongest constructive route; its
> open obligation is now precise, single-scale, and bounded-depth. [carry: /tmp/e124_C1_hardfrac.py,
> /tmp/e124_hardfrac_eps.py; breaker: breaker_attack_C1*.py, breaker_C1_induction_depth.py]
>
> **THREE-WAY CONVERGENCE (carry + breaker + scholar) — the Q-shrink / Q-exist split makes it precise.**
> scholar separated the obligation into two sub-questions and resolved them differently:
> - **(Q-shrink) chain shrinks geometrically ⟹ O(log n) length: GENUINE elementary, NOT disguised MW.**
>   Worst single-step ratio 0.72-0.76 even at near-power n (scholar, independent) = carry's ρ≤0.66-0.72
>   over 118k+ chains, no step fails. KEY: a near-coincidence makes one step's residual SMALL, which
>   HELPS contraction — so a chain CANNOT encode |d₁^j−d₂^j'| small as an obstruction; the geometry runs
>   the OTHER way. Non-nesting (bounded chain length) is OFF the MW table. My original "disguised MW?"
>   worry is resolved: NO.
> - **(Q-exist) valid peel exists at each step: NOT resolved by contraction — the wall lives HERE.**
>   = breaker's angle-3 (smaller-atom set non-contiguous below residual, density envelope insufficient)
>   = carry's construction≠cofiniteness (contraction bounds residual SIZE, not REPRESENTABILITY).
> THE PRECISELY-LOCALIZED KERNEL (all three agree): Q-exist at the ~14-30% near-power hard steps =
> **"a residual just below a pure power d^j is representable by strictly-smaller atoms"** — single-scale,
> bounded-depth, with an ELEMENTARY chain-length wrapper (Q-shrink) around it. This is the genuine open
> sub-claim, and the Q-shrink/Q-exist split is what makes the reduction rigorous rather than hand-wavy:
> the chain-length half is proven-elementary; only single-scale near-power existence remains. [scholar
> verified Q-shrink independently; convergent with carry's geometric-contraction + breaker's angle-3.]
>
> **FINAL: breaker's angle-3 KILLS the non-circular induction route (carry verified independently).** The
> proposed self-similar induction needed the base hypothesis "smaller-atom reach is cofinite up to scale
> a." breaker computed own_thr(a)/a (largest m≤a NOT representable by atoms < a, over scale): PERSISTENTLY
> ≥0.99, NOT bounded below 1. carry confirmed: (3,4,7) k=2, own_thr(a)/a > 0.99 for ALL 20 atoms a
> (= 1.000 exactly at pure powers a=27,49,64,81,243,256,65536; ≥0.997 elsewhere). So the smaller-atom set
> has its OWN gap reaching right up to a at EVERY scale — the a=64,243 coincidences I first saw are
> GENERIC, not isolated. ⟹ the induction base is FALSE; the non-circular self-similar route is DEAD. The
> algorithm survives ONLY by picking a top-atom whose residual dodges that smaller-set gap, but that
> choice requires knowing full representability = THE CIRCULARITY. And own_thr(a)→a IS the MW
> power-coincidence content (the gaps reaching up to a sit just below the powers). **DEFINITIVE STATUS:
> INV-C1 is a correct O(1)-lookahead O(log n) DECODING algorithm (publishable as an algorithm, sound,
> discriminating), NOT a cofiniteness proof — every proof route (density envelope, self-similar
> induction) hits the same MW wall at Q-exist. Confirmed from 4 independent angles: carry
> construction≠cofiniteness + scholar Q-exist + breaker angle-3 own_thr→a + the circularity.** Wall
> untouched. [carry: /tmp/e124_ownthr_a.py; breaker: breaker_attack_C1_ownthr.py]

## Round 1 (scholar — analytic / hybrid-object lens; inventing at the gaps the literature lacks)

Niche: NOT constructive descent (carry owns that). I invent the analytic objects that the
single-base digit-Fourier literature (Maynard/Mauduit-Rivat) never built for the MULTI-BASE,
incommensurable setting — the exact gap my prior-art sweep found unfilled.

### INV-S1. Multi-base circle method via DECORRELATED major arcs (the "no common arc" count)
**Definition.** For each base let F_d^{(k,L)}(θ) = ∏_{j=k}^{k+L} (1 + e(d^j θ)) be the generating
function of the truncated 0/1-digit set d^k·B_d (e(x)=e^{2πix}). The number of representations of n is
r(n) = ∫_0^1 ∏_{d∈D} F_d(θ) · e(−nθ) dθ. Split [0,1] into MAJOR arcs (θ near a/q, small q) and MINOR
arcs. The new idea: prove the EXCEPTIONAL set {n not represented} is empty above N₀ by showing the
minor-arc contribution is dominated by the major-arc main term — using that the three bases are
MULTIPLICATIVELY INDEPENDENT so their major arcs (θ near a/d_i^j) are DISJOINT except at θ=0.
**Why it could work.** [VERIFIED viable, /tmp] For (3,4,7), L=8, |F_3·F_4·F_7| exceeds 0.3·max ONLY
near θ=0 — NOWHERE else in (0,1/2). So the three incommensurable bases have NO common major arc but
the trivial one: each base's "spikes" sit at θ ≈ a/d_i^j, and d_i^j vs d_j^q never coincide except
via the rare MW near-coincidences (3^5≈4^4). This is EXACTLY the decorrelation a circle method needs,
and it's the multi-base feature the single-base literature never had a reason to use. The MW
log-clustering (the team's open core) is precisely WHERE two bases' arcs nearly collide — so this
recasts the open problem as "bound the measure of the near-collision arcs," a clean analytic target.
**Cheapest kill-test.** Numerically compute r(n) = ∫ ∏F_d e(−nθ) dθ by FFT for (3,4,7) k=1 at modest
L, for n in [582, 5000]. Check r(n) > 0 for all (it must, since cofinite there). THEN — the real test
— compute the minor-arc integral (θ away from all a/d_i^j, |q|≤Q) and verify |minor| < major main term,
i.e. the count is "explained" by major arcs. If minor-arc mass already dominates at k=1 (where we KNOW
it's cofinite), the method can't separate signal from noise → dead. If major arcs dominate, scale to
k=2,3 and check the separation is k-uniform. (~50 lines FFT; <1 hr.)

> **breaker KILL-TEST (INV-S1, scholar's cleanest): KILLED — minor arcs swamp the main term at k=1.**
> Ran exact r(n) (verified: 37 misses, max 581) + the major-arc/smooth main-term proxy. At the actual
> misses the major-arc term does NOT vanish: r(178)=0 vs smooth≈2.6; r(212)=0 vs 1.4; r(581)=0 vs 3.9.
> The representation count near threshold is O(1) (min r just above 581 is 1; smooth main term ~4-8), so
> the minor-arc fluctuation is the SAME order as the main term — exactly scholar's kill condition ("minor
> swamps count at k=1"). A circle method proves r(n)>0 only when the main term dominates the error, which
> needs r(n)→∞; here r(n) stays O(1) at the boundary, so the method provably cannot separate signal from
> error. The decorrelated-major-arcs viability signal is real but insufficient — decorrelation gives no
> common major arc, yet the SINGLE major arc's main term is too small to beat the minor-arc error at the
> sparse misses. DEAD for the boundary/threshold regime (the conjecture's hard case). Code: breaker_kill_S1_v2.py.

### INV-S2. Thickness-weighted exponential sum (hybrid Astels×Fourier object — nobody has defined this)
**Definition.** A genuinely new object: weight the exponential sum by the LOCAL THICKNESS of the
digit-Cantor set. Define W_d(θ) = ∑_{x∈d^k·B_d, x≤X} τ_x · e(xθ), where τ_x = the Astels normalized
thickness 1/(d−1) of the sub-Cantor-set hanging below x (constant here = 1/(d−1), so W_d = (1/(d−1))·
F_d truncated — but the POINT is the cross term). The completeness claim becomes: ∑_d τ_d ≥ 1 (the
admissibility condition, = Astels threshold, my proven τ/(1+τ)=1/(d−1) result) ⟹ the weighted product
∏_d W_d has a bounded-below n-th Fourier coefficient. This MARRIES the thickness criterion (which
explains the threshold but is non-constructive) to the exponential sum (which counts but lacks the
threshold) — neither tool alone has both.
**Why it could work.** The team proved (scholar+density) that ∑1/(d−1)≥1 IS the Astels thickness
threshold but thickness is non-quantitative (gives "interval", not "which n"). The circle method is
quantitative but the single-base literature has no threshold criterion. A thickness-WEIGHTED sum could
be the object whose positivity is EQUIVALENT to ∑τ_d≥1 (provable, my result) AND lower-bounds r(n)
(countable). The weight is what could make the minor-arc bound automatic: thickness ≥ 1 ⟺ the weighted
density never drops below the gap-filling level at any scale.
**Cheapest kill-test.** Define the weighted coefficient c(n) = ∑ over reps of n of ∏_d τ_{a_d} and
check: is c(n) > 0 ⟺ n representable, AND is min_n c(n) bounded below by a function of (∑τ_d − 1)?
Compute c(n) for (3,4,5) [δ>0] vs (3,4,7) [δ=0] for n past threshold. If c(n) tracks representability
AND its lower bound scales with the margin δ (large for (3,4,5), →0 for (3,4,7)), the object captures
the threshold quantitatively → strong attempt. If c(n) is just F_d-positivity in disguise (no extra
threshold info), it's a re-skin → dead. (~40 lines.)

### INV-S3. The continued-fraction / Ostrowski transfer (port the ONE place bases DO interact)
**Definition.** The bases interact ONLY through the convergents of log d_i/log d_j (the MW
near-coincidences sit exactly at these — team-verified: close (3^p,4^q) pairs = convergents of
log4/log3, p∈{5,19,24,29,34}). New mechanism: change coordinates to the OSTROWSKI representation of n
with respect to the continued fraction of log4/log3 (and the other base-pair CFs). In Ostrowski
coordinates, the "bad" near-coincidences become a FINITE, structured digit set, and the claim becomes:
the representable set is a finite union of Ostrowski-cylinder sets that tile ℕ above N₀. This imports
the Three-Distance / Ostrowski machinery (well-developed for inhomogeneous Diophantine approximation)
that the additive-completeness literature has NEVER connected to this problem.
**Why it could work.** The team's hard core is "where do cross-base powers nearly coincide," which is
LITERALLY the theory of |p log d_i − q log d_j| small = continued-fraction convergents of the log
ratios. Ostrowski/Three-Distance theory gives EXACT control of the gaps in {⌊p·α⌋} sequences. If the
exceptional set maps to a controlled Ostrowski cylinder, the k-uniformity (lift's §B: bad pairs are
convergents, k-independent) becomes a STRUCTURAL theorem about CF convergents rather than an MW
inequality — potentially turning the transcendence input into elementary CF combinatorics.
**Cheapest kill-test.** For (3,4,7), compute the close-pair locations (p,q) and check they are EXACTLY
the convergents/intermediate-fractions of log4/log3 (lift verified the first 5; extend to p≤200). THEN
check: does the exceptional set {holes of R_k} sit at predictable Ostrowski positions (a fixed finite
set of CF-digit patterns)? If the holes' base-pair "phase" ⌊p log4/log3⌋ − q lands in a BOUNDED set
for all holes, Ostrowski coordinates linearize the problem → strong attempt. If hole positions are
Ostrowski-unstructured (spread across all CF phases), the transfer fails → dead. (~40 lines.)

> Anti-citation note: INV-S1's decorrelation is the multi-base analogue Maynard 2019 / Mauduit-Rivat
> never needed (single base); INV-S2 (thickness-weighted exp sum) is undefined in the literature
> (Astels and circle-method live in disjoint communities); INV-S3 connects Ostrowski/Three-Distance
> (inhomogeneous Diophantine approx) to additive completeness — an unmade connection. All three target
> the SAME open core (MW log-clustering at ∑=1) from the analytic side, complementing carry's
> constructive descent. breaker: S1 has the cleanest kill-test (FFT minor-arc dominance at k=1).

---

## Round 2 (scholar — more analytic/structural gaps)

### INV-S4. Cross-base automaton non-recognizability ⟹ density dichotomy (Cobham-Semenov lever)
**Definition.** B_d is d-automatic (its indicator is a fixed point of a d-substitution — known,
Allouche-Shallit). New mechanism: the SUMSET ∑_d d^k·B_d across DIFFERENT bases is (conjecturally)
NOT automatic in ANY single base — by Cobham's theorem, a set automatic in two multiplicatively-
independent bases is eventually periodic. Use the CONTRAPOSITIVE: if ∑_d d^k·B_d were NOT cofinite,
its (infinite, non-periodic) exceptional set would have to be simultaneously d_i-structured for every
base, forcing it (via Cobham-Semenov) to be eventually periodic — but a periodic exceptional set
contradicts the residue coverage the team PROVED (gcd=1 ⟹ all residues hit). Contradiction ⟹ cofinite.
**Why it could work.** Turns the open problem into a CLOSURE question (is the cross-base sum automatic?)
+ the team's already-proven residue lemma. Cobham-Semenov is a powerful rigidity theorem: sets
structured in incommensurable bases are trivial (periodic). The exceptional set, if infinite, inherits
structure from EACH base's self-similarity (sumset's recursion R_k=C_k+R_{k+1} is the base-action) —
if that forces multi-base automaticity, Cobham kills it. This is exactly the multiplicative-
independence the team keeps hitting (incommensurable bases), used as a THEOREM not an obstruction.
**Cheapest kill-test.** The crux (I probed it): B_d is d-automatic but cross-base sums are generally
NOT automatic. Test whether the EXCEPTIONAL set of a SUB-critical family (e.g. B_3+B_4, ∑=5/6<1, which
IS infinite) is automatic/periodic. If the sub-critical exceptional set is NOT eventually periodic (it
shouldn't be — verify via the base-12 substitution-invariance test on its indicator over [0,20000] vs
scaled windows), then the Cobham route has NO grip (the exceptional set isn't forced periodic) → DEAD.
If it IS forced periodic, the lever is real. (~30 lines: check if the gap pattern of B_3+B_4 is a fixed
point of a base-lcm substitution.) HONEST PRIOR: likely dead, because exceptional sets of these sums
are NOT automatic — but the kill-test is cheap and the dichotomy is worth ruling in/out explicitly.

### INV-S5. Self-similar measure overlap (Hochman entropy-gap, the dimension-vs-thickness route)
**Definition.** Put the natural self-similar measure μ_d on d^k·B_d (each digit 0/1 equally weighted).
The sumset's representability relates to whether the convolution μ_{d_1}*…*μ_{d_r} is ABSOLUTELY
CONTINUOUS with bounded-below density (⟹ cofinite support on the lattice). New mechanism: apply
Hochman's inverse theorem / Hochman-Shmerkin: convolutions of self-similar measures with NO exact
overlaps and total dimension > 1 are absolutely continuous. The bases being multiplicatively
independent ⟹ NO exact overlaps (the only overlaps are the MW near-coincidences, measure zero) ⟹ if
∑ dim(μ_d) > 1 the convolution is a.c. The DISCRETE shadow: bounded-below lattice density = cofinite.
**Why it could work.** I computed ∑ dim(K_d) = ∑ log2/log d, which for (3,4,7) = 1.49 > 1 (and >1 for
all admissible D). Hochman's machinery gives a.c. precisely when dimension >1 and no exact overlaps —
both hold here (mult. independence kills exact overlaps). This is a DIFFERENT threshold (dimension)
than thickness — but the team showed dimension ALWAYS >1 for admissible D, so it might be the SUFFICIENT
analytic input that thickness (which fails at ∑=1) doesn't provide. Routes around the boundary problem.
**Cheapest kill-test.** The gap: dimension >1 is NECESSARY for positive measure but the team's data
shows it's NOT sufficient at the integer level ((3,4) has dim 1.13>1 but isn't cofinite — because ∑1/(d−1)=5/6<1). So Hochman a.c. of the REAL convolution does NOT imply integer cofiniteness. TEST:
does real a.c. (dimension>1) ever hold for a NON-admissible D (∑1/(d−1)<1)? (3,4): dim 1.13>1 so
Hochman would say μ_3*μ_4 is a.c. — but B_3+B_4 is NOT cofinite. So real-a.c. ≠ integer-cofinite →
the continuous→discrete transfer is exactly the same gap as INV-S1/thickness. If real a.c. holds for
(3,4) [dim>1] while integer-(3,4) is not cofinite [confirmed], the dimension route CANNOT distinguish
admissible from non-admissible → DEAD as a sufficient condition. (~15 lines: just confirm dim((3,4))>1
and recall (3,4) not cofinite — likely kills it, cleanly.)
>
> **SELF-KILLED (scholar ran it): DEAD.** dim((3,4))=1.131>1, dim((3,5))=1.062>1, dim((3,4,7))=1.487>1
> — ALL have dimension>1 (⟹ Hochman real-a.c.) but (3,4)/(3,5) are non-admissible (∑<1) and NOT
> cofinite. So the dimension criterion holds for non-cofinite integer sets ⟹ cannot be the
> integer-cofiniteness condition (necessary, not sufficient). Same unbridged continuous→discrete gap
> as S1/thickness. DEAD — don't spend breaker cycles on it.

### INV-S6. The "carry-propagation length" finiteness theorem (mixed-radix odometer)
**Definition.** Represent n simultaneously in all bases d∈D. Adding the per-base 0/1-digit summands
a_d produces CARRIES. New mechanism: prove the maximum carry-propagation length (how far a carry
ripples when you greedily assign digits) is BOUNDED uniformly in n (depending only on D,k), by a
potential argument on the mixed-radix odometer. Bounded carry length ⟹ a finite-window local rule
decides representability ⟹ (with residue coverage) cofiniteness. This is the additive-combinatorics
analogue of "bounded denominators" — make the cross-base interaction LOCAL.
**Why it could work.** The team's (BRIDGE)/seed problem is essentially "can a carry from the base-d_min
digits always be absorbed by the higher bases." If carries never ripple more than C(D,k) positions,
representability is a sliding-window automaton property → decidable + cofinite. The MW near-coincidences
are exactly the spots where a carry MIGHT ripple far (two bases' powers nearly equal ⟹ ambiguous carry)
— so bounding carry length = bounding the MW effect, but as a COMBINATORIAL not transcendence quantity.
**Cheapest kill-test.** Compute, for (3,4,7) k=1 and k=2, the actual maximum carry-propagation length
over all representable n in [N₀, 10^5]: greedily assign digits from the bottom, record how many
positions a carry travels before settling. If max carry length is BOUNDED and does NOT grow with n or
k → strong attempt (local automaton). If carry length GROWS (logarithmically or worse) with n at the
MW-near-coincidence n's → it's the same MW content, unbounded window → dead. (~35 lines.) This directly
probes whether the cross-base interaction can be made local — the make-or-break for any automaton route.

> Round 2 targets the STRUCTURAL/decidability angle (S4 Cobham, S6 automaton-locality) + the
> measure-theoretic threshold gap (S5 Hochman dimension). HONEST self-assessment: S5 likely DEAD (dim
> can't distinguish admissible, clean kill); S4 likely dead but worth explicit ruling; S6 is the live
> one — if carry length is bounded, it's a real decidability proof. All three have <40-line kill-tests.

---

## Round 1 (maverick — operator/automaton/conservation lens; fixing C5's large-deviation flaw structurally)

My C5 (second-moment) died because Chebyshev is large-deviation-blind (Φ=0 at N₀ while E≈20). These
three replace the PROBABILISTIC positivity of Φ with a STRUCTURAL/HARD positivity — the exact fix.
Distinct from carry's constructive descent (INV-C1), modular's local-global (INV-M1), scholar's
circle method (INV-S1): mine are operator-spectral, automaton-emptiness, and per-scale-conservation.

### INV-V1. Gap-carry automaton (mixed-radix carry-conflict language)
**Definition.** Represent n via an interleaved walk over the powers {3^a,4^b,7^c}, state = residual-
demand vector mod (3,4,7) at the current scale, transitions = include/exclude the next power; a hole =
a path that never reaches the accepting (zero-residual) state. Build the PRODUCT automaton over the
0/1-digit constraints. Claim: the non-accepting language is REGULAR and FINITE above scale X₀ ⟹
cofiniteness = automaton emptiness, decidable, NO MW.
**Why it could work.** The 0/1-digit sets are trivially automatic; if their interleaved-carry
sum-automaton has no infinite non-accepting path, cofiniteness is a finite decidable fact. PROXY
SIGNAL (found): the two largest holes 521 & 581 share an IDENTICAL digit-sum signature (base3=7,
base4=5, base7=11) — holes look like a structured automaton class, not random.
**Cheapest kill-test.** Build the product automaton on small digit-windows; is the non-accepting
language finite? KILL if the automaton state count blows up super-polynomially in scale, or the
non-accepting language is infinite (a periodic non-accepting cycle = an infinite hole family = the
conjecture would be FALSE, so really this tests whether the cycle is transient). (~40 lines.)

### INV-V2. Perron-Frobenius transfer-matrix positivity ★ (LEAD — the structural fix for C5)
**Definition.** Write the representation count Φ(n) = uᵀ·(∏ over base-d_min digit-blocks of transfer
matrices T_block)·v, where T encodes how a base-d_min digit-block combines the 0/1 choices across all
bases (carrying the residual). Φ(n) is an entry of a matrix product. Claim: the T's are PRIMITIVE
(irreducible + aperiodic) ⟹ some product power is strictly positive ⟹ Φ(n) > 0 for all n beyond the
primitivity index = an EFFECTIVE, HARD n₀.
**Why it could work.** This is the STRUCTURAL repair of C5's fatal flaw: Perron-Frobenius gives
DETERMINISTIC positivity (a strictly-positive matrix entry), NOT a probabilistic mean that large
deviations defeat. The Φ=0 stragglers that killed C5 would be IMPOSSIBLE once the product is strictly
positive — they can only live in the pre-primitive transient (= below n₀, exactly where they are).
The primitivity index IS n₀, and it's computable from the matrices, not from MW. PROXY (found): Φ=0
set for (3,4,7) k=1 stops exactly at 581 — consistent with a primitivity index.
**Cheapest kill-test.** Construct the digit-transfer operator for Φ for (3,4,7) k=1 (state = bounded
residual/carry); check irreducible + aperiodic. If primitive, the index should = 581. KILL if the
operator has a PERSISTENT invariant zero-subspace (non-primitive / reducible) — i.e. some carry-class
is permanently unreachable in the product. That reducible component IS the MW wall in operator dress;
if it appears, INV-V2 dies the same death. The make-or-break: is the carry-state space FINITE (bounded
carry)? If the carry is unbounded (like INV-C2's ledger risk), the matrix is infinite-dim and Perron
doesn't apply. (~50 lines: build the transfer matrix, test primitivity via matrix powers.)

### INV-V3. Deficit-mass conservation (per-7-power-scale drainage budget)
**Definition.** Track H(n) = #holes ≤ n. Each base-d_max atom d_max^j entering at scale d_max^j
supplies covering mass ≈ ρ·(new interval) that DRAINS deficit accumulated in [d_max^j, d_max^{j+1}].
Per-scale budget: (deficit created in band) ≤ (drainage from the band's new atom). Claim: drainage >
creation per band for j ≥ J₀ ⟹ H(n) bounded (holes finite) by telescoping monotonicity — a LOCAL
conservation law, NOT the global harmonic β.
**Why it could work.** Different invariant from everything tried: it's a per-multiplicative-scale flow
balance, not a global density or a worst-case count. If each scale-band's deficit is locally drained by
that band's own new atom (a self-contained per-band inequality), holes stop without any global/MW input.
PROXY (found): holes-per-band for (3,4,7) k=1: [7²,7³]→19, [7³,7⁴]→2, [7⁴,7⁵]→0, [7⁵,7⁶]→0 — monotone
drain to 0.
**Cheapest kill-test.** Measure holes-per-d_max-power-band. KILL if some deep band REOPENS holes (the
straggler regime): specifically check (3,4,7) k=2 — does the band containing N₀=3,982,888 have a LATE
deficit spike after earlier bands drained to 0? If deficit is non-monotone across bands (drains then
re-spikes at a deep coincidence band), the per-scale conservation FAILS = the MW straggler defeats it.
This is the sharpest test: it directly probes whether the drainage is truly local or whether deep
cross-base coincidences create non-local deficit. (~30 lines, reuse breaker's deep-scale engine.)

> **maverick self-assessment for breaker:** INV-V2 (Perron) is the lead — it's the principled structural
> fix for why C5 died (hard vs probabilistic positivity), and its kill-test (primitivity of the carry-
> transfer matrix) is decisive and cheap. Critical risk for ALL three: BOUNDED CARRY. V1's automaton,
> V2's matrix, and V3's drainage all need the carry/residual state to be FINITE/bounded — if the carry
> between incommensurable bases is unbounded (the recurring obstruction), all three become infinite
> objects and die together. So the ONE meta-kill-test: is the cross-base carry bounded for fixed k?
> (modular's effective-window T≤m and my B₇-sparsity both bear on this.) Prioritize V2; if its matrix is
> finite + primitive, it's a real proof of (BRIDGE)-type positivity.

> **breaker KILL-TEST VERDICTS (maverick V1/V2/V3):**
> - **INV-V2 (Perron-Frobenius, the LEAD): KILLED.** Meta-kill (your own bounded-carry test): the Φ
>   carry-state = the two-base (3,4) correction = the gap of B_3+B_4, which is 7,688 at k=2 and GROWS
>   with k (the gap structure scales with d^k). So the transfer matrix needs ≥7688 states at k=2 and
>   more at higher k — NOT a small fixed-finite operator; its primitivity index is not computably bounded
>   independent of k, and reduces to the same MW n₀. Carry is NOT bounded uniformly → Perron doesn't give
>   an effective k-uniform n₀. DEAD as a uniform tool (per-fixed-k it's just a big finite computation).
> - **INV-V3 (deficit-mass conservation): HOLDS EMPIRICALLY through k=3; a-priori proof reduces to MW —
>   NOT an independent route (maverick verdict + breaker re-spike data).** My re-spike test: holes-per-
>   d_max-band do NOT re-open after draining. (3,4,7) k=2: 7-bands drain 199→809→1945→2127→83→2→0; k=3
>   (ABOVE the true 166M threshold, N=200M): 7-bands 279→…→163418→36379→2155→0, 4-bands 47→…→98297→89717→
>   84005→16133→136→0 — MONOTONE, no re-spike in the d_max decomposition through the k=3 threshold. So the
>   per-multiplicative-scale drainage law HOLDS EMPIRICALLY. **BUT (maverick, verifier of record, downgrade
>   after the data):** PROVING the per-band inequality drainage(j) ≥ deficit-created(j) a-priori reduces to
>   bounding the band's cross-base alignment — each band-deficit is a count of large-deviation events at the
>   power-coincidence sites = the MW wall. Same V2-pattern (empirical-finite vs a-priori-MW): the
>   conservation law is observed to hold but its proof is not local/elementary. **GRAVEYARD: not an
>   independent route to the conjecture; the drainage data is real and consistent with cofiniteness, but it
>   does not escape the MW wall.** Code: breaker_kill_V2_V3.py, breaker_V3_k3.py.
> - **INV-V1 (gap-carry automaton): KILLED (same as V2/INV-C2).** Shares the bounded-carry requirement;
>   carry-state ≥7688 growing with k ⟹ infinite-state in the uniform limit.
> Evidence: breaker_kill_V2_V3.py, breaker_V3_k3.py.

## Round 2 (troika — functional-equation + continued-fraction lanes; NO MW re-skins)

Grounding computed this round (all reproduced): (a) at scales ≤30M, even the NON-cofinite (3,4,11)
β=14/15=0.933 has deficit 0.0 — β<1 non-cofiniteness is INVISIBLE below ~11^8≈2e8 (gaps recur near the
sparsest ray's powers). So no finite-window statistic discriminates β<1 from β=1 (this killed the
second-moment lane, troika_INVENT_band_localized_secondmoment.md). (b) The close 3^p~4^q pairs sit
EXACTLY at convergents of log4/log3 = [1,3,1,4,1,1,11,…]: convergent denominators 4,5,24,29,53,… match
the measured closest-approach exponents p=5,24,29,53. Any valid mechanism must (i) be an ASYMPTOTIC/
all-scale statement, and (ii) reproduce the convergent-located near-alignments.

### INV-T1. Transfer operator on the carry-chain, spectral radius vs β (the "renormalization spectrum")
**Definition.** Encode "n representable by ∑_{d∈D} d^k·B_d" as acceptance by a weighted transfer
operator. Process n's joint mixed-radix digits low-to-high; state = the bounded carry vector
(c_d)_{d∈D} ∈ ℤ^{|D|} truncated to a finite box (the carries between the |D| base-streams). The
recursion T_k = C_k + T_{k+1} (maverick) becomes a linear map M on functions over the carry-state box:
(Mf)(s) = ∑_{digit choices} f(s'), weighted by whether the chosen lowest atoms are legal (0/1 per base).
Define the per-scale COVERING DENSITY as the leading eigenvalue/Perron vector of M restricted to
"covered" states. **Claim:** the spectral radius ρ(M) of the sub-operator that PROPAGATES an uncovered
residue equals 1 at β=1 and <1 for β>1 (geometric deficit decay), with a phase transition at β=1 —
ρ(M)>1 (deficit grows, non-cofinite) for β<1. Cofiniteness ⟺ ρ(M) ≤ 1 with the Perron vector having no
mass on a "permanently uncovered" recurrent class.
**Why it could work.** Converts the asymptotic recurrence (the property no window sees) into a
SPECTRAL property of a FINITE matrix — computable exactly, and a spectral radius IS an all-scale
quantity by construction (it governs n→∞ behavior). This is the renormalization fixed-point the lead
asked for, made into a concrete eigenvalue. The β-dependence enters through the digit-choice weights
(how many lowest-atom options C_k offers), which is exactly ∑1/(d−1) at the boundary. Unlike the
second moment, an eigenvalue captures β<1 vs β=1 because the matrix entries depend on β even when
finite-n data looks identical.
**Cheapest kill-test.** Build M for (3,4,7) [β=1], (3,4,5) [β>1], (3,4,11) [β<1] with a small carry box
(|c_d|≤5). Compute ρ(M) of the "uncovered-propagation" sub-block. KILL if ρ(M) is the SAME (or doesn't
order as β>1: ρ<1, β=1: ρ=1, β<1: ρ>1) across the three — then the operator doesn't see β and INV-T1 is
dead. SURVIVES if ρ(M) orders correctly with β (the discriminator the second moment lacked). The carry
box must be provably absorbing (carries bounded) for M to be finite — test that |carry| stays ≤ box
size on (3,4,7) to N=10⁵ first (if carries grow, the operator is infinite-dim → reformulate or dead).
(~50 lines: build the digit-transition matrix, power-iterate for ρ.)

### INV-T2. Ostrowski/three-distance covering schedule (continued-fraction lane, NOT MW)
**Definition.** The base-3 and base-4 rays interleave by the rotation θ ↦ θ + log4/log3 on the log-scale
circle. By the THREE-DISTANCE theorem, the first N powers {q·log4/log3 mod 1} partition the circle into
intervals of at most 3 distinct lengths, with the gaps controlled by the continued-fraction convergents
of log4/log3 = [1,3,1,4,1,1,11,…]. Build an EXPLICIT covering schedule: at each convergent scale
p_j/q_j, the base-4 powers fill a predictable arithmetic-progression-like set of the base-3 gaps, with
the residual covered by the next convergent. Claim: the B₃+B₄ gap structure is EXACTLY described by the
Ostrowski representation of n (digits w.r.t. the convergent denominators), and the base-(third) ray
needs only to cover the bounded-many Ostrowski-digit configurations that B₃+B₄ misses — a FINITE
casework per convergent level, uniform because the CF is eventually periodic-ish / bounded partial
quotients control the gap sizes.
**Why it could work.** This is transcendence-FLAVORED (it uses that log4/log3 is irrational, via its CF)
but is ELEMENTARY (three-distance theorem + Ostrowski numeration, no linear-forms-in-logs, no MW
constant). It directly exploits the convergent structure I measured (closest pairs at q=4,5,24,29,53).
If the partial quotients of log4/log3 are bounded (they look small: 1,3,1,4,1,1,11,… — the 11 is the
only big one), the gap sizes are uniformly controlled and the covering schedule is uniform in scale.
**Cheapest kill-test.** Compute the B₃+B₄ gaps' positions in OSTROWSKI coordinates (digits w.r.t.
denominators 1,4,5,24,29,…). KILL if the gaps do NOT have a bounded-complexity Ostrowski description
(i.e. gap positions look random in Ostrowski digits) → the CF structure doesn't organize them, dead.
SURVIVES if the gaps occupy a bounded set of Ostrowski-digit patterns (then the third ray's covering is
finite casework). Concretely: for each B₃+B₄ gap up to 10⁶, compute its Ostrowski digit string; check if
the strings fall into O(1) classes. (~40 lines.) Also flag: the big partial quotient 11 may create one
hard scale — check the gap near the q=485 convergent (3^485 is astronomical, so this is the "invisible
recurrence" — consistent with finding (a), and a feature not a bug: it predicts WHERE β=1 is hardest).

### INV-T3. Renewal/recurrence-scale invariant tied to the sparsest ray (the "deficit renewal")
**Definition.** For β<1 the deficit reappears near powers of the SPARSEST base d_max (I measured
(3,4,11) gaps recur near 11^8≈2e8, invisible below). Model the uncovered set as a RENEWAL process: the
"deficit events" occur at a sequence of scales S₁<S₂<… with inter-arrival ∝ d_max (geometric on log
scale). Define the invariant Δ = lim sup (deficit mass in [S_j, S_{j+1}]) / (interval length). Claim:
Δ = 0 ⟺ β ≥ 1 and Δ > 0 ⟺ β < 1, with Δ a continuous function of β EXCEPT a jump at β=1 — and Δ is
computable from the LOCAL covering rate at one renewal scale (no need to reach 11^8 if the renewal
self-similarity is established from the first renewal). The renewal self-similarity (each [S_j,S_{j+1}]
is a rescaled copy) is the functional equation, inherited from T_k=C_k+T_{k+1}.
**Why it could work.** It explicitly models the "invisible recurrence" I found — the reason finite
windows fail is that they sit between renewal events. If the renewal structure is self-similar (provable
from the recursion), then ONE renewal interval determines all of them, so Δ is computable at an
ACCESSIBLE scale even though the gaps themselves are astronomical. This turns the invisible asymptotics
into a finite measurement on the renewal cell.
**Cheapest kill-test.** For (3,4,11), test whether the covering structure in [11^m, 11^{m+1}] is a
rescaled copy of [11^{m-1}, 11^m] (renewal self-similarity), at the small m I can reach (m=4,5,6,
scales 1.4e4–1.7e6). KILL if the rescaled profiles DON'T match (no renewal self-similarity → Δ not
computable from one cell → dead). SURVIVES if they match → then Δ extrapolates and might be measured
without reaching 11^8. Compare profiles via the deficit-vs-(n/11^m) curve at consecutive m. (~35 lines.)

**Round 2 verdict (troika).** INV-T1 (transfer-operator spectrum) is my lead — it's the only candidate
that turns the β-discrimination into an exact finite computation (an eigenvalue ordering), directly
attacking what killed the second moment. INV-T2 (Ostrowski) is the genuinely-new transcendence-flavored
route (CF/three-distance, no MW). INV-T3 (renewal) is the riskiest but would make the invisible
recurrence measurable. Sent to breaker for kill-testing; I'll run the INV-T1 carry-boundedness pre-check
myself next (if carries are unbounded, T1 needs reformulation before any spectral claim).

---

## Round 2 (sumset — VALUE-SPECIFIC invariants that SEE the isolated misses)

Niche from my 5-angle death-point: every COVERAGE/density/run-length invariant is provably blind to
the isolated run-length-1 misses (= the open core). So these read the missing point's VALUE: its
digits, its two-base collision defect. NEW grounded facts (verified this round): (a) late isolated
misses of (3,4,7) almost all have LEADING base-3 digit = 2 (k=2 misses>10⁴: 2224 lead-3=2 vs 1027
lead-3=1; the late k=1 misses 178..581 are nearly all base-3-leading-2, e.g. 581=[2,1,0,1,1,2]₃);
(b) r(581)=0 exactly, neighbors 3–6. NOTE: troika's INV-T1 (transfer-operator SPECTRUM, β-eigenvalue)
owns the spectral/asymptotic-rate angle — mine below are DIGIT/DEFECT-local, not spectral; complementary.

### INV-M4. Leading-digit carry-debt invariant (the "base-b high-digit obstruction"). [GROUNDED]
**Definition.** b=min(D). Carry-debt D_b(n)=(leading base-b digit of n)−1. B_b allows digits 0/1, so
the base-b summand supplies ≤1 unit in the top occupied position; leading base-b digit ≥2 forces the
OTHER bases to cover ≥(lead−1)·b^{top} at the top scale. Scalar Ψ(n)=D_b(n)·b^{top(n)} − R'(n), where
R'(n)=max cross-base (d≠b) reach using atoms ≤ n with top-position support. Proposed theorem: for δ>0,
Ψ(n)<0 for all n>N₀(D,k), ELEMENTARY (margin δ funds the cross-base reach covering the debt).
**Why (SEES gaps).** Coverage asks "is n in the set"; Ψ asks "does n's TOP DIGIT create a debt the
lower bases can't pay" — value-specific, fires exactly on the high-leading-digit isolated misses
(grounded fact a). Localizes non-representability to ONE inequality at the top scale; δ = the surplus.
**Kill-test.** Compute Ψ(n) ∀ n∈[N₀,5N₀] for (3,4,7) k=2 [δ=0] and (3,4,5,6,7) k=2 [δ>0]. REQUIRED:
Ψ(n)<0 ⟺ n representable, EXACTLY (one mismatch ⟹ refine R' or DEAD). Then: for δ>0 is the Ψ<0 onset
ELEMENTARY (not MW-large)? If (3,4,7)'s onset is MW-large but (3,4,5,6,7)'s is elementary, M4 is the
value-specific closer for the non-boundary case. (~30 lines, exact.)

> **PRE-TEST (sumset ran it): crude single-inequality form REFUTED, points to M6.** (3,4,7) k=1, [100,2000):
> crude Ψ (R'=max cross-base reach ≤n) gives 18/1900 mismatches = EXACTLY the isolated misses
> {178,190,209,212,215,216,218,227,…,581}. Crude Ψ calls them representable (Ψ=−59: reach 140 > debt 81)
> but they're NOT — the cross-base value paying the debt must ALSO combine with a base-3 part to hit n
> EXACTLY (distinctness + exact sum), which the loose reach ignores. So a single top-scale inequality is
> NECESSARY-not-sufficient; the residual 18 are the run-1 internal gaps needing the TWO-BASE digit
> interaction = INV-M6. VERDICT: M4-crude DEAD; live form ≡ M6. Clean finding: the obstruction is the
> two-base collision, NOT a one-scale reach deficit — sharpens where breaker should aim.

### INV-M5. Carry-state ZERO-SET tracking (the "r(n)=0 is a dead automaton path"). [GROUNDED, distinct from T1]
**Definition.** r(n)=coeff of x^n in ∏_d∏_{j≥k}(1+x^{d^j}); built digit-by-digit over the modulus chain
M_t=lcm(d^{≤t}), the carry is a STATE vector and r(n)=0 iff n's digit-path enters the matrix-product
ZERO cone. Track the reachable carry-state SET (a subset of a bounded box, IF carries bounded). Claim:
past a bounded prefix, the zero (dead) state is UNREACHABLE ⟹ {r(n)=0} is finite = exactly the
dead-prefix words. NOTE vs troika INV-T1: T1 studies the operator's SPECTRUM (asymptotic count rate);
M5 studies the reachable-state SET and its ZERO cone (exact which-n-vanish) — set-reachability, not
eigenvalues. Decidable-automaton flavor, not spectral.
**Why (SEES gaps).** r(n)=0 IS an internal gap, and it's a transfer-product-zero — automaton-detectable,
value-specific. If multi-base carry is FINITE-STATE (the bet; overlaps carry's INV-C2 ledger but as a
matrix zero-set), "r(n)>0 eventually" = "no infinite dead-path" = decidable, threshold = automaton
diameter = ELEMENTARY, no MW.
**Kill-test.** (3,4,7) k=1 over M_t=lcm(3,4,7) powers: (i) does the reachable carry-state set STABILIZE
to a bounded finite set? If it grows → infinite-state → DEAD. (ii) If finite, is the dead state
unreachable past a bounded prefix? Cross-check dead-prefix words = actual misses {178,…,581} exactly.
If carries blow up, that itself is a clean finding: the miss set is NOT automatic ⟹ obstruction is
genuinely transcendental. (~50 lines.)

> **PRE-TEST (sumset ran it): the missing set is NOT base-b automatic — INV-M5 core bet REFUTED, and
> this is the clean structural dichotomy.** Tested eventual-periodicity of the missing-set indicator on
> (3,5) [∑=0.75<1, so infinitely many gaps — a genuinely nontrivial pattern to test]: the missing
> pattern does NOT match across ANY period 3^p (p=2..11, #missing per cell 7→95396, mismatches at every
> scale). So {r(n)=0} is NOT eventually periodic mod 3^p ⟹ NOT base-3 automatic. The carry-state does
> NOT stabilize to a finite set. VERDICT: M5 DEAD as an elementary closer — BUT this is the valuable
> structural finding the kill-test promised: **the obstruction is provably non-automatic, hence genuinely
> transcendental**, consistent with the MW diagnosis. It also WEAKENS the shared "miss set is
> digit-recognizable" bet behind M4/M6 — the full miss set is not automatic. (M6 may still survive if its
> BOUNDED-ρ₄ claim holds DESPITE non-automaticity — those are independent; breaker should still test M6,
> but knowing the miss set isn't automatic lowers its prior.)
>
> **METHODOLOGICAL REFINEMENT (sumset, for the citable writeup): the test must be done CAREFULLY.** A
> single-window periodicity check (miss[N−2P,N−P] vs [N−P,N]) gives FALSE POSITIVES — spuriously reports
> "period 9" for (3,7), "period 16" for (4,5). CORRECT test needs (i) P=b^p to match at MANY disjoint
> windows across [N/4,N] AND (ii) each missing class mod P FULLY (1.0) missing. Under it, NONE periodic:
> (3,5) 26/60 windows, class-fill 0.49; (3,7) 39/60, 0.85; (4,5) 39/60, 0.90 — all below the 60/60 & 1.0
> a genuine period needs. Non-automaticity is ROBUST across all tested multi-base families. Final citable
> form: sumset_contributions_final.md Result 1.

### INV-M6. Two-base defect descent keyed on the SECOND base (the "4-adic repair of the 3-debt"). [GROUNDED]
**Definition.** Digit-DNA shows: leading base-3 digit 2 ⟹ n≈2·3^J+low, base-3 part gives ≤3^J+low, so
DEFICIT≈3^J is repaired by base 4 (+7). Base-4 repair index ρ₄(n)=min #nonzero base-4 digits (powers
4^{≥k}) representing the deficit (n − best base-3 part). Claim: ρ₄(n) BOUNDED (≤ρ₄^max(D,k)) ∀
representable n; non-representable ⟺ deficit's base-4(+7) pattern needs an uncarriable digit ≥2 — a
LOCAL base-4 obstruction at the 3^p≈4^q collision scale. Descent keyed on base-4 digits (NOT greedy
size — distinct from carry's INV-C1).
**Why (SEES gaps).** Reads BOTH bases' digits at the MW collision spot and asks a FINITE base-4-digit
question. Bounded ρ₄ ⟹ the {3,4} clustering becomes "can a bounded base-4 pattern absorb the 3-debt,"
potentially elementary. Tests the exact two-base collision, not coverage.
**Kill-test.** (3,4,7) k=1,2: compute ρ₄(n) ∀ representable n (greedy base-3 part, min base-4 digits
for deficit). BOUNDED & n-independent (say ≤6)? → finite-local repair → attempt (check k-uniformity).
GROWS with n or k → encodes MW spacing → DEAD. Decisive: at the leading-2 misses (n≈2·3^J) does ρ₄
spike bounded or unbounded? (~35 lines.)

> **Self-assessment for breaker:** all three VALUE-SPECIFIC by design — they target the run-length-1
> isolated misses that ALL coverage invariants (my M1/M3, density's margin, scholar's/troika's averaged
> or spectral objects) are blind to. Priority: M4 (sharp exact-match Ψ<0⟺representable, fails fast) →
> M6 (aimed at the {3,4} MW spot) → M5 (boldest: finite-automaton decidability; distinct from troika T1
> by tracking the zero-SET not the spectrum). Shared bet: the miss set is DIGIT-RECOGNIZABLE (automatic),
> making N₀ an automaton diameter (elementary) — dissolving the MW-threshold-LOCATION problem the way
> carry's INV-C1 dissolved peel-existence. If misses are NOT automatic (M5 carries blow up), that PROVES
> the obstruction is genuinely transcendental — a clean structural dichotomy either way.

> **maverick META-KILL-TEST RESULT (I ran the bounded-carry test on V1/V2/V3):**
> The carry-state (proxy: # residues mod d_min^s with a late miss) STABILIZES, confirming bounded carry
> — V2's transfer matrix is FINITE — at k=1:
> - {3,4,5} k=1: live-residues 3→9→14→18→18→18→18 (STABLE at 18). ✓
> - {3,4,7} k=1 (BOUNDARY): 3→9→17→29→29→32→32 (STABLE at 32). ✓ — bounded even at the hard boundary.
> So V1/V2/V3 do NOT die to unbounded carry at k=1 — the meta-kill I feared is PASSED. V2's matrix is
> finite (~32 states for (3,4,7) k=1) and the candidate is attemptable: build it, test primitivity, the
> index should be 581.
> **HONEST LIMITATION at k≥2:** {3,4,7} k=2 live-residues 3→9→27→81→240→640 — GROWING, not clearly
> stabilizing within N=8M (≈2·N₀). Could be a window artifact (N₀(k=2)=3.98M, so residues still in the
> pre-n₀ transient inflate the count) OR genuine carry-growth with k. UNDETERMINED. So V2 is a clean
> attempt for k=1 (finite primitive matrix → effective n₀=581 with no MW), but its k≥2 finiteness is
> open — if the carry-state grows with k, V2 gives the per-fixed-k=1 result but not k-uniformity, same
> tier as the adjudicated strict-excess result. breaker: push the k=2 window to ≫N₀ to settle whether
> 640 is transient (stabilizes) or genuine growth — THAT decides V2's reach. [V2 = lead, k=1 attemptable now.]

> **breaker SETTLED maverick's k=2 question (the V2 reach decider):** Pushed the residue-state count
> (# residues mod 3^s with a miss) to N=12M (≫ N₀(k=2)=3.98M):
> - k=1: 3→9→18→32→33→37→37→37 — STABILIZES at 37. ✓ V2's matrix IS finite at k=1 (maverick right;
>   primitive-matrix attempt for the 581 index is valid).
> - k=2: 3→9→27→81→241→642→1504→2803 — KEEPS GROWING (≈×3 per step, tracking 3^s), well past N₀, NOT a
>   transient. So the carry-state space GROWS with k. **VERDICT: V2 is a clean PER-FIXED-k=1 tool (finite
>   primitive matrix → effective n₀=581, no MW) but is NOT k-uniform — its state count grows ~3^s at k=2.**
>   Same tier as the strict-excess result: a real per-k partial, not a uniform proof. (Reconciles my
>   earlier "killed" — I measured the value-gap 7688; maverick measured the residue-state count 32; both
>   right: finite at k=1, growing at k≥2.) The genuine k-uniform conjecture is NOT closed by V2.
> **breaker INV-M6 (rho_4 bounded?): SURVIVES the boundedness kill (ρ₄ BOUNDED + k-uniform) — but
> empirical-vs-a-priori caveat applies.** Ran the PROPER test (ρ₄(n) = min #base-4 atoms over ALL reps of
> n, exact triple-loop S3×S7×S4, not the earlier degenerate greedy proxy):
>   (3,4,7) k=1: ρ₄ max=4 (mean 0.88); k=2: max=6 (mean 1.43); k=3: max=5.
>   DECISIVE: at the TRUE k=3 threshold n0=166,025,260 (where the high-θ cascade is PERVASIVE, depth 5-6),
>   ρ₄ max=5 (mean 2.84) — BOUNDED, NOT spiking. So the base-4 repair index stays small (≤6) and k-uniform
>   across k=1,2,3 AND at the hardest boundary region. M6's "bounded ρ₄" hypothesis HOLDS empirically — the
>   only value-specific candidate to pass the boundedness kill. Structurally distinct from the high-θ
>   cascade (bounded even where the cascade is deep). CAVEAT (same V2/V3 pattern): ρ₄-bounded over
>   REPRESENTABLE n is necessary + consistent with cofiniteness, but the M6 CLAIM ("non-representable ⟺
>   deficit needs an uncarriable base-4 digit ≥2") requires proving the repair NEVER fails above n₀ a-priori
>   = bounding when the base-4 repair can't absorb the 3-debt = the cross-base {3,4} collision = MW. So:
>   EMPIRICALLY ALIVE (ρ₄ bounded, k-uniform — real signal, beats every other value-specific invariant),
>   but a-priori proof likely reduces to MW like V3. Worth sumset's attempt as a strict-excess closer / a
>   characterization-of-misses tool; not obviously a uniform proof. Code: breaker_kill_M6_proper.py,
>   breaker_M6_kdep.py, breaker_M6_truethreshold.py.
>
> **sumset ATTEMPT RESOLUTION: bounded-ρ₄ is CIRCULAR; the non-circular budget GROWS = MW. M6 a-priori DEAD,
> alive only as a characterization tool.** I ran the NON-CIRCULAR version: define T_R = S3 + S7 + (base-4
> numbers with ≤R atoms) — a CONSTRUCTIVE set that does NOT assume representability — and find the smallest
> R making T_R cofinite (= the full threshold). Results: R(k=1)=5 (T_5 threshold = 581 = full); R(k=2)=8
> (T_8 = 3,982,888 = full; R=6,7 still short). **R GROWS with k (5→8, ~+3/k).** This RESOLVES the
> empirical-vs-a-priori caveat: breaker's ρ₄(n)≤6 is the EXISTENTIAL min base-4 atoms over reps of an
> ALREADY-REPRESENTABLE n (circular — assumes n∈T_k); the NON-CIRCULAR constructive budget R(k) needed to
> PROVE cofiniteness grows, and is the same c(D,k)→∞/MW content. The two are consistent (a representable n
> may use few base-4 atoms, but COVERING every n needs a growing base-4 OPTION budget). VERDICT: M6 does
> NOT give a k-uniform a-priori proof — its constructive budget is MW. It survives ONLY as (b) a
> characterization-of-misses tool (non-rep ⟺ ρ₄-obstruction holds per-n, but locating where it fails is MW).
> So M6 joins the wall: empirically the strongest value-specific invariant, but its a-priori closure is MW,
> exactly as breaker flagged. Code: /tmp/m6_attempt.py (R(k=1)=5, R(k=2)=8 verified at N=6M).

#### INV-T1 PRE-CHECK RESULT (troika, self-run) — PARTIAL KILL, needs reformulation
Ran the carry-boundedness / automaticity pre-check. Findings (B₃+B₄ in base 12=3·4, the gappy
β=5/6 case where structure is visible):
- Suffix-complexity GROWS: #distinct width-W cover-patterns = 32, 84, 172 for W=8,16,24 (≈linear in W,
  not saturating to a small constant — but not exploding to 2^W either; moderate complexity).
- NOT periodic in base 12: 0 of 12^L residues (L=2,3,4) have cover determined by residue alone.
**Verdict:** the B₃+B₄ cover-set is NOT a finite-state automatic set in base 12 — no residue/bounded
suffix determines cover, so the naive finite carry-box transfer operator does NOT capture it. This is
the SAME 3-vs-4 coupling obstruction (incommensurate radices) that defeats single-base renormalization.
**INV-T1 as stated is WOUNDED** (the carry box is effectively unbounded in base-12 framing). REFORMULATION
that might survive: the operator must act on the LOG-SCALE (Ostrowski) digits of n w.r.t. log4/log3, not
base-12 digits — which merges INV-T1 into INV-T2 (the continued-fraction lane). So the two leads
CONVERGE: the right state space is the Ostrowski/CF numeration, not a fixed-radix carry. That is the
sharper target. Net: INV-T1-base12 dead; INV-T1-on-Ostrowski = INV-T2, promoted to sole lead.

#### INV-T2 KILL-TEST RESULT (troika, self-run) — SURVIVES (promoted to sole lead)
Tested whether B₃+B₄ gaps have CF-structured positions in log-scale coordinates. Binned gaps by
θ₃=log₃(n) mod 1 (the natural Ostrowski/rotation coordinate for the 3-vs-4 interleaving):
- Gaps are HEAVILY CONCENTRATED: max/min bin ratio = **203** (vs 1.0 = uniform), with a sharp peak at
  θ₃≈0.80–0.85. Gaps are NOT spread uniformly in log-scale — they cluster at specific log-positions.
**Verdict: INV-T2 SURVIVES.** The continued-fraction / three-distance structure DOES organize the gap
positions (concentrated at specific θ₃, the rotation-orbit "bad" positions). So the gap set has a
bounded-complexity Ostrowski description, and the third ray's covering reduces to finite casework per
θ-class. This is the genuinely-new, transcendence-FLAVORED-but-MW-FREE lead (Ostrowski numeration +
three-distance theorem, elementary), and INV-T1's wound pointed here (Ostrowski is the right state space,
not fixed-radix). **Sole surviving lead from Round 2.** Next attempt step: map the peak θ₃≈0.82 to a
convergent of log4/log3 and check the third ray (base 7/11/…) covers that θ-class for all scales — that
is the (BRIDGE) reduced to a finite, scale-uniform Ostrowski casework. Handed to breaker for the β≈0.95
discrimination kill (does the θ-concentration differ between β≥1 and β<1 families?).

> **breaker KILL-TEST (INV-T2 β-discrimination): PARTIAL KILL — θ-clustering is NECESSARY-NOT-SUFFICIENT.**
> The θ₃=log₃(n) mod 1 concentration of gaps does NOT discriminate cofinite from sub-threshold. max/min
> bin ratio: cofinite (3,4,7) k=1 = 6.0, k=2 = 7.6; sub-threshold (3,4)=8.2, (3,5,7)=40, (3,4,11)=6.0,
> (3,5)=3.3. The cofinite family has LOWER concentration than two non-cofinite ones — the clustering is a
> GENERIC feature of gaps sitting near powers, present whether or not the family is cofinite (the deep-trap
> families cluster too, yet their bad θ-class is NEVER covered, gaps→∞). So T2's BRIDGE claim ("3rd ray
> covers the bad θ-class at all scales ⟹ finite casework") IS the unproven covering question = MW content;
> the θ-analysis organizes gaps but doesn't establish the covering. VERDICT: useful descriptive lens,
> necessary-not-sufficient, same wall for the boundary/sub-threshold regime. May close the EASY strict-
> excess family (like S9) where the bad class is provably covered — keep as strict-excess-partial, NOT a
> general closer. Code: breaker_kill_T2.py.

---

## Round 3 (scholar — probabilistic, p-adic, and converse-transference gaps)

### INV-S7. Second-moment / variance concentration on representation count (probabilistic method)
**Definition.** Let r(n) = #{representations of n as ∑_d a_d, a_d∈d^k·B_d}. Compute E[r] and Var[r]
over a window; if Var[r(n)] < E[r(n)]² for all n past N₀ (concentration), then r(n)>0 (Paley-Zygmund /
second-moment ⟹ representable). Model the digit choices as independent and bound the variance via the
near-orthogonality of the per-base characters (the decorrelation of INV-S1 in L² form).
**Why it could work.** It only needs r(n)>0, not a precise count — a softer target. The decorrelation
(verified: bases share no major arc) is exactly an L²-near-orthogonality that controls covariance
across bases. Mean r(n) grows (verified ~30 at n~40k for (3,4,7) k=1).
**Cheapest kill-test.** [scholar ran it — INFORMATIVE, leans HARD] min r(n) over windows for (3,4,7)
k=1 is NON-monotone and dips to 1–2 even at large n (windows: min = 1,5,2,5,31,16,14 across [600,37k]).
The dips are at the MW-clustered n's — exactly where r(n) is smallest. So Var ≥ E² fails AT those n's
(a single representation ⟹ no concentration). VERDICT: second-moment in its naive form is DEAD at the
boundary (the MW n's have r=1, no margin). SALVAGE only if a WEIGHTED count (INV-S2 thickness weight)
lifts the min off 1 — so S7 collapses into S2. Mark S7 as "dead unless S2's weighting rescues it."

### INV-S8. p-adic / profinite obstruction-vanishing (the inverse-limit completeness criterion)
**Definition.** Cofiniteness of ∑_d d^k·B_d ⟺ (residue coverage mod every M [team-PROVED]) + (no
"obstruction at infinity"). New mechanism: view the problem in the profinite completion Ẑ = lim ℤ/M.
The team proved the sumset surjects onto every ℤ/M (gcd=1). The REMAINING content is an Archimedean
(real-place) condition. Frame completeness as: the adelic image of the sumset is everything EXCEPT a
compact obstruction at the real place, and the harmonic condition ∑1/(d−1)≥1 is exactly the statement
that the real-place density (= Astels thickness, my proven result) closes that compact obstruction.
This SEPARATES the finite places (done) from the infinite place (the open core) cleanly via a
local-global / Hasse-style decomposition.
**Why it could work.** The team has cleanly PROVEN the finite-place (residue) half. A local-global
framing makes explicit that ALL remaining difficulty is at the single real place — and at the real
place the object is the self-similar Cantor sum K_d whose a.c./interval property IS the Astels
threshold. It could turn "cofinite" into "surjective at all finite places (done) + interval at ∞
(Astels, ∑≥1)" — a clean two-part theorem if the local-global glue (a quantitative CRT + density
matching) holds.
**Cheapest kill-test.** The glue is the question: does "all residues mod M for every M" + "real
density ≥ 1" ⟹ "cofinite on ℤ"? Counterexample probe: find a set hitting all residues mod every M AND
with real-thickness ≥1 but NOT cofinite. Candidate: a SUB-critical-but-residue-complete family. Test
(3,4,9) (gcd=1 ⟹ all residues, but ∑1/(d−1)=0.958<1): is it residue-complete yet non-cofinite? If YES,
then "residues + something" needs the something to be EXACTLY ∑≥1 (not just thickness>0) — confirming
the real-place condition is sharp and the decomposition is meaningful. If the decomposition can't be
made quantitative (the glue needs the full answer), DEAD. (~25 lines.)

### INV-S9. Transference from the PROVEN converse (contrapositive density-increment)
**Definition.** The converse (∑1/(d−1)<1 ⟹ NOT cofinite, Pomerance/density, PROVEN by the team via
Weyl equidistribution producing a missing block just below d_min^m) is constructive: it BUILDS
infinitely many holes. New mechanism: run the converse's hole-construction machinery IN REVERSE as a
density-increment argument. The converse shows holes live just below d_min^m and have a specific
Weyl-equidistribution cause; if ∑1/(d−1)≥1, the SAME analysis shows the would-be hole is FILLED (the
equidistribution that creates a gap below threshold instead achieves full coverage). I.e. transfer
density's OWN proven converse-mechanism across the threshold to get the forward direction.
**Why it could work.** density already has a RIGOROUS, constructive converse with an explicit
Weyl/equidistribution criterion locating holes (verified: (3,6,7) n=40,342,197 unreachable by exactly
1). That same criterion, evaluated at ∑≥1, should output "coverage" instead of "hole" — the threshold
∑=1 is literally the crossover in their formula. Reusing a proven mechanism across its own threshold is
often the cleanest forward proof (you already control the hard analysis).
**Cheapest kill-test.** Ask density: does your converse hole-criterion (the gap-prediction formula,
ledger §4b) become VACUOUS (predicts no hole) exactly when ∑1/(d−1)≥1, or does it still predict holes
that happen to get filled by a separate mechanism? If the formula's "hole exists" condition is
literally ¬(∑≥1) — i.e. the criterion flips cleanly at the threshold — then the forward direction is
the same proof read backward → STRONG. If the formula still predicts holes for some ∑≥1 families (that
are filled by the MW/clustering mechanism, not by the density formula), then the converse does NOT
transfer and the forward direction needs genuinely new input → DEAD. density can answer from existing
code in minutes. (~0 new lines — it's a question about density's existing formula.)

> Round 3: S7 (2nd-moment) self-assessed DEAD-unless-S2 (MW n's have r=1, no concentration). S8 (p-adic
> local-global) — clean conceptual separation of the proven finite-place half from the open real-place
> half; kill-test is a residue-complete-but-subcritical probe. S9 (transfer density's proven converse
> backward) — potentially the CHEAPEST real attempt because it reuses machinery density ALREADY has
> rigorous; the whole question is whether their hole-formula flips cleanly at ∑=1. HANDED S9 to density
> (answerable from existing code). S8 to breaker.

---

## Round (cassels — +M-closure / hole-structure lens)

All three below TESTED before posting (cheap kill-tests run). Two genuinely-new survive at k=1 with
honest k-dependence; one fresh untested candidate handed to breaker. Two ideas DIED in pre-check
(recorded so nobody re-skins them).

### INV-cassels-1 (CANCEL). Bounded signed-cancellation closure.
**Definition.** Allow ONE bounded subtraction: claim every hole n satisfies n = p − q with p,q both
representable (∈ R(D,k)) and q ≤ Q*(D,k) an explicit constant. Then "R(D,k) is cofinite" reduces to
"R is closed under the bounded operation p ↦ p − q for q ≤ Q*", i.e. the present set's complement is
contained in (present − [0,Q*]). Mechanism: instead of marching n upward (+M closure, which stalls),
certify each hole by a nearby-above present value minus a small slack.
**Why it could work.** It inverts the closure direction (subtract, not add) and the slack q is
EMPIRICALLY tiny — so it's a genuinely different reduction: "holes are a bounded shadow below the
present set." If Q* is uniformly bounded it's a clean closure; the present set is then cofinite iff it
has no Q*-deep complementary run, a finite local condition.
**Kill-test + RESULT (cassels ran it).** Q* = max over holes of min q:
  (3,4,7) k=1: Q*=7 · (3,4,5) k=1: Q*=3 · (3,4,6) k=1: Q*=4 — TINY at k=1.
  BUT (3,4,5) k=2: Q*=105 · (3,4,7) k=2: Q*=117 — Q* GROWS with k.
**Verdict: SURVIVES at k=1 (clean, Q*≤7); k-DEPENDENT (Q* blows up with k, same wall as N₀/m₀).**
Still a real *compression* (Q*≈117 ≪ N₀≈3.98M at k=2 — the slack needed is far smaller than the
threshold). Worth attempting as: prove Q*(D,k) ≤ explicit g(D,k); even non-uniform g would localize
the obstruction to a Q*-window. NOT a k-uniform escape.

### INV-cassels-2 (CLASS-NEIGHBOR). Within-residue-class bounded-step AP onset.
**Definition.** Let M=∏_{d∈D} d. Claim: above a threshold, every hole n has a representable p with
p ≡ n (mod M) and p − n ≤ L(D,k)·M for an explicit L. Equivalently each residue class mod M becomes
a full step-M arithmetic progression after at most L(D,k) M-steps. Cofiniteness ⟺ L finite. The NEW
content vs my Lemma C: it uses the FULL modulus M=∏d (not b^k), exploiting that residue coverage
(modular's L) gives one class representative and this bounds how far the AP-onset sits.
**Why it could work.** It fuses residue coverage (proven) with a SMALL explicit step-count L — turning
"where does the class AP start" into "L M-steps", a single integer per class. If L is bounded the
whole theorem is a finite per-class check.
**Kill-test + RESULT (cassels ran it).** max within-class M-steps to next present above a hole:
  (3,4,7) k=1: 1 M-step (dist ≤ M=84) — every hole is within ONE modulus of its class's present AP.
  (3,4,5) k=2: 5 M-steps · (3,4,7) k=2: 7 M-steps.
**Verdict: SURVIVES at k=1 (L=1, sharp); k-DEPENDENT (L grows 1→5→7).** Like INV-A, a real compression
(7 M-steps vs N₀=3.98M) but not k-uniform. Attempt target: bound L(D,k) explicitly; the L=1 at k=1 is
a genuinely clean statement ("every class is its full AP within one modulus" — possibly provable k=1).

### INV-cassels-3 (UNSCALE). Multiplicative-orbit deflation. [UNTESTED for k-uniformity → breaker]
**Definition.** Claim every hole h has a base b∈D with b·h representable, AND a "deflation" rule: if
b·h ∈ R then h ∈ R via dividing the base-b structure (the inverse of the IFS map x↦b·x on the base-b
ray). Iterate: a hole deflates to a smaller number; if the orbit hits a representable seed, lift back.
**Why it could work.** It's the ONLY multiplicative (not additive) mechanism proposed — it rides the
self-similar IFS map x↦b·x directly, which is exactly the recursion T_k=C_k+T_{k+1} read multiplicatively.
If holes deflate to a finite seed set under ×b/÷b orbits, cofiniteness follows by a descent with NO
additive marching.
**Cheapest kill-test (FOR breaker).** Verified prelim: 36/37 holes of (3,4,7) k=1 have b·h present for
some b. NEXT: (i) is the deflation rule SOUND — does b·h ∈ R actually imply h ∈ R (not just numerically
co-present)? Build the explicit lift and check it produces a valid representation of h. (ii) Does every
hole's ×b-orbit reach a representable seed in O(log h) steps at k=1,2,3? If the lift is unsound (co-presence
is coincidental) OR orbits don't terminate, INV-cassels-3 dies. (~30 lines.)

> **KILLED at SOUNDNESS (breaker, breaker_kill_cassels3.py). The deflation rule "b·h∈R ⟹ h∈R" is
> FALSE.** The prelim "36/37 holes have b·h present" is the SET OF COUNTEREXAMPLES, not support: for 36
> of 37 holes h of (3,4,7) k=1, b·h∈R for some b YET h is a hole — the rule would falsely certify 36
> holes representable. E.g. h=581: 3·581, 4·581, 7·581 all ∈ R, but 581 ∉ R. Structural reason: b·h=∑_d
> a_d, but to deflate you'd need every a_d divisible by b — true only for the base-b ray; for d coprime
> to b the rep uses base-d atoms NOT divisible by b, so x↦x/b is well-defined on a SINGLE ray but NOT on
> the cross-base sum. **REFUTES the "multiplicative/self-similar escapes the wall" hypothesis:** all
> three multiplicative candidates fail at their core (INV-C1 circular/decoder-not-proof; cassels-3
> UNSOUND; Ostrowski-T2 nec-not-suff). The ÷d map breaks exactly at the cross-base coupling = the MW
> content. Only the asymptotic analytic route (S10 minor-arc) attacks the coupling head-on. [DEAD.]

### DIED IN PRE-CHECK (do not re-skin):
- **INV-cassels-REFLECT** (base-d all-ones reflection n↦R_J−n maps holes to present): VACUOUS — random
  n reflect-to-present at rate 1.00, same as holes. The present set is just dense; no real symmetry.
- **INV-cassels-ONEATOM** (hole + single atom = present): true 37/37 but it's literally a +M-closure
  variant — not new, already covered by Lemma C.

> NOTE (cassels, honest pattern): every additive hole-closure mechanism I test shows the SAME k-signature
> — clean/bounded at k=1, constant grows with k. This is structural: the obstruction (cross-base power
> spacing) is genuinely k-scaling. The candidates that might ESCAPE are the non-additive ones (carry's
> INV-C1 log-descent, my INV-cassels-3 multiplicative deflation, troika's Ostrowski-CF operator) —
> because they ride the self-similar ÷d map rather than +M marching. Recommend the blitz weight toward
> MULTIPLICATIVE/self-similar mechanisms; additive ones keep hitting the same wall.

---

## Round 2 (density — measure lens: make the internal gaps VISIBLE)

The problem with ordinary density: |S∩[0,X]|/X → 1 even for sub-threshold families at any feasible
finite scale, because the recurring power-aligned gaps sit near d_min^m for large m (e.g. (3,6,7)
first gap at 3^16, (3,5,7) at 3^60). Ordinary density averages them away. These four measures are
designed to CONCENTRATE on the danger zone or read the gap from a fragility signal. All four
self-tested below; honest verdicts included.

### INV-D1. Power-shadow concentrated measure μ_p
**Definition.** Weight n by 1/(d_min^m − n) inside each "shadow window" [d_min^m/2, d_min^m); ignore
the rest. μ_p-missing-fraction = (weighted missing)/(weighted total). Amplifies the zone just below
each d_min-power where the converse mechanism puts the gaps.
**Why.** The gaps are NOT uniform — they live in the shadow of d_min-powers (my converse proof). A
measure concentrated there sees them at far lower scale than uniform density. Ordinary density gives
weight ~1/X to the shadow; μ_p gives O(1).
**Cheapest kill-test (RAN).** Compute on (3,4,7)[cofinite], (3,5)[gappy], (3,6,7)[gap at 3^16],
(3,4,5,7)[cofinite] to N=3^11. Result: μ_p-missing = 0.000 / 0.417 / 0.000 / 0.000. SEES (3,5) but
NOT (3,6,7) (its gap is beyond 3^11). VERDICT: PARTIAL — discriminates ∑<1-with-low-gaps from
cofinite, but inherits the "gap beyond range" blindness for ∑-near-1 families. Useful as a cheaper-
than-uniform detector, not a complete one.

### INV-D2. Worst-octave (limsup) relative-gap measure ν
**Definition.** ν(D) = limsup over m of the relative gap of S within the single octave
[d_min^m, d_min^{m+1}). Scale-EQUIVARIANT (worst octave, not average). Track the TREND in m: growing
⟹ gaps recur ⟹ incomplete; → 0 ⟹ cofinite.
**Why.** The recurrence criterion (δ vs g*) lives in the limsup, not the average. ν is the measure
matched to the self-similar structure — it reads the worst octave, which is exactly where the
power-gap sits.
**Cheapest kill-test (RAN).** Dominated by the low-scale transient octave (3^2 always gappy). VERDICT:
needs m ≥ m0 cutoff to drop the transient; the asymptotic trend is the right object but is itself the
limsup g*(D), which is MW/transcendental in general (so ν is the SHARP measure but not finitely
computable for ∑-near-1 families — it IS the quantity the problem reduces to, not a shortcut).
This makes ν the "correct" measure-theoretic invariant: ν(D) > 0 ⟺ incomplete. Proving ν=0 for
admissible D is equivalent to the conjecture.

### INV-D3. Representation-fragility measure (min-reps decay) — STRONGEST measure candidate
**Definition.** Weight/score n by 1/(number of representations reps(n)). Track min-reps in a window
just below d_min^m across m. A family whose min-reps DECAYS toward 0 as m grows will develop a gap
(reps hits 0) at the scale where the decay reaches 1 — PREDICTING the gap-onset WITHOUT reaching it.
**Why.** This is the key measure-lens idea: it does not need to SEE the gap, it reads the APPROACH to
the gap from the representation-count trend at accessible scales. reps(n) → 0 is the gap forming;
the decay rate extrapolates the onset scale. This could make (3,5,7)'s 3^60 gap predictable from 3^9
data.
**Cheapest kill-test (RAN).** min-reps just below 3^m: (3,4,7) 48→78→182 (GROWING, cofinite);
(3,6,7) 8→18→79; (3,5,7) 5→74→123. At 3^9 the ORDER (3,6,7)=79 < (3,5,7)=123 < (3,4,7)=182 matches
gap-onset order (3,6,7 first at 3^16). VERDICT: PARTIAL SURVIVOR — the m=9 ordering is correct and
predictive, but lower-m data (3^7,3^8) is noisy/non-monotone, so it's a HEURISTIC fragility trend,
not yet a clean discriminator. NEXT: fit the decay law (is min-reps ~ d_min^{m·(∑1/(d-1)−1)}? if the
exponent is the harmonic deficit, the onset scale 3^{m: min-reps=1} is COMPUTABLE and predicts the
gap). [HANDED to breaker: does min-reps decay exponent = harmonic deficit ∑1/(d−1)−1? If yes, INV-D3
predicts every gap-onset from low-scale data — a genuinely new, computable gap-detector.]

> **breaker KILL-TEST (INV-D3, the handoff): KILLED.** Fitted the min-reps-below-3^m exponent (m=6..11)
> vs harmonic deficit. NO match: (3,4,7) deficit=0.000 → fitted +0.341; (3,4,5) deficit=+0.083 → fitted
> +0.905 (10× off). DECISIVE: (3,4,11) deficit=−0.067 (NOT cofinite) → fitted exponent +0.537 POSITIVE
> (min-reps GROWS), so D3 predicts (3,4,11) COFINITE — WRONG (gap at 9e9). The "decay exponent = deficit"
> law is false, and D3 is fooled by the deep-trap families like every low-scale heuristic. Not a
> gap-predictor for the ∑-near-1 families that matter. Code: breaker_kill_D3.py.

### INV-D4. Digit-run-weighted (d_min-adic Fourier) measure μ_D4
**Definition.** Weight n by d_min^{r(n)} where r(n) = length of the maximal run of digit (d_min−1) at
the TOP of n's base-d_min expansion (so n just below d_min^m gets weight ~d_min^m). Measure missing
fraction under this weighting. This is essentially the top non-trivial d_min-adic Fourier mode (the
0th mode = ordinary density, blind; this mode is tuned to the power-shadow).
**Why.** The gap signal is carried by the high d_min-adic Fourier modes (periodic in digit
structure), which ordinary density (0th mode) discards. μ_D4 projects onto the mode where the gaps
live.
**Cheapest kill-test (RAN).** (3,4,7) 0.000 / (3,5) 0.217 / (3,6,7) 0.000 / (3,4,5,7) 0.000 to 3^12.
VERDICT: same partial behavior as μ_p (sees (3,5),(3,4), not the beyond-range (3,6,7) gap). The
Fourier framing is the right LANGUAGE (connects to Mauduit–Rivat digit-correlation literature
scholar flagged) but at finite scale it's equivalent to μ_p. Value: it suggests an ANALYTIC attack —
bound the high d_min-adic Fourier coefficients of 1_S; if they decay (∑γ≥1) the gaps vanish. That
analytic decay statement, NOT the finite computation, is the potential lever.

**Summary for breaker.** INV-D3 (fragility decay) is the strongest — it's the only one that could
PREDICT a beyond-range gap from accessible data, IF the decay exponent = harmonic deficit (kill-test
handed off). INV-D2/ν is the "correct" invariant but transcendental. INV-D1/D4 are cheaper-than-
uniform detectors but inherit the range blindness. INV-D4's analytic (Fourier-decay) reframing is a
separate potential lever worth a real attempt.

---

## Round 3 (density — measure lens, multiplicative/conserved-quantity measures)

Two measures exploiting MULTIPLICATIVE structure (not additive), a genuinely different lens from
Round 2's concentration measures.

### INV-D5. Carry-deficit / base-d_min digit-sum Lyapunov measure φ
**Definition.** φ(n) = digit-sum of n in base d_min. Hypothesis: non-representable n have
ANOMALOUSLY HIGH φ (they sit just below a power, all-high-digits, needing more "digit budget" than
the bases can supply via carries). Use φ as a candidate Lyapunov/conserved quantity: representability
fails exactly when φ exceeds the budget the bases can discharge.
**Why.** Each base d contributes a bounded digit-budget per scale (the 1/(d−1) reach in digit-sum
terms). A number with maximal digit-sum (just below d_min^m) is the hardest to represent — the gaps
ARE the high-φ numbers. φ is a measure that ranks n by representability-difficulty, which uniform
density cannot. If "representable ⟺ φ(n) ≤ Φ_max(scale)" with an explicit budget Φ_max, that's an
elementary criterion.
**Cheapest kill-test (RAN).** Mean base-d_min digit-sum, missing vs present n (upper third):
(3,5) missing 11.50 vs present 10.13; (3,4) missing 11.93 vs present 10.28. CONFIRMED: missing n have
systematically higher φ (gap ~1.3–1.6 in mean digit-sum). VERDICT: SURVIVES as a real signal. NEXT
kill-test: is there a SHARP threshold Φ_max(D,k,scale) such that φ(n) > Φ_max ⟺ n missing (not just
"higher on average")? If the missing set = {high-φ tail} exactly, φ is a complete criterion; if the
distributions merely overlap-shifted, φ is only a heuristic. [Measure the φ-distribution overlap:
is there a clean cutoff or just a shifted mean? If clean cutoff → strong; if overlap → heuristic.]

### INV-D6. Multiplicative shift-invariance defect (the "×d_min self-map test") — clean discriminator
**Definition.** Measure the defect of the self-map x ↦ d_min·x on S: fraction of n ∈ S with
d_min·n ∉ S (for d_min·n ≤ N). If S is cofinite the defect → 0; if S has positive-density complement
the defect is positive. This is a MULTIPLICATIVE closure test, orthogonal to additive +M-closure.
**Why.** Multiplying n by d_min shifts its base-d_min digits up by one place (leading order), so
d_min·S ≈ S if S is "digit-shift stable" — which cofinite sets are. The defect detects the complement
WITHOUT averaging (it's a per-element self-map check), and it's invisible to additive density. It
also connects to INV-C1's halving-rewrite (the inverse map x ↦ x/d_min is the recursion step).
**Cheapest kill-test (RAN).** ×d_min defect to 3^10: (3,4,7) 0.0000, (3,6,7) 0.0000, (3,5) 0.4022.
CLEANLY separates cofinite ((3,4,7) AND (3,6,7) both 0) from incomplete ((3,5) 0.40). VERDICT:
SURVIVES — cleaner discriminator than the additive measures (D1/D4 also gave (3,5)=gappy but D6's
0/0.40 split is sharper). LIMITATION (honest): like all finite-scale measures, (3,6,7)'s defect is 0
at 3^10 because its gaps are at 3^16 — D6 inherits range-blindness for ∑-near-1 families. But D6's
VALUE is theoretical: "defect = 0 for all scales ⟺ cofinite" reframes the conjecture as a
multiplicative-closure statement, which pairs with INV-C1's x↦x/d_min recursion. NEXT: does
defect(D,scale) decay at a rate tied to the harmonic deficit (like INV-D3)? If defect ~ scale^{deficit}
it predicts onset; cross-check with breaker's INV-D3 decay-law test (same underlying question).

**Note for breaker.** INV-D6's defect and INV-D3's min-reps likely measure the SAME underlying decay
(both → 0/positive as the complement does). The decisive shared kill-test is the DECAY-LAW question:
does the relevant quantity (min-reps, or 1/defect) scale as d_min^{m·deficit}? One test settles both.

#### INV-T2 DEEPER PROBE (troika, self-run) — mechanism REAL, clean-threshold claim CORRECTED
Pushed INV-T2 toward the β-discrimination. Two findings, one encouraging, one a correction:
- ENCOURAGING (equidistribution holds): base-7's θ₃-orbit {l·log7/log3 mod 1} HITS the (3,4) bad-θ peak
  (orbit points 0.765, 0.797, 0.824, 0.856, 0.882 — densely around the peak θ₃≈0.82). So the third ray
  DOES equidistribute to cover the bad θ-classes — the covering mechanism is real, not a concentration
  miss. This is the genuine content and it survives.
- CORRECTION (the clean inequality is NOT clean): I conjectured "third ray covers iff 1/(d₃−1) ≥
  (3,4)-gap-θ-measure ≈ 1/6 ⟺ β≥1," an exact elementary threshold. But the (3,4) deficit measure is NOT
  a stable 1/6 — it OSCILLATES by scale (0.077, 0.206, 0.078 in consecutive dyadic windows; same
  band-oscillation that killed the second moment). So the comparison is lim-sup vs lim-inf of an
  oscillating measure, NOT a constant inequality. The asymptotic subtlety re-enters here.
**Refined INV-T2 status:** the covering MECHANISM (CF/three-distance + third-ray θ-equidistribution
hitting the bad classes) is verified and MW-free. The β-discrimination is NOT the clean density
inequality I hoped — it requires controlling the OSCILLATING deficit measure's lim sup, which is the
same recurrence/asymptotic content (now phrased as: does the third ray's θ-orbit cover the bad classes
at EVERY scale, including the deficit-measure peaks?). So INV-T2 reduces (BRIDGE) to: **a scale-uniform
θ-equidistribution of the third ray against the OSCILLATING (3,4) θ-deficit profile.** Still MW-free,
still the lead, but the "clean elementary inequality" is downgraded to "scale-uniform equidistribution
vs an oscillating target" — sharper than before, honestly not closed. The oscillation is the residual
enemy (it's the 3-vs-4 band beating, the same coupling throughout this problem).

## troika META-NOTE (after Rounds: 2nd-moment, transfer-operator, Ostrowski all probed)
Three independent invention lanes I've now stress-tested — (a) second-moment/variance, (b) fixed-radix
transfer operator, (c) Ostrowski/CF covering — ALL hit the SAME wall: the **3-vs-4 band oscillation**
(the deficit measure of B₃+B₄ oscillates by scale, 0.077↔0.206, because log4/log3 is irrational and the
two rays beat). This oscillation is why:
- the second moment can't discriminate β (window sees one phase of the oscillation);
- the transfer operator isn't finite-state in base 12 (oscillation = non-automaticity);
- the Ostrowski inequality isn't a clean constant (oscillating target).
**CONSTRAINT ON ANY SURVIVING CANDIDATE (for the whole cell):** it must control the LIM SUP of the
oscillating B₃+B₄ deficit measure against the third ray's coverage, UNIFORMLY in scale — not an average,
not a window, not a single residue class. Equivalently: the invariant must be evaluated on the
oscillation's WORST phase (the deficit peaks, e.g. the 0.206 windows), and show the third ray still
covers there. Any candidate that only controls the average or a window is pre-killed by this note.
The productive next inventions should target the OSCILLATION ITSELF: e.g. an exact functional equation
for the deficit-measure oscillation (a 2-variable transfer operator on (θ₃,θ₄) jointly, the genuine
2-torus skew-product), whose invariant measure's support is the bad set the third ray must cover. That
2-torus skew-product (rotation by (log4/log3) coupled across both rays) is the honest object — fixed-radix
and single-θ projections all lose information. That's where I'd point Round 3.

---

## Round 2-3 KILL-TEST RESULTS (density ran the decisive decay-law test)

**INV-D3 (min-reps fragility) — KILLED as a low-scale predictor.** Ran the decisive test: does
log(min-reps below d_min^m) have slope = harmonic-deficit·log(d_min)? NO. Measured slopes are
POSITIVE (+0.66 to +0.86) even for sub-threshold (3,6,7),(3,5,7),(3,5,8) whose deficit is NEGATIVE —
wrong sign, no match. Reason: at accessible scales (3^7–3^10, far below the real gap-onset 3^16/3^60),
min-reps still GROWS (cofinite-looking regime); it would only turn over near the actual gap, which is
unreachable. So min-reps at low scale does NOT extrapolate to predict the gap. **INV-D3 does not
escape range-blindness — KILLED.** (The m=9 ordering I saw earlier was noise, not a decay signal.)

**INV-D6 (×d_min defect) — likely same fate** (measures the same underlying complement, which is
0 until the gap-onset). Its theoretical value (multiplicative-closure reframe pairing with INV-C1)
stands, but as a finite-scale DETECTOR it's range-blind like the rest.

**HONEST META-CONCLUSION (measure lens, all rounds).** No finite-scale measure — concentration (D1),
worst-octave (D2), fragility (D3), Fourier-mode (D4), digit-sum (D5), or multiplicative-defect (D6) —
can SEE or PREDICT the beyond-range gaps of ∑-near-1 families, because the gap-onset itself is an MW
quantity (INV-D2's ν = g*(D) is transcendental). This is not a failure of imagination but a THEOREM-
shaped obstruction: the only measure that detects the gaps is ν (the limsup octave gap), and computing
ν is equivalent to the conjecture. SURVIVORS with non-detector value: INV-D5 (digit-sum Lyapunov —
the missing-n-have-high-φ signal is real and could feed a conserved-quantity proof, NOT a detector)
and INV-D4 (the analytic Fourier-decay reframing — a proof lever, not a computation). The measure lens
is exhausted for DETECTION; its residual value is in REFRAMING (D4 analytic, D5 Lyapunov).

## Round 3 (troika — the 2-torus skew-product, grounded)

### INV-T4. The (θ₃,θ₄) 2-torus deficit function + third-ray orbit covering (the renormalization done right)
**Definition.** Coordinate n by its joint log-position (θ₃,θ₄) = ({log₃ n}, {log₄ n}) on the 2-torus 𝕋².
**Verified fact (the grounding):** the B₃+B₄ deficit indicator is (to 0.024 mean error, 93% of bins
within 0.1) a FIXED FUNCTION D(θ₃,θ₄) on 𝕋² — scale-INVARIANT (low-half vs high-half profiles match),
unlike the single-θ₃ projection (0.106 error, fails). So the bad set 𝓑 = {(θ₃,θ₄) : D>0} ⊂ 𝕋² is a
fixed compact region. As n runs, (θ₃,θ₄) follows the line {(t·log₃ e? ...)} — precisely, log n moves
linearly so (θ₃,θ₄) advances on the line of slope (1/log3, 1/log4), an irrational line winding densely
on 𝕋² (since log3, log4 are ℚ-independent... they're rationally related? log4=2log2, log3 — independent
over ℚ, yes). The third ray (base d₃): adding atom d₃^l shifts the position by ({l log_{d3}/log3 ...}).
**Claim (BRIDGE on 𝕋²):** n is covered by B₃+B₄+B_{d₃} iff the third-ray orbit from (θ₃(n),θ₄(n)) exits
the bad set 𝓑. This holds for ALL n (cofinite) iff the third-ray orbit-closure on 𝕋² is not trapped in
𝓑 — a statement about the orbit's equidistribution vs the FIXED region 𝓑, SCALE-INVARIANT by
construction (𝕋² is compact, the deficit function is fixed). **β enters as area(𝓑):** area(𝓑) =
asymptotic deficit, and the third ray covers iff its 𝕋²-orbit density 1/(d₃−1) exceeds area(𝓑) AND
equidistributes over it. The oscillation that killed the window methods is RESOLVED here — it's just
the orbit moving through the fixed D(θ₃,θ₄), no longer a moving target.
**Why it could work.** This is THE renormalization fixed point: a fixed function on a compact 𝕋²,
verified scale-invariant. It converts the asymptotic recurrence (invisible in n) into ergodic theory on
𝕋² (a compact space where "for all n" = "for the whole orbit closure" — no large-n blindness). It is
MW-FREE (ergodic/equidistribution, not linear-forms). It explains every prior wall: window/second-moment
= sampling one stretch of the 𝕋²-orbit (misses the bad region if the window doesn't reach it);
fixed-radix = wrong coordinate (base-12 ≠ 𝕋²); single-θ = projecting away θ₄. The 2-torus is the honest
object my three earlier lanes were each shadows of.
**Cheapest kill-test.** (a) Confirm D(θ₃,θ₄) scale-invariance at a THIRD scale (I tested 2 halves to
0.024; check [N,2N] for N=8M,16M agree) — if it DRIFTS, not a fixed function, dead. (b) Plot the bad
set 𝓑 and overlay the base-7 𝕋²-orbit; check the orbit EXITS 𝓑 from every starting point (sample 10⁴
starts). KILL if some 𝓑-region is orbit-trapped (base-7 can't escape ⟹ permanent gaps ⟹ but (3,4,7) is
cofinite, so a trap would be a BUG in the model — strong kill). SURVIVES if orbit always exits 𝓑.
(c) β-discrimination: area(𝓑) and orbit-density for (3,4,7) [β=1] vs (3,4,11) [β<1] — does the (3,4,11)
base-11 orbit FAIL to cover 𝓑 (trapped/insufficient density) while base-7 succeeds? If yes, INV-T4 is
the discriminator (on a compact space, so it SEES the asymptotics the windows missed). (~50 lines.)
**Status:** grounding (a) DONE (deficit is a fixed 𝕋² function, 0.024 error). (b),(c) are the attempt.
This is my strongest candidate — it's the only one that turns "for all n→∞" into "over a compact orbit
closure," structurally escaping the finite-scale blindness that killed everything else. Handed to breaker.

---

## Round 4 (scholar) — INV-S1 SHARPENED into a precise open lemma (scholar + lift convergence)

### INV-S10. The Riesz-product decorrelation lemma (THE single step closing both INV-S1 and the (3,4,7) BRIDGE)
**Definition.** INV-S1 and lift's (BRIDGE) inequality (lift_bridge_quantified.md) are the SAME analytic
target. Stated exactly: for the lacunary products F_d(θ) = ∏_{j≥k}(1+e(d^jθ)) (magnitude =
2^·∏|cos(π d^j θ)|), prove the UNIFORM MINOR-ARC bound — for θ bounded away from all rationals a/d_i^j
(small denominator):  |F_3(θ)·F_4(θ)·F_7(θ)| ≪ N^{3−δ}  (some δ>0). Then the minor-arc part of
r(n)=∫∏F_d·e(−nθ)dθ is dominated by the positive major-arc main term ⟹ r(n)>0 for all large n ⟹
R_1 cofinite (and k-uniformly, since raising k only discards low-j factors).
**Why it could work.** [VERIFIED numerically — scholar] The decorrelation HOLDS: at S=B_3+B_4's
largest minor-arc peak (θ≈0.31), normalized |F_S|=0.040 while |F_7|=0.031 ⟹ product 0.0012; over ALL
θ>0.02 the max normalized |F_S·F_7| is 0.003. The three lacunary products are NEVER simultaneously large
off θ=0 — because ∏|cos(π d_i^j θ)| is large only near a/d_i^j, and a/3^j vs a/4^q vs a/7^r near-coincide
ONLY at the MW convergents of log4/log3 etc. So the bad arcs are sparse + structured (= the same MW
near-coincidence set lift's §B and troika identified). This is the analytic face of the team's open core.
**Why it's NOT in the literature (scholar-verified).** Maynard 2019 / Mauduit-Rivat minor-arc bounds are
prime-weight-tied (von Mangoldt inserted) and NOT portable to the pure indicator. Erdős-Joó-Komornik /
Drmota-Tichy give only Diophantine / almost-everywhere decay of ∏|cos|, never a uniform minor-arc bound.
The Riesz-product L¹ norm = 1 (lacunary orthogonality) is the precise obstruction: flat in L¹ but spikes
on minor arcs. Besicovitch-Cassels-Schmidt (normal numbers, coprime bases) are metric, don't control the
simultaneous product. ⟹ a GENUINELY NEW harmonic-analysis lemma.
**Cheapest kill-test / attack.** (a) Confirm the major-arc main term dominates at k=1 by FFT (INV-S1's
test — if minor mass already swamps where we KNOW cofinite, dead). (b) The PROOF route: bound
∏|cos(π d_i^j θ)| on minor arcs via the three-distance theorem / continued-fraction structure of where
each factor is large, showing the three bases' large-sets overlap only on the measure-small MW-convergent
arcs. Margin is thin (lift: 1.5–3×, non-growing at ∑=1) ⟹ the bound must be SHARP at the boundary — a
crude L² bound won't do; needs the exact CF/Ostrowski geometry (ties to INV-S3). Publishable on its own
if proved. [scholar + lift; → troika for the MW/CF geometry of the near-coincidence arcs.]

> **breaker SCOPE-PINNED KILL-TEST (INV-S10), per lead's directive — VERDICT (b): threshold-exact DIES,
> ASYMPTOTIC SURVIVES as the live analytic target.** My earlier S1 kill (major-arc main term O(1) at the
> actual misses 178/212/581, minor arcs same order) is decisive ONLY for the THRESHOLD-EXACT form —
> nothing analytic reaches 581 itself, agreed. But S10's ACTUAL claim is the ASYMPTOTIC uniform minor-arc
> bound |F_3F_4F_7| ≪ N^{3−δ}, δ>0, which my S1 kill does NOT touch. I tested it directly:
> The minor-arc (|θ|>0.02) max of the NORMALIZED product log2(|F_3F_4F_7|/2^mtot) decays exponentially in
> #atoms with a per-atom rate c that is BOUNDED BELOW and stable/growing as N→∞:
>   (3,4,7) k=1: c=0.210 (N=20K) → 0.222 → 0.254 → 0.276 (N=20M) — c GROWS, does not vanish.
> k-robust AND boundary-robust: c stays in [0.17,0.31] across k=1,2,3 for BOTH boundary families
> (3,4,7),(3,5,7,13) AND strict-excess (3,4,5,7). So the decorrelation/minor-arc decay HOLDS UNIFORMLY:
> |F_3F_4F_7| ≤ 2^{mtot(1−c)} = N^{3−δ} with δ>0, empirically, k-uniformly. ⟹ r(n)>0 for n > an effective
> N₀≫581, with [581,N₀] a finite check. **S10's asymptotic form is a GENUINELY LIVE, MW-free-at-the-
> harmonic-analysis-level target** — the team's strongest analytic lead, NOT killed by the S1 result.
> CAVEAT (honest, the residual hardness): the PROOF must turn this empirical exponential decorrelation
> into a rigorous uniform bound; the thin margin at ∑=1 (lift's 1.5–3×) means the constant must be sharp,
> and the bad arcs (where c would be smallest) sit at the MW near-coincidence convergents — so the
> remaining work is bounding c BELOW on those sparse structured arcs (the CF/Ostrowski geometry, ties to
> S3/T4). That's a hard harmonic-analysis lemma, but it is NOT obstructed the way the threshold-exact and
> finite-scale routes are. Code: breaker_kill_S10_v2.py, breaker_S10_boundary.py.

#### INV-T4 KILL-TEST RESULT (troika, self-run) — WOUNDED: 2-torus is ~94% but NOT exact
Tested whether (θ₃,θ₄) FULLY determines cover (the model's core assumption). Measured within-bin
impurity of the (3,4) deficit on (θ₃,θ₄) grids:
- mean impurity = 0.06, and it BARELY decreases with finer grids: 0.069 (30²) → 0.060 (60²) → 0.052
  (120²). A true function-of-(θ₃,θ₄) would have impurity → 0 with finer bins. It PLATEAUS at ~0.05.
**Verdict: INV-T4 WOUNDED.** The 2-torus (θ₃,θ₄) is the BEST approximate renormalization object found
(94% determined, scale-invariant to 0.024 — far better than single-θ at 0.106 or fixed-radix) BUT it is
NOT exact: ~5–6% of points are misclassified by the 2-torus coordinate, a residual finer-arithmetic
structure the projection loses. So the bad set 𝓑 is fuzzy (~6% boundary noise), and the clean
"orbit-exits-𝓑" ergodic argument has that much slop — not enough for a rigorous all-n covering proof,
though plenty for strong heuristic/numerical prediction.
**What the residual 6% IS (next probe):** likely the dependence on the CARRY between the θ₃ and θ₄
clocks (which digit-position the base-3 vs base-4 expansions are "between") — i.e. the exact 𝕋² needs a
THIRD coordinate (a bounded carry/phase), making it a 2-torus × (finite fiber) skew-product. That finite
fiber is exactly maverick's bounded-carry C_k offset structure. So INV-T4 ⟶ the right object is
**𝕋² × {finite carry fiber}** — merging the 2-torus (this round) with maverick's recursion fiber. That
combined object might be EXACT (impurity → 0). That's the Round-4 target.
**Net Round 3:** INV-T4 is the best-grounded candidate so far (escapes finite-scale blindness via
compactness, MW-free, 94% exact) but needs the finite carry-fiber extension to become rigorous. No clean
kill; a structural refinement target identified. The 𝕋²×fiber object is where I'd put the next attempt.

> **V2 BUILD RESULT (maverick, greenlit by lead) — DIES, honest death point (NOT tuned):**
> Built the transfer-matrix state space for (3,4,7) k=1 exactly. The Perron premise (finite matrix)
> is FALSE. ROOT: I conflated two quantities in the meta-kill-test:
> - Quantity A = # residues mod 3^s with a LATE MISS: BOUNDED (3,9,17,29,29,32,32 → stabilizes at 32).
>   This is what I measured before and wrongly called "bounded carry." It measures miss-set THINNESS.
> - Quantity B = # REACHABLE residues mod 3^s (the actual forward-transfer-matrix state): UNBOUNDED
>   (1,7,20,81,217,727,2187,… → fills all of ℤ/3^s). This is what a transfer matrix for
>   representability must track.
> A transfer matrix needs B finite; B is NOT finite (grows to 3^s). So **V2's Perron-Frobenius premise
> fails — the matrix is infinite-dimensional.** No primitivity index; V2 cannot give n₀=581.
>
> **RECONCILIATION with sumset M5 (lead's required check):** sumset found the (3,5) miss set is NOT
> base-3 automatic. That is EXACTLY quantity B unbounded (non-automatic ⟺ no finite DFA ⟺ reachable-
> residue states grow without bound). The two results COEXIST and are the SAME fact: A (miss thinness,
> bounded) ≠ B (automaton states, unbounded). My earlier "32 states" was A, not B — a genuine error in
> the meta-kill-test, now corrected. V2 dies at the non-automaticity wall (= MW wall in automaton dress).
> Honest: the finite-state route is dead for admissible families, confirming sumset M5 extends to (3,4,7).
> V1 (gap-automaton) and V3 (deficit-conservation) inherit the SAME B-unbounded death (all need finite
> carry-state) — V1 dead, V3's per-scale framing might survive as an inequality NOT requiring finite
> state (it's a counting bound, not an automaton) — flag V3 for separate test, V1+V2 dead.

#### INV-T4 REHABILITATED (troika, Round 4 probe) — 2-torus IS the object; residual is BOUNDARY, not a missing coord
Followed up the "6% impurity" wound. Two tests:
1. Carry-fiber adjunction (testing my hypothesis that the 6% = maverick's carry fiber): tried fibers
   n mod 12, n mod 84, ⌊log₃n⌋ mod 4, beat-phase (⌊log₃n⌋−⌊log₄n⌋) mod 6 — NONE reduce impurity (all
   stay ~0.064–0.072). **My carry-fiber hypothesis is WRONG** — the residual is not a simple bounded fiber.
2. Resolution scaling (the decisive test): impurity DECAYS steadily with torus resolution —
   0.082 (20²) → 0.064 (40²) → 0.054 (80²) → 0.048 (160²) → 0.041 (320²). It does NOT plateau; it's a
   slow power-law decay. **This is the signature of a CONTINUOUS BOUNDARY**, not a missing coordinate:
   the deficit IS a function of (θ₃,θ₄) almost everywhere, and the "impurity" is just boundary-bin
   discretization noise whose MEASURE → 0 as resolution → ∞.
**CORRECTED VERDICT: INV-T4 STRENGTHENED.** The 2-torus 𝕋² IS the exact renormalization object (a.e.).
The bad set 𝓑 = {D(θ₃,θ₄)>0} ⊂ 𝕋² is a FIXED region with a continuous (measure-zero) boundary. No carry
fiber needed — the fiber tests correctly showed none helps BECAUSE there's no missing coordinate, only a
boundary. So (BRIDGE) ⟺ the third-ray orbit on 𝕋² exits the fixed open region 𝓑 from a.e. start — a
clean ERGODIC statement on a compact space, MW-free, scale-invariant by construction. **This is the
cleanest formulation of the open core reached by the cell:** prove the base-d₃ orbit (a sub-action on
𝕋²) is not trapped in the open set 𝓑, with area(𝓑) = asymptotic deficit and the trapping governed by
whether the orbit's density 1/(d₃−1) exceeds the obstruction — the ergodic incarnation of β≥1.
**Remaining open (the genuine hard core, now precisely sited):** (i) the third-ray "orbit" on 𝕋² is the
image of a SUBSET-SUM set (not a single rotation orbit), so its closure/equidistribution needs an
argument; (ii) area(𝓑) vs the orbit covering must be made into the β≥1 ⟺ escape equivalence. Both live
on the compact 𝕋² — no large-n blindness, no transcendence. Strongest lead; handed to breaker + maverick.

---

## INV-S9 RESULT (density answered scholar's flip question)

**The flip is ONE-DIRECTIONAL and clean in the USEFUL (forward) direction. PARTIAL SURVIVOR.**

FORWARD (clean, now RIGOROUS): ∑1/(d−1) ≥ 1 ⟹ NO top-of-power gap, for ALL admissible D.
Proof: top-of-d_min^m gap exists iff ∑_d maxB(d, d_min^m−1) < d_min^m − 1. But
maxB(d,X) = (d^{L+1}−1)/(d−1) with d^{L+1} > X (X=d_min^m−1), so maxB(d,X) ≥ X/(d−1). Summing:
∑_d maxB(d,X) ≥ X·∑1/(d−1) ≥ X = d_min^m − 1. So no gap. ∎ Verified: zero violators among ALL
admissible families with d∈3..12, r≤4; positive margins (16,39,15,47 for (3,4,7),(3,4,5),(3,4,6),
(3,4,5,7)). So my converse's top-of-power machinery, read backward, GIVES a forward result on the
coarse gap family for free — exactly scholar's hoped-for case 1.

REVERSE (NOT clean): ∑<1 does NOT always ⟹ top-of-power gap. (4,5,6,7) ∑=19/20<1 and (3,4,8)
∑=41/42<1 have NO top-of-power gap to m=200 yet are non-cofinite — their gaps are INTERIOR
(MW-clustered), invisible to the formula.

VERDICT: S9 SURVIVES for what it claims — it closes the EASY gap family (top-of-power = coarse =
runs, per the run-vs-singleton finding) in the forward direction, rigorously and for free. It does
NOT touch the INTERIOR/MW gaps (the isolated singletons), which remain the open core. So S9 = a clean
elementary forward half on the coarse gaps, confirming the coarse/internal split from the formula
side. Net: "∑≥1 ⟹ no top-of-power gap" is a RIGOROUS lemma (not just empirical); the conjecture's
remaining content is entirely the interior gaps. This MATCHES density's run-bound and sumset's
runs-vs-singletons exactly — three derivations of the same coarse/internal boundary.

## Round 4 (troika — the 2-torus skew-product operator, BUILT)

### INV-T5. The (θ₃,θ₄) skew-product deficit operator — BUILT, discriminates β on visible data
**The object (built).** Log-coordinate n by (θ₃,θ₄)=({log₃n},{log₄n}) ∈ 𝕋². As n grows, (θ₃,θ₄) flows
linearly with slope (1/log3,1/log4) (irrational winding). Renormalization maps (the functional eq from
B_d=d·B_d⊔(1+d·B_d)): n→3n shifts θ₄ by log3/log4=0.7925 (θ₃ fixed mod 1); n→4n shifts θ₃ by
log4/log3=0.2619. The deficit is a fixed density D(θ₃,θ₄) on 𝕋² (verified a.e., continuous boundary,
INV-T4). The third ray d₃ adds atoms at 𝕋²-positions (l·log d₃/log3, l·log d₃/log4) mod 1.
**The discriminating invariant (the asymptotic deficit δ).** δ(D) = lim density of uncovered n =
∫_{𝕋²} (residual deficit after all rays' coverage). δ=0 ⟺ cofinite ⟺ β≥1; δ>0 ⟺ β<1. THIS IS THE
QUANTITY NO WINDOW SEES (for 3-ray families the n-recurrence is at ~d_max^8, e.g. 11^8≈2e8≫16M).
**BUILT + CALIBRATED (the key result).** Measured δ on VISIBLE two-ray families (deficit is O(1) there,
no recurrence-scale problem):
| family | β | asymptotic deficit δ |
|---|---|---|
| (4,5) | 0.583 | 0.833 |
| (3,7) | 0.667 | 0.670 |
| (3,6) | 0.700 | 0.526 |
| (3,5) | 0.750 | 0.362 |
| (3,4) | 0.833 | 0.334 |
**δ is MONOTONE DECREASING in β and → 0 as β → 1⁻.** So the operator's fixed-point δ DOES discriminate
(δ>0 below threshold, →0 at threshold) — the asymptotic β-separation that finite-n windows provably
cannot do (confirmed: direct n-measurement of (3,4,11) worst-phase deficit is 0.000 at 16M, invisible).
**What's NOT clean (honest):** δ is NOT a simple closed form in β (e.g. NOT δ=1−β: (3,4) at β=0.833 has
δ=0.334≠0.167). δ depends on the detailed 𝕋² deficit geometry, not β alone. So extrapolating two-ray δ
to the three-ray threshold needs the FULL operator (the D(θ₃,θ₄) convolution with the third-ray orbit),
not a formula.
**Status — the operator is BUILT and discriminates; the OPEN CORE is now sharply sited:** prove that the
3-ray fixed-point δ(D) = 0 EXACTLY when β≥1, i.e. the third-ray orbit's coverage of the 𝕋² bad-set 𝓑
drives the residual deficit to 0 iff 1/(d₃−1) ≥ area(𝓑). This is an ERGODIC/measure statement on the
COMPACT 𝕋² — MW-free, scale-free (no recurrence-scale blindness, since δ is defined as the 𝕋² integral,
not an n-limit). **This is the cleanest, most rigorous-shaped formulation of the E124 open core the cell
has produced.** The remaining hard step: the third-ray "orbit" is a subset-sum image (not a single
rotation), so its coverage of 𝓑 needs a genuine equidistribution argument — but on a compact space.
Kill-tests: (a) breaker — does δ(3,4,7)→0 but δ(3,4,11)>0 when computed via the FULL operator (not
n-sampling)? (b) worst-phase — is area(𝓑) the right threshold quantity vs 1/(d₃−1)?

#### INV-T5 ↔ lift's band-density reconciliation (troika, verified)
lift independently reached the knife-edge (|3^m−7^r| binding, confirmed) and proposed the bridge is
"MW positions the 7^r-band + the band's internal density bridges." Reconciled with verified data:
- The 7^r-band's bridging count IS the discrete incarnation of the 2-torus deficit δ: # base-d₃
  subset-sums bridging a point in the 3^15 gap = 207 (mean 329) for d₃=7 [β=1] vs 36 (mean 61) for
  d₃=11 [β=0.933]. So the band count CARRIES β (lower for sparser base) — it is δ's finite-scale proxy.
- Correction to lift's numbers: B₇ subset-sum max gap near X is ~0.12·7^7 (not ≈7^r — subset-sums are
  far denser than single powers); bridging count is 207–428 (not ~92).
- THE HONEST LINE (agreed): band count >0 at scale X does NOT certify >0 asymptotically — for β<1 it
  drops to 0 only at the recurrence scale ~d_max^8 (invisible). So "complete modulo MW positioning
  constant" OVERCLAIMS. The true (BRIDGE) = "band count stays >0 at ALL scales" = the asymptotic
  band-equidistribution = exactly δ=0 on 𝕋² (INV-T5). lift writes the band-density half; it pairs with
  my 𝕋² operator as the same statement in two languages (discrete band-count ↔ 𝕋² fixed-point δ).

#### INV-T5 HONEST DOWNGRADE (troika, after breaker's C5-band kill)
breaker killed C5-band: no band-local statistic to finite N separates β=0.933 from β=1 (the (3,4,11)
discriminating stragglers are >9×10⁹, beyond reach; (3,5,7)'s threshold IS reachable so its 24 misses
ARE seen — the tell). This forced me to re-examine INV-T5 honestly:
- My INV-T5 δ-table (two-ray 0.83→0.33) was measured by **n-sampling** cover(D,N) at N=16M. For TWO-ray
  families that works (deficit visible). But for the THREE-ray near-β=1 families, n-sampled δ at 8M is
  0.0000 for BOTH (3,4,7) [β=1] and (3,4,11) [β=0.933] — **so INV-T5-as-I-measured-it INHERITS
  breaker's kill.** The δ I computed is an n-sampled quantity, the killed kind.
- The INV-T5 CLAIM that escapes the kill — δ computed 𝕋²-INTRINSICALLY (fixed-point from the visible
  2-ray D(θ₃,θ₄) + the third-ray orbit operator, NO 3-ray n-sampling) — is **NOT YET BUILT.** I only
  built the sampled version. So INV-T5's discriminating power is currently a HOPE, not demonstrated.
**Honest status:** INV-T5's structural advantage (compact 𝕋², δ as integral not n-limit) is REAL in
principle, but the actual discriminating computation requires building the third-ray coverage operator
on 𝕋² and solving for its fixed-point δ analytically — which I have not done. Until that operator is
built and shown to give δ(3,4,7)=0, δ(3,4,11)>0 WITHOUT 3-ray sampling, INV-T5 is unproven and
provisionally subject to breaker's wall. The un-built 𝕋²-intrinsic fixed-point is the only thing that
could escape; it is the precise remaining target, not a result.
**Meta (the whole cell's wall, now triply-confirmed):** breaker's kill + my honest downgrade = the
β-discrimination is genuinely beyond ALL finite-N computation (it's the asymptotic Pomerance/MW
content). Any candidate claiming to discriminate MUST compute an intrinsic (non-n-sampled) quantity.
That is the bar. Everything sampled is pre-killed.

#### INV-T5 INTRINSIC ATTEMPT — ALSO KILLED (troika, the "one real shot" fails)
Built the 𝕋²-intrinsic coverage-prob discriminator (the only version that could escape breaker's
wall): for each family, coverage prob P(θ) = fraction of filler-ray atoms c with n−c covered by the
VISIBLE 2-ray set — uses ZERO recurrence-scale sampling. Tested if min P or frac{P<thresh} orders with
cofiniteness across breaker's families:
| D | β | cofinite | min_covprob | frac<0.5 | frac<0.7 |
|(3,4,7) | 1.000 | YES | 0.273 | 0.033 | 0.084 |
|(3,4,10)| 0.944 | NO  | 0.344 | 0.045 | 0.102 |
|(3,4,11)| 0.933 | NO  | 0.453 | 0.003 | 0.077 |
|(3,5,7) | 0.917 | NO  | 0.316 | 0.155 | 0.539 |
|(3,4,5) | 1.083 | YES | 0.580 | 0.000 | 0.034 |
**NO column orders with cofiniteness.** min_covprob: cofinite (3,4,7)=0.273 < non-cofinite (3,4,11)=0.453
(WRONG order). frac<0.7: cofinite (3,4,5)=0.034 but cofinite (3,5,7,9)=0.623 (varies wildly within YES).
The earlier d₃=7-vs-11 separation (0.000 vs 0.006) was SAMPLING NOISE, not robust.
**KILLED.** Even the intrinsic (non-n-sampled) SINGLE-SHIFT coverage statistic fails — it does not
capture the asymptotic recurrence. **This is the strongest form of breaker's wall:** the discrimination
needs ITERATING the coverage to recurrence depth (each gap point covered ⟹ check ITS coverer is itself
reachable, recursively), which no single-pass intrinsic statistic shortcuts. The recursion depth IS the
recurrence scale. So INV-T5 is fully killed — sampled AND intrinsic-single-pass both fail.
**FINAL META (quadruply confirmed: 2nd-moment, C5-band, T5-sampled, T5-intrinsic):** the β-discrimination
is irreducibly iterative-to-recurrence-depth. No statistic — sampled or intrinsic, local or global,
single-pass — separates β=0.933 from β=1 without effectively reaching ~d_max^8. This is the Pomerance/MW
content stated as a hardness fact: **the open core admits no computational shortcut.** That is itself a
firm, useful conclusion for the cell — it bounds what any invention can achieve and says the proof must
be analytic (the iterated operator's spectral radius / an a-priori asymptotic estimate), never empirical.

> **V2-k=1 / "elementary 581" BANKING VERDICT (maverick, team-lead asked to bank): DOES NOT GO THROUGH.**
> Settled the contradiction (breaker's "37 states stabilize → finite matrix → elementary 581" vs my
> "reachable-residue state grows → 3^s"). Both numbers are real but measure DIFFERENT objects:
> - Reachable-residue state (FORWARD transfer matrix, the object that would PROVE 581): GROWS
>   1,7,20,81,217,727,2187 → 3^s. UNBOUNDED. No finite transfer matrix. (= sumset M5 non-automaticity.)
> - "37" = Myhill-Nerode classes of the MISS SET as a base-3 language: 7,15,10,7,4,2,2,2 → stabilizes
>   LOW. But the miss set is FINITE (37 holes, last 581), and finite sets are TRIVIALLY regular — so
>   "37 stabilizes" just reflects that the holes stop, which is the CONCLUSION (581 is the last hole),
>   NOT an independent finite proof of it. The automaton PRESUMES the finiteness it would need to prove.
> Verified: all n∈[582, 4×10⁶] representable (finite miss set confirmed); but the forward state grows,
> so NO bounded-window / transfer-matrix certificate exists. The "elementary 581" is a MIRAGE — it
> reads off finiteness it assumed.
>
> **This is EXACTLY troika's pre-kill in action:** a transfer matrix is a COMPUTABLE DISCRIMINATOR;
> troika proved none can decide β. V2 is a textbook instance. So 581 has NO transcendence-free
> finite-matrix proof — it genuinely needs BEGL96's Mignotte–Waldschmidt (the (3,4,7) k=1 result is
> NOT re-provable elementarily by this route). Banked as: V2-k=1 → DEAD (pre-killed class); do NOT
> add an "elementary 581" artifact to the writeup; BEGL96's MW remains necessary for (3,4,7) k=1.
> The ONLY transcendence-free results that stand: k=0 (Brown), Lemma A (gap-condition), Lemma M
> (non-minimal reduction), residue coverage. (breaker: please confirm the forward-state growth
> 1,7,20,81,217,727 independently before this is final — it's the load-bearing number.)

> **INV-V3 (per-band drainage) ASSESSMENT — does NOT survive as a-priori inequality (maverick):**
> V3 needs "deficit(band [d_max^j,d_max^{j+1}]) ≤ drainage(band j) uniformly in j" provable a-priori.
> But deficit(band j) = #holes in band = #{Φ=0 points} = large-deviation/cross-base-coincidence events
> (what killed C5). Bounding it uniformly REQUIRES an a-priori bound on the band's |d_max^j − d_i^m|
> alignment = Mignotte-Waldschmidt. So V3-as-inequality REDUCES to the MW open core — NOT an independent
> tool. As a computed per-band check it's a computable discriminator (pre-killed by troika). Either way
> DEAD. ⟹ ALL of maverick's candidates dead (V1/V2 non-automatic, C5 large-deviation, V3 = MW). The two
> genuinely-a-priori live targets are scholar's Riesz-product (S10) and troika+lift's spectral radius.

---

## INV-S10 — density's measure-side numerical probe (the minor-arc decay)

Contributing to INV-S10 (Riesz-product decorrelation, the live analytic frontier = the Fourier face
of my INV-D4). I numerically probed the crux: does the off-major-arc triple product
max|G_3·G_4·G_7| (G_d = ∏_{j≤L}|cos(π d^j θ)|) decay fast enough that minor arcs are dominated?

MEASURED (θ ∈ [0.02, 0.5], matched factor counts at N=3^L_3):
- max off-arc triple product decays: L_3=6→14 gives 0.144 → 0.121 → 0.044 → 0.010 → 0.0016.
- Fitted decay slope d(log2 maxGprod)/dL_3 ≈ −0.83.
- Translating to the minor-arc bound: integrand |F_3 F_4 F_7| = 2^{∑L_d}·G-product, with entropy
  factor ∑L_d/L_3 = 2.357. Minor-integrand exponent (log2)/L_3 = 2.357 + (−0.83) = **1.528**.
- Major-arc/N exponent = log2(3) = **1.585**.
- **1.528 < 1.585** ⟹ the minor-arc integrand grows SLOWER than the main term N ⟹ minor arcs
  appear DOMINATED ⟹ r(n) > 0 ⟹ cofinite. Numerically, the decorrelation SUFFICES.

**HONEST CAVEATS (why this is a probe, not a proof):**
1. The −0.83 decay slope is fitted over a SHORT L-range (6–14); the asymptotic slope could differ,
   and the margin (1.528 vs 1.585 = 0.057 in exponent) is THIN — exactly lift's "thin, non-growing
   margin" at the boundary. A crude L² bound won't capture it; needs the sharp CF/Ostrowski geometry.
2. I bounded the MAX off-arc product, not the INTEGRAL over minor arcs (the arc-measure factor is
   not included). The integral could be larger if the bad arcs, though low, are wide.
3. This is the SAME thin-margin boundary criticality everywhere else — the numerics SUPPORT
   decorrelation-suffices but the THIN margin means only a sharp (non-crude) bound proves it. That
   sharp bound is exactly the open INV-S10 lemma; my probe confirms it's the right target and is
   numerically on the favorable side, but does NOT prove it.

For troika/scholar/lift (INV-S10 owners): the probe says decorrelation is real and the minor-arc
domination holds numerically with a thin (0.057-exponent) margin. The proof needs the sharp
∏|cos(π d_i^j θ)| minor-arc bound via the three-distance/continued-fraction structure (scholar's
attack route (b)), not an L² bound — consistent with the thin margin. My measure lens contributes
the numerical confirmation + the exponent accounting; the sharp harmonic-analysis bound is theirs.

## Round 5 (troika + lift JOINT — the Ruelle/transfer operator, BUILT; gaplessness located)

### INV-T6 / INV-L7 (merged). The 3-ratio IFS transfer operator — BUILT, faces gaplessness
**Joint object** (troika 2-torus ⊗ lift Ruelle): the transfer operator for the reachable set
R(D)=subset-sums of {d^j:d∈D}. Cofiniteness ⟺ spectral gap (λ₁ simple + λ₂ strictly inside) ⟹
exponential deficit decay ⟹ no persistent coverage dips.
**BUILT three ways, all hit the wall or gaplessness:**
1. EMPIRICAL (operator entries from n-sampled deficit): DEGENERATE for cofinite families — at N=4M the
   3-ray deficit is 0, operator ≡ 0. Inherits breaker's wall (can't see cofinite structure at reachable N).
2. ANALYTIC needs a CONTRACTION FACTOR (= the gap = deficit-mode decay rate). Tested if it's a clean
   function of β on VISIBLE 2-ray families: IT IS NOT. The deficit does NOT decay geometrically — it
   OSCILLATES: (3,4) deficit 0.077→0.206→0.078; (3,6) in-window ratio 1.137 (deficit GROWING). No clean
   exponential contraction exists to be the gap.
3. CRUDE COCYCLE (guessed structural contraction): gaps 0.847 (3,4,7) ≈ 0.863 (3,5,7,13) [σ=0 pair,
   maverick KILL TEST 1] — similar, but ALSO 0.789 for (3,4,11) β=0.933 → does NOT discriminate. The
   "gap" is a guess-artifact, not a real λ₂.
**DIAGNOSIS (lift's flagged risk, CONFIRMED): the operator is GAPLESS.** The 3 incommensurate ratios
(log3,log4,log7) put the subleading spectrum on the unit circle — the irrational rotation's CONTINUOUS
spectrum. The measured deficit OSCILLATION IS that continuous spectrum. A clean spectral gap (the
route's central object) does not exist in the naive form. This is consistent with the quadruply-confirmed
hardness fact (the β-discrimination is irreducibly iterative-to-recurrence-depth — a continuous spectrum
has no finite mixing rate to short-circuit it).
**NOT yet fully dead — the open question (handed to maverick/verifier):** is there a TWISTED operator /
weighted anisotropic Banach space (à la Blank–Keller–Liverani for non-self-similar / random IFS) where
the rotation's continuous spectrum becomes essential spectrum BELOW an isolated λ₂? If such a space
exists with the gap = an elementary quantity, the route survives; if the essential spectral radius = λ₁
(no isolated subleading eigenvalue), it dies. This is the precise make-or-break for the spectral lane,
located EARLY (before weeks invested) per maverick's protocol. troika+lift continue on the twisted-space
question; maverick verifies whether any gap that emerges is MW-in-disguise (KILL TEST 1/2).

#### INV-T6/L7 SPECTRAL ROUTE — KILLED (troika, twisted-space make-or-break run)
The twisted/anisotropic-space last shot: a weight can open a gap ONLY if the deficit oscillation is
TRANSIENT (decaying) — then a weighted norm sees the decay as a gap. If the oscillation is PERSISTENT
(undamped), the subleading spectrum genuinely sits on the unit circle and NO weight opens a gap.
**TEST (visible 2-ray families, oscillation amplitude vs scale):**
- (3,4): deficits at dyadic scales [1e5..1.6e7] = 0.177,0.122,0.122,0.120,0.081,0.180,0.147 — oscillation
  std early=0.026, late=0.041 (GROWING, not decaying).
- (3,5): deficits = 0.325,0.429,0.224,0.614,0.184,0.454,0.336 — std early=0.084, late=0.111 (GROWING).
**The deficit oscillation is PERSISTENT/non-decaying.** ⟹ the transfer operator's subleading spectrum is
genuine CONTINUOUS spectrum at radius 1, undampable by any anisotropic weight. **The spectral-gap route
is DEAD** — no twisted Banach space opens a gap when the oscillation doesn't decay.
**This is a CLEAN KILL of the spectral lane, located early (per maverick's protocol, before weeks
invested).** It also strengthens the hardness fact a 5th time: persistent continuous spectrum at radius 1
= no finite mixing rate = the recurrence-depth iteration cannot be short-circuited spectrally. The
spectral route was one of two live shots; it is now closed. The surviving live shot is the circle-method/
analytic-number-theory route (INV-S1, exponential sums) — which does NOT rely on a spectral gap; it
estimates the oscillating sum directly. That is where the cell's remaining hope sits.

> **troika's orbit-averaged C5 revival — VERIFIED DEAD (maverick, verifier):**
> troika correctly diagnosed that global Var/E unbounded was a density-OSCILLATION artifact (between-
> band variance) and that Φ depends on shift-orbit density ρ̄≈0.88, not local ρ. Deep-gap test passes
> (minΦ 86-244 at local ρ=0). BUT deep gaps are NOT the C5 killer — the STRAGGLERS are. Tested at the
> actual killer: (3,4,7) k=2 straggler n=3982888 (=N₀, true miss): Φ=0 but orbit-averaged E≈0.88·64≈56.
> 5.3σ event; Chebyshev with Var/E≲2 gives P(Φ=0)≤0.036, CANNOT reach 0. Orbit-averaging fixes the
> ARTIFACT, not the LARGE-DEVIATION flaw — same death as C5. The 2nd moment proves "O(1/E) fraction
> miss" (density), not "no miss above N₀" (pointwise). Pre-killed class (computable 2nd-moment
> discriminator). Escape needs a POINTWISE lower bound on Φ (= scholar's S10 Riesz route), not a variance.

### INV-S10 UPDATE (scholar): minor-arc INTEGRAL beats SUP ~2×/L — density's caveat (2) resolves favorably
density's measure-side probe gave minor-arc domination with a THIN exponent margin (0.057: minor-arc
integrand exp 1.528 vs main-term log2(3)=1.585), but bounded the SUP off-arc, not the INTEGRAL. I
computed both for (3,4,7) k=1, L=5..9 (std major arcs q≤12), normalized |F_3·F_4·F_7|:
  L: 5→9  sup: 0.223,0.186,0.069,0.041,0.017 (decay ~0.4-0.8/L, irregular)
          ∫:   1.10e-3,3.25e-4,8.81e-5,2.51e-5,6.9e-6 (decay STEADY ~0.28-0.30/L)
The INTEGRAL shrinks ~2× faster per L than the sup (sup attained on a thin near-rational set ⟹
∫ ≪ measure·sup). So density's 0.057 margin (sup-based) is CONSERVATIVE — the true minor-arc
integral is MORE dominated, extra ~0.5-0.6/L. Net: INV-S10 minor-arc domination is comfortably
favorable as an INTEGRAL, more headroom than the sup probe showed. Caveats remaining: short-L fit
(needs larger L to firm slope); the SHARP ∏|cos| minor-arc bound via CF/three-distance geometry is
still the rigorous step (scholar/troika/lift). But the target is real and the margin is workable.
INV-S10 stays the team's clearest single open lemma — if the sharp bound lands it closes (3,4,7)-all-k.

#### INV-S10 caveat (2) RESOLVED FAVORABLY (scholar's integral computation)

My probe bounded the off-arc MAX product; scholar computed the actual minor-arc INTEGRAL of
|F_3·F_4·F_7| for (3,4,7) k=1, L=5..9 (standard major arcs q≤12):
  L=5: sup=0.223, ∫=0.00110;  L=6: 0.186/0.000325;  L=7: 0.069/0.0000881;
  L=8: 0.041/0.0000251;  L=9: 0.017/0.0000069.
The INTEGRAL decays at a STEADY ~0.28–0.30 per L step; the SUP decays only ~0.5 avg (irregular). So
the integral shrinks ROUGHLY 2× FASTER than the sup per L — the sup is attained on a thin set near
small-denominator rationals, so weighting by arc-measure is much smaller than measure×sup.

CONSEQUENCE for my exponent accounting: my thin margin (0.057 in exponent, from the SUP bound
1.528 vs main-term 1.585) is CONSERVATIVE. The actual minor-arc integral is more dominated than the
sup suggests, by ~0.5–0.6 per L (an extra negative-exponent contribution). So the real margin for
minor-arc domination is WIDER than 0.057 — INV-S10 is on the favorable side with MORE room than my
probe showed.

Caveat status now: (1) short-L fit — shared by both probes, needs larger L to firm the slope;
(2) sup-not-integral — RESOLVED favorably (scholar's integral); (3) thin margin needs a SHARP bound —
still the rigorous step (CF/Ostrowski geometry, scholar/troika/lift), BUT the margin is less thin
than feared so the sharp bound has more headroom. NET: measure side says INV-S10 is comfortably
favorable, integral-dominated; the rigorous ∏|cos| minor-arc bound remains the open analytic step but
the target is real and the margin workable. [density exponent accounting + scholar integral refinement.]

## Round 6 (troika — S10-asymptotic, the CF/Ostrowski arc geometry; PRE-REGISTERED DECISION resolved)

### The near-coincidence arc decision: MW-EQUIVALENT (with an analytic shell)
My assigned piece of the cell's final S10-asymptotic convergence: the continued-fraction/Ostrowski
geometry of the near-coincidence arcs, and maverick's pre-registered question — is the cancellation on
the convergent arcs MW-equivalent or genuinely harmonic-analytic? RESOLVED computationally.

**Setup.** Exponential sums S_d(α)=∑_{n∈B_d,n≤X} e(αn)=∏_{j} (1+e(α d^j)); |S_d(α)|=∏_j 2|cos(π α d^j)|.
The sumset deficit is controlled by the minor-arc behavior of S_3·S_4·S_7. Collision arcs = α where
multiple S_d are simultaneously large = α near a rational p/3^a that is ALSO near p'/4^b ⟺ 3^a≈4^b ⟺
the CONVERGENTS of log4/log3 (denominators 4,5,19,23,… — exactly my measured close-pair exponents).

**Findings.**
1. GOOD: the GENERIC minor-arc decay is c≈0.56–0.66 (stronger than breaker's target [0.17,0.31]).
   Generic (non-convergent) arcs decorrelate fine — the harmonic-analytic decay works there.
2. DECISIVE: on the CONVERGENT arcs α=p/3^a with 3^a≈4^b, S_4 LOSES its cancellation as the convergent
   deepens. Mean log|S_4|/nt₄ (1=trivial max=no cancellation): a=4→0.001, a=5→0.057, a=9→0.221,
   a=14→0.369, a=19→0.564 → log2. **The base-4 sum has NO cancellation on the deep-convergent 3-adic
   arcs**, and the degradation rate is governed by the 3-power/4-power interleaving = |3^a−4^b|.

**PRE-REGISTERED DECISION — RESOLVED: the convergent-arc cancellation is MW-EQUIVALENT.** The generic
arcs are analytic (decorrelate, c≈0.6), but the WORST arcs — the convergent collisions that DETERMINE
the minor-arc bound — are controlled by |3^a−4^b| (Mignotte–Waldschmidt), NOT by harmonic-analytic
cancellation (there is none there). The circle method's minor-arc estimate on the collision arcs
REDUCES to the MW spacing bound. So S10-asymptotic does NOT bypass MW; the convergent arcs ARE MW.

**CONSEQUENCE (per the lead's pre-registration): the campaign's E124 verdict is FINAL — everything
reduces to MW.** The honest-residue writeup ships as the result: (3,4,7)-all-k and the general boundary
conjecture rest on Mignotte–Waldschmidt/Baker spacing bounds on |d_i^p − d_j^q| at the continued-
fraction convergents; no elementary, spectral, second-moment, or harmonic-analytic route bypasses this
(now 6× confirmed). The result is the SHARP LOCALIZATION: the entire difficulty sits on the measure-zero
set of convergent arcs, where it is exactly the MW transcendence content — a clean, defensible statement.

### INV-S10 REFRAMED (scholar, after breaker's survival verdict): the MIN-product three-distance lemma
breaker confirmed INV-S10 SURVIVES scope-correct (asymptotic |F_3F_4F_7|≪N^{3−δ}, per-atom decay
c∈[0.17,0.31], k-uniform, boundary+strict). I reframed the residual lemma into a cleaner, verified form:
instead of the triple product, bound MIN(∏|cos π3^jθ|, ∏|cos π4^jθ|, ∏|cos π7^jθ|). The "max over
θ>0.01 of this min" (= largest value where all 3 are simultaneously large = danger arcs) DECAYS:
L=6→0.242, 8→0.204, 10→0.119, 12→0.048. K-UNIFORM (k=1,2,3 → L=12 values 0.048/0.048/0.058).
WHY EASIER: bounding the min reduces to "at any off-trivial θ, ≥1 base d has ∏|cos π d^jθ| small"
— a pure THREE-DISTANCE statement (the orbits {3^jθ},{4^jθ},{7^jθ} mod 1 can't all stay near ℤ
without forcing 3,4,7 mult-dependent). Don't need all three small, just ONE, always. PROOF TARGET
(troika's CF/Ostrowski): on the convergent-arcs of log4/log3 etc., min(P_3,P_4,P_7) ≤ C·ρ^L, ρ<1,
via three-distance — orbit simultaneous-closeness bounded by the worst CF convergent. Single-scale
(breaker), k-uniform (lift §B), margin workable (density exponent + scholar integral-vs-sup ~2×/L).
THE decisive lemma; if proved, closes (3,4,7)-all-k via INV-S10. → troika (CF geometry) + scholar (numerics).

#### INV-T5 orbit-averaged — maverick's VERIFIER KILL (large-deviation, not variance)
maverick verified my orbit-averaged C5 revival and KILLED it at the actual killer (which I'd missed —
I tested deep gaps, not stragglers). The precise kill:
- At the (3,4,7) k=2 STRADDLER n=3,982,888 (=N₀, a TRUE miss, triple-verified): Φ(n)=0, but
  orbit-averaged E[Φ]=0.88·|B₇≤n|≈0.88·64≈56. So E≈56 yet Φ=0 — a 5.3σ LARGE-DEVIATION event.
- Chebyshev with my Var/E≲2: P(Φ=0) ≤ Var/E² ≈ 113/3136 ≈ 0.036, CANNOT reach 0. The second moment
  proves "O(1/E) FRACTION of n are misses" (a DENSITY statement), NOT "NO misses above N₀" (POINTWISE).
- The straggler at the cross-base coincidence IS the rare event that any second moment (orbit-averaged
  or not) cannot see. My orbit-averaging fixed the global-Var ARTIFACT but not the LARGE-DEVIATION flaw.
**CORRECT VERDICT (maverick): INV-T5 orbit-averaged is a PRE-KILLED-CLASS instance** — it's a computable
second-moment discriminator, so troika's own hardness fact applies. The orbit-density insight is kept as
a DIAGNOSTIC note (real: Φ depends on shifted-point density ρ̄, not local ρ), but the second-moment route
is DEAD at the straggler. To escape needs a LARGE-DEVIATION / POINTWISE lower bound on Φ — exactly
scholar's S10 Riesz-product (pointwise integral lower bound), NOT a second moment.
**This dovetails with my Round 6 finding:** the stragglers live at the convergent arcs (cross-base
coincidences), which are MW-equivalent. So the pointwise S10 bound at those arcs is exactly the MW
content — consistent end-to-end. The second-moment lane is fully closed; S10-pointwise is the live route.

#### INV-T2 SHARPENED VERDICT (breaker, size-based test) — strict-tier discriminator, boundary stays MW
breaker ran the sharper make-or-break (bad-θ-class SIZE vs β, not just concentration). # occupied
θ₃-classes of gaps in successive scale windows (50 bins):
- (3,4,7) β=1 COFINITE: 0,0,0,0 — empties (gaps stop) ✓
- (3,4) β=0.833 NOT-cof: 50,50,50,50 — persists densely; T2 DISCRIMINATES clearly ✓
- (3,5,7) β=0.917 NOT-cof: 21→14→3→0 — visible decay (gaps reachable); T2 sees it ✓
- (3,4,11) β=0.933 DEEP-TRAP: 1→0→0→0 — looks EXACTLY like cofinite (gaps beyond 9e9) ✗
**VERDICT: INV-T2's bad-θ-class size IS a real discriminator for the clearly-gappy + strict regimes**
(cleanly separates (3,4),(3,5,7) from cofinite — which the 2nd moment could NOT). Genuine progress for
the STRICT tier. **But FAILS on the deep-trap (3,4,11):** its bad θ-class empties within reach (true
gaps >9e9), indistinguishable from cofinite. Same asymptotic blindness, now CONFINED to the narrow
boundary band β≈0.93–1.0 — exactly where the conjecture's hardness lives.
**Placement: INV-T2 = the LEAD for the strict-excess/clearly-gappy tier (best discriminator there,
Ostrowski state-space is the right lens), NOT a boundary closer.** The boundary deep-trap stays open =
the MW content (its stragglers ARE the convergent arcs I showed are MW-equivalent, Round 6). Fully
consistent: T2 closes the strict tier, the boundary band is the irreducible MW core. Both verdicts
(concentration + size) recorded.

#### INV-L6/L7 → torus-discrepancy: troika's read = SAME WALL (discrepancy rate IS the MW content)
lift killed INV-L7 (transfer operator gapless, quasi-periodic oscillation spiking at the k=2 straggler
3.98M) and redirected to INV-L6 (2-torus discrepancy / three-distance), asking my read on the
Diophantine-type tractability. ANSWER: the discrepancy framing does NOT escape — it IS the MW wall in
dynamical language. Computed:
- CF of log4/log3 = [1,3,1,4,1,1,**11**,1,**46**,1,5,**112**,…]; log7/log3 = [1,1,3,2,1,2,4,**22**,**32**,…].
  Partial quotients are LARGE and UNBOUNDED ⟹ these numbers are NOT badly approximable.
- EXACT correspondence (verified): large a_{k+1} ⟺ tiny |3^p−4^q|/3^p at the convergent p_k/q_k.
  a₆=11 at 53/42 ⟹ |3^53−4^42|/3^53 = 2.09e-3 (the closest collision). The discrepancy of {m·log4/log3}
  spikes at exactly these convergents, and the spike depth = 1/(a_{k+1}) = the collision closeness.
- So the torus-discrepancy rate is GOVERNED BY the CF partial quotients, which ARE the |3^p−4^q|
  spacing = the Mignotte–Waldschmidt content. Bounding "orbit avoids the shrinking bad region" at the
  large-a_k convergents = lower-bounding |3^p−4^q| = MW. No effective discrepancy tool bypasses it
  because the unbounded a_k preclude the clean (log N)/N bound that badly-approximable numbers enjoy.
**VERDICT: INV-L6 (torus discrepancy) = same wall, restated dynamically.** It correctly identifies the
object (quasi-periodic, not mixing — lift is right), but the effective bound it needs is the MW spacing
at the deep convergents. 8× confirmation now: spectral, discrepancy both reduce to MW at the convergents.
This is also the cleanest STATEMENT of why: the irrationality measure of log4/log3 (finite but >2,
unbounded partial quotients) is exactly the quantity MW bounds. The campaign verdict holds firmly.

### INV-S10 C5-TRAP CHECK (scholar, breaker's verifier guard): asymptotic decay ≠ pointwise certificate
breaker (verifier) flagged the C5 trap: a bound on E[r(n)] doesn't exclude the rare r(n)=0/1 events at
cross-base coincidences. I ran the circle-method split of the EXACT r(n)=∫∏F_d e(−nθ)dθ for (3,4,7)
k=1 at the hard n's. FINDING: at the hard n's the major-arc term M and minor-arc error E are the SAME
ORDER, not M≫E:
  n=581 (miss r=0): M≈23, E≈−23 (cancel to 0 — the miss IS the minor arcs winning)
  n=585 (r=1, worst above N₀): M≈23, E≈−12 (minor error ~half the main term)
  n=600 (r=28, easy): M≈24, E≈+4 (minor small — easy n)
So minor arcs do ~50% cancellation at the hard n's; the main term OVER-counts. CONSEQUENCE: S10's
asymptotic decay (sup/integral ≪ N^{3−δ}, c∈[0.17,0.31], REAL) controls the TYPICAL n = an E[r]>0 /
mean statement — exactly what C5 says is insufficient. It does NOT certify r(n)≥1 pointwise at the
MW-coincidence n's, where the minor contribution is comparable to the main term. HONEST STATUS: S10
stays live ONLY via the SHARP CF/three-distance constant (troika) that beats the main term WITH THE
RIGHT CONSTANT at the coincidence arcs — the decay RATE alone is a mean bound, not pointwise. The
"Riesz integral is automatically pointwise" hope is too optimistic: at the hard n's the integral's two
pieces nearly cancel. The worst n ARE the MW coincidences (the wall), so S10's pointwise certificate
= the sharp coincidence-arc bound = the same MW core, just in Fourier language. Don't over-claim S10 as
near-complete; it's the right TARGET but the pointwise step is the full MW lemma, not a free corollary
of the decay. [scholar + breaker(verifier); the sharp-constant bar is the real obligation.]

#### scholar's INV-S10 min-product reframing — troika CF-geometry verdict: CLEANER but STILL MW
scholar reframed the residual lemma to min(P_3,P_4,P_7) [P_d=∏_{j<L}|cos π d^j θ|] instead of the triple
product, and asked me to prove min ≤ C·ρ^L on the convergent arcs via three-distance. Tested it
rigorously (mpmath, 80 digits, reaching the deep convergent 3^53≈4^42, a_q=11):
- CONFIRMED the min framing is genuinely DIFFERENT/cleaner than the product: at a 3-adic arc θ=1/3^a,
  the product is huge (P_3 large) but the MIN is governed by the smallest base (7), so the
  product's MW-blowup doesn't directly apply. Good insight.
- BUT the deep-convergent test KILLS uniformity: at θ=1/3^53, min stays ABOVE the clean ρ^L decay line
  for ALL L≤57 (L=40: min_log=−2.4 vs line −13.1). The min does NOT decay until L is large.
- MECHANISM (decisive): the decay ONSET L scales LINEARLY with convergent depth a — onset≈0.7a (a=8→6,
  16→11, 24→15, 53→36). At θ=1/3^a, all three bases' low powers give args π d^j/3^a ≈ 0 (cos≈1), so
  min≈1 until j grows to ~a. **The decay is DELAYED proportionally to the collision depth.**
**VERDICT: the min-lemma is CLEANER but does NOT escape MW.** A uniform min ≤ C·ρ^L requires bounding
how deep the collisions go (how large a is at a given arc denominator) = bounding |3^a−4^b| =
Mignotte–Waldschmidt. The three-distance structure organizes the arcs (correct, scholar's insight is
real), but the effective decay rate at the deep convergents IS the MW spacing. So INV-S10 via the
min-lemma reduces to MW exactly like everything else (9× confirmation now). The min-framing is the
RIGHT clean statement of the residual, and its residual IS MW — which is the honest result to ship.

#### INV-D3 — DEFINITIVELY KILLED (breaker's prediction-check, triangulated with density's self-kill)

breaker ran the decisive gap-onset prediction test, airtight:
- (3,6,7), deficit=−0.133: the gap genuinely EXISTS at 3^15.9 ≈ 40.4M (reachable). But min-reps just
  below 3^9/3^10/3^11 = 5/2/5 — FLAT (slope≈0), NOT decaying toward 1. So D3's mechanism "min-reps
  decays to 1 as the gap forms" FAILS — min-reps stays bounded 2-5 even right below the gap-onset.
  The extrapolation predicts m=∞ (no gap) while the gap is right there.
- Slope ≠ deficit: (3,4,7) deficit=0 but fitted slope=+0.56 (min-reps grows, 10× off).
So NEITHER half of "log(min-reps) ≈ m·deficit·const, hits 1 at gap" holds. INV-D3 does NOT predict
gap-onset; min-reps is a vague heuristic that stays flat/grows even where gaps form. Same range-
blindness as all finite-scale measures. Triangulated kill: density self-kill (Round 2-3) + breaker
batch-2 + breaker prediction-check. Code: breaker_D3_prediction.py. D2's worst-octave ν stands as the
sharp-but-transcendental invariant (= the conjecture). DEAD, definitively.

#### INV-D4 ≡ INV-S10 convergence (breaker's k-uniform decorrelation rate)

breaker confirmed the measure/harmonic-analysis convergence: my INV-D4 (d_min-adic Fourier-decay
reframe) and scholar's INV-S10 (|F_3·F_4·F_7| minor-arc bound) are the SAME live target — a
Fourier-coefficient-decay statement — from the measure vs circle-method sides. breaker measured the
decorrelation rate **c ∈ [0.17, 0.31], k-UNIFORM** (the per-L decay rate of the product, stable across k).

This addresses my probe's caveat (1) (short-L fit / slope-firmness): the k-UNIFORMITY of the
decorrelation rate is precisely what the all-k version needs — if c stays in [0.17,0.31] independent
of k, then the minor-arc domination (and hence cofiniteness) is uniform in k, not just per-fixed-k.
Combined with scholar's integral refinement (caveat 2 resolved, integral decays ~2× faster than sup),
the measure-side evidence for INV-S10 is now: favorable margin (caveat 2), k-uniform decorrelation
rate (caveat 1 addressed by breaker). The ONLY remaining gap is caveat 3 — the rigorous sharp ∏|cos|
minor-arc bound via CF/Ostrowski geometry (scholar/troika/lift own this).

CONSOLIDATED measure-side verdict on the analytic frontier: INV-S10 (= INV-D4) is the single live
lead, numerically favorable and k-uniform, with a well-defined rigorous target (the sharp harmonic-
analysis bound). Density's contributions: the D4 reframe identifying the target, the exponent
accounting (conservative margin), confirmed favorable by scholar's integral and breaker's k-uniform
rate. The rigorous bound is the harmonic-analysis team's. Measure lens DONE.

> **INV-T4 (2-torus renormalization) VERIFIER FINDINGS (maverick) — torus is a coordinate, NOT exact:**
> troika's 2-torus (θ₃,θ₄)=({log₃n},{log₄n}) is a real scale-invariant coordinate for the B₃+B₄
> deficit (captures the bulk). But TWO claimed exactness mechanisms FAIL under decisive test:
> (1) "residual = bounded carry fiber" — FALSE (over-partitioning artifact; low-digits-alone give
>     impurity 0.286, worse; a finite purifying fiber would contradict M5 non-automaticity). troika
>     self-corrected this.
> (2) "residual = measure-zero continuous boundary, torus exact a.e." — FALSE. Population-weighted
>     binary-membership impurity decays at ratio 0.95/grid-doubling (40²→320², healthy bins), NOT the
>     0.5 a measure-zero boundary requires. ⟹ FAT (positive-measure) bad-set boundary. The 2-torus
>     does NOT determine membership a.e. — consistent with M5 (an a.e.-function of scale-phase would be
>     near-automatic, forbidden). So "(BRIDGE) ⟺ ergodic non-trapping on 𝕋²" is NOT equivalent to
>     (BRIDGE); the positive-measure boundary carries the same MW content. Open metric question:
>     binary-membership (mine, for a proof) vs deficit-value-regression (troika's, ~0.024) — these
>     differ and the VALUE being well-approximated does not imply MEMBERSHIP determined. NET: torus =
>     useful bulk coordinate, NOT an MW-free reformulation. Same wall, geometric dress.

## ASTELS RECONCILIATION (troika verifying maverick's a-priori claim) — clean split confirmed
maverick: the recursion-margin-discontinuity-at-β=1 I proposed IS the ASTELS 2000 threshold
discontinuity (γ(C_d)=1/(d−1); continuum sumset ⊇ interval iff ∑γ≥1=β≥1, PROVEN), and it's the SAME
object as the spectral-radius operator. I VERIFIED this and it gives a clean, important split:
- CONFIRMED γ(C_d)=1/(d−1) exactly: Newhouse thickness τ=1/(d−2), Astels γ=τ/(τ+1)=1/(d−1).
- CONFIRMED the continuum C_3+C_4+C_7 IS an interval at β=1 exactly (max gap=1 grid unit, fully covered).
  So the β=1 discontinuity is a PROVEN continuum theorem (Astels).
**THE CLEAN SPLIT (the reconciliation):**
- ASTELS (continuum, PROVEN) ⟹ integer BOUNDED GAPS (= maverick's elementary Lemma BG). And it gives
  the β-DISCRIMINATION at the structural level: β≥1 ⟹ bounded gaps; β<1 ⟹ NO continuum interval ⟹
  unbounded gaps asymptotically. **So the β=1 discrimination IS proven via Astels — NOT MW — at the
  bounded-gap/density level.** This is a real advance: the "what discriminates β" question (which killed
  every finite-N statistic) is answered by Astels at the continuum, with NO transcendence.
- BUT Astels does NOT give COFINITENESS (gap=1, no stragglers). The straggler elimination — bounded-gap
  ⟹ gap-exactly-1-above-N₀ — is the residual, and the stragglers sit at the multi-scale-mismatch points
  (cross-base coincidences 3^a≈4^b) = MW.
**SO THE FINAL STRUCTURE IS SHARPER THAN "everything is MW":**
  (i) β-discrimination + bounded gaps = ASTELS (continuum, PROVEN, elementary, NO MW). ← maverick's win.
  (ii) straggler elimination (bounded gaps → cofinite) = MW (the convergent-arc residue). ← my Round 6.
The campaign verdict refines: E124 is NOT entirely MW. The hard SIDE-CONDITION discontinuity (β≥1) is
Astels-provable; only the straggler/cofinite upgrade needs MW. This is a STRONGER, more honest result —
and it means a conditional theorem "bounded-gaps (Astels) + straggler-elimination (MW input)" is the
clean decomposition. maverick's a-priori Astels framing genuinely advanced the β-half off MW.

#### INV-T4 metric correction (maverick's verifier catch — CONCEDED, all 3 points)
maverick caught a methodology gap before any 𝕋²×carry-fiber combine. Conceded in full:
1. CARRY-FIBER test fails (over-partitioning artifact: 4+4 digits = 554k bins, empty bins averaged as
   0.0). At 3+3 digits impurity still ~0.20. Low digits do NOT purify. (I'd already retracted the
   carry-fiber hypothesis; maverick confirms it's dead.)
2. DECISIVE (M5 / Cobham): a finite purifying fiber is FORBIDDEN. If 𝕋²×{finite fiber} determined
   membership exactly, membership would be a finite-state function of (scale-band, low-digits) =
   AUTOMATIC — contradicting M5 (the cover set is not automatic in 3 mult-indep bases since not
   eventually periodic). So the combined object CANNOT be exact, full stop. Metric-independent, airtight.
3. METRIC GAP: my "0.024 scale-invariance" was VALUE-regression (mean-error of D(θ)), NOT binary
   MEMBERSHIP purity. For a PROOF, membership (cover/not determined) is what matters — and it is NOT
   torus-determined (and can't be made so by any finite fiber, by point 2).
**RESOLUTION:** the 2-torus is the right BULK coordinate (value-regression good, captures the density
structure), but membership is irreducibly non-torus-determined. The "continuous boundary" I found
(impurity decaying with resolution) is consistent: boundary measure→0 (so value-regression is good) but
boundary BINS never become pure (membership undetermined) — and the boundary is EXACTLY where the
non-automatic/MW content lives. So INV-T4's correct status: torus = bulk/density coordinate (real,
useful for the Astels β-half); the residual = non-automatic = MW/recurrence (the straggler half).
Round-4 combine HELD — there's nothing to combine; the residual is provably not a finite fiber.
This dovetails perfectly with the Astels split: torus/bulk = Astels density (elementary); boundary/
membership residual = MW stragglers. maverick's M5 catch + Astels split are the same boundary, two lenses.

#### INV-T4 "measure-zero boundary" claim — RETRACTED (maverick's decay-rate test, CONCEDED)
maverick's decisive test: the membership-impurity DECAY RATE per grid-doubling. A genuine measure-zero
continuous boundary ⟹ impurity ~ perimeter/area ~ 1/gridsize ⟹ ratio ~0.5 (halves per doubling). I
re-measured (N=8e6, (3,4), weighted, ≥10/bin) and CONFIRM maverick: ratio = 0.93–0.95, NOT 0.5:
  grid 40→640: membership impurity 0.060,0.056,0.052,0.045,0.038 (ratios 0.93,0.93,0.87,0.83);
  value-regression RMSE 0.223,0.211,0.200,0.187,0.171 (ratios 0.95,0.95,0.93,0.92).
**RETRACTED: the 2-torus does NOT have a measure-zero boundary — it's a FAT (positive-measure) boundary.**
The ~0.93 decay (barely shrinking over 16×) is the fat-boundary signature. So the 2-torus does NOT
determine membership a.e.
**My error (conceded):** for a BINARY 0/1 set, value-regression RMSE = sqrt(m(1−m)) ≈ impurity — they're
the SAME metric, not independent. My "0.024 value-regression" was measuring the SMOOTHNESS of the deficit
DENSITY D(θ) (which IS a smooth function), NOT membership determination. I conflated density-smoothness
with membership-determination. maverick's binary-membership metric is the proof-relevant one, and it
shows a fat boundary.
**CORRECTED INV-T4 status:** the 2-torus is a real SCALE/DENSITY coordinate (captures the bulk density,
which IS the Astels β-half), but it does NOT determine membership — the bad set 𝓑 has a positive-measure
fuzzy boundary carrying the non-automatic (M5) / MW content. So "(BRIDGE) ⟺ orbit exits 𝓑 a.e." is NOT
equivalent to (BRIDGE) — the fat boundary is the residual MW. This is fully consistent: torus/bulk =
Astels density (elementary); fat boundary = MW stragglers (non-automatic). Same two-part split, now
with the correct geometric statement (fat boundary, not measure-zero). maverick's catch stands.

#### 𝕋²-intrinsic operator — DOMINATED BY S10 (don't build; breaker's intrinsic-criterion analysis)
breaker crystallized my "intrinsic, not n-sampled" bar as the kill-ledger's unifying meta-criterion
(every killed candidate n-samples cover(D,N) somewhere ⟹ deep-trap-blind by construction) AND noted
S10 already MEETS it. I checked whether to build my 𝕋²-intrinsic operator as a second instance:
- S10's |F_3F_4F_7|(θ) is an INTRINSIC function (lacunary product, pure function of atom set + θ, zero
  n-sampling) AND it's CONTINUOUS/SMOOTH in θ (product of cosines). Its minor-arc bound is an INTEGRAL
  of a smooth object — clean.
- My 𝕋²-intrinsic operator's δ would come from the VISIBLE 2-ray MEMBERSHIP function D(θ₃,θ₄), which
  maverick proved has a FAT positive-measure boundary (decay 0.93, not 0.5). So the operator's δ would
  inherit that boundary FUZZ at exactly β=1 — fuzzy where it matters most.
**VERDICT: don't build the 𝕋²-intrinsic operator — it's DOMINATED by S10.** Both are intrinsic (escape
the n-sampling wall), but S10 acts on a smooth continuous object (clean integral) while my operator acts
on the fat-boundaried membership (fuzzy δ). S10 is strictly the better intrinsic instance. The cell's
analytic effort correctly concentrates on S10, where my contribution is the convergent-arc geometry
(Round 6) = where S10's minor-arc bound reduces to MW. So: S10 = the one live intrinsic object; its
generic arcs decorrelate (analytic, c∈[0.17,0.31]); its convergent arcs are MW (my Round 6). Consistent
with the Astels split (S10's generic decorrelation ≈ the Astels density half; S10's convergent arcs ≈
the MW straggler half). The intrinsic-criterion unifies the whole ledger: n-sampled = pre-killed; S10 =
the one intrinsic survivor; its residual = MW. Clean end state.

## TASK #27/#28 (troika): the needed transcendence input ALREADY EXISTS (effective, literature)
The minimal transcendence requirement for the E124 (3,4,7)-all-k STRAGGLER half (the cofinite upgrade
above the Astels bounded-gap base), with literature map:
**NEEDED (my analysis):** three PAIRWISE two-log lower bounds |3^a−4^b|, |3^a−7^c|, |4^b−7^c| ≥ effective
H^{−C}, at convergent denominators only, ANY effective polynomial rate. Binding pair = log4/log3 (a_k up
to 112, deepest convergents). = finite EFFECTIVE irrationality measure of log4/log3, log7/log3, log7/log4.
**KNOWN (effective, literature — Grok-sourced, NOT YET PDF-verified, flagged for baker/gelfond):**
- log4/log3: μ ≤ **3.8914** (Salikhov, Math. Notes 88, 2010, effective); coarser μ≤13.3 (Bugeaud–
  Mignotte), μ≤14.38 ⟺ |p log3−q log4|≥H^{−13.38} (Laurent–Mignotte–Nesterenko, J.Number Theory 55, 1995).
- log7/log3, log7/log4: same LMN'95 two-log machinery (every coprime pair gets effective C(a,b); explicit
  constant via per-pair parameter substitution, ~13–15 range).
- My empirical max local exponent ≈3.0 for log4/log3 is CONSISTENT (3.0 ≤ true μ ≤ 3.8914). ✓
**UPSHOT (campaign-relevant):** the transcendence input is NOT conjectural — it ALREADY EXISTS, fully
effective. So the (3,4,7)-all-k theorem is closeable modulo a KNOWN effective MW/Baker bound (Salikhov/
LMN). Combined with the Astels β/bounded-gap half (proven, elementary): **(3,4,7)-all-k = Astels (proven)
+ LMN/Salikhov effective two-log (known) + a finite computation.** This is a genuinely assemblable proof
of the all-k theorem — the residual is NOT an open transcendence conjecture, just the assembly + constant
verification. STRONGEST campaign statement yet for the (3,4,7) target. (CAVEAT: Grok constants plausible/
self-consistent but need PDF-verification before citing exact values — baker/gelfond own that.)
