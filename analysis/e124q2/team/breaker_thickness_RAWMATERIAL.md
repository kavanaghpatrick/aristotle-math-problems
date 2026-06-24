# breaker: RAW MATERIAL for the discrete-Astels / thickness assault

Artillery support for maverick/cassels/density/scholar. All COMPUTED, validated atom-sieve engine
(`breaker_atom_sieve.py`, exact to 9e9). Ground-truth test set built (admissible vs sub-threshold).

## 1. Single-base B_d gap/bridge structure (EXACT, self-similar)
B_d = 0/1-digit base-d numbers. S(d,k)=d^k·B_d (scaling), so structure is k-invariant up to dilation.
- Just below d^m: largest 0/1 value = all-ones = (d^m−1)/(d−1). Gap to d^m = d^m − (d^m−1)/(d−1).
- **gap / allones → (d−2) EXACTLY.** (d=3:1, d=4:2, d=5:3, d=7:5, d=11:9.)
- **Max contiguous BRIDGE in a single B_d = 2** (consecutive 0/1 numbers, e.g. {0,1},{d,d+1}). For ALL d.
- So single B_d is a thin Cantor-like set: bridges length ≤2, gaps up to ~d^m. Newhouse thickness ≈ 0.
- The two governing constants are DIFFERENT: thinness/gap-ratio ~ (d−2); admissibility mass ~ 1/(d−1).

## 2. Sumset thickness emerges from COMBINING bases (the Astels mechanism), COMPUTED
Max-bridge grows as bases are added (N=10M, k=0):
  (3,)        β=0.500  max_gap=2391484  max_bridge=2        not cofinite
  (3,4)       β=0.833  max_gap=404718   max_bridge=225325   not cofinite
  (3,4,7)     β=1.000  max_gap=0        max_bridge=interval COFINITE
Single thin sets (bridge 2) sum to an interval once enough mass accumulates — exactly Astels: sumset
of Cantor sets contains an interval when ∑ thickness-contributions cross a threshold.

## 3. ★ THE HARD CONSTRAINT a correct discrete-thickness definition MUST satisfy ★
At finite N the global gap/bridge structure CANNOT separate cofinite from not:
  (3,4,7)  β=1.000 : max_gap=0 at N=10M  (truly cofinite)
  (3,4,11) β=0.933 : max_gap=0 at N=10M  (NOT cofinite — first exception >9e9, deep trap)
They look IDENTICAL empirically up to 10M (and (3,4,11) stays clean to 9e9).
⟹ A valid discrete-thickness invariant must be a LOCAL, SCALE-INVARIANT quantity derived from the
   ATOM structure {d^j}, computable in closed form — NOT an empirical max-gap/max-bridge measurement,
   which the deep trap fools. The invariant must evaluate to "≥ threshold" for (3,4,7) and
   "< threshold" for (3,4,11), matching β≥1 exactly.

## 4. GROUND-TRUTH TEST SET (for killing wrong definitions fast)
COFINITE (admissible, β≥1): (3,4,7) β=1, (3,4,5) β=1.083, (3,5,7,13) β=1, (3,4,11,16) β=1, all 21
  knife-edge sum=1 families, all 45 small families with β≥1.
NOT COFINITE (β<1) but look cofinite to large N (the discriminating hard cases):
  (3,4,11) β=0.9333 — clean to 9e9
  (3,4,10) β=0.9444 — clean to 200M
  (3,4,12) β=0.9242 — clean to 200M
  (3,5,7)  β=0.9167 — clean to 200M
NOT COFINITE, visibly (easy negatives): (3,4) β=0.833, (3,5) β=0.75, (3,4,9) β=0.958 (misses at 59048),
  (3,4,13) β=0.9167 (misses to 56.8M).
A candidate thickness τ(D) is CORRECT iff: τ(D) ≥ τ_crit ⟺ β(D) ≥ 1, on ALL the above. I can test any
proposed τ against this set in minutes.

## 5. Standing offer to attackers
Send me a candidate discrete-thickness formula τ(D) (or τ of the atom set). I compute it on the
ground-truth set and report PASS/FAIL within minutes, with the exact family that breaks it if it fails.

## 6. PRE-TESTED candidate thickness definitions (computed vs ground truth)
| candidate τ(D), crit=1 | separates cofinite/not? | verdict |
|---|---|---|
| harmonic β = Σ 1/(d−1) | YES (min cof 1.000 > max not-cof 0.958) | **CORRECT** (= Pomerance) |
| naive Astels Σ 1/(d−2) | NO — (3,4) [not cof] τ=1.5 beats many cofinite | WRONG (over-counts) |
| box-dim Σ log2/log d | NO — 355 false positives for d<20,r≤4 | WRONG (maverick confirmed) |

**The verified constraint for the discrete-Astels theorem**: the only normalization that reproduces
the cofiniteness boundary is τ_d = 1/(d−1) (each B_d contributes 1/(d−1), threshold Σ ≥ 1). NOT the
Hausdorff/box dimension (log2/log d), NOT the naive gap-thickness 1/(d−2). Box-dim counterexample:
(4,5,6,7) has box-dim 1.674 (above the min cofinite box-dim 1.487) but β=0.95<1 ⟹ NOT cofinite.
So a discrete-Astels "thickness" must be defined so that single B_d has thickness 1/(d−1) — i.e. it
must be the MEASURE/density contribution (Pomerance reach = 1/(d−1) per density's ledger), not a
dimension. This pins the metric for the thickness theorem. Code: breaker_thickness_candidates.py,
breaker_boxdim_check.py.

### 6b. RIGOROUS DERIVATION (maverick's γ, breaker-verified): WHY 1/(d−1), not 1/(d−2)
The renormalized ray d^k·B_d is the digit-Cantor set C_d. Two thickness constants, both real:
- **Newhouse thickness** τ_N(C_d) = 1/(d−2) — the raw bridge/gap ratio (my §1 gap-structure constant).
- **Astels NORMALIZED thickness** γ(C_d) = τ_N/(1+τ_N) = (1/(d−2))/((d−1)/(d−2)) = **1/(d−1)**.
Astels' theorem (Trans. AMS 2000) is ADDITIVE in the NORMALIZED thickness: ∑_i γ(C_i) ≥ 1 ⟹ the
sumset C_{d_1}+…+C_{d_r} contains an interval. So the right invariant is
  **τ(D) := ∑_{d∈D} γ(C_d) = ∑_{d∈D} 1/(d−1)**,  τ_crit = 1.
This is EXACTLY BEGL96's admissibility condition — explaining why ∑1/(d−1)≥1 is the threshold: it is
Astels' sum-of-normalized-thicknesses ≥ 1. The (d−2) is the raw gap-ratio; the 1/(d−1) is the
normalized/additive thickness that actually drives interval-formation. (breaker-verified: γ=τ_N/(1+τ_N)
= 1/(d−1) exactly for d=3..11; full gauntlet τ(D)≥1 ⟺ cofinite passes on all 17 families including the
4 deceptive sub-threshold ones — immune to deep-trap empirical-appearance since τ is a function of D only.)
**HONEST SCOPE (the caveat that matters):** τ(D)=β, so "τ≥1 ⟺ cofinite" restates Pomerance BY
CONSTRUCTION — it is the correct discrete-thickness DEFINITION/predicate (passes the test set), but it
does NOT by itself PROVE cofiniteness. The proof-power is the Astels REAL→DISCRETE TRANSFER (τ≥1 ⟹ the
DISCRETE sumset has an integer interval/seed), which is the OPEN part = breaker's config-dependent
finite-stage decay finding ((3,5,7,9) ex=0.042 fails) + maverick's v8 boundary case = the MW wall.
So: right thickness, right critical value; the transfer is the transcendence content. Code: breaker_verify_tau.py.

## 7. SEQUENTIAL FILL DATA (for task #15: thickness-product ⟹ interval) + a TRAP WARNING
As bases are added (k=1), n0 (last miss) and miss-count up to N=20M:
  (3,4,7):  (3,)→n0=20M  (3,4)→n0~20M  (3,4,7) β=1.000→n0=581 ✓
  (3,4,5):  ... (3,4,5) β=1.083→n0=79 ✓
  (3,5,7,13): (3,5,7) β=0.9167→n0=523010 (353 miss, LOOKS like interval!) (3,5,7,13) β=1→n0=112 ✓
  (4,5,6,7,8): (4,5,6) β=0.783→n0=11.4M  (4,5,6,7) β=0.950→n0=44 (9 miss, LOOKS cofinite!) (4,5,6,7,8) β=1.093→n0=3 ✓

★ TRAP WARNING for task #15: the transition to "looks like a finite interval" happens BELOW β=1
(around β≈0.92–0.95), NOT at β=1. (3,5,7) β=0.917 and (4,5,6,7) β=0.95 both present as cofinite at
N=20M (n0=523010 / n0=44) but are NOT cofinite (Pomerance: β<1 ⟹ infinite misses, just very deep).
⟹ A "thickness-product ≥ 1 ⟹ sumset is an interval" lemma CANNOT be proved by exhibiting a finite
covered interval (that fires falsely at β≈0.95). The lemma must derive the interval at EXACTLY the
β≥1 (=Σ1/(d−1)≥1) threshold, with the proof's "interval-closes" step keyed to the reach constant
1/(d−1) per base — the only quantity that flips precisely at β=1. Empirically, β<1 always eventually
re-opens a gap (Pomerance), so any finite-interval-based sufficient condition is unsound near the boundary.
Code: breaker_sequential_fill.py.
