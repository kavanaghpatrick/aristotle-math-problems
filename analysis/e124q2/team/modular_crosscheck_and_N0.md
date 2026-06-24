# Cross-check of sumset Theorem B + definitive N0 thresholds (modular)

**Author:** modular. Two verification results the team needs before building on prior claims.

---

## 1. sumset's Theorem B: CONCLUSION correct, LEMMA A false

Cross-checked `sumset_crt_residue_theorem.md` against my brute-force-verified core
(`/tmp/local_core.py`, `/tmp/crosscheck*.py`).

**Lemma A is FALSE.** Claim: `(d^k·B_d) mod M = gcd(d^k,M)·(ℤ/M)` (full subgroup of multiples of
gcd(d^k,M)). Reality: the single term is a Cantor-like **proper** subset. Counterexample
`(3¹·B_3) mod 9 = {0,3}`, NOT `{0,3,6}` — residue 6 is unreachable. The faulty step is
"finite additively-closed submonoid = the full subgroup": it IS a subgroup, but equals
`d^k·(B_d mod M/gcd)`, and `B_d mod p^a` has only `2^{⌈a/v_p(d)⌉}` residues (my Theorem C), not
all of them. The "add the same residue many times" argument fails for **pre-period** residues
(when p|d, low powers d^j appear with multiplicity 1, not unbounded).

**Exact formula in Theorem B fails for gcd(D)>1.** 182 counterexamples in my sweep
(D∈combinations of {3,4,…,27}, k≤3, M<80), ALL with gcd(D)>1: e.g. `T([3,9],1) mod 9 = {0,3}`
while the formula predicts `{0,3,6}`; `T([9,27],1) mod 27 = {0,9}` vs predicted `{0,9,18}`.

**The corollary actually used IS TRUE.** For gcd(D)=1: full residue coverage, **0 failures**
across all those D, k≤3, M<150. So "gcd(D)=1 ⟺ no congruence obstruction" stands. The correct
proof is my lemma (L) (per-prime coprime witness + CRT, `modular_local_landscape.md` §5), which
never invokes the false single-term subgroup claim. sumset's downstream corollaries (1,2,3) and
the seed-interval reduction only use the gcd=1 case and are unaffected.

---

## 2. Definitive cofiniteness thresholds N0(k) for the BEGL96-proven triple (3,4,7)

Three different N0(2) values were circulating: cassels 195353, sumset 785743, modular 3,982,888.
**Resolved by exact reachability to bound 6×10^6 with a verified 5000-covered tail:**

| k | TRUE N0 (largest non-representable) | verified |
|---|---|---|
| 1 | 581 | tail covered |
| 2 | **3,982,888** | 5000-tail covered, bound 6M & 12M |
| 3 | **166,025,260** | density's value, bound >166M, bit-for-bit match with breaker's engine |

**CORRECTION (Jun 10):** my earlier N0(3)=57,751,591 (bound 80M) was itself a FALSE FREEZE — the
80M bound was too small and the true largest miss is at 166,025,260 (density + breaker, larger
bound). Exactly the trap I flagged for others; I fell into it at k=3. The N0(2) value is solid.
195353 and 785743 ARE non-representable but are **not** the largest — bound-limited measurements.
**N0(k)/d_max^k grows** (83 → 81,283 → 484,330 for d_max=7), so N0(k) is **super-d_max^k** — the
seed threshold blows up faster than a clean power of d_max. Any seed-interval lemma must allow the
threshold to grow at least this fast; cassels' "~d_max^k" is a lower bound on the growth, not the
rate.

**Action for team:** use N0(2)=3,982,888, N0(3)=57,751,591 (not the smaller circulating values)
when calibrating the seed-interval / carry-debt threshold.

## Files
`/tmp/crosscheck.py`, `/tmp/crosscheck2.py`, `/tmp/crosscheck3.py`, `/tmp/resolve_n0.py`,
`/tmp/threshold_clean.py`, `/tmp/threshold3.py`.
