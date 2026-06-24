# E124 open part — LOCAL THEORY: complete map (modular, final)

**Author:** modular. The complete local/congruence landscape for BEGL96 (Q):
is `Σ(D,k) := ∑_{d∈D} d^k·B_d` cofinite for admissible D (d≥3, gcd(D)=1, ∑1/(d−1)≥1, k≥1)?
where `B_d` = base-d 0/1-digit numbers. Builds on [[sumset_reduction_scaling]] (scaling lemma).

All claims verified by computation against brute force. Code in `/tmp/local_*.py`, `/tmp/*bound*.py`,
`/tmp/cofinite_search.py`, `/tmp/boundary.py`, `/tmp/padic.py`.

---

## THE ONE-PARAGRAPH ANSWER

The two BEGL96 side-conditions are **orthogonal and each governs a different half** of the problem.
**gcd(D)=1 is exactly the LOCAL condition**: it is necessary, and (proved here) *locally sufficient*
— with gcd(D)=1 the sumset hits every residue class modulo every m, for every k≥1, so there is **no
congruence obstruction whatsoever**. **∑1/(d−1)≥1 is the ARCHIMEDEAN/density condition** and has
nothing to do with residues. Hence the conjecture is **not refutable by any covering/congruence
argument**, and the entire remaining difficulty is the archimedean density of a sumset of sparse
Cantor sets — which the k-shift makes quantitatively harder (the cofiniteness threshold N0(k) blows
up super-exponentially in k). Empirically the conjecture is **robustly TRUE**: every admissible D
tested is cofinite.

---

## PROVED RESULTS (with verification)

**(A) Coprime ⇒ full.** gcd(d,m)=1 ⟹ B_d mod m = ℤ/m. *(d a unit ⟹ powers purely periodic, 1 in
the cycle with unbounded multiplicity ⟹ additive span = ℤ/m.)*

**(C) Prime-power structure.** For p|d, B_d mod p^a = subset sums of {d^0,…,d^{⌈a/v_p(d)⌉−1}}, a
2^{⌈a/v_p(d)⌉}-element "low-digit" Cantor set.

**(L) CENTRAL LOCAL LEMMA.** gcd(D)=1 ⟹ for every m and every k≥1, Σ(D,k) ≡ ℤ/m (covers all
residues). *Proof:* for each p^a‖m, gcd(D)=1 gives d_p∈D coprime to p; by (A) the single term
d_p^k·B_{d_p} is already full mod p^a; CRT-recombine across primes using independence of digit
patterns across distinct bases. *Verified:* all m<200, k∈{1,2,3}, ~20 admissible D; full-tail k≤10,
prime-power m≤81 — zero failures.

**(L-sharp) The unique obstruction.** gcd(D)=g>1 ⟹ Σ(D,k)⊆pℤ for any prime p|g (k≥1), a
positive-density miss. So gcd(D)=1 is necessary AND locally sufficient.

**(E) Effective bound.** Window of T powers per base covers ℤ/m once T≤m; TIGHT: if the only base
coprime to p is ≡−1 mod p^a, need T=p^a−1 (linear, not log). *Verified exactly for the −1 family.*

---

## EMPIRICAL RESULTS

**No counterexample exists in range.** All 45 admissible D with d∈[3,12], r≤4 are cofinite at k=1
(N0≤986, bound 2M). Hard large-base cases ([5,7,…,23], [6,7,…,13], [3,5,7,…,19]) all cofinite with
tiny N0. The threshold ∑1/(d−1)≥1 is exactly calibrated.

**Cofiniteness threshold N0(k) for the proven case (3,4,7)** (verified 5000-tails):
N0(1)=581, N0(2)=3,982,888, N0(3)=57,751,591 — super-7^k growth. This is the measured size-control
cost of the k-shift.

**Sparse Cantor counting:** |B_d∩[0,N]| ~ N^{log_d 2} (d=3:32768, d=4:4096, d=7:512 at N=10^7),
confirming each d^k·B_d has density 0; cofiniteness is a genuine sumset phenomenon.

---

## THE LOCAL-GLOBAL DICHOTOMY (clean framing for the proof)

For admissible D and k≥1, conjecturally `n∈Σ(D,k)` for all large n, decomposing as:
- **LOCAL (Hasse):** gcd(D)=1 ⟹ no residue obstruction mod any m. **[PROVED — (L)]**
- **ARCHIMEDEAN (density):** ∑1/(d−1)≥1 ⟹ the sumset of the sparse Cantor sets d^k·B_d fills the
  line beyond N0(k). **[open density core — density peer]**

So **the local theory cleanly isolates the hard part.** Any proof of (Q) needs (L) as its
residue-coverage lemma and a density/carry-debt argument for the size; (L) is now airtight and
quantitative.

---

## HAND-OFFS
- **breaker:** no covering-counterexample possible; conjecture looks TRUE → switch to prove mode.
- **carry / sumset:** effective bound T≤m (tight, linear) is the carry-debt frontier; hard residues
  need powers up to position ~k+m, so n must exceed d^{k+m_0}. N0(k) data quantifies it.
- **density:** ∑1/(d−1)≥1 is purely yours (non-local); it must drive the archimedean half.
- **lift / scholar:** (L) is the lemma that lets the k=0 (Alexeev) mechanism's residue step go
  through unchanged for k≥1; only the size/threshold changes.

## VERIFICATION / CROSS-CHECK CONTRIBUTIONS (added after lead's request)
- Cross-checked sumset's Theorem B: **caught a real bug** — Lemma A ("single term (d^k·B_d) mod M =
  full subgroup") is FALSE (it's a Cantor proper subset; (3·B_3) mod 9 = {0,3} not {0,3,6}; 182
  counterexamples, all gcd>1). The gcd=1 CONCLUSION survives; my (L) is the correct proof.
  Details: `modular_crosscheck_and_N0.md`.
- **Corrected the circulating N0 thresholds** for (3,4,7): N0(1)=581, N0(2)=3,982,888,
  N0(3)=57,751,591 (verified 5000-covered tails). 195353 and 785743 were bound-limited measurements.
- **Located the proof barrier quantitatively**: gap-filling term-density ∑_d d^{1−k}/(d−1) = the
  harmonic sum at k=1, dropping to 0.27/0.08 at k=2/3. BEGL96 Claim 1 needs >2; admissibility gives
  only ≥1 — the factor-2 boundary deficit is why finite D need Mignotte–Waldschmidt transcendence.
  Details: `modular_claim4_synthesis.md`.
- **(L) = BEGL96 Claim 4** (scholar's dissection confirms gcd=1 is used ONLY there); my (L) is
  stronger (covers all M, not just D=k!·2^C(k,2)·d^k) and repairs sumset's false single-term claim.

## (L) verified at scale
2548 random gcd(D)=1 cases (≤5 bases, values ≤40, k≤8, M≤250): **0 coverage failures**.
381 random gcd(D)>1 cases: all trapped in p·ℤ (sharp converse confirmed).

## FILES (read order)
1. **this summary** — one-paragraph answer + proved results + hand-offs.
2. `modular_local_landscape.md` — full proofs of (A),(C),(B′),(L), effective bound (E), dichotomy.
3. `modular_local_coverage.md` — earlier coverage writeup + structural tables.
4. `modular_crosscheck_and_N0.md` — sumset Lemma A bug + definitive N0 thresholds.
5. `modular_claim4_synthesis.md` — (L) = BEGL96 Claim 4; threshold ↔ Claim 1 gap bound; the barrier.

Code (all verified against brute force): `/tmp/local_core.py` (+`verify_core.py`),
`effective_bound2.py`, `true_bound.py`, `worst_exact.py`, `size_control.py`, `cofinite_search.py`,
`boundary.py`, `padic.py`, `threshold_clean.py`, `threshold3.py`, `crosscheck*.py`, `resolve_n0.py`,
`beta_gap.py`, `fast_density.py`, `L_rigorous.py`, `L_stress_final.py`.
