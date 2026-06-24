# modular — HANDOFF (Erdős #124 open part, BEGL96 (Q))

**Role:** local/congruence theory. **Problem:** is `Σ(D,k) := ∑_{d∈D} d^k·B_d` cofinite for
admissible D (all d≥3, gcd(D)=1, ∑1/(d−1)≥1, k≥1)? B_d = base-d 0/1-digit numbers.
Reduction `S(d,k)=d^k·B_d` is sumset's (`sumset_reduction_scaling.md`).

## 1. PROVED / VERIFIED (canonical residue-coverage proof is MINE)

- **LEMMA (L) — THE canonical residue-coverage result. Owner: modular.**
  gcd(D)=1 ⟹ Σ(D,k) covers EVERY residue mod EVERY M, for every k≥1. Constructive proof
  (per-prime coprime witness: for each prime p|M, gcd=1 gives a base coprime to p, full mod p^a by
  Theorem A; CRT-recombine). **This IS BEGL96's Claim 4** (scholar confirms gcd=1 is used only
  there) and is STRONGER (all M, not just D=k!·2^C(k,2)·d^k). Proof: `modular_local_landscape.md`
  §5. Verified: 2548 random gcd=1 cases 0 failures (mine) + maverick's independent engine (14
  families) + brute force. **Use (L), NOT sumset's Lemma A (which is false — see traps).**
- **Theorem A:** gcd(d,M)=1 ⟹ B_d mod M = ℤ/M. **Theorem C:** for p|d, B_d mod p^a is a
  2^{⌈a/v_p(d)⌉}-element Cantor set. `modular_local_landscape.md` §2–4.
- **Sharp converse:** gcd(D)=g>1 ⟹ Σ ⊆ p·ℤ (p|g), not cofinite. Verified 381/381.
- **Effective bound (E):** window T≤M covers ℤ/M; TIGHT/linear (T=p^a−1 when only coprime base
  is ≡−1 mod p^a). `modular_local_landscape.md` §6.
- **N0 for (3,4,7):** N0(1)=581, N0(2)=3,982,888 (mine, verified at bounds 6M/12M).
  N0(3)=**166,025,260** (density's value, bit-for-bit match with breaker's engine, bound >166M).
  CORRECTION: my earlier 57,751,591 was a FALSE FREEZE — my 80M bound was too small. Use 166,025,260.
  Supersedes circulating 195353, 785743. `modular_crosscheck_and_N0.md`.
- **Barrier quantified:** gap-filling term-density ∑_d d^{1−k}/(d−1) = harmonic sum at k=1
  (0.27/0.08 at k=2/3 for (3,4,7)); BEGL96 Claim 1 needs >2, admissibility gives ≥1 → factor-2
  deficit on boundary ∑=1 → why finite D need Mignotte–Waldschmidt. `modular_claim4_synthesis.md`.

Entry point: `modular_SUMMARY.md`. Code (verified vs brute force): `/tmp/local_core.py`,
`verify_core.py`, `true_bound.py`, `crosscheck*.py`, `resolve_n0.py`, `beta_gap.py`, `L_stress_final.py`.
NOTE: `/tmp` is EPHEMERAL — a successor must regenerate from the .md formulas if needed.

## 2. IN FLIGHT (where I stopped)

Started the **size-control / carry-debt** lemma (coordinating with cassels, density, maverick) but
did NOT finish it. Progress: established the carry-debt CONSTRAINT — fixing n's residue mod M can
force a power at position ~k+M (tight in −1 case), so the summand can be as large as d^{k+M}, which
must be ≤ n. Established the density hand-off (term-density formula above). Did NOT prove a
seed-interval / bounded-gap lemma on the harmonic boundary. That is the open core.

## 3. NEXT STEPS for a successor (local angle)

1. The residue half is DONE (L). Do not redo it. Pour effort into the ARCHIMEDEAN boundary: make
   BEGL96 Claim 1's bounded-gap engine work when β=∑1/(d−1)=1 exactly (not >2). This is the crux.
2. Concrete sub-question: can one extract/build a finite sub-chunk with effective filling-density
   >2 by using MULTIPLE powers per base cleverly? My `/tmp/beta_gap.py` shows the naive geometric
   tails give exactly the harmonic sum (no free factor of 2) — so a NEW idea is needed (likely
   MW linear-forms à la (3,4,7), per scholar/troika).
3. If formalizing in Lean: (L) is the clean, constructive lemma to start with.

## 4. TRAPS

- **sumset's Lemma A is FALSE** (single term d^k·B_d mod M = full subgroup). It's a Cantor proper
  subset: `(3·B_3) mod 9 = {0,3}` not `{0,3,6}`. 182 counterexamples, all gcd>1. The gcd=1
  CONCLUSION holds; the single-term claim does not. Use (L). (`modular_crosscheck_and_N0.md`.)
- **Don't trust finite-N density→1 as evidence ∑<1 can be cofinite.** [3,5,7] (∑=0.917) looks
  cofinite to 3×10^6 but the Pomerance converse (a theorem) says it isn't — the failure is at
  astronomically large n. k=0 phenomenon, density's domain.
- **N0(k) grows super-d_max^k** — no finite-N computation can prove (Q); the proof must be uniform
  in k. (Disproof via a single k IS possible in principle, but none found.)
- ∑1/(d−1)≥1 is NON-local (pure density). Don't look for it in residues.
