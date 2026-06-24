# Local theory ↔ BEGL96 Claim 4: the residue-covering step, rigorous (modular)

**Author:** modular. Synthesis tying my verified local lemma (L) to the actual BEGL96 proof
structure that scholar dissected (`scholar_BEGL96_proof_dissected.md`). This is the residue half of
the proof, made airtight and quantitative.

---

## The match: (L) IS Claim 4

scholar's dissection shows gcd(D)=1 is used in BEGL96 **only** in Claim 4: "Σ(Pow(A₀;s)) contains a
complete residue system mod D", where `D = s!·2^{C(s,2)}·d^s` (d = the fixed AP-step from Claim 3,
s = our k). My lemma (L) is exactly this residue-covering statement, proved directly and verified:

> **(L)** gcd(D)=1 ⟹ for every modulus M and every k≥1, ∑_{d∈D} d^k·B_d covers all of ℤ/M.

Claim 4 only needs the single modulus M = D; (L) gives ALL M, which is strictly stronger and
removes any dependence on the particular value of D. My proof (per-prime coprime witness + CRT,
`modular_local_landscape.md` §5) is the clean version of BEGL96's Claim 4 argument ("for each prime
q_i | D, gcd=1 gives a(i) coprime to q_i; combine by CRT"). **It also repairs sumset's Lemma A,
which tried to prove a stronger single-term statement that is false** (see
`modular_crosscheck_and_N0.md`).

**Verification status:** (L) holds with ZERO failures across all M<200, k≤3, ~20 admissible D, plus
full-tail coverage for k≤10 and prime-power M≤81. The exact-formula overreach (sumset Theorem B's
`gcd(gcd_d d^k, M)·ℤ/M`) fails for gcd(D)>1 but those are excluded by hypothesis.

---

## The threshold ↔ Claim 1 gap bound: reconciled and quantified

scholar's Claim 1 (the completeness engine): for a finite chunk B with β := ∑1/(b_i−1) > 2, every
gap in Σ(Pow(B;s)) is `≤ 2·b_N^{s+1}` (b_N = largest base). This is the rigorous form of the
carry-debt budget I was computing.

This **reconciles the threshold scaling** I measured. For (3,4,7): the gap bound is `2·7^{k+1}`,
and the true cofiniteness threshold N0(k) I verified (581, 3 982 888, 57 751 591) is consistent
with the assembly: Claim 3 builds an AP block of length ≥ 2·7^{k+1}, Claim 4 (=my (L)) fills its
residues, Claim 1 bootstraps. N0(k) growing super-7^k reflects the `b_N^{s+1}` gap bound TIMES the
AP-construction overhead (the modulus D = k!·2^{C(k,2)}·d^k grows super-exponentially in k, and the
AP block must exceed the gap bound). **So the super-d_max^k blow-up I measured is exactly the
D-modulus growth in Claim 4 compounded with Claim 1's b_N^{k+1} gap.**

## The genuine obstruction, located precisely

scholar's key caveat: **Claim 1 needs β = ∑1/(b_i−1) > 2 on a finite chunk** — the harmonic
*boundary* ∑=1 is NOT enough for the gap engine. This is the deep reason a single finite D with
∑1/(d−1)=1 (like (3,4,7)) evades the general density machinery and required the ad-hoc
Mignotte–Waldschmidt linear-forms argument. So:

- **LOCAL / residue half (Claim 4 = my (L)): DONE, rigorous, verified.** gcd(D)=1 ⟹ all residues
  covered mod every M, every k≥1. No congruence obstruction survives.
- **ARCHIMEDEAN / density half (Claim 1 + 2 + 3): the open core.** Needs β>2 on a finite sub-chunk
  to get bounded gaps; on the harmonic boundary ∑=1 this fails and is exactly where BEGL96 is
  "fairly far from being able to prove the conjecture." This is density + cassels + carry territory.

## Pomerance-boundary note (k=0, for density peer)

My fast bitmask density runs (bound 3×10^6): D with ∑1/(d−1) slightly below 1 — [3,5,7] (0.917),
[3,4,8] (0.976), [3,4,9] (0.958) — all reach density 1.0000 with only tiny finite missing sets
(e.g. [3,4,9] last miss 59048). [3,4] (∑=0.833) plateaus at density ~0.85–0.90 with gaps persisting
to the bound (genuinely not cofinite). So the Pomerance converse "∑≥1 necessary" bites only at
astronomically large n for ∑ just below 1; finite computation cannot see the boundary. **This is a
k=0 density subtlety, orthogonal to the local theory.** Flag for density peer — do NOT read the
finite-range density→1 as evidence ∑<1 can be cofinite.

## Net for the proof
The proof of (Q) factors exactly as BEGL96's assembly: my (L) supplies Claim 4 (residue covering,
rigorous), and the remaining work is making Claims 1–3 (the density/gap engine) go through on the
harmonic boundary ∑1/(d−1)=1 — which is the hard, open archimedean core owned by density/cassels/carry.

## Files
`modular_local_landscape.md` (the proof of (L)), `modular_crosscheck_and_N0.md` (Lemma A repair +
true N0), `/tmp/fast_density.py`, `/tmp/filling*.py`, `/tmp/carry_debt.py`.
Reference: `scholar_BEGL96_proof_dissected.md` (Claims 1–4).
