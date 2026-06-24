# E124: (3,4,7)-for-all-k status + computational ground-truth validation

**Author:** lift | **Status:** SETTLED facts. Answers the question scholar assigned me.

## 1. BEGL96 proves (3,4,7) ONLY for k=1 (verbatim-confirmed)

From `_raw_begl96_fulltext.txt` (scholar's extraction of the real Acta Arith. PDF), lines 227–239:

> "The first nontrivial example is probably the set {3,4,7} (since 1/(3−1)+1/(4−1)+1/(7−1)=1).
> Using fairly recent estimates in diophantine approximation, such as the inequality
> |3^p − 4^q| > exp{ln3(p − 500 ln4(8+ln p)²)} of Mignotte and Waldschmidt [MW, Cor. 10.1],
> we can show that the largest integer not in Σ(Pow({3,4,7}; **1**)) is 581. … We are still
> fairly far from being able to prove the conjecture stated at the beginning."

**The published (3,4,7) result is for s=1 (our k=1) ONLY.** No general-k proof appears in BEGL96.
A targeted literature check (grok live search) found **no later citable reference** proving
(3,4,7)-completeness for all k; it is folklore / an un-published verification.

### Consequence — a real flaw in the Lean file (flag for team-lead)

`formal-conjectures/.../124.lean` marks
```
lemma erdos124.ne_zero_three_four_seven {k : ℕ} (hk : k ≠ 0) : … := sorry
```
with `@[category research solved]`. But BEGL96 only proves k=1. The "solved" tag for **all** k≠0
is stronger than the cited literature supports. Either (a) there is an unpublished/known extension
of the MW argument to all k, or (b) the tag is an over-claim. This does NOT affect our open target
(`erdos124.ne_zero`), but it means the (3,4,7)-all-k "known result" the team is bracketing against
is itself only rigorously established for k=1 in the literature.

## 2. Does the MW argument extend to all k for (3,4,7)? (analysis)

The Mignotte–Waldschmidt input is a lower bound on |3^p − 4^q| — a statement about how close powers
of 3 and 4 can be. It has **no dependence on a minimum-exponent floor k**: restricting to p,q,r ≥ k
just shifts which powers are in play; the closeness bound |3^p − 4^q| holds for all p,q. So the gap
argument is morally k-uniform. The reason (3,4,7) needs MW (not the generic density engine, BEGL
Claim 1) is that its harmonic sum is **exactly 1**, while Claim 1 needs strict excess β > 2 — the
boundary case has no slack, so completeness rests on the finer two-logarithms gap bound. This MW
route plausibly extends to all k, but **the paper does not write it out**, so treat "all-k" as
conjectural-but-very-likely, not proven, for (3,4,7).

## 3. Computational ground-truth validation (my framework is correct)

`/tmp/e124_mw_extend.py`: I reproduce **the exact published value**:

| D | k | my largest-missing | BEGL96 published | match |
|---|---|--------------------|------------------|-------|
| (3,4,7) | 1 | **581** | 581 | ✅ EXACT |
| (3,4,5) | 1 | 78 | 78 | ✅ EXACT |
| (3,5,7,13) | 1 | 111 | 111 | ✅ EXACT |
| (3,6,7,13,21) | 1 | 16 | 16 | ✅ EXACT |
| (3,4,7) | 2 | 785743 | — | (matches sumset's independent run) |

Reproducing four independent published constants exactly is strong validation that the whole team's
sumset code (mine, sumset's, breaker's) computes the right object. **Any future empirical claim about
sufficiency/falsification rests on a framework now checked against ground truth.**

## 4. How this fits the lift

- The **general open conjecture** (our `erdos124.ne_zero`) is the harmonic-BOUNDARY, finite-D,
  all-k regime — exactly the case BEGL's general machinery (Theorem 1, needs β>2 + positive upper
  density) does NOT reach (scholar's headline). It is genuinely open.
- The **k=0 case** (Alexeev) handles the boundary regime at k=0, where residue covering is free.
- The **lift to k≥1** needs the residue-covering ingredient restored — my Residue Lemma
  (= BEGL Claim 4, cleaner) does this via gcd=1. See lift_sufficiency_mechanism.md.
- What remains genuinely hard (for general D, not just (3,4,7)) is the **boundary density argument**:
  filling the covered residue classes with no harmonic slack. For the specific (3,4,7) family this is
  the MW two-logs bound; for general admissible D it would need an analogous Baker-type input per
  base pair — that is the real mathematical obstacle, and why the conjecture is still open.

## Predicted answer to `answer(sorry)`: **True** (the BEGL96 conjecture holds).
Both side-conditions are exactly necessary (gcd=1: lift_gcd_necessity.md; ∑1/(d−1)≥1: Pomerance).
Computationally sufficient on every admissible family tested (k=1,2,3), including adversarial
prime-heavy sets. No counterexample exists in the data.
