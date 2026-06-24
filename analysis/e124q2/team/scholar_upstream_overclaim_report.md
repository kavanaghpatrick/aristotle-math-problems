# Upstream over-claim report: `Erdos124.ne_zero_three_four_seven` is tagged `solved` but BEGL96 proves only k=1

**Status:** DOCUMENT ONLY — drafted so it can be filed verbatim as a GitHub issue against the
`google-deepmind/formal-conjectures` repository, pending owner approval. Do NOT post externally.
**Author:** scholar (Erdős #124 literature team). **Date:** 2026-06-10.

---

## Summary

The lemma `Erdos124.ne_zero_three_four_seven` in
`FormalConjectures/ErdosProblems/124.lean` is annotated `@[category research solved, AMS 11]`
and its docstring attributes the result to Burr–Erdős–Graham–Li [BEGL96]. The Lean statement
asserts completeness of `Σ(Pow({3,4,7}; k))` **for every `k ≠ 0`** (i.e. all `s ≥ 1`). However,
the cited source proves this **only for `k = 1` (`s = 1`)**. BEGL96 establishes no statement for
`(3,4,7)` at general `k ≥ 2`; the general-`k` case is part of the conjecture that BEGL96
explicitly leaves OPEN. The `solved` tag therefore over-states what the literature supports.

This is a labelling/provenance issue, not a claim that the lemma is false (it is almost certainly
true — see "Is it actually true?" below). The fix is to either restrict the lemma to `k = 1`, or
re-tag it appropriately and adjust the attribution.

## The Lean statement in question

```lean
/--
All sufficiently large integers can be written as a + b + c where a has only the digits 0, 1
in base 3, b only the digits 0, 1 in base 4, c only the digits 0, 1 in base 7.

Provee by Burr, Erdős, Graham, and Li [BEGL96]
-/
@[category research solved, AMS 11]
lemma erdos124.ne_zero_three_four_seven {k : ℕ} (hk : k ≠ 0) :
    ∀ᶠ n in atTop,
      n ∈ sumsOfDistinctPowers 3 k + sumsOfDistinctPowers 4 k + sumsOfDistinctPowers 7 k :=
  sorry
```

The universally-quantified `{k : ℕ} (hk : k ≠ 0)` makes this a claim **for all `k ≥ 1`**.

## What BEGL96 actually proves (verbatim)

Source: S. A. Burr, P. Erdős, R. L. Graham, W. W.-C. Li, "Complete sequences of sets of integer
powers", *Acta Arith.* **77** (1996), 133–138. Free PDF (ICM, CC-BY):
`http://matwbn.icm.edu.pl/ksiazki/aa/aa77/aa7722.pdf`. DOI: 10.4064/aa-77-2-133-138.

In §3 ("Concluding remarks"), BEGL96 write (verbatim, p. 137; `Pow(A; s)` uses exponents `≥ s`,
so `Pow(·; 1)` means exponents `≥ 1`, matching the Lean `k = 1`):

> "The first nontrivial example is probably the set {3, 4, 7} (since 1/(3−1) + 1/(4−1) + 1/(7−1)
> = 1). Using fairly recent estimates in diophantine approximation, such as the inequality
> |3^p − 4^q| > exp{ln 3 (p − 500 ln 4 (8 + ln p)^2)} of Mignotte and Waldschmidt [MW,
> Corollary 10.1], **we can show that the largest integer not in Σ(Pow({3, 4, 7}; 1)) is 581.**"

The only `(3,4,7)` assertion in the paper is for `Σ(Pow({3,4,7}; 1))` — the **`s = 1`** (k = 1)
set. The paper proves the largest missing integer is 581 (a `k = 1` statement).

Two paragraphs later BEGL96 state, regarding the general conjecture (which includes all `s`):

> "**We are still fairly far from being able to prove the conjecture stated at the beginning.**"

The "conjecture stated at the beginning" is, verbatim from §1:

> "Conjecture. For any s, Pow(A; s) is complete if and only if (i) ∑_{a∈A} 1/(a−1) ≥ 1,
> (ii) gcd{a ∈ A} = 1."

So the *all-`s`* statement — including `(3,4,7)` for `k ≥ 2` — is explicitly part of the OPEN
conjecture, not a proved result. BEGL96 contains no proof, and no statement, of `(3,4,7)`
completeness for any `s ≥ 2`.

## The precise gap

| Object | BEGL96 status |
|---|---|
| `Σ(Pow({3,4,7}; 1))` complete (k = 1) | PROVED (largest miss = 581), via Mignotte–Waldschmidt |
| `Σ(Pow({3,4,7}; s))` complete for `s ≥ 2` (k ≥ 2) | NOT proved; part of the open conjecture |
| The Lean lemma (all `k ≠ 0`) | asserts the union of both rows; only the first is in [BEGL96] |

The Mignotte–Waldschmidt lower bound on `|3^p − 4^q|` does plausibly extend to control the `s ≥ 2`
case (it is a lower bound for all exponents `p, q`), so a proof for general `k` is likely within
reach by the same method plus a finite computation — but BEGL96 did not carry it out and did not
state it. Calling the all-`k` lemma `solved` and attributing it to [BEGL96] is not supported by
the cited text.

## Is the lemma actually true? (so reviewers don't over-correct)

Almost certainly YES. Independent computation (this team) confirms `Σ(Pow({3,4,7}; k))` has a
finite exceptional set for `k = 1, 2, 3` (largest missing integers 581, 785743, 57751591
respectively; the `k=2,3` values verified converged at N = 1M / 130M, with long gap-free tails).
So the lemma's *content* is well-supported empirically. The issue is purely that the `solved` tag
+ `[BEGL96]` attribution claim a published proof for all `k`, whereas BEGL96 published a proof
only for `k = 1`.

(Minor secondary note, not part of the over-claim: BEGL96's §3 also prints largest-missing values
78 / 111 / 16 for `{3,4,5}` / `{3,5,7,13}` / `{3,6,7,13,21}` at `s = 1`; independent 3-method
recomputation gives 79 / 112 / 17 — an apparent off-by-one in those three secondary examples.
The headline `(3,4,7) → 581` reproduces exactly. This does not affect the lemma above but is worth
noting if those numbers ever migrate into the formalization.)

## Suggested resolution (for the maintainers to choose)

One of:
1. **Restrict to `k = 1`**: change the binder to a fixed `k = 1` (or `s = 1`) and keep
   `research solved` with the [BEGL96] attribution — this matches exactly what is proved.
2. **Keep the all-`k` statement but re-tag** as `research open` (or a "conjectured / empirically
   verified" category if one exists), and adjust the docstring to say BEGL96 proved the `k = 1`
   case, with the general `k` case following the same Mignotte–Waldschmidt method but not carried
   out in [BEGL96].
3. **Split** into two lemmas: a `solved` one for `k = 1` ([BEGL96]) and an `open`/conjectural one
   for general `k`.

Also: the docstring typo "Provee" → "Proved".

## Citations

- [BEGL96] S. A. Burr, P. Erdős, R. L. Graham, W. Wen-Ching Li, *Complete sequences of sets of
  integer powers*, Acta Arith. 77 (1996), 133–138. DOI 10.4064/aa-77-2-133-138. PDF:
  http://matwbn.icm.edu.pl/ksiazki/aa/aa77/aa7722.pdf
- [MW] M. Mignotte, M. Waldschmidt, *Linear forms in two logarithms and Schneider's method, II*,
  Acta Arith. 53 (1989), 251–287 (Corollary 10.1, the `|3^p − 4^q|` bound used by BEGL96).

## Addendum (matveev + scholar, Jun 12 2026): the k=1 §3 compression is JUSTIFIED; the all-k tag remains over-claimed

A finding from the (3,4,7) k=2 assembly (matveev, source `PROOF_347_k2.md` + CLAIMS.md "matveev —
VERIFICATION + CORRECTION"), refined after the Ridout resolution. Two parts:

**(1) BEGL96's §3 compression is JUSTIFIED (not an error).** BEGL96's entire (3,4,7) argument is the
one §3 sentence: "Using |3^p−4^q|>exp{…} of MW, we can show that the largest integer not in
Σ(Pow({3,4,7};1)) is 581." This compresses a genuine, non-trivial tail-closure step (the
finite-to-infinite bridge above N₀). Aristotle's machine-verified k=2 reduction (Jun 2026) shows the
compression is justified: via a symmetric subset-sum interval-doubling reduction, the tail closure is
equivalent to a per-atom GAP LEMMA `atomSum(<v) ≥ v + 2N₀`, which is a DISJUNCTION of pairwise
statements (it fails only if BOTH other-base power-gaps are simultaneously small = a triple
coincidence), so a SINGLE citable 2-log linear-forms (MW) bound on one pair already discharges it for
a FIXED triple at FIXED k. So BEGL's elision is a real-but-pairwise-MW-closable step — NOT a gap in
their proof. (An earlier draft of this addendum called the closure "joint/non-elementary"; that was
the JOINT-equidistribution object, which the gap-lemma reduction BYPASSES for fixed k. Corrected.)

**(2) The all-k tag REMAINS an over-claim (the report's core finding, intact).** The 124.lean
`ne_zero_three_four_seven` `research solved` tag for all k≠0 still claims more than is proven. Only
FIXED k closes via the pairwise route: the gap lemma's `N₀(k)` and the crossover are PER-k, not
k-uniform (mahler: `N₀(k)` is super-geometric). After the Ridout resolution, the inductive step
k→k+1 is k-uniformly closable (Ridout corollary, ineffective; or per-k effective via the gap lemma),
so the ENTIRE remaining all-k content is the per-k BASE CASE (the "SEED": for every k a gap-free
doubling-width seed interval near `N₀(k)`), which is OPEN. So the all-k statement is open, the tag
over-claims. [The "581" value and the MW-finiteness mechanism are correct, L2-verified.]

**Honest framing:** the §3 k=1 compression is justified (pairwise-MW-closable); the all-k tag is the
over-claim. Internal accuracy only; do NOT file or publish without owner sign-off. Source/credit:
matveev (k=2 reduction, PROOF_347_k2.md).
