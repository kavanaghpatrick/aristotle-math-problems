# modular — correction to INV-M1 (band-bracket dead; INV-C1 survives)

**Author:** modular. Standalone correction (INVENTIONS.md was under concurrent write-race; recording
here durably). Reconciled with carry.

## The reconciliation (verified at n=78161, D=(3,5,7,9), k=2)

INV-C1 (carry, valid-peel) peels the BIG atom 5^7 = 78125, leaving residual 36 = 27 + 9 (both atoms
< 5^7). Contraction residual/n = 0.00046 — INV-C1 is DELIGHTED (huge contraction). INV-M1 (mine)
reads the SAME atom as min-top-atom/n = 0.9995 ≈ 1 — size-defect θ ≈ 1, UNHAPPY. **Same atom,
opposite verdicts.** Code: `/tmp/reconcile.py`.

## Verdicts

- **(a) The BAND-BRACKET [θ-upper, ρ-lower] I proposed is DEAD.** θ → 1 at single-base power
  clusters (n just above d^j), so there is no bounded band. "Residual fed to smaller atoms via the
  MIN-top-atom" is the wrong mechanism.
- **(b) INV-C1 (carry) is NOT killed** and never depended on my band. Its obligation is "largest
  VALID peel leaves residual ≤ ρn", ρ ≤ 0.66; tiny residuals at clusters HELP it.
- **(c) INV-M1's "bounded size-defect θ<1" was the WRONG invariant.** Minimizing the top atom is not
  what representability needs. RESCOPED: my durable contribution to the archimedean half is NOT the
  size-defect — it is **(L) as the local half** plus **confirming carry's no-nesting** (the sparse
  high-θ tail escapes power-clusters in O(1) peels, /tmp/nesting_test.py, /tmp/nesting_k3.py). The
  correct archimedean invariant is carry's valid-peel contraction, not my θ.

## Net for the team

The strongest surviving structure for the E124 k≥1 open core is:
**(L) [local, PROVED, mine] + INV-C1 valid-peel contraction [archimedean, carry] + no-nesting of
power-clusters [reduced obligation, modular+carry].** The remaining rigorous step is carry's: prove
the pure-power neighbors don't nest indefinitely (a bounded-height Diophantine non-coincidence, much
weaker than full Mignotte–Waldschmidt). INV-M1 as originally stated is superseded by INV-C1; I keep
(L) and the nesting confirmation as the durable parts.

See also: INVENTIONS.md (carry's INV-C1 + nesting results), modular_local_landscape.md ((L) proof).

---

## CORRECTION 2 (breaker overturned my "single-scale" nesting claim at the boundary) — Jun 10

My "the cascade does NOT nest, MW wall is single-scale" finding was based on (3,4,5)/(3,5,7,9) AND a
(3,4,7) k=3 run that was **BELOW the true threshold** — I tested against N0(3)≈57M (the false-freeze
I had already been warned about) instead of the true N0(3)=166,025,260. I fell into exactly the trap
I flagged for others.

**breaker re-ran (3,4,7) k=3 ABOVE 166M (to N=200M) and the picture REVERSES at the boundary:**
- high-θ (>0.8) chains are **PERVASIVE** (5000/5000 of n in the window), depth **5–6**, and do NOT
  thin even +29M above n0. So at the boundary ∑1/(d−1)=1 with k≥3 the cascade is **universal and
  bounded-but-deep**, NOT the sparse single-scale picture I reported for strict-excess / low-k.

**Structural corroboration (modular, /tmp/nesting_boundary_recheck.py):** near n0=166M for (3,4,7) k=3
the atoms are SPARSE — largest atom ≤ n0 is 3^17 = 129,140,163, and the next atom (4^14 = 268,435,456)
is 139M higher. So every n in [129M, 268M] must be built around 3^17 plus a large residual, forcing
deep high-θ peel chains. This is exactly breaker's pervasive depth-5–6.

**CORRECTED VERDICT:** the M1-salvage + INV-C1 single-peel localization is SOUND for **strict-excess
(∑>1) and low k** (a real partial — a strict-excess closer candidate), but at the **boundary ∑=1 with
k≥3** — where the hardest case (3,4,7) lives — the high-θ set is NOT sparse and the peel-recursion
stays high-θ for ~6 levels, every one needing MW control. So it is **NOT a boundary closer**. The one
mildly hopeful note (breaker's): the cascade DEPTH is bounded (~6, not growing within reach), so the
MW content is finite-depth per n rather than unbounded — but it is pervasive, not sparse.

Lesson logged: I must test nesting/threshold claims ABOVE the verified N0, and for (3,4,7) k=3 that is
166,025,260, never 57M. The durable parts of my work are unaffected: (L) [residue half, proved] stands;
only the archimedean "single-scale" localization was boundary-wrong. Code: breaker_nesting_boundary2.py
/ boundary3.py (breaker), /tmp/nesting_boundary_recheck.py (modular corroboration).

---

## CORRECTION 3 (carry: the combination does NOT close cofiniteness — circularity) — Jun 10

carry worked the logic one step further and is RIGHT: INV-C1's recursion takes REPRESENTABILITY as
input, so it cannot prove cofiniteness. C1 is a sound O(log n) DECODER for the already-representable
set (peel the largest atom of any representation → smaller representable residual, tautologically),
and its contraction (residual ≤ 0.72n, geometric, elementary) is real — but it never establishes
"n > n0 IS representable," which is the whole question.

I checked the cleanest NON-circular form: (*) "for every n>n0, ∃ atom a≤n with (n−a) representable."
Strong induction via (*) is genuinely non-circular (doesn't assume n representable; base = n0 region),
and (*) is strictly WEAKER than representability — it holds at 34 NON-representable n for (3,4,7) k=1
(6,8,15,17,…). So the induction FRAMEWORK is sound. BUT proving (*) for all n>n0 requires showing
R_{<n} + atoms covers n, and THAT covering is exactly the unproven density/MW content. C1's
contraction bounds residual SIZE, not residual REPRESENTABILITY. So the wall is untouched.

**FINAL HONEST STATUS of my INVENTION BLITZ contributions:**
- (L) [residue/local half]: PROVED, verified, independent of all of this. STANDS.
- INV-M1 (size-defect band): DEAD (wrong invariant; superseded by INV-C1).
- "single-scale no-cascade localization": CORRECTED to strict-excess/low-k partial only (Correction 2).
- M1-envelope + INV-C1 combination: does NOT close cofiniteness (Correction 3) — both presuppose
  representability where it's in doubt. M1-envelope = real partial on bulk structure; C1 = sound
  decoder + elementary contraction. NOT a closure.

Net: my one durable proved result is (L). Everything archimedean I proposed is either dead, a partial,
or a non-closing structural observation. Recorded to keep my files consistent with carry's INVENTIONS.md
final verdict. Code: /tmp/circularity.py.

**REFEREE-PROOF BANKED STATEMENT (modular + carry, final, aligned):** The E124 k≥1 open core is
**REDUCED to** "pure-power neighbors don't nest indefinitely" (a bounded-height Diophantine
non-coincidence, much weaker than full Mignotte–Waldschmidt, possibly elementary — pending scholar's
genuine-vs-disguised-MW verdict). It is **NOT CLOSED**. The pieces: (L) [local/residue half, PROVED,
machine-verified] + the no-nesting reduction [OPEN] + INV-C1's contraction [elementary, but DOWNSTREAM
of representability — a sound O(log n) decoder, not a representability proof]. IF the no-nesting is
proved elementarily, THEN with (L) and density's envelope it could close — but that IF is the whole
game and nothing on the team supplies it yet. Do NOT state "closed"; state "reduced."
