# EXP9 — Top-5 Sub-Conjecture Attacks (Bare Sketches)

These are 5-10 line bare sketches for the post-cross-critique top-5. Each is a TENTATIVE attack — full submission would require running through the gap-targeting gate and auto-context attachment.

## Attack 1 — D1 (kernel-quadratic Mordell-Siegel)

**ID:** D1 | **Adjusted EV:** 63 (T=7, I=9)
**Status vs prior slots:** PARTIAL DUPLICATE — covered as L3+L4 inside `yolo_e938_meta` (slot 1316) but never **isolated** as an independent submission target. Worth re-submitting standalone with cleaner statement.

```
OPEN GAP: Erdős 938 sub-claim — Kernel-quadratic powerful finiteness
Source: formal-conjectures/FormalConjectures/ErdosProblems/938.lean (D1 from EXP9 tree)
Domain: nt

For any FIXED triple of positive squarefree integers (b1, b2, b3), let
  K(b1, b2, b3) := {(a1, a2, a3) ∈ ℕ³ : b1 a1² + b3 a3² = 2 b2 a2²,
                    rad(b_i) ∣ a_i for i ∈ {1,2,3},
                    a_i ≥ 1, and (a1²b1³, a2²b2³, a3²b3³) is a 3-term AP
                    of consecutively-enumerated powerful numbers}.

theorem erdos_938_kernel_finite (b1 b2 b3 : ℕ)
    (h1 : Squarefree b1) (h2 : Squarefree b2) (h3 : Squarefree b3) :
    {x : ℕ × ℕ × ℕ | let (a1, a2, a3) := x;
      b1 * a1^2 + b3 * a3^2 = 2 * b2 * a2^2 ∧
      ∀ i ∈ ({b1, b2, b3} : Finset ℕ), Nat.rad i ∣ (if i = b1 then a1 else if i = b2 then a2 else a3) ∧
      ∃ k, ({a1^2*b1^3, a2^2*b2^3, a3^2*b3^3} : Finset ℕ) =
        {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1), Nat.nth Nat.Powerful (k+2)}}.Finite := by sorry

Status: OPEN. Unconditional per-kernel finiteness via Mordell-Siegel
(Mathlib.NumberTheory.SiegelsLemma + Mathlib.NumberTheory.Pell). The
distinguishing feature from prior submissions: kernel triple is FIXED,
not allowed to vary. The kernel-uniformity (vary over all (b1,b2,b3))
remains the OPEN dim-2 / Bombieri-Lang core.
```

**Plausibility (Aristotle reaches):** 4/10. Mathlib has both Pell and SiegelsLemma. The hard part is the radical constraint `rad(b_i) | a_i` and the consecutiveness gate, neither of which has clean Mathlib infrastructure. Expected outcome: `compiled_partial` with Siegel finiteness via genus reduction.

---

## Attack 2 — C7 (Chan 2025 + non-cube-middle remainder)

**ID:** C7 | **Adjusted EV:** 50 (T=5, I=10)
**Status vs prior slots:** NEW ANGLE. Chan 2025 (arXiv:2503.21485) was referenced in slot 1311 (heath_brown) but never extracted as a DECOMPOSITION TARGET.

```
OPEN GAP: Erdős 938 reduction — Non-cube-middle finiteness suffices
Source: arXiv:2503.21485 (Chan 2025); E938 (C7 from EXP9 tree)
Domain: nt

By Chan 2025 Theorem 1, the case where n_{k+1} (the middle term of a
consecutive powerful 3-AP) is a perfect cube with a single odd-power
prime in n_k OR n_{k+2} is finite. To establish E938 it suffices to prove:

theorem erdos_938_non_cube_middle :
    {P : Finset ℕ | Set.IsAPOfLength P.toSet 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)} ∧
      ¬ ∃ m, Nat.nth Nat.Powerful (k+1) = m^3}.Finite := by sorry

Status: OPEN. The cube-middle slice is settled by Chan 2025 plus She 2025
(arXiv:2507.16828); the remaining non-cube-middle slice is the open core
of E938. Decomposition: E938 ⇔ (cube-middle finite, KNOWN) ∧ (non-cube-middle finite).
```

**Plausibility:** 3/10. The non-cube-middle case is the genuine open hard part. But by EXPLICITLY excluding the resolved sub-case, Aristotle's MCGS is denied the easy "Chan 2025 + done" pattern and forced into the actually-open territory. May surface a different lemma than slot 1311 did.

---

## Attack 3 — N5 (CRT local-to-global construction)

**ID:** N5 | **Adjusted EV:** 45 (T=5, I=9)
**Status vs prior slots:** NEW ANGLE. No prior slot attempted CRT-based construction.

```
OPEN GAP: Erdős 938 falsification axis — Local-to-global lifting
Source: erdosproblems.com/938 (N5 from EXP9 tree)
Domain: nt

For every modulus M and every admissible residue triple (r0, r1, r2) ∈ (ℤ/Mℤ)³
forming a 3-AP with r_i powerful mod M (in the sense of v_p(r_i) ≥ 2 for
every prime p | gcd(r_i, M)), there exists an INTEGER 3-AP (n0, n1, n2) of
CONSECUTIVE powerful numbers with n_i ≡ r_i (mod M).

theorem erdos_938_crt_lift (M : ℕ) (hM : 0 < M) (r : Fin 3 → ZMod M)
    (h_ap : r 1 - r 0 = r 2 - r 1)
    (h_powerful_mod : ∀ i, ∀ p : ℕ, p.Prime → (p : ZMod M) ∣ r i →
        ((p^2 : ℕ) : ZMod M) ∣ r i) :
    ∃ (n : Fin 3 → ℕ) (k : ℕ),
      (∀ i, (n i : ZMod M) = r i) ∧
      Set.IsAPOfLength ({n 0, n 1, n 2} : Set ℕ) 3 ∧
      {n 0, n 1, n 2} = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
                          Nat.nth Nat.Powerful (k+2)} := by sorry

Status: OPEN. RESOLUTION EITHER DIRECTION: if true, then since mod-72
admits 593 distinct AP residue triples, lifting yields ≥ 593 distinct
consecutive powerful 3-APs, falsifying E938 (giving infinitude). If false,
the failure of lifting at small M (e.g. M = 360) constrains the open
families.
```

**Plausibility:** 2/10 for full closure either way; 5/10 for `compiled_partial` with explicit small-M counterexamples (lifting fails at M = 360 already known to obstruct most residue classes — would yield a structural lemma). Real value: forces the AI to think about the CONSTRUCTIVE direction it has never been given.

---

## Attack 4 — R7 (5-smooth powerful S-unit)

**ID:** R7 | **Adjusted EV:** 42 (T=7, I=6)
**Status vs prior slots:** NEW ANGLE. No prior slot has restricted to S-unit subsets.

```
OPEN GAP: Erdős 938 sub-claim — 5-smooth consecutive powerful 3-APs
Source: erdosproblems.com/938 (R7 from EXP9 tree)
Domain: nt / diophantine

Let S = {2, 3, 5} and let A_S := {n ∈ ℕ | n powerful ∧ all primes dividing n
are in S}. Then A_S admits only finitely many consecutive powerful 3-APs
(within A_S, viewed as a subsequence of the powerful numbers).

theorem erdos_938_5smooth_finite :
    {P : Finset ℕ | Set.IsAPOfLength P.toSet 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)} ∧
      ∀ n ∈ P, ∀ p : ℕ, p.Prime → p ∣ n → p ∈ ({2, 3, 5} : Finset ℕ)}.Finite := by sorry

Status: OPEN, but Baker linear-forms-in-logs gives S-unit equation
finiteness UNCONDITIONALLY for {2,3,5}-units. The powerful constraint
reduces to a specific S-unit AP equation 2c^α = a^β + e^γ over S =
{2,3,5}-units. Evertse's theorem + Bilu-Hanrot effective bounds give
explicit finiteness.
```

**Plausibility:** 5/10. Mathlib has partial transcendental theory; Aristotle has demonstrated Baker-style reasoning in prior slots (slot 737 Sophie Germain divisor scan). The S-unit equation framework is well-developed; Aristotle could plausibly construct the finite list of 5-smooth powerful triples in AP (likely just {(1,4,16) — but wait, 16 not powerful via this S-smooth def... corrections needed inside}, etc.) and exhaust them.

---

## Attack 5 — C3 (squares + non-square-non-cube parametrization split)

**ID:** C3 | **Adjusted EV:** 45 (T=5, I=9)
**Status vs prior slots:** PARTIAL DUPLICATE — Erdős-Mollin-Walsh squares-only case has been touched in `yolo_w4a_e938_unconditional_extract` but not as an EXPLICIT decomposition target.

```
OPEN GAP: Erdős 938 decomposition — Square slice + non-square slice
Source: E938 (C3 from EXP9 tree)
Domain: nt

In the Golomb parametrization n = a²b³ with b squarefree, decompose
E938 into TWO sub-claims:
  X := only finitely many consecutive powerful 3-APs where all three
       have b = 1 (i.e., all three are perfect squares).
  Y := only finitely many consecutive powerful 3-APs where at least
       one term has b ≥ 2 (i.e., at least one is non-square powerful).

theorem erdos_938_squares_only_finite :
    {P : Finset ℕ | Set.IsAPOfLength P.toSet 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)} ∧
      ∀ n ∈ P, ∃ m, n = m^2}.Finite := by sorry

theorem erdos_938_nonsquare_some_finite :
    {P : Finset ℕ | Set.IsAPOfLength P.toSet 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)} ∧
      ∃ n ∈ P, ¬ ∃ m, n = m^2}.Finite := by sorry

Status: BOTH X and Y are OPEN. X is the Erdős-Mollin-Walsh squares case
specialized to consecutiveness; Y is the genuinely-new non-square slice.
Decomposition: E938 ⇔ X ∧ Y.
```

**Plausibility:** X: 3/10 (Erdős-Mollin-Walsh adjacent, has been chipped at for decades). Y: 2/10 (most of the difficulty is here). Real value of submitting as a DECOMPOSITION is that Aristotle's MCGS can attempt X via Mordell-curve enumeration and treat Y separately, instead of trying to prove the merged form.
