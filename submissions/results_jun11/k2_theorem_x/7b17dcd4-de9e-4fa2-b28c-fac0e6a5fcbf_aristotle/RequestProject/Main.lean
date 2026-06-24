import Mathlib

open scoped BigOperators
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-!
# Erdős problem 124 — the `(3,4,7)` case for `k = 2`

`sumsOfDistinctPowers d k` is the set of natural numbers obtainable as a sum of distinct
powers `d^j` with all exponents `j ≥ k`.  Equivalently this is `d^k · B_d`, where `B_d` is
the set of integers whose base-`d` representation uses only digits `0,1`.

The target statement (`erdos124_347_k2`) asserts that the pointwise sumset
`3²·B₃ + 4²·B₄ + 7²·B₇` is cofinite, with every integer `> 3 982 888` representable.

## Status

This is an **open** problem.  This file records:

* the exact formal statement (`erdos124_347_k2`), currently left as `sorry`;
* the two genuinely machine-verified computational facts that the proof reduces to
  (`baseCovered31_true` and `gapLemma_verified_1e30`), both proven by `native_decide`
  with only the standard `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.

The full reduction is documented in `PROOF_NOTES.md`.  In brief: the tail theorem follows
from an elementary *symmetric interval-doubling* induction once one knows the **gap lemma**

> for every atom `v = 3^e, 4^e, 7^e` with `v > 14 348 907 (= 3¹⁵)`,
> the sum of all atoms strictly below `v` is `≥ v + 2·3 982 888`.

The gap lemma is true and verified here for all atoms up to `10³⁰` (in fact it holds with a
positive margin, minimised at `7⁹`), but a proof for *all* atoms must control power
near-coincidences (`3^p ≈ 4^q ≈ 7^r`) and hence requires effective lower bounds for linear
forms in logarithms (Mignotte–Waldschmidt), which are not available elementarily nor in
Mathlib.  This is the genuinely open kernel of the problem.
-/

/-- The set of naturals that are a sum of distinct powers `d^j` with every exponent `j ≥ k`. -/
def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  { n | ∃ s : Finset ℕ, (∀ j ∈ s, k ≤ j) ∧ n = ∑ j ∈ s, d ^ j }

/-! ## Verified computational facts underpinning the reduction -/

/-- A bitset subset-sum reachability pass: `reachBA bound atoms` has a `1` at index `k`
iff `k ≤ bound` is a sum of a sub-multiset of `atoms`. -/
def reachBA (bound : ℕ) (atoms : List ℕ) : ByteArray := Id.run do
  let mut arr := ByteArray.mk (Array.replicate (bound + 1) (0 : UInt8))
  arr := arr.set! 0 1
  for a in atoms do
    let mut k := bound
    while k ≥ a do
      if arr.get! (k - a) == 1 then arr := arr.set! k 1
      k := k - 1
  return arr

/-- The base atom set: all atoms `≤ 3¹⁵ = 14 348 907`, i.e. `3²..3¹⁵, 4²..4¹¹, 7²..7⁸`
(31 atoms, total sum `33 841 349`). -/
def baseAtoms31 : List ℕ :=
  (List.range' 2 14).map (fun e => 3 ^ e) ++
  (List.range' 2 10).map (fun e => 4 ^ e) ++
  (List.range' 2 7).map  (fun e => 7 ^ e)

/-- Base-coverage check: every `n` in `[3 982 889, 29 858 460]` is a subset sum of the base
atoms.  Here `29 858 460 = 33 841 349 − 3 982 889 = Σ_base − N₀ − 1`. -/
def baseCovered31 : Bool := Id.run do
  let arr := reachBA 33841349 baseAtoms31
  let mut ok := true
  let mut k := 3982889
  while k ≤ 29858460 do
    if arr.get! k != 1 then ok := false
    k := k + 1
  return ok

/-- **Verified base coverage.**  With atoms `≤ 3¹⁵`, the symmetric middle interval
`(N₀, Σ_base − N₀) = (3 982 888, 29 858 461)` is gap-free. -/
theorem baseCovered31_true : baseCovered31 = true := by native_decide

/-- Gap-lemma check up to a cap: for every atom `v` (= power of 3, 4 or 7, exponent `≥ 2`)
with `v ≤ cap` and `v > 3¹⁵`, the sum of all atoms strictly below `v` is `≥ v + 2·N₀`. -/
def gapOK (cap : ℕ) : Bool := Id.run do
  let atoms := (((List.range' 2 80).map (fun e => 3 ^ e) ++
                 (List.range' 2 80).map (fun e => 4 ^ e) ++
                 (List.range' 2 80).map (fun e => 7 ^ e)).filter (fun a => a ≤ cap)).mergeSort (· ≤ ·)
  let mut acc : ℕ := 0
  let mut ok := true
  for v in atoms do
    if v > 14348907 then
      if !(acc ≥ v + 7965776) then ok := false
    acc := acc + v
  return ok

/-- **Gap lemma, verified for all atoms `≤ 10³⁰`.**  (The margin is minimised at `7⁹`, with
value `+2 299 182 > 0`.)  A proof for *all* atoms requires effective linear-forms-in-logs
bounds; see `PROOF_NOTES.md`. -/
theorem gapLemma_verified_1e30 : gapOK (10 ^ 30) = true := by native_decide

/-! ## The target statement -/

/-- **Erdős problem 124, the (3,4,7) case for `k = 2`** (OPEN).

Every integer `n > 3 982 888` is `a + b + c` with `a` a sum of distinct powers `3^j`
(`j ≥ 2`), `b` a sum of distinct powers `4^j` (`j ≥ 2`), and `c` a sum of distinct powers
`7^j` (`j ≥ 2`).

This is left as `sorry`: the statement reduces (see `PROOF_NOTES.md`) to the *gap lemma*
above, whose proof for arbitrarily large power near-coincidences requires effective bounds
on linear forms in logarithms and is beyond current elementary / Mathlib means. -/
theorem erdos124_347_k2 : ∀ n : ℕ, 3982888 < n →
    n ∈ sumsOfDistinctPowers 3 2 + sumsOfDistinctPowers 4 2 + sumsOfDistinctPowers 7 2 := by
  sorry
