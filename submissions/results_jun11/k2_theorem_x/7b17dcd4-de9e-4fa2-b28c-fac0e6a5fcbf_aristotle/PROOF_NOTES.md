# Erdős 124 — the `(3,4,7)` case for `k = 2`: reduction and open kernel

**Target.** With `N₀ := 3 982 888`, every integer `n > N₀` lies in
`R := 3²·B₃ + 4²·B₄ + 7²·B₇`, i.e. `n` is a sum of distinct powers `3^j (j≥2)`, distinct
powers `4^j (j≥2)`, and distinct powers `7^j (j≥2)`.

Equivalently (digit recursion `d^k·B_d = {0,d^k}+d^{k+1}·B_d`), `R` is exactly the set of
**subset sums of the atom set**
```
A = { 3^j : j ≥ 2 } ∪ { 4^j : j ≥ 2 } ∪ { 7^j : j ≥ 2 },
```
each atom used at most once. (The atom values are pairwise distinct, so a subset sum is a
genuine choice of distinct exponents per base.) The task is to show the subset-sum set of `A`
contains every `n > N₀`.

This document records a **complete elementary reduction** of the tail theorem to a single
arithmetic inequality (the *gap lemma*), and explains why that inequality is the genuinely
open kernel.

---

## 1. Symmetry of finite subset-sum sets

For a finite atom set `S ⊆ A` with total `Σ := Σ_{a∈S} a`, let `Reach(S) ⊆ [0,Σ]` be its
subset-sum set. Taking complements of subsets gives the exact **symmetry**
```
n ∈ Reach(S)  ⟺  Σ − n ∈ Reach(S).
```
Hence the set of *non-reachable* points in `[0,Σ]` is symmetric about `Σ/2`. In particular,
if `N₀` is the largest non-reachable point in the lower half, its mirror `Σ − N₀` is the
smallest non-reachable point in the upper half, and the **contiguous middle**
`(N₀, Σ − N₀)` is gap-free.

For `V ≥ 0` write `S_V := { a ∈ A : a ≤ V }` and `Σ_V := Σ_{a∈S_V} a`. (Atoms `> V` cannot
participate in any sum `≤ V`, so for `n ≤ V`, `n ∈ Reach(S_V) ⟺ n ∈ Reach(A)`.)

---

## 2. Symmetric interval-doubling induction

**Invariant `I(V)`:** the interval `(N₀, Σ_V − N₀)` is entirely contained in `Reach(S_V)`.

**Step.** Suppose `I(V)` holds and `v` is the next atom above `V` (so `S_{v} = S_V ∪ {v}`,
`Σ_{v} = Σ_V + v`). Then
```
Reach(S_v) = Reach(S_V) ∪ (Reach(S_V) + v) ⊇ M ∪ (M + v),
```
where `M := (N₀, Σ_V − N₀)`. Now `M + v = (N₀ + v, Σ_v − N₀)`. The two open intervals `M`
and `M + v` together cover `(N₀, Σ_v − N₀)` **iff** they overlap or abut, i.e. iff
```
        N₀ + v ≤ Σ_V − N₀      ⟺      v ≤ Σ_V − 2·N₀.        (★)
```
Under `(★)`, `I(v)` holds. Note this uses the *full* symmetric width `Σ_V − N₀` of the
contiguous middle — the naive "single growing interval from `N₀`" stalls immediately, which
is why the symmetry in §1 is essential.

**Conclusion.** If the base invariant `I(V₀)` holds and `(★)` holds for every atom `v > V₀`,
then `I(V)` holds for all `V`, and `Σ_V → ∞`, so every `n > N₀` is in `Reach(A)`. ∎ (modulo
the base and `(★)`)

---

## 3. The base case (machine-verified)

Take `V₀ = 3¹⁵ = 14 348 907`. Then
```
S_{V₀} = { 3²..3¹⁵, 4²..4¹¹, 7²..7⁸ }   (31 atoms),   Σ_{V₀} = 33 841 349.
```
`I(V₀)` is the statement that `(N₀, Σ_{V₀} − N₀) = (3 982 888, 29 858 461)` is gap-free,
i.e. **every `n ∈ [3 982 889, 29 858 460]` is a subset sum of `S_{V₀}`.**

This is a finite check and is **verified** in `RequestProject/Main.lean` as
`baseCovered31_true` (a `native_decide` over a 34 M-entry reachability bitset, using only
the `Lean.ofReduceBool` / `Lean.trustCompiler` axioms).

*Why `3¹⁵`?* With the smaller base `S_{8 944 672}` (atoms `≤ 4¹¹`) the contiguous middle only
reaches `15 509 553`, and the next atom `3¹⁵` violates `(★)`. Including `3¹⁵` in the base is
exactly what is needed: the first atom above the base is then `4¹² = 16 777 216`, which (and
every atom beyond) satisfies `(★)` — see §4.

---

## 4. The gap lemma `(★)` — the open kernel

`(★)` says: for every atom `v > 3¹⁵`,
```
        atomSum(<v) := Σ_{a ∈ A, a < v} a  ≥  v + 2·N₀  = v + 7 965 776.        (GAP)
```

**Verified range.** `(GAP)` holds for every atom `v ≤ 10³⁰` (theorem `gapLemma_verified_1e30`),
and in fact computations to `10¹²⁰` show the margin `atomSum(<v) − v − 2N₀` is always
positive, with global minimum `+2 299 182` attained at the *small* atom `v = 7⁹ = 40 353 607`;
for all atoms beyond `≈ 5·10⁷` the margin exceeds `5·10⁷`.

**Why it is true but hard.** Writing `c_d(v)` for the smallest power of base `d` that is `≥ v`,
one has the exact identity
```
atomSum(<v) = Σ_{d∈{3,4,7}} (c_d(v) − d²)/(d − 1),
```
with `c_d(v) = v` for the base of which `v` is a power and `c_d(v) > v` otherwise. The
elementary bound `c_d(v) ≥ v` gives only
```
atomSum(<v) ≥ v − 18,
```
short of `(GAP)` by `2N₀ + 18`. The missing slack is
```
Σ_{d ≠ base(v)} (c_d(v) − v)/(d − 1),
```
the (weighted) distances from `v` up to the next powers of the *other two* bases. This is
small precisely at **power near-coincidences** `3^p ≈ 4^q ≈ 7^r`: there `atomSum(<v)/v → 1`
and the slack could in principle drop below `2N₀`. Ruling this out for all large `v`
requires a *lower* bound on how close distinct powers of `3, 4, 7` can be — an **effective
linear-form-in-logarithms** estimate (Mignotte–Waldschmidt, *Acta Arith.* 53 (1989)). The
mere integrality `c_d(v) − v ≥ 1` is far too weak, and no elementary irrationality-measure
argument supplies an *effective* bound. This is the same machinery `BEGL96` invoked already
for the `k = 1` largest non-representable value `581`.

Such effective transcendence bounds are **not present in Mathlib** and cannot be derived
elementarily, which is why the full tail theorem is left as `sorry`. The reduction above
shows that `(GAP)` for all atoms `v > 3¹⁵` is *equivalent in difficulty* to the original
problem: everything else (symmetry, the doubling induction, and the base case) is elementary
and, for the base, machine-verified.

---

## 5. Summary of the dependency

```
  erdos124_347_k2  (OPEN)
        ⇑  (elementary: §1 symmetry  +  §2 interval-doubling induction)
  base case I(3¹⁵)                 gap lemma (GAP) for all atoms v > 3¹⁵
   ⇑ native_decide                  ⇑ verified ≤ 10³⁰; general case needs
  baseCovered31_true                 Mignotte–Waldschmidt  ← the open kernel
```
