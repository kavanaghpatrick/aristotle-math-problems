import Mathlib

/-!
# Erdős Problem 273 — Covering system with p-1 moduli (p ≥ 5)

**Problem**: Is there a covering system where every modulus has the form `p - 1`
for some prime `p ≥ 5`?

**Status**: OPEN (in the sense of distinct moduli). The `p ≥ 3` case is solved (true).
The `p ≥ 5` constraint removes modulus 2 (from `p = 3`).

## Proof strategy

As formalized below (without a distinctness requirement on moduli), a trivial
covering system works: take `{0 mod 4, 1 mod 4, 2 mod 4, 3 mod 4}` where
`4 = 5 - 1` and `5` is prime with `5 ≥ 5`.

**Note**: The *interesting* open problem requires the moduli to be *distinct*.
The formalization below does not impose that constraint, making the problem
solvable by this simple construction.
-/

/-- A strict covering system of a commutative ring R is a finite collection of
residue classes (cosets of ideals) that cover every element of R, with each
modulus being a nontrivial proper ideal. -/
structure StrictCoveringSystem (R : Type) [CommRing R] where
  /-- The (finite, nonempty) index type -/
  ι : Type
  [fin : Fintype ι]
  [nonempty : Nonempty ι]
  /-- The modulus for each residue class, given as an ideal -/
  moduli : ι → Ideal R
  /-- The residue (offset) for each class -/
  residues : ι → R
  /-- Each modulus is a proper ideal (not the whole ring) -/
  moduli_ne_top : ∀ i, moduli i ≠ ⊤
  /-- Each modulus is nontrivial (not zero) -/
  moduli_ne_bot : ∀ i, moduli i ≠ ⊥
  /-- The residue classes cover every element -/
  covers : ∀ x : R, ∃ i, x - residues i ∈ moduli i

attribute [instance] StrictCoveringSystem.fin StrictCoveringSystem.nonempty

/-
PROBLEM
**Erdős Problem 273**: There exists a covering system of ℤ where every modulus
has the form `p - 1` for some prime `p ≥ 5`.

Proved using the trivial covering system `{0 mod 4, 1 mod 4, 2 mod 4, 3 mod 4}`
where `4 = 5 - 1` and `5` is prime.

PROVIDED SOLUTION
Construct the trivial covering system {0 mod 4, 1 mod 4, 2 mod 4, 3 mod 4}. Use ι := Fin 4, moduli := constant function returning Ideal.span {(4 : ℤ)}, residues i := (i : ℤ).

For moduli_ne_top: use Ideal.span_singleton_eq_top and decide that 4 is not a unit.
For moduli_ne_bot: use Ideal.span_singleton_eq_bot and decide that 4 ≠ 0.
For covers: given x : ℤ, use i = ⟨(x % 4).toNat, ...⟩. Then x - i is divisible by 4, so x - i ∈ Ideal.span {4}. Use Ideal.mem_span_singleton and Int.emod_add_ediv.

For the second part: for all i, use p = 5, which is prime, 5 ≥ 5, and 5 - 1 = 4. Show Ideal.span {↑(5 - 1 : ℕ)} = Ideal.span {(4 : ℤ)} by norm_num.
-/
theorem erdos_273 :
    ∃ c : StrictCoveringSystem ℤ, ∀ i,
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
    c.moduli i = Ideal.span {↑(p - 1)} := by
      -- Define the covering system with moduli $p - 1$ for primes $p \geq 5$.
      use ⟨Fin 4, fun _ => Ideal.span {(4 : ℤ)}, fun i => i.val, by
        simp +decide [ Ideal.span_singleton_eq_top ], by
        norm_num [ Ideal.span_singleton_eq_bot ], by
        intro x
        use ⟨Int.toNat (x % 4), by
          grind +ring⟩
        generalize_proofs at *;
        erw [ Ideal.mem_span_singleton ] ; norm_num; omega;⟩
      generalize_proofs at *;
      exact fun i => ⟨ 5, by norm_num, by norm_num, rfl ⟩