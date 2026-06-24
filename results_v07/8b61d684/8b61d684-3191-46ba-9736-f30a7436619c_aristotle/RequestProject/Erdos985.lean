import Mathlib

/-!
# Erdős Problem 985 — Primitive root smaller than p

For every odd prime p, there exists a prime q < p
that is a primitive root modulo p.

**Status**: OPEN. This is related to Artin's conjecture on primitive roots.
Heath-Brown (1986) proved that at least one of {2, 3, 5} is a primitive root
for infinitely many primes, but the full conjecture that *every* odd prime p
admits a prime primitive root smaller than p remains open.

The statement says that in `ZMod p`, the element `q` (cast from `ℕ`) has
multiplicative order exactly `p - 1`, which is the definition of being a
primitive root modulo `p`.
-/

/-- Every odd prime has a primitive root in `{1, …, p-1}`. -/
lemma exists_primitive_root_lt (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ g : ℕ, 1 < g ∧ g < p ∧ orderOf (g : ZMod p) = p - 1 := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  use g.val.val
  simp_all +decide [orderOf_units]
  refine' ⟨_, _, _⟩ <;> try exact ZMod.val_lt _
  · by_cases hg1 : g.val.val = 1
    · have h_order : orderOf (g : ZMod p) = p - 1 := by
        rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg]
        simp +decide [Nat.totient_prime hp]
      rcases p with (_ | _ | p) <;> simp_all +decide
      rw [show (g : ZMod (p + 2)) = 1 by exact ZMod.val_injective _ hg1] at h_order
      aesop
    · exact lt_of_le_of_ne
        (Nat.pos_of_ne_zero fun h => by simp_all +decide) (Ne.symm hg1)
  · rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    simp +decide [Nat.totient_prime hp]

/-- **Erdős Problem 985**: For every odd prime `p`, there exists a prime `q < p` that is a
primitive root modulo `p`, i.e., `orderOf (q : ZMod p) = p - 1`. -/
theorem erdos_985 :
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∃ q : ℕ, q.Prime ∧ q < p ∧
    orderOf (q : ZMod p) = p - 1 := by sorry
