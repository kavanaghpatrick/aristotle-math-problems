import Mathlib

open scoped BigOperators
open Finset Nat

set_option maxHeartbeats 800000

/-!
# Erdős Problem 672 (k=4, l=3)

For any positive integers n and d with gcd(n, d) = 1, the product
n(n+d)(n+2d)(n+3d) is never a perfect cube.

## Mathematical background

This is a deep result in Diophantine equations, proved by
Hajdu-Tengely-Tijdeman (Publ. Math. Debrecen, 2009) and independently
by Győry-Hajdu-Pintér (Compos. Math., 2009).

### Proof outline (Hajdu-Tengely-Tijdeman)

1. **Coprimality analysis** (`prime_divides_at_most_one`): For primes p ≥ 5,
   p divides at most one of the four AP terms n, n+d, n+2d, n+3d.
   This follows from gcd(n,d) = 1 and the fact that if p divides two
   terms n+id and n+jd, then p | (j-i)d, but p ≥ 5 > |j-i| ≥ 1,
   so p | d, then p | n, contradicting gcd(n,d) = 1.

2. **Cubefree decomposition**: Each term factors as 2^a · 3^b · c³ with
   (a,b) ∈ {0,1,2}², and the c values are pairwise coprime and coprime to 6.

3. **Ternary equation reduction**: The AP condition (consecutive differences
   equal d) yields a finite list of ternary cubic equations
   A·x³ + B·y³ = C·z³ with {2,3}-smooth coefficients.

4. **Resolution via Frey curves**: Each ternary equation is resolved using
   Hellegouarch-Frey elliptic curves, the modularity theorem (Wiles-Taylor),
   and level-lowering (Ribet-Bennett-Skinner). The resulting modular form
   spaces S₂(Γ₀(N)) are verified to be trivial for all relevant levels N.

### Status in Mathlib

Steps 3-4 require deep arithmetic geometry (Frey curves, modularity theorem,
modular forms computation) not currently available in Mathlib. The formalized
helper lemmas below cover step 1 and the algebraic identity underlying the
approach. The main theorem remains sorry'd pending formalization of the
required machinery.

### Key identity

The algebraic identity n(n+d)(n+2d)(n+3d) + d⁴ = (n²+3nd+d²)²
reduces the problem to the Mordell-type equation z² = y³ + d⁴.
-/

-- ============================================================================
-- Helper lemmas (all proved)
-- ============================================================================

/-- The product ∏ᵢ₌₀³ (n + i·d) equals n·(n+d)·(n+2d)·(n+3d). -/
lemma prod_range_four (n d : ℕ) :
    (∏ i ∈ Finset.range 4, (n + i * d)) = n * (n + d) * (n + 2 * d) * (n + 3 * d) := by
  exact Finset.prod_range_succ _ _ |> Eq.trans <| by rw [ Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one ] ; ring;

/-- Key algebraic identity over ℤ: the product plus d⁴ is a perfect square. -/
lemma product_identity (n d : ℤ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) + d ^ 4 = (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 := by
  ring

/-- Consecutive AP terms n+i·d and n+(i+1)·d are coprime when gcd(n,d) = 1. -/
lemma coprime_consecutive_ap (n d : ℕ) (h : n.gcd d = 1) (i : ℕ) :
    (n + i * d).gcd (n + (i + 1) * d) = 1 := by
  norm_num [ ( by ring : n + ( i + 1 ) * d = n + i * d + d ) ];
  assumption

/-- For primes p ≥ 5, p divides at most one of the four AP terms.
    This is the key coprimality result needed for the cubefree decomposition. -/
lemma prime_divides_at_most_one (n d : ℕ) (h : n.gcd d = 1) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (i j : Fin 4) (hi : p ∣ (n + i * d)) (hj : p ∣ (n + j * d)) : i = j := by
  simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Fin.ext_iff ];
  haveI := Fact.mk hp; simp_all +decide [ ← eq_sub_iff_add_eq ] ;
  exact Nat.mod_eq_of_lt ( show ( i : ℕ ) < p by linarith [ Fin.is_lt i ] ) ▸ Nat.mod_eq_of_lt ( show ( j : ℕ ) < p by linarith [ Fin.is_lt j ] ) ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using hj.resolve_right ( by rw [ ZMod.natCast_eq_zero_iff ] ; intro H; have := Nat.dvd_gcd ( show p ∣ n from by rw [ ← ZMod.natCast_eq_zero_iff ] at *; aesop ) H; aesop ) ;

-- ============================================================================
-- Modular obstructions (proved) — partial results towards the Thue equation
-- ============================================================================

/-- Cubes modulo 9 are exactly {0, 1, 8}. -/
lemma cubes_mod_9 : ∀ x : ZMod 9, x ^ 3 ∈ ({0, 1, 8} : Finset (ZMod 9)) := by decide

/-- If α ≡ 1 mod 3 (i.e., α mod 9 ∈ {1,4,7}), then 2α³+1 is not a cube mod 9.
    This eliminates one-third of residue classes for the Thue equation β³ = 2α³+1. -/
lemma thue_mod9_obstruction :
    ∀ α : ZMod 9, α ∈ ({1, 4, 7} : Finset (ZMod 9)) →
    ∀ β : ZMod 9, β ^ 3 ≠ 2 * α ^ 3 + 1 := by decide

/-- If α ≡ 1, 2, or 4 mod 7, then 2α³+1 is not a cube mod 7.
    This eliminates additional residue classes for the Thue equation. -/
lemma thue_mod7_obstruction :
    ∀ α : ZMod 7, α ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    ∀ β : ZMod 7, β ^ 3 ≠ 2 * α ^ 3 + 1 := by decide

-- ============================================================================
-- Key intermediate results (stated, sorry'd)
-- ============================================================================

/-- The Thue equation β³ - 2α³ = 1 has no solution with α > 0.
    This is a classical result (Euler, 1770), provable via descent in ℤ[∛2].
    It is needed for the fully coprime case of the main theorem.

    The modular obstructions above eliminate α ≡ 1 mod 3 (via mod 9)
    and α ≡ 1, 2, 4 mod 7. The remaining cases require deeper methods
    (infinite descent or Baker's theorem on linear forms in logarithms). -/
lemma thue_cube_minus_2cube_eq_1 (α β : ℕ) (hα : α > 0) :
    β ^ 3 ≠ 2 * α ^ 3 + 1 := by
  sorry

/-- No three distinct positive cubes are in arithmetic progression.
    Equivalently, x³ + z³ = 2y³ implies x = z (for positive integers).
    This follows from `thue_cube_minus_2cube_eq_1` and its variant. -/
theorem no_three_cubes_in_ap (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x ^ 3 + z ^ 3 = 2 * y ^ 3) : x = z := by
  sorry

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- **Erdős Problem 672 (k=4, l=3)**: For any positive integers n and d with
    gcd(n, d) = 1, the product n(n+d)(n+2d)(n+3d) is never a perfect cube.

    This is a theorem of Hajdu-Tengely-Tijdeman (2009) and Győry-Hajdu-Pintér (2009).
    The proof requires Frey curves and the modularity theorem, which are not
    currently available in Mathlib. See the module docstring for the full proof outline. -/
theorem erdos_672_k4_l3 :
    ∀ n d : ℕ, n > 0 → d > 0 → n.gcd d = 1 →
    ¬ ∃ y : ℕ, (∏ i ∈ Finset.range 4, (n + i * d)) = y ^ 3 := by
  sorry
