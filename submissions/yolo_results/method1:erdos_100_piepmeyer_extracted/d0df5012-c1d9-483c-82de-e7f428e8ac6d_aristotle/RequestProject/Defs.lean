import Mathlib

/-! # Erdős Problem 100 (Piepmeyer Configuration)

We construct 9 points in ℝ² such that:
- Any two distinct pairwise distances differ by at least 1
- The diameter is less than 5
-/

set_option maxHeartbeats 800000

noncomputable section

open Real Finset

/-- Euclidean plane -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- A Finset of points has the "separated distances" property if any two distinct
pairwise distances differ by at least 1. -/
def DistancesSeparated (A : Finset E2) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    dist a b ≠ dist c d → |dist a b - dist c d| ≥ 1

/-- Create a point in EuclideanSpace from coordinates -/
def mkPt (x y : ℝ) : E2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![x, y]

@[simp] lemma mkPt_apply_0 (x y : ℝ) : (mkPt x y) 0 = x := by
  simp [mkPt, WithLp.equiv]

@[simp] lemma mkPt_apply_1 (x y : ℝ) : (mkPt x y) 1 = y := by
  simp [mkPt, WithLp.equiv]

lemma dist_sq_mkPt (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mkPt x₁ y₁) (mkPt x₂ y₂) ^ 2 = (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  have h := EuclideanSpace.dist_eq (mkPt x₁ y₁) (mkPt x₂ y₂)
  rw [h, sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

lemma mkPt_ne_of_fst_ne {x₁ y₁ x₂ y₂ : ℝ} (h : x₁ ≠ x₂) :
    mkPt x₁ y₁ ≠ mkPt x₂ y₂ := by
  intro heq
  apply h
  have h0 : (mkPt x₁ y₁) 0 = (mkPt x₂ y₂) 0 := by rw [heq]
  simp at h0
  exact h0

lemma mkPt_ne_of_snd_ne {x₁ y₁ x₂ y₂ : ℝ} (h : y₁ ≠ y₂) :
    mkPt x₁ y₁ ≠ mkPt x₂ y₂ := by
  intro heq
  apply h
  have h1 : (mkPt x₁ y₁) 1 = (mkPt x₂ y₂) 1 := by rw [heq]
  simp at h1
  exact h1

-- Key constants
def s2 : ℝ := √2
def s3 : ℝ := √3
def α  : ℝ := √(2 - s3)

-- Derived constants
def t₀ : ℝ := (1 + s2) * α
def r₀ : ℝ := t₀ / s3
def R₀ : ℝ := r₀ + t₀
def S₀ : ℝ := R₀ + r₀

-- The 9 points
def P : Fin 9 → E2 := fun i => match i with
  | ⟨0, _⟩ => mkPt 0 r₀
  | ⟨1, _⟩ => mkPt (-(r₀ * s3 / 2)) (-(r₀ / 2))
  | ⟨2, _⟩ => mkPt (r₀ * s3 / 2) (-(r₀ / 2))
  | ⟨3, _⟩ => mkPt 0 R₀
  | ⟨4, _⟩ => mkPt (-(R₀ * s3 / 2)) (-(R₀ / 2))
  | ⟨5, _⟩ => mkPt (R₀ * s3 / 2) (-(R₀ / 2))
  | ⟨6, _⟩ => mkPt 0 (-S₀)
  | ⟨7, _⟩ => mkPt (S₀ * s3 / 2) (S₀ / 2)
  | ⟨8, _⟩ => mkPt (-(S₀ * s3 / 2)) (S₀ / 2)

-- The Finset
def A₀ : Finset E2 := image P univ

-- Squared distance values
def D₁ : ℝ := (3 + 2 * s2) * (2 - s3)
def D₂ : ℝ := 3 + 2 * s2
def D₃ : ℝ := 6 + 4 * s2
def D₄ : ℝ := (3 + 2 * s2) * (2 + s3)

end

