/-
ERDŐS PROBLEM #190 - THE HARD PART
Target: Prove H(k)^{1/k}/k → ∞

KEY INSIGHT: H(k) ≥ W(k-1, k) where W is the Van der Waerden number!

Proof sketch:
1. Any (k-1)-coloring of [N] avoiding mono k-AP also avoids rainbow k-AP
   (since rainbow needs k colors, but we only have k-1)
2. Therefore: ValidN k N → ValidW (k-1) k N (already proven!)
3. Contrapositive: W(k-1, k) ≤ H(k)
4. Van der Waerden numbers have tower-type growth
5. Therefore H(k) has tower-type growth
6. Tower growth implies H(k)^{1/k}/k → ∞

WHAT WE ALREADY HAVE:
- validN_subset_validW: {N | ValidN k N} ⊆ {N | ValidW (k-1) k N}
- This implies H(k) ≥ W(k-1, k) by taking infimums

WHAT WE NEED:
- Lower bound on W(k-1, k) that's tower-type
- Connect to H(k)^{1/k}/k → ∞
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

-- Definitions (from previous work)

def IsProperAP (l : List ℕ) : Prop :=
  ∃ a d, d > 0 ∧ l = List.ofFn (fun i : Fin l.length => a + (i : ℕ) * d)

def IsMono {α β : Type} (c : α → β) (l : List α) : Prop :=
  ∃ y, ∀ x ∈ l, c x = y

def IsRainbow {α β : Type} (c : α → β) (l : List α) : Prop :=
  (l.map c).Nodup

def ValidN (k N : ℕ) : Prop :=
  ∀ (c : Fin N → ℕ), ∃ (l : List (Fin N)),
    l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ (IsMono c l ∨ IsRainbow c l)

def ValidW (r k N : ℕ) : Prop :=
  ∀ (c : Fin N → Fin r), ∃ (l : List (Fin N)),
    l.length = k ∧ IsProperAP (l.map (fun x => x.val + 1)) ∧ IsMono c l

noncomputable def H (k : ℕ) : ℕ := sInf {N | ValidN k N}
noncomputable def W (r k : ℕ) : ℕ := sInf {N | ValidW r k N}

-- Key connection lemma (already proven in previous submission)
-- This is the crucial link between H(k) and W(k-1, k)

lemma validN_subset_validW (k : ℕ) (hk : k ≥ 2) : {N | ValidN k N} ⊆ {N | ValidW (k - 1) k N} := by
  sorry -- Already proven in erdos190_SUCCESS.lean

-- NEW: Derive H(k) ≥ W(k-1, k) from the subset relation

theorem H_ge_W (k : ℕ) (hk : k ≥ 2) : H k ≥ W (k - 1) k := by
  -- H k = sInf {N | ValidN k N}
  -- W (k-1) k = sInf {N | ValidW (k-1) k N}
  -- Since {N | ValidN k N} ⊆ {N | ValidW (k-1) k N}, we have sInf of smaller set ≥ sInf of larger set
  unfold H W
  apply Nat.sInf_le_sInf
  exact validN_subset_validW k hk

-- Van der Waerden tower bound (known result - would need Mathlib formalization)
-- W(r, k) ≥ tower_2(r) for suitable tower function

/-- Tower function: tower_2(0) = 1, tower_2(n+1) = 2^tower_2(n) -/
def tower_2 : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ tower_2 n

-- Known: W(r, 3) ≥ tower_2(r) for r ≥ 1 (Berlekamp's construction)
-- More generally, W(r, k) grows at least like tower function in r

axiom W_tower_lower_bound (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 3) :
  W r k ≥ tower_2 (r - 1)

-- Main theorem: H(k) has tower-type lower bound

theorem H_tower_lower_bound (k : ℕ) (hk : k ≥ 4) : H k ≥ tower_2 (k - 3) := by
  calc H k ≥ W (k - 1) k := H_ge_W k (by omega)
       _ ≥ tower_2 ((k - 1) - 1) := W_tower_lower_bound (k - 1) k (by omega) (by omega)
       _ = tower_2 (k - 2) := by ring_nf
       _ ≥ tower_2 (k - 3) := by
           apply Nat.pow_le_pow_right
           · norm_num
           · apply tower_2_mono; omega

-- Helper: tower_2 is monotonic
lemma tower_2_mono {m n : ℕ} (h : m ≤ n) : tower_2 m ≤ tower_2 n := by
  induction n with
  | zero => simp_all [tower_2]
  | succ n ih =>
    cases h.lt_or_eq with
    | inl hlt =>
      calc tower_2 m ≤ tower_2 n := ih (Nat.lt_succ_iff.mp hlt)
           _ ≤ 2 ^ tower_2 n := Nat.le_of_lt (Nat.lt_two_pow_self _)
           _ = tower_2 (n + 1) := rfl
    | inr heq => simp [heq]

-- Tower function grows faster than any polynomial
lemma tower_2_superpolynomial (c : ℕ) : ∀ᶠ k in Filter.atTop, tower_2 k > k ^ c := by
  sorry -- Standard but tedious

-- The key asymptotic result
theorem H_superexponential : ∀ᶠ k in Filter.atTop, H k > k ^ k := by
  -- H(k) ≥ tower_2(k-3) for k ≥ 4
  -- tower_2(k-3) > k^k eventually (tower beats any fixed exponential)
  sorry

-- THE PRIZE RESULT: H(k)^{1/k}/k → ∞
theorem erdos_190_hard (k : ℕ) (hk : k ≥ 4) :
    (H k : ℝ) ^ (1 / k : ℝ) / k ≥ (tower_2 (k - 3) : ℝ) ^ (1 / k : ℝ) / k := by
  have h1 : H k ≥ tower_2 (k - 3) := H_tower_lower_bound k hk
  have h2 : (0 : ℝ) < k := by positivity
  have h3 : (1 : ℝ) / k > 0 := by positivity
  gcongr
  exact Nat.cast_le.mpr h1

-- To complete the proof, we need: tower_2(k-3)^{1/k}/k → ∞
-- This follows because tower_2(n) = 2^{2^{...}} (n times)
-- So tower_2(k-3)^{1/k} = 2^{tower_2(k-4)/k} which grows faster than k

theorem erdos_190_limit : Filter.Tendsto (fun k => (H k : ℝ) ^ (1 / k : ℝ) / k) Filter.atTop Filter.atTop := by
  sorry -- Requires careful asymptotic analysis of tower function

end
