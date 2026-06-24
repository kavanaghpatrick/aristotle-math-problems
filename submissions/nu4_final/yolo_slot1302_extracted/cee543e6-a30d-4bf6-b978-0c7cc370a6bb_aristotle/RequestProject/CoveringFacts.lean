import Mathlib.Tactic

/-! ## Computational facts for the Selfridge covering system -/

private abbrev k₀ : ℕ := 2931991
private abbrev P : ℕ := 5592405

/-- 2^24 - 1 is divisible by each Selfridge prime -/
lemma dvd_two_pow_24_sub_one_3 : 3 ∣ (2 ^ 24 - 1 : ℤ) := by norm_num
lemma dvd_two_pow_24_sub_one_5 : 5 ∣ (2 ^ 24 - 1 : ℤ) := by norm_num
lemma dvd_two_pow_24_sub_one_7 : 7 ∣ (2 ^ 24 - 1 : ℤ) := by norm_num
lemma dvd_two_pow_24_sub_one_13 : 13 ∣ (2 ^ 24 - 1 : ℤ) := by norm_num
lemma dvd_two_pow_24_sub_one_17 : 17 ∣ (2 ^ 24 - 1 : ℤ) := by norm_num
lemma dvd_two_pow_24_sub_one_241 : 241 ∣ (2 ^ 24 - 1 : ℤ) := by norm_num

/-- Each Selfridge prime divides P -/
lemma selfridge_dvd_P_3 : 3 ∣ P := by norm_num
lemma selfridge_dvd_P_5 : 5 ∣ P := by norm_num
lemma selfridge_dvd_P_7 : 7 ∣ P := by norm_num
lemma selfridge_dvd_P_13 : 13 ∣ P := by norm_num
lemma selfridge_dvd_P_17 : 17 ∣ P := by norm_num
lemma selfridge_dvd_P_241 : 241 ∣ P := by norm_num

/-- Covering base cases: for each r mod 24, a Selfridge prime divides k₀ * 2^r + 1 -/
lemma cover_r0 : 7 ∣ (k₀ * 2 ^ 0 + 1) := by norm_num
lemma cover_r1 : 3 ∣ (k₀ * 2 ^ 1 + 1) := by norm_num
lemma cover_r2 : 5 ∣ (k₀ * 2 ^ 2 + 1) := by norm_num
lemma cover_r3 : 3 ∣ (k₀ * 2 ^ 3 + 1) := by norm_num
lemma cover_r4 : 17 ∣ (k₀ * 2 ^ 4 + 1) := by norm_num
lemma cover_r5 : 3 ∣ (k₀ * 2 ^ 5 + 1) := by norm_num
lemma cover_r6 : 5 ∣ (k₀ * 2 ^ 6 + 1) := by norm_num
lemma cover_r7 : 3 ∣ (k₀ * 2 ^ 7 + 1) := by norm_num
lemma cover_r8 : 13 ∣ (k₀ * 2 ^ 8 + 1) := by norm_num
lemma cover_r9 : 3 ∣ (k₀ * 2 ^ 9 + 1) := by norm_num
lemma cover_r10 : 5 ∣ (k₀ * 2 ^ 10 + 1) := by norm_num
lemma cover_r11 : 3 ∣ (k₀ * 2 ^ 11 + 1) := by norm_num
lemma cover_r12 : 7 ∣ (k₀ * 2 ^ 12 + 1) := by norm_num
lemma cover_r13 : 3 ∣ (k₀ * 2 ^ 13 + 1) := by norm_num
lemma cover_r14 : 5 ∣ (k₀ * 2 ^ 14 + 1) := by norm_num
lemma cover_r15 : 3 ∣ (k₀ * 2 ^ 15 + 1) := by norm_num
lemma cover_r16 : 241 ∣ (k₀ * 2 ^ 16 + 1) := by norm_num
lemma cover_r17 : 3 ∣ (k₀ * 2 ^ 17 + 1) := by norm_num
lemma cover_r18 : 5 ∣ (k₀ * 2 ^ 18 + 1) := by norm_num
lemma cover_r19 : 3 ∣ (k₀ * 2 ^ 19 + 1) := by norm_num
lemma cover_r20 : 13 ∣ (k₀ * 2 ^ 20 + 1) := by norm_num
lemma cover_r21 : 3 ∣ (k₀ * 2 ^ 21 + 1) := by norm_num
lemma cover_r22 : 5 ∣ (k₀ * 2 ^ 22 + 1) := by norm_num
lemma cover_r23 : 3 ∣ (k₀ * 2 ^ 23 + 1) := by norm_num

/-- The covering: for each r in {0,...,23}, a covering prime divides k₀ * 2^r + 1 -/
lemma covering_for_residue (r : Fin 24) :
    ∃ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), p ∣ (k₀ * 2 ^ r.val + 1) := by
  fin_cases r <;> simp only [] <;> first
  | exact ⟨7, by simp, cover_r0⟩
  | exact ⟨3, by simp, cover_r1⟩
  | exact ⟨5, by simp, cover_r2⟩
  | exact ⟨3, by simp, cover_r3⟩
  | exact ⟨17, by simp, cover_r4⟩
  | exact ⟨3, by simp, cover_r5⟩
  | exact ⟨5, by simp, cover_r6⟩
  | exact ⟨3, by simp, cover_r7⟩
  | exact ⟨13, by simp, cover_r8⟩
  | exact ⟨3, by simp, cover_r9⟩
  | exact ⟨5, by simp, cover_r10⟩
  | exact ⟨3, by simp, cover_r11⟩
  | exact ⟨7, by simp, cover_r12⟩
  | exact ⟨3, by simp, cover_r13⟩
  | exact ⟨5, by simp, cover_r14⟩
  | exact ⟨3, by simp, cover_r15⟩
  | exact ⟨241, by simp, cover_r16⟩
  | exact ⟨3, by simp, cover_r17⟩
  | exact ⟨5, by simp, cover_r18⟩
  | exact ⟨3, by simp, cover_r19⟩
  | exact ⟨13, by simp, cover_r20⟩
  | exact ⟨3, by simp, cover_r21⟩
  | exact ⟨5, by simp, cover_r22⟩
  | exact ⟨3, by simp, cover_r23⟩
