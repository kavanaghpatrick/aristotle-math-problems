import Mathlib

open scoped Classical

namespace SeqIntersection

/-- Sequence of `v`-values for `u^2 = 2*v^2 - 1` (Pell-type). -/
def SeqA : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | n + 2 => 6 * SeqA (n + 1) - SeqA n

/-- Sequence of `v`-values for `d^2 = 3*v^2 - 2` (Pell-type). -/
def SeqB : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => 4 * SeqB (n + 1) - SeqB n

def is_SeqA (v : ℕ) : Prop := ∃ n, SeqA n = v
def is_SeqB (v : ℕ) : Prop := ∃ n, SeqB n = v

/-- Uniqueness for order-2 linear recurrences in a ring. -/
private lemma rec_eq_of_init_eq {R : Type} [Ring R] (c : R) (f g : ℕ → R)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hf : ∀ n, f (n + 2) = c * f (n + 1) - f n)
    (hg : ∀ n, g (n + 2) = c * g (n + 1) - g n) : f = g := by
  funext n
  have hpair : ∀ k, f k = g k ∧ f (k + 1) = g (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
        have hk2 : f (k + 2) = g (k + 2) := by
          calc
            f (k + 2) = c * f (k + 1) - f k := hf k
            _ = c * g (k + 1) - g k := by simpa [ih.1, ih.2]
            _ = g (k + 2) := (hg k).symm
        exact ⟨ih.2, hk2⟩
  exact (hpair n).1

/-- Order-2 recurrence in `ZMod m` matching `SeqA`. -/
def SeqA_mod (m : ℕ) : ℕ → ZMod m
  | 0 => 1
  | 1 => 5
  | n + 2 => 6 * SeqA_mod m (n + 1) - SeqA_mod m n

/-- Order-2 recurrence in `ZMod m` matching `SeqB`. -/
def SeqB_mod (m : ℕ) : ℕ → ZMod m
  | 0 => 1
  | 1 => 3
  | n + 2 => 4 * SeqB_mod m (n + 1) - SeqB_mod m n

lemma SeqA_pos_strict (n : ℕ) : 0 < SeqA n ∧ SeqA n < SeqA (n + 1) := by
  induction n with
  | zero =>
      simp [SeqA]
  | succ n ih =>
      have hpos_succ : 0 < SeqA (n + 1) := lt_of_le_of_lt (Nat.zero_le _) ih.2
      have hnle : SeqA n ≤ SeqA (n + 1) := Nat.le_of_lt ih.2
      have hsub : 6 * SeqA (n + 1) - SeqA (n + 1) = 5 * SeqA (n + 1) := by
        have h6 : 6 * SeqA (n + 1) = 5 * SeqA (n + 1) + SeqA (n + 1) := by
          simpa using (Nat.succ_mul 5 (SeqA (n + 1)))
        calc
          6 * SeqA (n + 1) - SeqA (n + 1)
              = (5 * SeqA (n + 1) + SeqA (n + 1)) - SeqA (n + 1) := by simpa [h6]
          _ = 5 * SeqA (n + 1) := by
              simpa using Nat.add_sub_cancel_right (5 * SeqA (n + 1)) (SeqA (n + 1))
      have h5le : 5 * SeqA (n + 1) ≤ SeqA (n + 2) := by
        have : 6 * SeqA (n + 1) - SeqA (n + 1) ≤ 6 * SeqA (n + 1) - SeqA n :=
          Nat.sub_le_sub_left hnle (6 * SeqA (n + 1))
        simpa [SeqA, hsub] using this
      have hlt_mul : SeqA (n + 1) < 5 * SeqA (n + 1) := by
        simpa [one_mul] using
          (Nat.mul_lt_mul_of_pos_right (by decide : (1 : ℕ) < 5) hpos_succ)
      have hlt_succ : SeqA (n + 1) < SeqA (n + 2) := lt_of_lt_of_le hlt_mul h5le
      exact ⟨hpos_succ, hlt_succ⟩

lemma SeqB_pos_strict (n : ℕ) : 0 < SeqB n ∧ SeqB n < SeqB (n + 1) := by
  induction n with
  | zero =>
      simp [SeqB]
  | succ n ih =>
      have hpos_succ : 0 < SeqB (n + 1) := lt_of_le_of_lt (Nat.zero_le _) ih.2
      have hnle : SeqB n ≤ SeqB (n + 1) := Nat.le_of_lt ih.2
      have hsub : 4 * SeqB (n + 1) - SeqB (n + 1) = 3 * SeqB (n + 1) := by
        have h4 : 4 * SeqB (n + 1) = 3 * SeqB (n + 1) + SeqB (n + 1) := by
          simpa using (Nat.succ_mul 3 (SeqB (n + 1)))
        calc
          4 * SeqB (n + 1) - SeqB (n + 1)
              = (3 * SeqB (n + 1) + SeqB (n + 1)) - SeqB (n + 1) := by simpa [h4]
          _ = 3 * SeqB (n + 1) := by
              simpa using Nat.add_sub_cancel_right (3 * SeqB (n + 1)) (SeqB (n + 1))
      have h3le : 3 * SeqB (n + 1) ≤ SeqB (n + 2) := by
        have : 4 * SeqB (n + 1) - SeqB (n + 1) ≤ 4 * SeqB (n + 1) - SeqB n :=
          Nat.sub_le_sub_left hnle (4 * SeqB (n + 1))
        simpa [SeqB, hsub] using this
      have hlt_mul : SeqB (n + 1) < 3 * SeqB (n + 1) := by
        simpa [one_mul] using
          (Nat.mul_lt_mul_of_pos_right (by decide : (1 : ℕ) < 3) hpos_succ)
      have hlt_succ : SeqB (n + 1) < SeqB (n + 2) := lt_of_lt_of_le hlt_mul h3le
      exact ⟨hpos_succ, hlt_succ⟩

lemma SeqA_le_six_mul_succ (n : ℕ) : SeqA n ≤ 6 * SeqA (n + 1) := by
  have hnle : SeqA n ≤ SeqA (n + 1) := Nat.le_of_lt (SeqA_pos_strict n).2
  exact le_trans hnle (by
    have : (1 : ℕ) ≤ 6 := by decide
    simpa [one_mul] using (Nat.mul_le_mul_right (SeqA (n + 1)) this))

lemma SeqB_le_four_mul_succ (n : ℕ) : SeqB n ≤ 4 * SeqB (n + 1) := by
  have hnle : SeqB n ≤ SeqB (n + 1) := Nat.le_of_lt (SeqB_pos_strict n).2
  exact le_trans hnle (by
    have : (1 : ℕ) ≤ 4 := by decide
    simpa [one_mul] using (Nat.mul_le_mul_right (SeqB (n + 1)) this))

lemma SeqA_cast_eq_mod (m n : ℕ) : (SeqA n : ZMod m) = SeqA_mod m n := by
  have h0 : (SeqA 0 : ZMod m) = SeqA_mod m 0 := by simp [SeqA, SeqA_mod]
  have h1 : (SeqA 1 : ZMod m) = SeqA_mod m 1 := by simp [SeqA, SeqA_mod]
  have hf : ∀ k,
      (SeqA (k + 2) : ZMod m) = (6 : ZMod m) * (SeqA (k + 1) : ZMod m) - (SeqA k : ZMod m) := by
    intro k
    have hle : SeqA k ≤ 6 * SeqA (k + 1) := SeqA_le_six_mul_succ k
    simpa [SeqA, Nat.cast_sub hle, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
  have hg : ∀ k,
      SeqA_mod m (k + 2) = (6 : ZMod m) * SeqA_mod m (k + 1) - SeqA_mod m k := by
    intro k; rfl
  have hfun : (fun t => (SeqA t : ZMod m)) = SeqA_mod m :=
    rec_eq_of_init_eq (R := ZMod m) (c := (6 : ZMod m)) (f := fun t => (SeqA t : ZMod m))
      (g := SeqA_mod m) h0 h1 hf hg
  simpa using congrArg (fun f => f n) hfun

lemma SeqB_cast_eq_mod (m n : ℕ) : (SeqB n : ZMod m) = SeqB_mod m n := by
  have h0 : (SeqB 0 : ZMod m) = SeqB_mod m 0 := by simp [SeqB, SeqB_mod]
  have h1 : (SeqB 1 : ZMod m) = SeqB_mod m 1 := by simp [SeqB, SeqB_mod]
  have hf : ∀ k,
      (SeqB (k + 2) : ZMod m) = (4 : ZMod m) * (SeqB (k + 1) : ZMod m) - (SeqB k : ZMod m) := by
    intro k
    have hle : SeqB k ≤ 4 * SeqB (k + 1) := SeqB_le_four_mul_succ k
    simpa [SeqB, Nat.cast_sub hle, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
  have hg : ∀ k,
      SeqB_mod m (k + 2) = (4 : ZMod m) * SeqB_mod m (k + 1) - SeqB_mod m k := by
    intro k; rfl
  have hfun : (fun t => (SeqB t : ZMod m)) = SeqB_mod m :=
    rec_eq_of_init_eq (R := ZMod m) (c := (4 : ZMod m)) (f := fun t => (SeqB t : ZMod m))
      (g := SeqB_mod m) h0 h1 hf hg
  simpa using congrArg (fun f => f n) hfun

private lemma periodic_of_shift_eq_init {R : Type} [Ring R] (c : R) (f : ℕ → R) (P : ℕ)
    (hP0 : f P = f 0) (hP1 : f (P + 1) = f 1)
    (hf : ∀ n, f (n + 2) = c * f (n + 1) - f n) : Function.Periodic f P := by
  have hshift : (fun n => f (n + P)) = f := by
    have h0 : (fun n => f (n + P)) 0 = f 0 := by simpa using hP0
    have h1 : (fun n => f (n + P)) 1 = f 1 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hP1
    have hg : ∀ n,
        (fun n => f (n + P)) (n + 2) = c * (fun n => f (n + P)) (n + 1) - (fun n => f (n + P)) n := by
      intro n
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hf (n + P))
    exact rec_eq_of_init_eq (R := R) (c := c) (f := fun n => f (n + P)) (g := f) h0 h1 hg hf
  intro n
  simpa using congrArg (fun g => g n) hshift

lemma SeqA_mod_periodic_3080 : Function.Periodic (SeqA_mod 3080) 12 := by
  have h0 : SeqA_mod 3080 12 = SeqA_mod 3080 0 := by native_decide
  have h1 : SeqA_mod 3080 (12 + 1) = SeqA_mod 3080 1 := by native_decide
  have hrec : ∀ n,
      SeqA_mod 3080 (n + 2) = (6 : ZMod 3080) * SeqA_mod 3080 (n + 1) - SeqA_mod 3080 n := by
    intro n; rfl
  simpa using periodic_of_shift_eq_init (R := ZMod 3080) (c := (6 : ZMod 3080)) (f := SeqA_mod 3080)
    (P := 12) h0 (by simpa [Nat.add_comm] using h1) hrec

lemma SeqB_mod_periodic_3080 : Function.Periodic (SeqB_mod 3080) 120 := by
  have h0 : SeqB_mod 3080 120 = SeqB_mod 3080 0 := by native_decide
  have h1 : SeqB_mod 3080 (120 + 1) = SeqB_mod 3080 1 := by native_decide
  have hrec : ∀ n,
      SeqB_mod 3080 (n + 2) = (4 : ZMod 3080) * SeqB_mod 3080 (n + 1) - SeqB_mod 3080 n := by
    intro n; rfl
  simpa using periodic_of_shift_eq_init (R := ZMod 3080) (c := (4 : ZMod 3080)) (f := SeqB_mod 3080)
    (P := 120) h0 (by simpa [Nat.add_comm] using h1) hrec

private lemma mem_image_of_periodic {α : Type} [DecidableEq α] (f : ℕ → α) (P : ℕ)
    (hper : Function.Periodic f P) (n : ℕ) (hP : 0 < P) : f n ∈ (Finset.range P).image f := by
  let r := n % P
  have hr : r < P := Nat.mod_lt _ hP
  have hiter : f (r + P * (n / P)) = f r := by
    induction (n / P) with
    | zero => simp
    | succ q ih =>
        have hstep := hper (r + P * q)
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep.trans ih
  have hdecomp : r + P * (n / P) = n := by
    simpa [r, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.mod_add_div n P)
  have hn : f n = f r := by
    simpa [hdecomp] using hiter
  refine Finset.mem_image.2 ?_
  refine ⟨r, Finset.mem_range.2 hr, hn.symm⟩

def SeqA_res_3080 : Finset (ZMod 3080) := (Finset.range 12).image (SeqA_mod 3080)
def SeqB_res_3080 : Finset (ZMod 3080) := (Finset.range 120).image (SeqB_mod 3080)

lemma SeqA_res_3080_inter_SeqB_res_3080 : SeqA_res_3080 ∩ SeqB_res_3080 = {1} := by
  native_decide

lemma SeqA_SeqB_mod_3080_intersection (v : ℕ) (hA : is_SeqA v) (hB : is_SeqB v) : v % 3080 = 1 := by
  have hA' : (v : ZMod 3080) ∈ SeqA_res_3080 := by
    rcases hA with ⟨n, rfl⟩
    have hmem : SeqA_mod 3080 n ∈ SeqA_res_3080 := by
      have : SeqA_mod 3080 n ∈ (Finset.range 12).image (SeqA_mod 3080) :=
        mem_image_of_periodic (f := SeqA_mod 3080) (P := 12) SeqA_mod_periodic_3080 n (by decide)
      simpa [SeqA_res_3080] using this
    simpa [SeqA_cast_eq_mod 3080 n] using hmem
  have hB' : (v : ZMod 3080) ∈ SeqB_res_3080 := by
    rcases hB with ⟨n, rfl⟩
    have hmem : SeqB_mod 3080 n ∈ SeqB_res_3080 := by
      have : SeqB_mod 3080 n ∈ (Finset.range 120).image (SeqB_mod 3080) :=
        mem_image_of_periodic (f := SeqB_mod 3080) (P := 120) SeqB_mod_periodic_3080 n (by decide)
      simpa [SeqB_res_3080] using this
    simpa [SeqB_cast_eq_mod 3080 n] using hmem
  have hvInter : (v : ZMod 3080) ∈ SeqA_res_3080 ∩ SeqB_res_3080 := by
    simpa [Finset.mem_inter] using And.intro hA' hB'
  have hv1 : (v : ZMod 3080) = (1 : ZMod 3080) := by
    have : (v : ZMod 3080) ∈ ({1} : Finset (ZMod 3080)) := by
      simpa [SeqA_res_3080_inter_SeqB_res_3080] using hvInter
    simpa using (Finset.mem_singleton.mp this)
  have : v % 3080 = 1 % 3080 := (ZMod.natCast_eq_natCast_iff' v 1 3080).1 hv1
  simpa using this

theorem SeqA_SeqB_only_one (v : ℕ) (hA : ∃ n, SeqA n = v) (hB : ∃ m, SeqB m = v) : v = 1 := by
  have hvmod : v % 3080 = 1 := SeqA_SeqB_mod_3080_intersection v hA hB
  -- TODO: strengthen the congruence to an equality.
  sorry

end SeqIntersection