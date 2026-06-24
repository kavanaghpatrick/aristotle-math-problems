import Mathlib

set_option maxHeartbeats 800000

/-- List of all triples (a^5+b^5, a, b) for 0 ≤ a < b ≤ n. -/
def quinticPairSums (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((List.range (n + 1)).flatMap fun b =>
    (List.range b).map fun a => (a ^ 5 + b ^ 5, a, b))

/-- The sum component is duplicate-free across all pairs. -/
def quinticSumsNodup (n : ℕ) : Bool :=
  ((quinticPairSums n).map Prod.fst).Nodup

/-
Key: if quinticSumsNodup holds, the sums a^5+b^5 are all distinct
    across pairs (a,b) with a < b ≤ n.
-/
lemma quinticSumsNodup_imp (n : ℕ) (h : quinticSumsNodup n = true) :
    ∀ a b c d : ℕ, a < b → c < d →
      a ≤ n → b ≤ n → c ≤ n → d ≤ n →
      a ^ 5 + b ^ 5 = c ^ 5 + d ^ 5 → a = c ∧ b = d := by
  intro a b c d hab hcd ha hb hc hd hsum
  have h1 : (a ^ 5 + b ^ 5, a, b) ∈ quinticPairSums n := by
    exact List.mem_flatMap.mpr ⟨ b, List.mem_range.mpr ( by linarith ), List.mem_map.mpr ⟨ a, List.mem_range.mpr ( by linarith ), rfl ⟩ ⟩
  have h2 : (c ^ 5 + d ^ 5, c, d) ∈ quinticPairSums n := by
    unfold quinticPairSums; aesop;
  have h3 : (a ^ 5 + b ^ 5, a, b) = (c ^ 5 + d ^ 5, c, d) := by
    unfold quinticSumsNodup at h;
    simp +zetaDelta at *;
    rw [ List.nodup_map_iff_inj_on ] at h;
    · specialize h _ h1 _ h2 ; aesop;
    · exact List.Nodup.of_map Prod.fst h
  grind

theorem erdos_324_quintic_bounded_200 :
    ∀ a b c d : ℕ, a < b → c < d →
      a ≤ 200 → b ≤ 200 → c ≤ 200 → d ≤ 200 →
      a ^ 5 + b ^ 5 = c ^ 5 + d ^ 5 → a = c ∧ b = d := by
  have h : quinticSumsNodup 200 = true := by native_decide
  exact quinticSumsNodup_imp 200 h