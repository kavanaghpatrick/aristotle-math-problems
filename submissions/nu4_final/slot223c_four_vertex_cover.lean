/-
  slot223c_four_vertex_cover.lean

  LEMMA: Any graph on 4 vertices with independence number ≥ 2 has vertex cover ≤ 2.

  FROM 3-ROUND DEBATE (Jan 3, 2026):
  This is pure graph theory, independent of the Tuza problem structure.

  PROOF IDEA:
  - A graph H on 4 vertices with α(H) ≥ 2 is NOT K₄
  - The complement H̄ has clique number ≤ 2 (since α(H) = ω(H̄))
  - By König-Egerváry or direct case analysis:
    - If H has ≤ 3 edges: τ(H) ≤ 2 (easily find 2-vertex cover)
    - If H has 4 edges: It's C₄ or K₄⁻, both have τ = 2
    - If H has 5 edges: It's K₄⁻ = K₄ minus one edge, τ = 2

  Actually simpler: On 4 vertices, τ = 3 only for K₄ (which has α = 1).
  Since α ≥ 2, we have H ≠ K₄, so τ ≤ 2.

  1 SORRY: The case analysis or König argument
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any graph on ≤ 4 vertices with independence number ≥ 2 has vertex cover ≤ 2.

    The only 4-vertex graph with τ = 3 is K₄, which has α = 1.
    Since we have α ≥ 2, the graph is not K₄, so τ ≤ 2.

    CASE ANALYSIS:
    Let H be a graph on S with |S| ≤ 4 and α(H) ≥ 2.
    Let {u, w} be an independent set (exists by α ≥ 2).
    Claim: S \ {u, w} is a vertex cover of size ≤ 2.

    Proof: Every edge e of H has at least one endpoint.
    Since {u, w} is independent, no edge has both endpoints in {u, w}.
    So every edge has at least one endpoint in S \ {u, w}.
    Hence S \ {u, w} is a vertex cover. |S \ {u, w}| ≤ 4 - 2 = 2. ∎ -/
theorem four_vertex_cover (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (hS : S.card ≤ 4)
    (h_ind : ∃ u w, u ∈ S ∧ w ∈ S ∧ u ≠ w ∧ ¬H.Adj u w) :
    ∃ C : Finset V, C.card ≤ 2 ∧ C ⊆ S ∧
      ∀ e : Sym2 V, e ∈ H.edgeFinset → (∃ v ∈ e, v ∈ S) → ∃ v ∈ C, v ∈ e := by
  -- The independent set {u, w} gives us the cover S \ {u, w}
  -- Since {u, w} is independent, every edge in H[S] has an endpoint in S \ {u, w}
  --
  -- Detailed argument:
  -- 1. |S \ {u, w}| = |S| - |{u, w}| = |S| - 2 ≤ 4 - 2 = 2
  --    (since u, w ∈ S and u ≠ w)
  -- 2. S \ {u, w} ⊆ S is immediate
  -- 3. For any edge e in H with an endpoint in S:
  --    - If e has both endpoints in {u, w}, then H.Adj u w, contradiction
  --    - So e has at least one endpoint outside {u, w}
  --    - That endpoint is in S \ {u, w}
  sorry

end
