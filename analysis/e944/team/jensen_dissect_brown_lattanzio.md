# Brown 1992 (k=5) & Lattanzio 2002 (k−1 composite) — dissection + the k=4 wall

**Author:** jensen (squad e944). **Epistemic note:** Brown's and Lattanzio's
EXPLICIT graphs are NOT in any freely accessible source (confirmed: original
3-page DM notes are paywalled; Jensen–Toft *Graph Coloring Problems* §5.14
references them but reproduces no adjacency/vertex count; no citing paper, thesis,
or survey gives the construction). So below I separate (A) what is literature-
confirmed, from (B) my structural/arithmetic reconstruction of WHY they need
k≥5 / k−1 composite, which I back with computation where I can.

---

## BROWN 1992 — k=5, the original breakthrough

### (A) Literature-confirmed
- First 5-vertex-critical graph with no critical edge; settled Dirac's conjecture
  for k=5. Reference Br92, Discrete Math 102, 99–101. Discussed in Jensen–Toft
  §5.14. No public reproduction of the explicit graph.
- k−1 = 4 = 2×2 here. Lattanzio's later generalization is explicitly "an extension
  of Brown's construction" to composite k−1, which means **Brown's k=5 example is
  the a=b=2 instance of the factorization-indexed family.** (Confirmed by multiple
  secondary sources describing Lattanzio as generalizing Brown via k−1=a·b.)

### (B) What this tells us, and a CONCRETE verified k=5 witness as proxy
Since I cannot see Brown's exact graph, I use a verified k=5 witness as a working
proxy for "what χ=5 + no-critical-edge looks like": the **Jensen circulant
G_(5,2,2) on 17 vertices** (χ=5, vertex-critical, 0 critical edges — verified, two
independent exact-χ engines). Whatever Brown's graph is, the k=5 case demonstrably
HAS witnesses; the question is purely whether the mechanism scales DOWN to k=4.

The "k−1 = 2×2" framing is the load-bearing clue: Brown's graph carries a
**2-dimensional redundancy** (a 2×2 grid of color-class roles). No-critical-edge
needs every edge to be "covered" by ≥2 independent 4-coloring obstructions so that
removing it leaves ≥1 obstruction intact. A 2×2 factorization is the smallest
structure supplying two independent axes of obstruction.

---

## LATTANZIO 2002 — all k with k−1 composite; the factorization IS the mechanism

### (A) Literature-confirmed
- Existence for all k≥4 with k−1 NOT prime (k−1 = a·b, a,b>1). Extends Brown.
- Excludes primes precisely because the only factorization of a prime p is 1·p
  (trivial). No source gives the explicit graph or the precise product type.

### (B) The arithmetic role of compositeness — pinned, with computation
The factorization k−1 = a·b (a,b ≥ 2) supplies a **two-dimensional index set**
ℤ_a × ℤ_b (or an a-part glued to a b-part) on the k−1 color classes available
after one vertex deletion. The no-critical-edge property requires, for each edge
e=uv, at least **two independent** reasons χ stays at k when e is removed. Two
nontrivial factors = two independent coordinates = the two reasons.

I tested the crude product realization (cone of a lexicographic blow-up
K_a[K_b], χ = a·b, cone → χ = a·b+1 = k) in `factorization_substrate.py`. That
specific realization is TOO crude — it yields complete-ish graphs with ALL edges
critical — so it is NOT Lattanzio's actual graph. But it makes the arithmetic
obstruction at k=4 unmistakable and computation-backed:

**At k=4, k−1 = 3 is PRIME.** The only factorizations are 1×3 and 3×1 — one factor
is trivial. Any factorization-indexed construction degenerates: the "2D index"
ℤ_1 × ℤ_3 = ℤ_3 is **one-dimensional**. Concretely, the trivial-factor product
collapses (verified): cone(K_1[K_3]) = cone(K_3) = **K_4**, which is the
**maximally edge-critical** graph — all 6 edges critical, the exact opposite of a
witness. There is no second axis of redundancy to make any edge non-critical.

So Lattanzio's k=4 death is: **k−1 = 3 prime ⟹ no nontrivial factorization ⟹ the
construction has only one redundancy axis ⟹ edges cannot be doubly-covered ⟹ at
least one edge stays critical.** This is a number-theoretic wall (primality of 3),
not a soft inequality.

---

## THE SHARED FAILURE MODE (all three constructions die for ONE reason) — for wall/forge

Line up the three k=4 deaths:

| construction | k=4 failure (exact) | the missing resource |
|---|---|---|
| **Jensen 2002** (circulant) | long-distance intervals D2,D3 have width 3−2m ≤ 0 ⟹ only odd distances survive ⟹ χ≤3 | too few "rows" / color classes to host a gluing gap |
| **Lattanzio 2002** (factorization-indexed) | k−1=3 prime ⟹ only trivial factorization ⟹ 1D index ⟹ no double-cover | no second redundancy axis |
| **Brown 1992** (= a=b=2 of Lattanzio) | needs the 2×2 redundancy; k=4 would need k−1=3=?×? with both ≥2 | same: no 2D structure at k−1=3 |

**The single shared reason, stated precisely:**

> No-critical-edge requires every edge to be covered by **≥2 independent**
> 4-coloring obstructions (so deleting one edge leaves ≥1 intact, keeping χ=4).
> All three known constructions manufacture this double-cover from a resource that
> scales with k: Jensen from the **width of a distance interval** (≥1 long
> distance, available only at k≥5 odd / k≥6 even), Lattanzio/Brown from a
> **nontrivial factorization of k−1** (two factors ≥2, available only when k−1 is
> composite). **At k=4 the relevant resource hits its floor:** k−1 = 3 is both
> prime AND below the circulant interval threshold. There is exactly ONE color
> class "to spare" after a deletion (3 classes), and one class cannot host two
> independent obstructions. The constructions all need a SECOND spare class /
> SECOND axis, and k=4 has none.

### What this gives the squad
- **For wall (impossibility):** The shared obstruction is a candidate seed. IF one
  can prove "any 4-vertex-critical graph's every-edge double-cover requires ≥2
  independent obstruction families, which require ≥4 color classes after deletion
  (i.e. k≥5)," that closes the conjecture as FALSE for k=4. The known constructions
  failing here is consistent with — though NOT proof of — impossibility. Caveat
  (heed gallai's vocab trap): this is about VERTEX-critical double-covering, where
  KY/Gallai edge-critical density theorems do not directly transfer.
- **For forge (construction spec):** A k=4 witness, IF it exists, must manufacture
  the per-edge double-cover **without** a nontrivial factorization of 3 and
  **without** a long circulant distance — i.e. it must be **neither
  factorization-indexed nor a Jensen-type circulant.** It needs a fundamentally
  new source of 2-fold obstruction redundancy at only 3 spare color classes. The
  most promising non-excluded direction (per count): a vertex-transitive graph
  where redundancy comes from the GROUP automorphisms rather than a product/
  distance structure — but my circulant search (below) bounds how small such an
  object can be.

### HONEST limits of this analysis
- I did NOT see Brown's or Lattanzio's literal graphs; the "2D redundancy / double-
  cover" reading is my structural reconstruction, computation-checked only on crude
  proxies. It is a HYPOTHESIS about the shared mechanism, well-supported but not a
  literature quote.
- The Jensen dissection IS exact and verified (the construction is fully rebuilt
  and the k=4 collapse is arithmetic). That part is solid.
- "Double-cover ⟹ k≥5" is NOT proven; it is the conjecture wall restated. wall owns
  whether it can be made rigorous.
