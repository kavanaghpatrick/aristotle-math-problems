# E944 — The circulant sub-case: toward "no circulant is a (4,1)-witness"

**Owner:** wall. **Goal (team-lead directive):** convert Steiner's published *lean* ("we lean towards
thinking [circulant (4,1)-graphs] do not exist", Skottová–Steiner 2025 arXiv:2508.08703 §5) into a
THEOREM. Per proximity, Steiner gives NO general circulant argument — the mod-3 mechanism here is new.

**Status (honest):** strong computational result + partial proof. The full theorem is NOT yet closed;
the precise remaining gap is stated in §4. Adversarial review requested from skeptic.

---

## 0. Setup & locked facts used

- Target: a (4,1)-witness = 4-vertex-critical graph with no critical edge (archivist defs; skeptic's
  ncard lock ⟹ finite suffices, no de Bruijn–Erdős needed).
- **gallai Theorem 2** (rainbow certificate): edge uv non-critical ⟺ in EVERY proper 3-coloring of
  G−u, N(u)∖{v} uses all 3 colors. **gallai Theorem 3/4**: witness ⟹ δ≥6 and at every vertex, in
  every 3-coloring of G−v, N(v) is colored EXACTLY 2-2-2. [proven, literature-corroborated: Prop 5.1]
- **algebra orbit lemma** (vertex-transitive): Aut(G) preserves χ, so an edge is critical iff its
  whole Aut-orbit is. In a circulant, the rotation ℤ_n acts; edges split into difference-orbits
  {±s : translates}. "No critical edge" ⟺ every difference-orbit is simultaneously non-critical.

## 1. THE COMPUTATIONAL RESULT  [VERIFIED — dual-checker, n=11..22, all cases]

> Across ALL 52 four-vertex-critical circulants C_n(S) with |S|=3 on n=11..22, EACH has exactly 6
> proper 3-colorings of G−v (i.e. the 3-coloring is UNIQUE up to permuting the 3 colors), and EXACTLY
> ONE difference-orbit is critical (n critical edges). Hence NONE is a (4,1)-witness.

Extended (count, independently): min #critical-edges = n for all 4-vc circulants up to n≈40 across
arbitrary distance sets — never 0. proximity's non-circulant 6-regular scan: 0 vertex-critical at
n=11 (266 graphs), n=12 (7849). All consistent: no circulant witness found anywhere.

The critical orbit is the "tightest" one; e.g. C_n(1,2,5): difference-1 (Hamilton cycle) is critical,
all others non-critical; critical fraction → 0 as n grows but never reaches 0.

## 2. THE MECHANISM (mod-3 rigidity)  [PROVEN for a NARROW residue sub-family only]

**Residue Lemma (corrected scope).** Let G=C_n(S) be 4-vertex-critical. The map c(v)=v mod 3 is a
proper 3-coloring of G−0 **iff for every s∈S both s≢0 (mod 3) AND s≢n (mod 3)** — the second condition
because a *wrapping* edge {v, v+s−n} has endpoints differing by (s−n) mod 3, not s mod 3. (I initially
missed the wrap condition; skeptic-style self-check caught it. Verified: only **8 of the 52** 4-vc
circulants on n=11..22 are residue-proper — e.g. C₁₃(1,2,5); the other 44 are NOT.)

WHEN residue-proper, the neighborhood N(0)={±s} gets color multiset M={s mod3}⊎{(n−s) mod3}, and the
arithmetic (a=#{s≡1 mod3}) gives distribution (a,a,2(3−a)) for n≡1 mod 3: a=1→(1,1,4), unbalanced
⟹ two singleton colors ⟹ two critical edges (gallai Thm 4). **This rigorously proves C₁₃(1,2,5)-type
(residue-proper, a≠2) circulants have a critical edge.** [PROVEN, but covers only the 8/52 sub-family.]

This is an honest PARTIAL mechanism, NOT the general circulant theorem. The general result is §3.

## 3. THE GENERAL CASE — computational, with the crux isolated  [VERIFIED n≤22; NOT proven]

Tested directly (fast checker): the a=2 residue case (which the §2 arithmetic would PERMIT 2-2-2) does
NOT escape — C₁₉(1,4,8), C₁₉(1,5,7) (the only 4-vc a=2 candidates at n≤19) are NOT witnesses: each has
6 colorings of G−0 and N(0)=(1,1,4), one critical orbit. Reason: for these S the residue map is NOT
proper (wrap edges, §2), so the genuine unique coloring is a different AP-block partition that lands
(1,1,4) anyway. So the obstruction is real but its PROOF is not the simple residue computation.

**The crux** (uniform across all 52 cases n≤22, verified): every 4-vc circulant has G−v **uniquely
3-colorable** (exactly 6 colorings = 3! permutations), and that unique coloring colors N(0) unbalanced
(some color a singleton) ⟹ a critical orbit ⟹ not a witness.

## 4. THE REMAINING GAP (precise) — task #12

To complete "no circulant is a (4,1)-witness" the one needed lemma is:

> **(Uniqueness Lemma, OPEN).** For every 4-vertex-critical circulant C_n(S), the graph C_n(S)−v is
> uniquely 3-colorable (its proper 3-colorings are a single orbit under permuting the 3 colors).

GIVEN this lemma, the theorem follows: the unique coloring colors N(0) with some distribution; if it
were 2-2-2 at every vertex the graph would be a witness, but [the data shows, and one would prove via
the AP-block structure of the unique coloring + the χ=4 constraint] the balance fails on at least one
orbit. The lemma is verified for all 52 four-vc circulants on n≤22; a supporting structural fact is
that the union of any two color classes of C_n(S)−v is connected (Kempe-chain rigidity ⟹ unique
3-colorability — verified on the tested cases). An n-uniform proof is NOT yet in hand. This is the
honest open step; route (B) (direct ℤ_n eigenvalue/averaging on the 2-2-2 constraint) is unexplored.

## 5. What IS rigorously established (safe to cite) vs. what is computational

PROVEN:
- (algebra) orbit lemma: in a circulant, an edge is critical iff its whole difference-orbit is; "no
  critical edge" ⟺ every difference-orbit simultaneously non-critical.
- (gallai Thm 4) a circulant witness needs N(0) colored 2-2-2 in EVERY 3-coloring of G−0.
- (§2, this file) residue-proper circulants with a≠2 (the 8/52 sub-family incl. C₁₃(1,2,5)) have a
  critical edge — a clean number-theoretic proof.

COMPUTATIONAL (verified, not proven):
- ALL 52 four-vc circulants n=11..22 have a uniquely-3-colorable G−v and exactly one critical orbit
  ⟹ none is a witness. count: min #critical = n (>0) for all 4-vc circulants to n≈40, any S.
- No circulant witness at any degree (6/8/10) for n≤25. proximity: no non-circulant 6-reg vc graph
  n≤12 either.

**HONEST BOTTOM LINE:** the computational evidence that no circulant is a (4,1)-witness is very strong
and matches Steiner's published lean; the mod-3 mechanism explains the densest sub-family rigorously
and is new (Steiner had no general argument — proximity). But the GENERAL circulant impossibility is
NOT a theorem yet; it hinges on the Uniqueness Lemma (§4), which is open. Do not overclaim.
