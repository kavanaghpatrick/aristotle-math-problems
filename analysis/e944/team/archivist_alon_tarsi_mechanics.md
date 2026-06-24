# Alon–Tarsi / Combinatorial Nullstellensatz — proof mechanics for the E944 graph-polynomial attack

For gallai+wall (CN/Alon-Tarsi impossibility lane). Precise theorem statements + sign conventions + the criticality-angle verdict. Sources cited; the q=3-criticality angle is NOVEL (absent from literature) — confirmed by targeted search.

## 1. Alon–Tarsi theorem (Alon & Tarsi, Combinatorica 12 (1992) 125–134)
Graph polynomial: f_G(x₁,…,xₙ) = ∏_{(vᵢ,vⱼ)∈E, i<j} (xᵢ − xⱼ), vertices labeled v₁…vₙ.

**(a) Coefficient ↔ orientation count (Lemma 2.2 / Cor 2.3).** Expand f_G in monomials. For an outdegree sequence d=(d₁,…,dₙ), the coefficient of ∏ xᵢ^{dᵢ} has absolute value |EE(D) − EO(D)|, for ANY orientation D of G with outdegree(vᵢ)=dᵢ.
- An **Eulerian subgraph** H of digraph D = a subdigraph where every vertex has in-deg = out-deg in H (NOT necessarily connected; empty subgraph counts, and is even). Equivalently a disjoint union of directed cycles.
- **EE(D), EO(D)** = number of Eulerian subgraphs with an EVEN / ODD number of edges.
- Sign convention: each oriented edge agreeing with the reference order i<j contributes +xⱼ, disagreeing contributes −xᵢ. The signed expansion yields the EE−EO count. |EE−EO| is independent of which D (with given outdegrees) you pick; EE−EO itself is well-defined up to global sign.
- ⟹ **coefficient ≠ 0 ⟺ EE(D) ≠ EO(D).**

**(b) The theorem proper (Thm 1.1).** If digraph D has EE(D) ≠ EO(D), then for ANY lists S(v) with |S(v)| = outdeg(v)+1, G has a proper coloring with c(v)∈S(v). ⟹ (Cor 1.2) if G has an orientation with max outdegree ≤ d and EE≠EO, then G is (d+1)-choosable, hence (d+1)-colorable. If D is acyclic or has no odd directed cycle, EO(D)=0 so the condition holds automatically.

## 2. Alon–Tarsi number AT(G)
AT(G) := 1 + min{ Δ⁺(D) : orientation D of G with EE(D)≠EO(D) }. Then **χ(G) ≤ ch(G) ≤ AT(G)** (ch = choice/list number).
- STRICT AT(G) > χ(G) DOES occur (e.g. some graphs with χ=3 but AT≥4; some Mycielskians). NO clean characterization in terms of vertex/edge-criticality — it depends on existence of an outdegree/parity-imbalanced orientation.
- PRIOR ART (closest to our angle): **"k-Alon-Tarsi-critical graphs"** ARE a studied notion (Electron. J. Combin. 23(3) #P3.37): graphs with AT(G)≥k but every proper subgraph has smaller AT-number — the AT-analogue of chromatic criticality. Also k-list-critical graph edge/degree lower bounds use AT(G) (Combinatorica, Springer s00493-016-3584-6). These are the relevant prior literature, but NONE addresses our exact question.

## 3. Combinatorial Nullstellensatz (Alon 1999, CPC 8:7–29, Thm 1.2)
If f∈F[x₁…xₙ], deg(f)=Σtᵢ, and the coeff of ∏xᵢ^{tᵢ} is nonzero, then for any Sᵢ⊆F with |Sᵢ|>tᵢ, ∃ (s₁…sₙ)∈∏Sᵢ with f(s)≠0.

## 4. ★ THE q=3 / criticality angle — VERDICT: NOVEL (not in literature)
Targeted search confirms each of these is ABSENT from the literature (= the angle is genuinely new; gallai's hope is unexplored, which is good news for novelty but means no off-the-shelf theorem):

(i) **No** known result equating/relating the signed sum ∑_{c:V→{1,ω,ω²}} ∏_{(u,v)∈E}(ω^{c(u)}−ω^{c(v)}) to the NUMBER of proper 3-colorings or to a Tutte/flow invariant. (The nowhere-zero ℤ₃-flow ↔ 3-coloring Tutte connection is classical but INDEPENDENT of Alon-Tarsi; AT gives existence/choosability, not enumeration.) Tarsi has separate work relating the graph polynomial to the number of proper colorings — worth chasing if you want the enumeration link (M. Tarsi, graph polynomial & number of colorings).

(ii) The contrapositive **"G 4-chromatic ⟹ EE(D)=EO(D) for EVERY orientation D with Δ⁺≤2"** is TRUE (immediate from the theorem: an EE≠EO outdeg-≤2 orientation would make G 3-choosable hence 3-colorable). BUT it is NOT studied in the literature as an independent non-3-colorability certificate — it's tautological from AT. So you can USE it (it's correct), but there's no prior machinery built on it.

(iii) **THE KEY QUESTION IS OPEN/UNTOUCHED:** No literature links EE−EO orientation counts or graph-polynomial coefficients to:
   - the appearance of an EE≠EO outdeg-≤2 orientation EXACTLY on each G−v (vertex-criticality),
   - or the distinction G−e critical (EE≠EO appears, 3-colorable) vs non-critical (EE=EO persists).
gallai's hope — that vertex-criticality (every G−v gains an EE≠EO orientation) forces a parity/sign identity constraining the NUMBER of critical edges — is **not addressed anywhere**. This is a novel direction.

(iv) Adjacent known results (context, not solutions): Ellingham–Goddyn (AT ⟹ d-regular planar d-edge-colorable is d-edge-choosable, 4CT-relevant); AT(planar)≤5; Matiyasevich's graph-polynomial-mod-7 4CT reformulation (independent of AT orientation method). None resolves the criticality question.

## NET for the proof team
- The framework (1)-(3) is solid and exactly as gallai's computation found (K4: 0 bounded monomials = not 3-colorable; each edge-quotient = 12 = critical, matching EE≠EO appearing). USE these statements verbatim.
- The criticality/parity identity gallai wants is NOT in the literature → it has to be PROVEN from scratch (good: novel, no collision; bad: no theorem to cite). The signed orientation count IS structurally different from B₁ (a coloring count), so it genuinely can see what the chromatic polynomial can't — gallai's premise is sound.
- The one literature thread to mine if you want enumeration (not just existence): **M. Tarsi's work relating the graph polynomial to the NUMBER of proper colorings** (West's altar.pdf cites it). If a signed-sum = (count) identity exists anywhere, it's there.

## ★ FINAL VERDICT — AT LEVER IS DEAD (gallai's density-kill, 2026-06-11)
NOT pursued the Tarsi count identity — gallai showed it can't escape, and the reason cleanly classifies the whole AT framework against the squad's meta-obstruction (residue §8, "density/specificity trap"):
- The graph polynomial f_G is HOMOGENEOUS of degree m=|E|. The bounded-degree monomials (≤2n) that carry the NOVEL Alon-Tarsi signed-orientation-PARITY structure VANISH when m>2n. A witness has m≥3n (gallai Thm 3, the min-deg-6 density). So the novel signed-parity content has NO monomials to live in for a dense witness.
- The Tarsi "signed sum = #colorings" identity, IF it exists, is DENSITY-ROBUST (a count doesn't care about m vs 2n) — but that means it IS the banned B₁/count object (Theorem-4 territory), gaining nothing. It's B₁ in orientation clothing.
- ⟹ In the AT framework, NOVELTY (signed parity, bounded monomials → dies at density) and DENSITY-ROBUSTNESS (the count → is the banned object) are MUTUALLY EXCLUSIVE. The toolkit splits exactly along the squad's density/specificity trap. AT lever DEAD; no Tarsi pull needed.
- Related prior art to note in the residue (does NOT change the verdict): k-Alon-Tarsi-critical graphs (EJC 23(3) #P3.37).
