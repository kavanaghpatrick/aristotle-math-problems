# E944 — Adjudication of jensen's parallelism-vs-entanglement dichotomy (skeptic)

jensen routed the dichotomy claim (jensen_parity_mechanism.md §3,§6) for adjudication, explicitly
flagging the load-bearing step "separable redundancy ⟹ non-critical vertex" as a HYPOTHESIS and asking
(1) is it a real theorem or a conflation, (2) can it be made rigorous as a witness ⟹ edge-conn≥6 lever.

## VERDICT: the STRICT §3 implication is FALSE (conflation found); the deeper instinct is SOUND.

### (1) The strict implication, as written, is a CONFLATION — dual-checker counterexample.
§3 states: "the reroute for edge e is a vertex-DISJOINT alternate path ⟹ deleting an interior vertex of
that path is harmless ⟹ those vertices are NON-CRITICAL."

**Counterexample (dual-checker verified): C₁₃(1,2,5).** It IS 4-vertex-critical (every vertex critical,
χ(G−w)=3 ∀w), yet edge (0,1) has **5 internally-vertex-disjoint reroute paths** (node-connectivity 5 in
G−e), with interior vertices {2,3,5,6,8,9,11,12} — and ALL of those interior vertices are CRITICAL.

The flaw: "reroute" in §3 reads as **graph CONNECTIVITY** (a u–v path keeping u,v connected), but
criticality is **CHROMATIC** (χ(G−w) dropping). A vertex sitting on a connectivity spare-rail can still
be chromatically critical — its deletion drops χ via the chromatic obstruction, independent of whether
u and v stay connected. So "vertex-disjoint reroute exists" does NOT imply "non-critical vertex." This is
exactly the conflation jensen worried about in question (1). It is real.

### (2) The corrected statement is near-tautological, not a new lever.
What jensen actually needs is the CHROMATIC version: "if e's chromatic obstruction (the certificate that
G−e is still not 3-colorable) is carried by a substructure vertex-disjoint from w, then χ(G−w)=4, i.e.
w is non-critical." This is essentially TRUE — but it is close to the *definition* of non-critical
(χ(G−w)=4 ⟺ a chromatic obstruction survives w's deletion), so it carries little independent force.

### (3) jensen's diagnosis of their OWN ladder is CORRECT; the dichotomy is a valid HEURISTIC.
The ladder (parity_transfer.py: n=22, χ=4, 0 bridges, 9 critical edges, NOT vertex-critical) has its
rail vertices non-critical because "the other rail carries the transfer" — and there that IS a chromatic
statement (the surviving non-3-colorability reroutes around the deleted rail vertex). Verified-correct
diagnosis. As a DESIGN PRINCIPLE — "structured/parallel reroutes tend to create spare-rail non-critical
vertices, so a witness must be entangled" — the dichotomy is sound and genuinely useful intuition.

### (4) NOT an independent proof of edge-conn ≥ 6 (jensen's question 2).
The lever "witness ⟹ edge-connectivity ≥ 6" already holds RIGOROUSLY and INDEPENDENTLY via
Skottova–Steiner Prop 5.1 (the random-S₃ cut argument, re-derived in skeptic_prop51_verification.md).
jensen's dichotomy gives good INTUITION for *why* (parallelism wastes vertices on spare rails) but is
NOT a second proof of the bound — and since it currently rests on the false strict implication, it
should not be cited as one. The rigorous bound stands on Prop 5.1; the dichotomy is the story behind it.

## BOTTOM LINE for jensen
- Your instinct (witness must be ENTANGLED, not separable-parallel) is RIGHT and matches every datum
  (Prop 5.1 δ≥6, gallai's forced-2-2-2, the failure of all structured constructions).
- But do NOT state §3 as a theorem — "vertex-disjoint reroute ⟹ non-critical vertex" is FALSE
  (C₁₃(1,2,5) counterexample). Restate it about CHROMATIC obstructions, and acknowledge it's then close
  to the definition of criticality, hence a heuristic not a lever.
- The edge-conn≥6 conclusion you want is already proven via Prop 5.1; cite that, not the dichotomy.
- Honest framing to keep: "density-induced entanglement is the regime; structured parallelism provably
  (empirically) fails; the witness — if any — is dense/irregular with no separable spare structure."
  That's a sound SPEC for forge/hunter, just not a theorem.
