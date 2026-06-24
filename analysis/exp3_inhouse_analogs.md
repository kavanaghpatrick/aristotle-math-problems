# In-House Analogs Already in Project Dossiers (for novelty scoring)

This is the reference set against which EXP3 outputs are scored for novelty.
If a model proposes an analog that matches anything below, it is "already in
our dossiers" and scored 0 on the novelty axis.

## E938 — prior analogs (from `research_fusion/runs/erdos_938/02_analogies.json`)

All 10 are within mathematics — additive combinatorics, combinatorics on words,
discrete geometry, extremal graph theory, incidence geometry.

1. Cap Set Problem (additive_combinatorics) — slice rank
2. Corners Theorem (additive_combinatorics) — hypergraph removal lemma
3. Dejean's Conjecture (combinatorics_on_words) — Currie-Rampersad template method
4. Roth's Theorem (additive_combinatorics) — Fourier analytic method
5. Arithmetic removal lemma (additive_combinatorics) — Green 2005 / Král-Serra-Vena 2009
6. Induced graph removal lemma (extremal graph theory) — Szemerédi regularity + Alon-Fischer-Krivelevich-Szegedy
7. Szemerédi-Trotter Theorem (incidence geometry) — polynomial partitioning
8. Lonely Runner Conjecture (combinatorics) — Fourier series for indicator functions
9. Ruzsa-Szemerédi induced matching (extremal graph theory) — triangle removal lemma
10. Erdős distinct distances (discrete geometry) — Guth-Katz polynomial partitioning

Domains covered: NONE in physics, CS, biology, or economics. All in mathematics.

## E373 — prior analogs (from `research_fusion/runs/erdos_373/debates/`)

1. Hardy-Ramanujan partition asymptotics + Stirling-Bernoulli (analytic NT)
2. Baker-Matveev linear-forms-in-logs (Diophantine approximation, NT)
3. Frey-Hellegouarch / Ribet level-lowering (modular forms, AG)
4. ABC conjecture (NT)
5. Bennett-Skinner ternary Diophantine (NT)
6. Möbius randomness / Liouville sign change (analytic NT)
7. Furstenberg correspondence / Gowers norms (additive combinatorics)
8. Dynamics on homogeneous spaces (ergodic theory)
9. p-adic analysis (NT)
10. Various Diophantine approximation techniques (NT)

Domains covered: NONE in physics, CS, biology, or economics.

## Adjacent: cross-domain catalog

There IS a `cross_domain_breakthroughs_catalog.md` in the analysis dir, but
it is a catalog of WHAT could be useful, not actual analog mining for these
two problems. Reviewed and confirmed not used as input to either problem's
analog-mining dossier.

## What counts as "genuinely new attack vector" for EXP3 scoring

A response scores high on novelty if:
- The named analog is in physics, CS, biology, or economics (off-domain)
- The named technique is NOT one of the in-house analogs above
- The bridge proposes a CONCRETE construction (named object, computable
  parameter) absent from the dossiers above

A response scores low on novelty if:
- The analog turns out to be a re-skin of an in-house item (e.g., "Ising model
  ground state" maps to "density of zeroes in Z" which is just additive
  combinatorics with extra physics jargon)
- The bridge is "consider an analogous structure" with no computable parameter
