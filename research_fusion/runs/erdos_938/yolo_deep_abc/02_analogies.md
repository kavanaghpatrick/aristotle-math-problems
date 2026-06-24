# Analogies — abc-conditional structural sandwich, Erdős 938

## Closest analog: Chan 2022 itself
Chan applies abc to powerful 3-APs (not necessarily consecutive). The proof technique:
- Write n_i = a_i² b_i³ canonically (Chan Def 1)
- Apply abc to the triple after coprime reduction
- Get d ≫_ε N^{1/2-ε}

Our deep iteration deploys the **same machinery on the AP identity n_{k+1}² = n_k · n_{k+2} + d²**, which is a cleaner application (only one abc invocation, on a triple where all three terms are automatically powerful).

## Analog 1: Erdős-Mollin-Walsh (E364)
- E364: no 3 consecutive integers (n, n+1, n+2) are all powerful.
- E938: only finitely many 3-APs of consecutive powerful numbers (n_k, n_{k+1}, n_{k+2}).
- Both abc-conditional in known forms; E364's abc-conditional proof is known to follow from Hyyrö-Walsh-Mollin work plus Chan-style argument.
- E938 is harder because the consecutive-IN-A condition is weaker than n, n+1, n+2 (no integer-step constraint).

## Analog 2: Mihăilescu / Catalan
- Catalan: 8, 9 are the only consecutive perfect powers (x^p - y^q = 1 with p,q ≥ 2 has only (3²,2³)).
- Proved unconditionally (Mihăilescu 2002).
- Powerful number version: how many (n, n+1) both powerful? Folklore + conditional results bound this.

## Analog 3: Granville-Tucker abc applications
- Granville-Tucker "It's as easy as abc" (Notices AMS 2002) catalogs abc consequences.
- Specifically: abc ⟹ Fermat-like ⟹ finiteness of certain Diophantine equations.
- Our sandwich is a "structural" abc-conditional consequence, not finiteness — explicitly weaker by design.

## Analog 4: Lehmer's totient (E412)
- Conditional theorem: under GRH or under abc, "Lehmer's totient" k(n) = (n-1)/φ(n) has bounded denominators.
- Pattern: take a famous open problem, find a CONDITIONAL bound that's provable, formalize that.
- Our sandwich follows this pattern: instead of full finiteness, give a clean conditional bound that captures Chan + consecutive.

## What's NOVEL in this iteration vs. slot 1284 (iter2)
- Slot 1284 stated the problem and Chan's bound, but claimed it was "partial, not closing" without giving the rigorous statement of what IS closing.
- This iteration explicitly STATES the abc-conditional sandwich as a formalizable theorem.
- This iteration explicitly STATES the open gap (no abc-only finiteness).
- This iteration provides the cleaner AP-identity abc application: n_{k+1}² = n_k · n_{k+2} + d².
