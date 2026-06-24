# troika: generalizing the BEGL96 (3,4,7) mechanism to arbitrary admissible D

My refined lane (per team lead): extract the BEGL96 (3,4,7) mechanism and generalize to arbitrary
admissible D. Decorrelated from sumset (who owns the CRT-at-scale route). All verified computationally.

## CORRECTION (breaker was right — I retract earlier thresholds)
breaker caught that my earlier "converged" thresholds were truncation artifacts. CORRECTED, verified
by THREE independent engines (numpy bitset, big-int bitshift, recursive subset-sum):
| k | OLD (wrong) | CORRECT N₀ for (3,4,7) | verified to |
|---|---|---|---|
| 1 | 581 | **581** (unchanged, = BEGL96) | exact |
| 2 | 785 743 | **3 982 888** | N=70M; 4^12,4^13 bands empty |
| 3 | 57 751 591 | **166 025 260** (≥ this; 4^14 band empty, 3^18/7^10/4^15 unchecked) | N=300M |
The lesson: NEVER trust "largest gap ≈ cutoff" — recompute with margin. (breaker's standing warning.)

## THE MECHANISM FINGERPRINT (the lead's question: how does the BEGL96 induction bottom out?)
The largest exceptional integers sit in **thin bands just above/below high powers of the bases**:
- 785743 ≈ 4^10 / 1.34;  3982888 ≈ 4^11 / 1.05;  166025260 ≈ 3^17 · 1.29.
- The bands THIN as the power grows (4^9 band: several exceptionals; 4^11 band: 2; 4^12+: empty).
**Why these are the hard n:** to represent n just below a big power d^J, you cannot use d^J (it
overshoots) — you must rebuild n entirely from the SMALLER atoms of all bases. Whether that succeeds
depends on how the smaller powers of the *different* bases interleave near n, i.e. on the spacing
|dᵢ^p − dⱼ^q|. **This is exactly the quantity Mignotte–Waldschmidt bound (BEGL96's |3^p−4^q| Cor.
10.1).** The induction bottoms out at the power-boundary bands; MW certifies the bands eventually
close. This is the fingerprint the lead asked me to find, and it transfers to general D.

## KEY STRUCTURAL LEMMA (troika, RIGOROUS) — why MW is always available
> **Lemma.** For admissible D (all d≥3, gcd(D)=1, |D|≥2), D contains a multiplicatively-independent
> pair {a,b} (log a / log b ∉ ℚ, i.e. a^p ≠ b^q for all p,q≥1).
>
> **Proof.** Multiplicative-dependence (a~b iff a,b are both powers of a common integer) is an
> EQUIVALENCE relation: its classes are exactly {powers of a fixed primitive base c}, where the
> primitive base of n = ∏pᵢ^{eᵢ} is ∏pᵢ^{eᵢ/g}, g = gcd(eᵢ). (Transitivity verified exhaustively
> on [2,200); follows because a~b ⟺ primRoot(a)=primRoot(b).) If D had NO independent pair, all of D
> would lie in one class — all powers of a common c>=2 — forcing c divides gcd(D), contradicting gcd(D)=1. QED

Verified: 0 violations across all 5429 admissible gcd=1 families with d∈[3,40], |D|≤5.

**Consequence:** the MW linear-forms machinery is structurally AVAILABLE for every admissible D —
there is always a multiplicatively-independent base pair to which a Baker/MW lower bound on
|a^p - b^q| applies. This removes one obstacle to generalization (the tool always has a target).

## The "dominant pair" structure (empirical, candidate condition X)
Every harmonic-boundary family has a multiplicatively-independent pair carrying the bulk of the
density:
| D | dominant indep pair | pair density / total |
|---|---|---|
| (3,4,7) | {3,4} | 0.833 / 1.000 |
| (3,5,7,13) | {3,5} | 0.750 / 1.000 |
| (3,4,10,19), (3,4,11,16) | {3,4} | 0.833 / 1.000 |
| (3,6,7,13,21) | {3,6} | 0.700 / 1.000 |
The picture generalizing (3,4,7): a dominant mult-indep pair {a,b} carries most of the density
(MW controls its interleaving), and the remaining bases plug the residual gap + supply residue
coverage (via gcd=1 + the Residue Lemma, [[lift_sufficiency_mechanism]]).

## Honest status of the generalization
- **What generalizes cleanly:** (i) the d^k scaling reduction; (ii) gcd=1 necessity; (iii) residue
  covering; (iv) **the existence of a mult-independent pair (my Lemma) — so MW is always applicable**;
  (v) the band-boundary fingerprint of where the induction bottoms out.
- **What does NOT yet generalize:** a *uniform* MW/Baker bound across an arbitrary pair {a,b} with the
  effective constants needed to bound N₀(D,k), AND the combinatorial argument that the remaining
  bases close every band. BEGL96 did this only for (3,4,7) by hand (one explicit MW inequality + a
  finite check to 581). For general D the effective constants and band-closure are open — this is
  exactly the regime BEGL call themselves "fairly far from."
- **The realistic generalized theorem** (condition X as weak as I can presently justify):
  *If D is admissible AND its dominant mult-independent pair {a,b} satisfies an effective MW bound
  with the residual bases supplying full residue coverage and bounded-gap density (maverick's Lemma
  BG, [[maverick_bounded_gap_lemma]]), then R(D,k) is cofinite for every k.* The hypotheses (iii)–(v)
  are met for ALL admissible D; the open part is purely the EFFECTIVE/quantitative MW step + band
  closure, not a structural obstruction. **No elementary closure; not bare-submittable.**

See also [[troika_SUMMARY]], [[troika_synthesis_difficulty_located]], [[breaker_engine_and_347anomaly]].
