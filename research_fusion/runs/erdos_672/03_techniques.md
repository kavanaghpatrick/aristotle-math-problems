# Erdős 672 — Stage 3 Techniques Shortlist (k = 4, ℓ = 3)

## Ranking by fit-score

### Rank 1: HTT/GHP ternary-equation chain (fit 0.55)

**Reference**: Hajdu, Tengely, Tijdeman 2009 (cubes case);
Győry, Hajdu, Pintér 2009 (general power case).

**Pipeline**:
1. Smooth-part / cubefree-part decomposition of each AP term.
2. Reduction to finite list of ternary equations `A*X^3 + B*Y^3 = C*Z^3`.
3. Frey curve attachment + modularity (Wiles-Taylor).
4. Bennett-Skinner level-lowering to bounded-radical level.
5. Empty-newform verification at target levels.

**Strengths**: published, well-documented, exact case (k=4, l=3).
**Weaknesses**: Mathlib's Frey/modularity infrastructure is partial.
Aristotle would need to either find existing lemmas or accept partial
axiomatization of the modularity step.

**Aristotle fit**: HIGH. Aristotle's informal reasoner can decompose into
lemmas it can attempt one-by-one, and the deepest sub-step (modularity)
is well-documented as a named theorem.

### Rank 2: Bennett-Bruin-Győry-Hajdu Frey-only chain (fit 0.50)

**Reference**: BBGH 2006 (k <= 11 case).

**Pipeline**: Direct Frey curve from the 4-term AP, modularity, level
analysis, empty newform space verification.

**Strengths**: more direct than HTT, avoids the explicit ternary list.
**Weaknesses**: relies on Frey infrastructure not fully in Mathlib;
the level-lowering step depends on multiple intermediate results.

### Rank 3: Hypergeometric / Baker's bounds (fit 0.35)

**Reference**: Bilu-Hanrot-Voutier, Baker bounds.

**Pipeline**: Effective bounds on solutions to Thue equations, finite
enumeration of residual cases.

**Strengths**: effective, computational.
**Weaknesses**: the constants are large; would generate an unwieldy
proof certificate; formalization requires nontrivial constant-tracking.

### Rank 4 (REJECTED): Erdős-Ko-Rado shifted-AP transplant (fit 0.05)

Grok's verdict (May 30 2026): not viable. The obstruction is arithmetic
(S-unit, local solubility, Mordell-Weil rank), not combinatorial.

### Rank 5: Computational closure on small ranges (fit 0.20)

Bound `max(n, d) <= 10^6` and exhaustively verify. Insufficient as a full
proof of the (k=4, l=3) case (does not extend), but Aristotle could
produce a clean Decidable verification of small-range bounded statement.

## Selection

We select Rank 1 (HTT/GHP ternary-equation chain) as the primary named
technique for the FUSION dossier. Reason: it is the publishedproof for the
exact case, it is the one Aristotle most plausibly formalizes, and it lets
us frame the submission honestly as "formalize the known proof, not find
a new one".

The honest-disclaimer must surface that this is FORMALIZATION-LANE work,
not gap-closure novel work.
