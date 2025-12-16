# Launch Decision: December 13, 2025

## Current State

| Project | Status | Type |
|---------|--------|------|
| HOMFLY v5 | IN_PROGRESS | Algebraic proof (Boris + Refactor) |
| HOMFLY v3 | IN_PROGRESS | Outcome-focused |
| SAT LRAT | IN_PROGRESS | Pure Boris (no code) |
| Quantum Collision | FAILED | Timeout |

**Available slots**: 2

## Mass Launch Candidates Assessment

| Problem | Type | Risk |
|---------|------|------|
| PHP_5 Width | Lower bound proof | HIGH (adversary reasoning) |
| Self-Dual Code | Construction/search | HIGH (existence proof) |
| Sorting Network C(18) | Lower bound proof | VERY HIGH (combinatorial) |
| QAOA MaxCut | Quantum optimization | HIGH (Quantum Collision failed) |
| Polynomial Calculus | Proof complexity | HIGH (abstract) |

## Critical Insight

All mass_launch problems are **open research problems**, not **verification tasks**.

Boris Pattern works best for:
- ✅ "Make this code mathematically rigorous" (HOMFLY v4, v5)
- ✅ "Verify this certificate" (SAT LRAT)
- ❌ "Solve this open problem" (mass_launch)

## Decision

**WAIT before launching more.**

Rationale:
1. We have 3 diverse experiments running (algebraic, verification, minimal)
2. Quantum Collision already failed - suggests hard problems don't work
3. Better to learn from current experiments first
4. 2 slots in reserve allows quick iteration on what works

## Next Actions

1. Archive completed projects
2. Monitor in-progress experiments
3. When results come in, analyze which PATTERN worked
4. Then decide what to launch next based on evidence
