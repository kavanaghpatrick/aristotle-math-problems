# CLAUDE.md - Math Project

> Extends `~/.claude/CLAUDE.md` (global). Project-specific rules.

---

## Mission

Solve OPEN mathematical problems using Aristotle. Not verification. Not formalization of known results. Only genuinely unsolved problems.

---

## The One Rule

**Never let the proving agent write the theorem statement.**

The prover receives a LOCKED Lean theorem. It can only fill the proof body. Nothing else.

```lean
-- LOCKED - cannot be modified
theorem target : (exact_formal_statement) := by
  sorry  -- prover fills only this
```

---

## Why This Matters

When you give Aristotle English, it finds the easiest valid interpretation:
- Proves ∃ instead of ∀
- Adds restrictive hypotheses
- Explores examples instead of proving
- Defines the statement as `Prop` but never proves it

When you give Aristotle a locked formal statement, it has no escape hatch.

---

## Workflow

1. **Formalize first** - Create exact Lean theorem statement with explicit quantifiers
2. **Verify the formalization** - Does it match the original problem exactly?
3. **Lock and submit** - Prover gets immutable theorem, fills proof only
4. **Verify the output** - Does the proven theorem match what was requested?
5. **Iterate on near-wins** - Don't scatter across problems; finish what's close

---

## Sources

- **Formal Conjectures**: https://github.com/google-deepmind/formal-conjectures (pre-formalized problems)
- **Aristotle**: `aristotle prove-from-file problem.lean`

---

## Verification

After any "success" (0 sorries + compiles):

```
□ Does the proven theorem have the same quantifiers as intended?
□ Did the AI add any restrictive hypotheses?
□ Is the proven statement actually the target, or something easier?
```

---

## Reference

- `ARISTOTLE_12_SUBMISSIONS_ANALYSIS.md` - What we learned from 12 failed attempts
