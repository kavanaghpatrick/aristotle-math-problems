---
name: number-theory
description: "Number theory knowledge base queries. Use when working on NT problems (Feit-Thompson, Erdős, Wolstenholme, primes, modular arithmetic). Provides KB search, proven techniques, and failed approach warnings."
---

# Number Theory Knowledge

Query the math-forge knowledge base for number theory findings.

## When to Use
- Starting work on any NT problem (FT p=3, Erdős conjectures, Wolstenholme, etc.)
- Looking for proven techniques in number theory domain
- Checking what approaches have been tried and failed

## Steps

1. **Search for related findings**:
   ```bash
   mk search "<problem keywords>" --domain nt
   ```

2. **Get full problem context**:
   ```bash
   mk find "<problem_id>"
   ```

3. **Check failed approaches** (CRITICAL — do NOT repeat these):
   ```bash
   mk failed "<problem keywords>"
   ```

4. **Review proven techniques**:
   ```bash
   mk strategies nt
   ```

## Key NT Areas in KB
- **Feit-Thompson p=3**: 16+ proven constraints, cubic/quartic residues, Wieferich conditions
- **Erdős problems**: 370, 850, 427, 350, 36, 364, 1052 — various stages
- **Wolstenholme/WSS**: Proven infrastructure (slots 594-595)
- **Carmichael/Artin/Agoh-Giuga**: Proven structural results

## Output
Present findings grouped by type: [PROVEN] theorems first, then [TECHNIQUE] insights, then [FAILED] warnings. Always include slot numbers for provenance.
