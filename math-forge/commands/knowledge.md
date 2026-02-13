---
name: knowledge
description: "Get comprehensive knowledge report for a specific problem"
arguments: "problem_id"
---

# /math-forge:knowledge $ARGUMENTS

Get everything we know about a mathematical problem.

## Steps

1. Run comprehensive lookup:
```bash
mk find "$ARGUMENTS"
```

2. Synthesize the report:
   - **Problem status**: open/partial/proven/false
   - **Proven results**: List all [PROVEN] findings with slot numbers
   - **Failed approaches**: List all [FAILED] with reasons and avoid patterns
   - **False lemmas**: Any disproven claims (CRITICAL warnings)
   - **Active strategies**: What's currently in flight
   - **Untried strategies**: Potential new angles

3. Provide actionable summary:
   - If problem is open: suggest next approach based on what we know
   - If problem has near-misses: suggest closing the gap
   - If problem has many failures: warn against repeating them
