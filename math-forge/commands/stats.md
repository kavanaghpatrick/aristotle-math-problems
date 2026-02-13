---
name: stats
description: "Show math-forge knowledge base dashboard and statistics"
---

# /math-forge:stats

Display the knowledge base dashboard.

## Steps

1. Run stats:
```bash
mk stats
```

2. Present the dashboard showing:
   - Total findings by type (theorem, technique, failure, false_lemma, etc.)
   - Domain distribution (NT, algebra, combinatorics, analysis)
   - Strategy outcomes (proven, partial, failed, in_flight, untried)
   - Problem count and freshness

3. If KB is empty, suggest running bootstrap:
```bash
math-forge/scripts/bootstrap.sh
```
