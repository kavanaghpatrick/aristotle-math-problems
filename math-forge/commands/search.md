---
name: search
description: "Search the math-forge knowledge base for findings, techniques, and approaches"
arguments: "query"
---

# /math-forge:search $ARGUMENTS

Search the knowledge base for relevant mathematical findings.

## Steps

1. Run the search:
```bash
mk search "$ARGUMENTS" --limit 10
```

2. If results found, synthesize:
   - Group by finding type (theorems, techniques, failures)
   - Highlight the most relevant findings
   - Note any failed approaches as warnings

3. If no results, suggest:
   - Broader search terms
   - Related problem IDs
   - Run `mk stats` to see what's in the KB

4. Present results with slot provenance and actionable recommendations.
