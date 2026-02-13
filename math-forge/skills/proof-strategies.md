---
name: proof-strategies
description: "Proof strategy comparison and cross-domain technique transfer. Use when choosing between approaches, comparing technique effectiveness, or looking for techniques from related problems."
---

# Proof Strategy Analysis

Compare and select proof strategies using KB data.

## Steps

### 1. Survey Proven Techniques
```bash
mk strategies                    # All domains
mk strategies nt                 # Number theory only
mk strategies combinatorics      # Combinatorics only
```

### 2. Search for Specific Techniques
```bash
mk search "induction"
mk search "pigeonhole"
mk search "Euler criterion"
mk search "native_decide"
```

### 3. Check What Failed
```bash
mk failed "<technique or problem>"
```

### 4. Cross-Domain Transfer
Look for techniques proven in one domain that might apply to another:
- NT techniques (modular arithmetic, Euler criterion) → algebraic problems
- Combinatorial techniques (pigeonhole, counting) → NT bounds
- Computational techniques (native_decide, interval_cases) → bounded cases

## Strategy Selection Criteria
1. Has this approach been tried before? Check `mk failed`
2. Has a related technique worked on a related problem? Check `mk strategies`
3. Is there a bounded case we can prove first? Consider Track B (native_decide)
4. Is the domain NT/algebra (75-100% AI success) or combinatorics (7-50%)?

## Output
Present a ranked list of candidate strategies with:
- Prior evidence (slot numbers, success/failure history)
- Estimated feasibility based on domain and technique
- Recommended approach with justification
