---
name: failed
description: "Check failed approaches and false lemmas before writing a sketch"
arguments: "keyword (optional)"
---

# /math-forge:failed $ARGUMENTS

Check what approaches have been tried and failed.

**CRITICAL: Run this BEFORE writing any proof sketch to avoid repeating known-bad approaches.**

## Steps

1. Query failed approaches:
```bash
mk failed "$ARGUMENTS"
```

2. Present each failure with:
   - What was tried (approach name)
   - Why it failed (specific reason)
   - What to avoid (avoid_pattern)
   - Which slot attempted it

3. Add strong warning:
   > Do NOT repeat any approach listed above without a fundamentally new angle.
   > Each failed approach was attempted by Aristotle and proven to not work.

4. If no failures found for this keyword, note that explicitly — it means the approach space is unexplored.
