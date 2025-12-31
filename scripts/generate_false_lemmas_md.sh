#!/bin/bash
# Generate FALSE_LEMMAS.md from database
# The database is the source of truth; this script regenerates the MD file

DB="/Users/patrickkavanagh/math/submissions/tracking.db"
OUTPUT="/Users/patrickkavanagh/math/docs/FALSE_LEMMAS.md"

cat > "$OUTPUT" << 'HEADER'
# FALSE LEMMAS - DO NOT USE

> **⚠️ AUTO-GENERATED FILE** - Do not edit directly!
> Source of truth: `submissions/tracking.db` table `false_lemmas`
> Regenerate with: `./scripts/generate_false_lemmas_md.sh`

**Last generated**: $(date '+%Y-%m-%d %H:%M:%S')

This document lists lemmas that have been PROVEN FALSE. Do not use these in any proof attempts.

---

## Quick Reference

| Evidence | Meaning | Count |
|----------|---------|-------|
| 🔴 ARISTOTLE-VERIFIED | Actual Aristotle counterexample | $(sqlite3 "$DB" "SELECT COUNT(*) FROM false_lemmas WHERE evidence_level='aristotle_verified'") |
| 🟠 AI-VERIFIED | AI agents verified the math | $(sqlite3 "$DB" "SELECT COUNT(*) FROM false_lemmas WHERE evidence_level='ai_verified'") |
| 🟡 REASONING-BASED | Sound reasoning, no formal verification | $(sqlite3 "$DB" "SELECT COUNT(*) FROM false_lemmas WHERE evidence_level='reasoning_based'") |
| ⚪ TRIVIALLY FALSE | Obvious logical error | $(sqlite3 "$DB" "SELECT COUNT(*) FROM false_lemmas WHERE evidence_level='trivially_false'") |

---

HEADER

# Now dynamically replace the placeholders
TIMESTAMP=$(date '+%Y-%m-%d %H:%M:%S')
ARISTOTLE_COUNT=$(sqlite3 "$DB" "SELECT COUNT(*) FROM false_lemmas WHERE evidence_level='aristotle_verified'")
AI_COUNT=$(sqlite3 "$DB" "SELECT COUNT(*) FROM false_lemmas WHERE evidence_level='ai_verified'")
REASONING_COUNT=$(sqlite3 "$DB" "SELECT COUNT(*) FROM false_lemmas WHERE evidence_level='reasoning_based'")
TRIVIAL_COUNT=$(sqlite3 "$DB" "SELECT COUNT(*) FROM false_lemmas WHERE evidence_level='trivially_false'")

cat > "$OUTPUT" << EOF
# FALSE LEMMAS - DO NOT USE

> **⚠️ AUTO-GENERATED FILE** - Do not edit directly!
> Source of truth: \`submissions/tracking.db\` table \`false_lemmas\`
> Regenerate with: \`./scripts/generate_false_lemmas_md.sh\`

**Last generated**: $TIMESTAMP

This document lists lemmas that have been PROVEN FALSE. Do not use these in any proof attempts.

---

## Quick Reference

| Evidence | Meaning | Count |
|----------|---------|-------|
| 🔴 ARISTOTLE-VERIFIED | Actual Aristotle counterexample | $ARISTOTLE_COUNT |
| 🟠 AI-VERIFIED | AI agents verified the math | $AI_COUNT |
| 🟡 REASONING-BASED | Sound reasoning, no formal verification | $REASONING_COUNT |
| ⚪ TRIVIALLY FALSE | Obvious logical error | $TRIVIAL_COUNT |

---

## Summary Table

EOF

# Add summary table
sqlite3 -separator '|' "$DB" << 'SQL' >> "$OUTPUT"
SELECT
    '| ' || pattern_number || ' | `' || lemma_name || '` | ' ||
    CASE evidence_level
        WHEN 'aristotle_verified' THEN '🔴 ARISTOTLE'
        WHEN 'ai_verified' THEN '🟠 AI-VERIFIED'
        WHEN 'reasoning_based' THEN '🟡 REASONING'
        WHEN 'trivially_false' THEN '⚪ TRIVIAL'
    END || ' | ' || discovered_by || ' ' || discovered_date || ' |'
FROM false_lemmas ORDER BY pattern_number;
SQL

# Add table header at the right place
sed -i '' 's/^## Summary Table$/## Summary Table\n\n| # | Lemma | Evidence | Source |\n|---|-------|----------|--------|/' "$OUTPUT"

echo "" >> "$OUTPUT"
echo "---" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Add detailed entries for each pattern
sqlite3 "$DB" "SELECT pattern_number, lemma_name, evidence_level, false_statement,
    false_statement_english, counterexample, why_false,
    discovered_by, discovered_date, verified_by, verification_date,
    impact, avoid_pattern, correct_approach, notes
FROM false_lemmas ORDER BY pattern_number" | while IFS='|' read -r num name evidence stmt stmt_eng counter why disc disc_date verif verif_date impact avoid correct notes; do

    # Map evidence level to emoji
    case "$evidence" in
        aristotle_verified) badge="🔴 **ARISTOTLE-VERIFIED**" ;;
        ai_verified) badge="🟠 **AI-VERIFIED**" ;;
        reasoning_based) badge="🟡 **REASONING-BASED**" ;;
        trivially_false) badge="⚪ **TRIVIALLY FALSE**" ;;
    esac

    cat >> "$OUTPUT" << PATTERN
## Pattern $num: $name

**Status**: ❌ FALSE | $badge

**Statement** (FALSE):
\`\`\`
$stmt_eng
\`\`\`

**Counterexample**:
\`\`\`
$counter
\`\`\`

**Why it's FALSE**: $why

PATTERN

    # Add optional fields if present
    if [ -n "$verif" ]; then
        echo "**Verified by**: $verif ($verif_date)" >> "$OUTPUT"
        echo "" >> "$OUTPUT"
    fi

    if [ -n "$impact" ]; then
        echo "**Impact**: $impact" >> "$OUTPUT"
        echo "" >> "$OUTPUT"
    fi

    if [ -n "$avoid" ]; then
        echo "**Avoid**: $avoid" >> "$OUTPUT"
        echo "" >> "$OUTPUT"
    fi

    if [ -n "$correct" ]; then
        echo "**Correct approach**: $correct" >> "$OUTPUT"
        echo "" >> "$OUTPUT"
    fi

    if [ -n "$notes" ]; then
        echo "**Notes**: $notes" >> "$OUTPUT"
        echo "" >> "$OUTPUT"
    fi

    echo "---" >> "$OUTPUT"
    echo "" >> "$OUTPUT"
done

# Add footer
cat >> "$OUTPUT" << 'FOOTER'
## Database Queries

```sql
-- Quick summary
SELECT * FROM v_false_lemmas_summary;

-- Full details for a pattern
SELECT * FROM false_lemmas WHERE pattern_number = 1;

-- Find by lemma name
SELECT * FROM false_lemmas WHERE lemma_name LIKE '%cover%';

-- All AI-verified patterns
SELECT lemma_name, counterexample FROM false_lemmas
WHERE evidence_level = 'ai_verified';
```
FOOTER

echo "Generated $OUTPUT from database"
