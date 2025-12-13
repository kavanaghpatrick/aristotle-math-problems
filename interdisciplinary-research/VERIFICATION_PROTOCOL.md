# VERIFICATION PROTOCOL: Ensuring Problems Are Genuinely Unsolved

**Mission:** Create GitHub issues for interdisciplinary problems and THOROUGHLY VERIFY each one.

**Lesson Learned:** Our first attempt had 30% error rate (6/20 already solved). We CANNOT repeat this mistake.

---

## Verification Criteria (ALL Must Pass)

### 1. Genuinely Unsolved (CRITICAL)
- ✅ No proof published in peer-reviewed venue
- ✅ Explicitly stated as "open problem" in recent (2020-2025) papers
- ✅ Active research community seeking solution
- ❌ NOT an IMO/Putnam problem (those have known solutions)
- ❌ NOT a "well-known result" with existing proof
- ❌ NOT solved before 2020 (we want cutting-edge)

### 2. Suitable for Aristotle (IMPORTANT)
- ✅ Clear, finite mathematical formulation
- ✅ Provable (not just computational verification)
- ✅ Formalizable in Lean 4
- ✅ Discrete/algebraic structure (preferred)
- ❌ NOT requiring entirely new Mathlib infrastructure
- ❌ NOT purely physical intuition without formal structure

### 3. Good Success Probability (PREFERRED)
- ✅ Recent progress (2023-2025) indicating tractability
- ✅ Known proof techniques exist (even if hard)
- ✅ Bounded/finite cases available
- ✅ Success probability 5-70% range
- ❌ NOT famous intractable problems without sub-cases

### 4. Impact (MOTIVATION)
- ✅ Advances physics/CS, not just pure math curiosity
- ✅ Real-world applications
- ✅ Interdisciplinary connections
- ⚠️  Pure math problems okay if significant enough

---

## Verification Process (For Each Problem)

### Step 1: Create GitHub Issue
```
Title: [Domain] Problem Name (Success: X%)
Labels: interdisciplinary, [domain], tier-X
Body:
- Problem statement
- Why unsolved
- Interdisciplinary connection
- Recent status
- Formalizability
- Success probability
- References
```

### Step 2: Web Verification (CRITICAL)
1. **Google Scholar Search:**
   - Search: `"[problem name]" proof solved`
   - Search: `"[problem name]" 2024 OR 2025`
   - Check: Any papers claiming to solve it?

2. **arXiv Search:**
   - Recent preprints (last 6 months)
   - Check abstracts for "we prove" or "we solve"

3. **Wikipedia/MathWorld:**
   - Check if listed as solved
   - Check references for solution papers

4. **Domain-Specific Checks:**
   - NIST PQC standards (cryptography)
   - OEIS sequences (number theory)
   - Complexity Zoo (computational complexity)

### Step 3: Decision Matrix
| Finding | Action |
|---------|--------|
| Proof found (peer-reviewed) | ❌ CLOSE issue immediately |
| Claimed proof (arXiv, unverified) | ⚠️  Note in issue, monitor |
| No recent activity (5+ years) | ⚠️  Lower priority, keep open |
| Recent "open problem" statement | ✅ KEEP issue |
| Recent breakthrough progress | ✅✅ HIGH priority, keep open |

### Step 4: Document Finding
Add comment to GitHub issue:
```
## Verification Status (Date)

**Google Scholar:** [summary]
**arXiv:** [summary]
**Recent Papers:** [list]
**Verdict:** ✅ VERIFIED UNSOLVED / ❌ SOLVED / ⚠️ NEEDS MONITORING

**Evidence:** [links]
```

---

## Systematic Approach

### Phase 1: Top Tier (9 problems, 30-40% success) ← START HERE
1. Spectral Gap Bounds for Odd-Diameter Graphs (30-45%)
2. QC Syndrome Decoding Complexity (30-40%)
3. Sorting Network Size for n=18 (35%)
4. Jones Polynomial Certifiable Cases (30-40%)
5. Resolution Complexity for Specific SAT Formulas (35%)
6. Polar Codes Finite Blocklength Scaling (30-35%)
7. Quantum Query Complexity - Collision Problem (30%)
8. Quantum Communication - Disjointness (30%)
9. Two-Sided Vertex Expansion Beyond 60% (25-40%)

**Process:** Create issue → Verify → Keep/Close → Move to next

### Phase 2: High-Value (16 problems, 20-30% success)
Only proceed if Phase 1 successful (≥7/9 verified unsolved)

### Phase 3: Medium (13 problems, 15-20% success)
Only proceed if Phase 2 successful

### Phase 4: Lower Priority (remaining problems)
Only if time permits and previous phases successful

---

## Red Flags (Immediate Investigation Required)

1. **Problem appears in textbooks** → Likely solved
2. **IMO/Putnam/competition problem** → Has known solution
3. **"Well-known result" or "classical theorem"** → Already proven
4. **Solved date in Wikipedia** → Definitely solved
5. **Multiple Google results with "proof"** → Investigate immediately
6. **No papers since 2020** → May be intractable
7. **OEIS sequence has formula** → Problem likely solved

---

## Success Metrics

**Target:** ≥80% verification rate (≥7/9 top problems genuinely unsolved)

**Acceptable:** ≥70% verification rate (≥6/9 top problems)

**Unacceptable:** <70% verification rate (need better research)

**Last Attempt:** 70% verification rate (14/20), but that included 14 from original list. The 6 removed were all from original batch.

**This Attempt Goal:** ≥85% verification rate

---

## Example Verification (Template)

### Problem: Spectral Gap Bounds for Odd-Diameter Graphs

**Step 1: Create Issue** ✅
- Issue #XX created with full details

**Step 2: Web Verification**

**Google Scholar Search:**
```
Query: "spectral gap" "odd diameter" "Exoo" 2024
Results:
- Exoo (2024) "Improved bounds..." - states problem remains open
- No papers claiming full solution found
```

**arXiv Search:**
```
Query: spectral gap odd diameter
Recent: 3 papers in 2024, all cite Exoo, none claim solution
```

**Domain Check:**
- Liu et al. (2023) "Unsolved Problems in Spectral Graph Theory" - lists as open

**Step 3: Decision**
✅ VERIFIED UNSOLVED
- Multiple 2024 papers cite as open
- Liu et al. (2023) explicit "unsolved problems" list
- Exoo (2024) improved bounds but didn't solve
- Active research community

**Step 4: Document**
Added verification comment to issue #XX with links

---

## Workflow

For EACH of 72+ problems:
1. Create GitHub issue (5 min)
2. Web verification (10-15 min)
3. Decision + documentation (5 min)
4. **Total: 20-25 min per problem**

**Estimated time for top 9:** 3-4 hours
**Estimated time for all 72:** 24-30 hours (spread over multiple sessions)

---

## Start Point

Begin with Top Tier Problem #1:
**Spectral Gap Bounds for Odd-Diameter Graphs**

Create issue → Verify → Document → Proceed to #2
