#!/usr/bin/env python3
"""
Multi-agent audit workflow for Lean submissions.

Sends code to Grok and Gemini for independent review, records results in database.
Usage: python3 scripts/multi_agent_audit.py submissions/file.lean [--submission-uuid UUID]
"""

import subprocess
import json
import sqlite3
import sys
import os
import re
from pathlib import Path
from datetime import datetime

# Paths
MATH_DIR = Path(__file__).resolve().parent.parent
DB_PATH = MATH_DIR / "submissions" / "tracking.db"

# API Keys
GROK_API_KEY = os.environ.get("GROK_API_KEY")
GEMINI_AVAILABLE = subprocess.run(["which", "gemini"], capture_output=True).returncode == 0


def run_grok_audit(code: str, filename: str) -> dict:
    """Send code to Grok for critical issue review."""
    if not GROK_API_KEY:
        return {"status": "skipped", "reason": "GROK_API_KEY not set"}

    prompt = f"""You are a Lean 4 code reviewer. Review this submission for CRITICAL issues only.

DO NOT solve any math. DO NOT discuss proof strategy.
ONLY check for these specific bugs:

1. **sInf unrestricted**: Does any definition use `sInf {{n | ∃ E : Finset (Sym2 V), ...}}`
   without requiring `E ⊆ G.edgeFinset`? This allows non-graph edges.

2. **Finset.sym2 self-loops**: Does code use `.sym2` on a Finset?
   Remember: `{{1,2,3}}.sym2 = {{s(1,1), s(1,2), s(1,3), s(2,2), s(2,3), s(3,3)}}` includes self-loops!
   Self-loops like `s(v,v)` are NOT valid SimpleGraph edges.

3. **Set vs Finset**: Is `Set V` used with `.edgeFinset` without `DecidablePred`?

4. **Axiom declarations**: Any `axiom` declarations (forbidden in submissions)?

5. **Missing instances**: Graph operations without `[DecidableRel G.Adj]`?

Respond with JSON only:
{{
  "critical_issues": [{{
    "type": "sinf_unrestricted|sym2_selfloop|set_finset|axiom|missing_instance",
    "line": <line_number_or_null>,
    "description": "brief description"
  }}],
  "warnings": ["warning1", "warning2"],
  "verdict": "PASS|FAIL|NEEDS_REVIEW"
}}

File: {filename}
```lean
{code}
```"""

    # Write request to temp file for curl
    request = {
        "messages": [{"role": "user", "content": prompt}],
        "model": "grok-4",
        "temperature": 0,
        "max_tokens": 1000
    }

    req_file = Path("/tmp/grok_audit_req.json")
    req_file.write_text(json.dumps(request))

    try:
        result = subprocess.run(
            ["curl", "-s", "-X", "POST",
             "https://api.x.ai/v1/chat/completions",
             "-H", f"Authorization: Bearer {GROK_API_KEY}",
             "-H", "Content-Type: application/json",
             "-d", f"@{req_file}"],
            capture_output=True,
            text=True,
            timeout=180
        )

        if result.returncode != 0:
            return {"status": "error", "error": result.stderr}

        response = json.loads(result.stdout)
        content = response.get("choices", [{}])[0].get("message", {}).get("content", "")

        # Try to extract JSON from response
        json_match = re.search(r'\{[\s\S]*\}', content)
        if json_match:
            return {"status": "success", "result": json.loads(json_match.group())}
        else:
            return {"status": "success", "result": {"raw": content}}

    except subprocess.TimeoutExpired:
        return {"status": "timeout"}
    except Exception as e:
        return {"status": "error", "error": str(e)}


def run_gemini_audit(code: str, filename: str) -> dict:
    """Send code to Gemini for semantic review."""
    if not GEMINI_AVAILABLE:
        return {"status": "skipped", "reason": "gemini CLI not available"}

    prompt = f"""Review this Lean 4 submission for mathematical formalization correctness.

Focus on:
1. Do the DEFINITIONS match the mathematical intent? (e.g., triangle covering must use actual graph edges)
2. Are there any semantic gaps between the Lean statement and the likely mathematical intent?
3. Could any definition allow "trivial" proofs that don't reflect the real problem?

Specific checks:
- For covering numbers: Must restrict edge sets to G.edgeFinset
- For Finset.sym2: Remember it includes diagonal elements s(v,v)
- For graph operations: Need DecidableRel G.Adj

Respond with JSON:
{{
  "definition_issues": [{{"name": "def_name", "issue": "description"}}],
  "semantic_gaps": ["gap1", "gap2"],
  "verdict": "CORRECT|SUSPICIOUS|INCORRECT",
  "confidence": 0.0-1.0
}}

File: {filename}
```lean
{code}
```"""

    try:
        result = subprocess.run(
            ["gemini", "-p", prompt],
            capture_output=True,
            text=True,
            timeout=120
        )

        if result.returncode != 0:
            return {"status": "error", "error": result.stderr}

        content = result.stdout
        json_match = re.search(r'\{[\s\S]*\}', content)
        if json_match:
            return {"status": "success", "result": json.loads(json_match.group())}
        else:
            return {"status": "success", "result": {"raw": content}}

    except subprocess.TimeoutExpired:
        return {"status": "timeout"}
    except Exception as e:
        return {"status": "error", "error": str(e)}


def run_local_audit(filepath: Path) -> dict:
    """Run local audit scripts."""
    results = {"syntax": None, "definitions": None}

    # Syntax check
    try:
        syntax_result = subprocess.run(
            ["./scripts/validate_submission.sh", str(filepath)],
            capture_output=True,
            text=True,
            cwd=MATH_DIR,
            timeout=120
        )
        results["syntax"] = {
            "passed": syntax_result.returncode == 0,
            "output": syntax_result.stdout + syntax_result.stderr
        }
    except Exception as e:
        results["syntax"] = {"passed": False, "error": str(e)}

    # Definition audit
    try:
        def_result = subprocess.run(
            ["./scripts/audit_definitions.sh", str(filepath)],
            capture_output=True,
            text=True,
            cwd=MATH_DIR,
            timeout=60
        )
        results["definitions"] = {
            "passed": def_result.returncode == 0,
            "output": def_result.stdout + def_result.stderr
        }
    except Exception as e:
        results["definitions"] = {"passed": False, "error": str(e)}

    return results


def record_audit(db: sqlite3.Connection, submission_uuid: str,
                 local_results: dict, grok_results: dict, gemini_results: dict):
    """Record audit results in database."""

    # Update submission record
    grok_passed = (grok_results.get("status") == "success" and
                   grok_results.get("result", {}).get("verdict") == "PASS")
    gemini_passed = (gemini_results.get("status") == "success" and
                     gemini_results.get("result", {}).get("verdict") == "CORRECT")

    db.execute("""
        UPDATE submissions SET
            grok_reviewed = 1,
            grok_issues = ?,
            gemini_reviewed = 1,
            gemini_issues = ?
        WHERE uuid = ?
    """, (
        json.dumps(grok_results),
        json.dumps(gemini_results),
        submission_uuid
    ))

    # Log audit
    db.execute("""
        INSERT INTO audit_log (submission_id, action, agent, details)
        SELECT id, 'multi_agent_audit', 'multi', ?
        FROM submissions WHERE uuid = ?
    """, (
        json.dumps({
            "local": local_results,
            "grok_verdict": grok_results.get("result", {}).get("verdict"),
            "gemini_verdict": gemini_results.get("result", {}).get("verdict")
        }),
        submission_uuid
    ))

    db.commit()


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 multi_agent_audit.py <file.lean> [--submission-uuid UUID]")
        sys.exit(1)

    filepath = Path(sys.argv[1])
    if not filepath.exists():
        print(f"Error: File not found: {filepath}")
        sys.exit(1)

    # Parse optional UUID
    submission_uuid = None
    if "--submission-uuid" in sys.argv:
        idx = sys.argv.index("--submission-uuid")
        if idx + 1 < len(sys.argv):
            submission_uuid = sys.argv[idx + 1]

    print("=" * 70)
    print("MULTI-AGENT AUDIT WORKFLOW")
    print("=" * 70)
    print(f"File: {filepath}")
    print(f"UUID: {submission_uuid or 'not specified'}")
    print()

    # Read code
    code = filepath.read_text()
    filename = filepath.name

    # Phase 1: Local audits
    print("Phase 1: Local Audits")
    print("-" * 40)
    local_results = run_local_audit(filepath)

    syntax_ok = local_results["syntax"]["passed"]
    defs_ok = local_results["definitions"]["passed"]
    print(f"  Syntax:      {'✅ PASS' if syntax_ok else '❌ FAIL'}")
    print(f"  Definitions: {'✅ PASS' if defs_ok else '❌ FAIL'}")

    if not syntax_ok:
        print("\n❌ ABORTING: Syntax errors must be fixed first")
        print(local_results["syntax"].get("output", "")[:500])
        sys.exit(1)

    # Phase 2: Grok review
    print()
    print("Phase 2: Grok Review (Critical Issues)")
    print("-" * 40)
    grok_results = run_grok_audit(code, filename)

    if grok_results["status"] == "success":
        verdict = grok_results.get("result", {}).get("verdict", "UNKNOWN")
        print(f"  Verdict: {verdict}")

        issues = grok_results.get("result", {}).get("critical_issues", [])
        if issues:
            print(f"  Critical issues ({len(issues)}):")
            for issue in issues:
                print(f"    - [{issue.get('type')}] {issue.get('description')}")
    elif grok_results["status"] == "skipped":
        print(f"  Skipped: {grok_results.get('reason')}")
    else:
        print(f"  Error: {grok_results.get('error', 'unknown')}")

    # Phase 3: Gemini review
    print()
    print("Phase 3: Gemini Review (Semantic)")
    print("-" * 40)
    gemini_results = run_gemini_audit(code, filename)

    if gemini_results["status"] == "success":
        verdict = gemini_results.get("result", {}).get("verdict", "UNKNOWN")
        confidence = gemini_results.get("result", {}).get("confidence", "?")
        print(f"  Verdict: {verdict} (confidence: {confidence})")

        def_issues = gemini_results.get("result", {}).get("definition_issues", [])
        if def_issues:
            print(f"  Definition issues ({len(def_issues)}):")
            for issue in def_issues:
                print(f"    - {issue.get('name')}: {issue.get('issue')}")
    elif gemini_results["status"] == "skipped":
        print(f"  Skipped: {gemini_results.get('reason')}")
    else:
        print(f"  Error: {gemini_results.get('error', 'unknown')}")

    # Phase 4: Record in database
    if submission_uuid and DB_PATH.exists():
        print()
        print("Phase 4: Recording in Database")
        print("-" * 40)

        conn = sqlite3.connect(DB_PATH)
        record_audit(conn, submission_uuid, local_results, grok_results, gemini_results)
        conn.close()
        print("  ✅ Audit recorded")

    # Summary
    print()
    print("=" * 70)
    print("AUDIT SUMMARY")
    print("=" * 70)

    grok_verdict = grok_results.get("result", {}).get("verdict", "SKIPPED")
    gemini_verdict = gemini_results.get("result", {}).get("verdict", "SKIPPED")

    all_pass = (
        syntax_ok and defs_ok and
        grok_verdict in ["PASS", "SKIPPED"] and
        gemini_verdict in ["CORRECT", "SKIPPED"]
    )

    if all_pass:
        print("✅ ALL CHECKS PASSED")
        print("   Safe to submit to Aristotle")
    else:
        print("⚠️  ISSUES FOUND - Review before submitting")
        if not defs_ok:
            print("   - Local definition audit failed")
        if grok_verdict == "FAIL":
            print("   - Grok found critical issues")
        if gemini_verdict == "INCORRECT":
            print("   - Gemini found semantic issues")

    sys.exit(0 if all_pass else 1)


if __name__ == "__main__":
    main()
