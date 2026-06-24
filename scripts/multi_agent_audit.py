#!/usr/bin/env python3
"""
Multi-agent audit workflow for Lean submissions.

Sends code to Claude and Gemini for independent cross-model review, records
results in database. This is the G2-L2 adversary node of the Method-1
verification gauntlet: a second and third model (NOT the author) inspect the
formalization for critical Lean bugs (Claude) and semantic/faithfulness gaps
(Gemini).

Grok was REMOVED (2026-06-01): the x.ai team has no access to a live model
(grok-4 / grok-4.3 both dead — re-confirmed in the Method-1 scale-up plan,
Risk 3). The dead Grok node is replaced by a Claude reviewer so the ensemble is
Gemini + Claude, per the plan's "G2-L2 cross-model adversary (Gemini+Claude,
NOT Grok)".

Usage: python3 scripts/multi_agent_audit.py submissions/file.lean [--submission-uuid UUID]
"""

import subprocess
import json
import sqlite3
import sys
import os
import re
import tempfile
from pathlib import Path
from datetime import datetime

# Paths
MATH_DIR = Path(__file__).resolve().parent.parent
DB_PATH = MATH_DIR / "submissions" / "tracking.db"

# CLI availability. Both Gemini and Claude are invoked via the repo's standard
# `bash -c 'TOOL -p "$(cat tmpfile)"'` pattern (see debate.py). The `claude`
# entry point is a login-shell function (teamclaude proxy), so Claude is invoked
# through a login shell (`bash -lc`) which sources it. Codex is the fallback
# third model if Claude is unreachable, keeping the ensemble at two non-Gemini
# reviewers' worth of coverage without ever resurrecting Grok.
GEMINI_AVAILABLE = subprocess.run(["which", "gemini"], capture_output=True).returncode == 0
CODEX_AVAILABLE = subprocess.run(["which", "codex"], capture_output=True).returncode == 0


def _parse_verdict_json(content: str) -> dict:
    """Extract the last JSON object from a model's free-text reply."""
    matches = re.findall(r'\{[\s\S]*?\}', content)
    # Prefer the largest/last balanced-looking object that parses.
    for cand in reversed(matches):
        try:
            return json.loads(cand)
        except Exception:
            continue
    # Greedy single-object fallback.
    m = re.search(r'\{[\s\S]*\}', content)
    if m:
        try:
            return json.loads(m.group())
        except Exception:
            pass
    return {"raw": content}


def run_claude_audit(code: str, filename: str) -> dict:
    """Send code to Claude (3rd ensemble model) for critical-issue review.

    Replaces the dead Grok node. Claude is the always-available cross-model
    adversary in the Method-1 gauntlet. Invoked via a login shell so the
    `claude` shell function (teamclaude proxy) resolves; falls back to Codex if
    the Claude entry point is unavailable.
    """
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

6. **Statement faithfulness**: Has the theorem statement been weakened, bounded,
   or had a hypothesis stripped relative to a faithful formalization? Flag any
   `native_decide`/`decide` over an injected numeric ceiling, or a conclusion
   that is strictly weaker than the apparent intent.

Respond with JSON only:
{{
  "critical_issues": [{{
    "type": "sinf_unrestricted|sym2_selfloop|set_finset|axiom|missing_instance|weakened_statement",
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

    prompt_file = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
            f.write(prompt)
            prompt_file = f.name

        # Try Claude first (login shell sources the `claude` function).
        result = subprocess.run(
            ["bash", "-lc", f'claude -p "$(cat \'{prompt_file}\')"'],
            capture_output=True,
            text=True,
            timeout=300,
        )
        content = (result.stdout or "").strip()

        # Fallback to Codex if Claude produced nothing usable.
        if (result.returncode != 0 or not content) and CODEX_AVAILABLE:
            result = subprocess.run(
                ["bash", "-c",
                 f'codex exec --full-auto --sandbox read-only "$(cat \'{prompt_file}\')"'],
                capture_output=True,
                text=True,
                timeout=300,
            )
            content = (result.stdout or "").strip()

        if not content:
            err = (result.stderr or "")[-500:]
            return {"status": "error", "error": f"empty reply; stderr: {err}"}

        return {"status": "success", "result": _parse_verdict_json(content)}

    except subprocess.TimeoutExpired:
        return {"status": "timeout"}
    except FileNotFoundError:
        return {"status": "skipped", "reason": "neither claude nor codex CLI available"}
    except Exception as e:
        return {"status": "error", "error": str(e)}
    finally:
        if prompt_file and os.path.exists(prompt_file):
            os.unlink(prompt_file)


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

    prompt_file = None
    try:
        # Write prompt to a temp file and read via shell to avoid arg-length
        # limits on large Lean files (repo standard, cf. debate.py).
        with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
            f.write(prompt)
            prompt_file = f.name

        result = subprocess.run(
            ["bash", "-c", f'gemini -p "$(cat \'{prompt_file}\')"'],
            capture_output=True,
            text=True,
            timeout=180
        )

        content = (result.stdout or "").strip()
        if not content:
            stderr = "\n".join(
                line for line in (result.stderr or "").split("\n")
                if "DeprecationWarning" not in line and "punycode" not in line and line.strip()
            )
            return {"status": "error", "error": stderr[:500] or "empty reply"}

        return {"status": "success", "result": _parse_verdict_json(content)}

    except subprocess.TimeoutExpired:
        return {"status": "timeout"}
    except Exception as e:
        return {"status": "error", "error": str(e)}
    finally:
        if prompt_file and os.path.exists(prompt_file):
            os.unlink(prompt_file)


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
                 local_results: dict, claude_results: dict, gemini_results: dict):
    """Record audit results in database.

    Claude is the 3rd ensemble model (replacing dead Grok). To avoid an
    unowned schema change, the Claude reviewer payload is persisted in the
    existing `grok_issues` column (the legacy "critical-issue reviewer" slot);
    the JSON itself is self-describing (`status`/`result`). The write is
    defensive: columns that don't exist are skipped so the audit never crashes
    the caller.
    """
    # Try the full update; fall back to only-existing columns.
    try:
        db.execute(
            "UPDATE submissions SET grok_issues = ?, gemini_issues = ? WHERE uuid = ?",
            (json.dumps(claude_results), json.dumps(gemini_results), submission_uuid),
        )
    except sqlite3.OperationalError:
        # One of the columns may be absent on an older DB — write what we can.
        for col, payload in (("grok_issues", claude_results),
                             ("gemini_issues", gemini_results)):
            try:
                db.execute(
                    f"UPDATE submissions SET {col} = ? WHERE uuid = ?",
                    (json.dumps(payload), submission_uuid),
                )
            except sqlite3.OperationalError:
                pass

    # Log audit (agent='gemini+claude').
    try:
        db.execute("""
            INSERT INTO audit_log (submission_id, action, agent, details)
            SELECT id, 'multi_agent_audit', 'gemini+claude', ?
            FROM submissions WHERE uuid = ?
        """, (
            json.dumps({
                "local": local_results,
                "claude_verdict": claude_results.get("result", {}).get("verdict"),
                "gemini_verdict": gemini_results.get("result", {}).get("verdict"),
            }),
            submission_uuid,
        ))
    except sqlite3.OperationalError:
        pass

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

    # Phase 2: Claude review (3rd ensemble model; replaces dead Grok)
    print()
    print("Phase 2: Claude Review (Critical Issues)")
    print("-" * 40)
    claude_results = run_claude_audit(code, filename)

    if claude_results["status"] == "success":
        verdict = claude_results.get("result", {}).get("verdict", "UNKNOWN")
        print(f"  Verdict: {verdict}")

        issues = claude_results.get("result", {}).get("critical_issues", [])
        if issues:
            print(f"  Critical issues ({len(issues)}):")
            for issue in issues:
                print(f"    - [{issue.get('type')}] {issue.get('description')}")
    elif claude_results["status"] == "skipped":
        print(f"  Skipped: {claude_results.get('reason')}")
    else:
        print(f"  Error: {claude_results.get('error', 'unknown')}")

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
        record_audit(conn, submission_uuid, local_results, claude_results, gemini_results)
        conn.close()
        print("  ✅ Audit recorded")

    # Summary
    print()
    print("=" * 70)
    print("AUDIT SUMMARY")
    print("=" * 70)

    claude_verdict = claude_results.get("result", {}).get("verdict", "SKIPPED")
    gemini_verdict = gemini_results.get("result", {}).get("verdict", "SKIPPED")

    all_pass = (
        syntax_ok and defs_ok and
        claude_verdict in ["PASS", "SKIPPED"] and
        gemini_verdict in ["CORRECT", "SKIPPED"]
    )

    if all_pass:
        print("✅ ALL CHECKS PASSED")
        print("   Safe to submit to Aristotle")
    else:
        print("⚠️  ISSUES FOUND - Review before submitting")
        if not defs_ok:
            print("   - Local definition audit failed")
        if claude_verdict == "FAIL":
            print("   - Claude found critical issues")
        if gemini_verdict == "INCORRECT":
            print("   - Gemini found semantic issues")

    sys.exit(0 if all_pass else 1)


if __name__ == "__main__":
    main()
