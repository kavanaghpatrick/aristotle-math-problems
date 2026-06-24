#!/usr/bin/env python3
"""
verification_gauntlet.py — The fail-closed, fetch-time verification gauntlet.

This is the SINGLE entry point that decides whether an Aristotle result counts as
a genuine advance. It is the EXCLUSIVE writer of `compiled_advance` /
`target_resolved=1`. Every gate fails CLOSED: any error, ambiguity, or missing
input drops the row to its pre-gauntlet ceiling — never promotes.

Four ordered gates (Method-1 / Recipe-B scale-up plan, Segment 4):

  G1  MACHINE-CHECK   — real `lake build` against the formal-conjectures env
                        (mathlib v4.22.0) + `#print axioms` closure check +
                        inline detect_failure_modes() (F1/F3/F4/F6/F9 + em-taut).
  G2  FAITHFULNESS    — statement_diff.compare_statements() (deterministic L1)
                        + multi_agent_audit cross-model adversary on ambiguity (L2).
  G3  LITERATURE      — biblio_gate.check_literature() (fail-closed on UNKNOWN).
  G4  PROMOTION       — target_resolved = 1 / compiled_advance IFF
                        G1 build-clean AND G2.faithful AND G3.status == 'CLEAR'.
                        Populates cost_usd + mathematical_content_score.

Contract (run_gauntlet):
    run_gauntlet(uuid, lean_path, summary_path=None, source_conjecture=None,
                 problem_id=None)
      -> {verdict: <status-enum>, target_resolved: int,
          g1: dict, g2: dict, g3: dict, cost_usd: float|None,
          mathematical_content_score: int|None, reasons: list}

    RULE: target_resolved=1 / compiled_advance IFF G1 build-clean AND G2.faithful
          AND G3.status=='CLEAR'; otherwise fail-closed to
          compiled_no_advance / compiled_partial.
    If source_conjecture/problem_id unavailable, run G1+G2-structural only and
    NEVER promote to advance.

biblio_gate and statement_diff are built in PARALLEL this phase. This module
codes to their published contracts and degrades fail-closed if they are not yet
importable (G3 -> UNKNOWN, G2 -> structural-only). Only G1 is unit-tested
standalone now (no mocks) against a real extracted .lean.

CLI:
    python3 scripts/verification_gauntlet.py <lean_file> [--uuid UUID]
        [--source-conjecture FILE] [--problem-id ID] [--summary FILE]
        [--json] [--g1-only]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Optional

# ── Paths / env ──────────────────────────────────────────────────────────────
MATH_DIR = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = MATH_DIR / "scripts"
DB_PATH = MATH_DIR / "submissions" / "tracking.db"

# The CANONICAL Method-1 build environment is the formal-conjectures repo
# (mathlib v4.22.0 / lean4 v4.22.0). Its .lake/packages holds a fully-built
# mathlib cache, so a candidate .lean symlinked against it builds in seconds.
# NOTE: codex_proof_loop builds against the *root* repo (mathlib f897ebcf /
# lean4 v4.24.0). The plan (Risk 7) explicitly mandates the formal-conjectures
# rev for G1, NOT codex_proof_loop's mismatched root rev.
FORMAL_CONJECTURES = MATH_DIR / "formal-conjectures"
FC_LAKE_PACKAGES = FORMAL_CONJECTURES / ".lake" / "packages"
FC_TOOLCHAIN = FORMAL_CONJECTURES / "lean-toolchain"
FC_MANIFEST = FORMAL_CONJECTURES / "lake-manifest.json"
FC_MATHLIB_REV = "v4.22.0"

# Standard, kernel-trusted axioms permitted in a mathlib proof. Anything else
# (notably a user `axiom` declaration, or `sorryAx`) is a closure violation.
SAFE_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

DEFAULT_BUILD_TIMEOUT = 300  # seconds (G1 lake build cap, plan §4)
DEFAULT_AXIOM_TIMEOUT = 150  # seconds (#print axioms is cheap once built)

# Canonical status enum (CLAUDE.md, post-2026-05-28).
ST_SUBMITTED = "submitted"
ST_COMPILE_FAILED = "compile_failed"
ST_COMPILED_PARTIAL = "compiled_partial"
ST_COMPILED_NO_ADVANCE = "compiled_no_advance"
ST_COMPILED_ADVANCE = "compiled_advance"
ST_DISPROVEN = "disproven"

# Aristotle wall-clock → $ rate (directional; no SDK cost field exists). Plan §4
# labels Aristotle cost a wall-clock estimate. Override via env.
ARISTOTLE_USD_PER_HOUR = float(os.environ.get("ARISTOTLE_USD_PER_HOUR", "0") or "0")


# ── Reused primitives (import; fall back gracefully) ─────────────────────────
# audit_proven.detect_failure_modes + audit_file are load-bearing for G1.
sys.path.insert(0, str(SCRIPTS_DIR))

try:
    from audit_proven import (  # type: ignore
        detect_failure_modes as _detect_failure_modes,
        audit_file as _audit_proven_file,
    )
    _HAVE_AUDIT_PROVEN = True
except Exception as _e:  # pragma: no cover - defensive
    _HAVE_AUDIT_PROVEN = False
    _AUDIT_PROVEN_ERR = str(_e)

    def _detect_failure_modes(content: str, filename: str = ""):  # type: ignore
        return []

    def _audit_proven_file(path):  # type: ignore
        return ([], None, None)

# codex_proof_loop primitives: extract_theorem_statement (G2 fallback),
# count_sorries (G1 sorry count consistent with the rest of the repo).
try:
    from codex_proof_loop import (  # type: ignore
        extract_theorem_statement as _cpl_extract_stmt,
        count_sorries as _cpl_count_sorries,
    )
    _HAVE_CPL = True
except Exception:
    _HAVE_CPL = False

    def _cpl_count_sorries(code: str) -> int:  # type: ignore
        n = 0
        in_block = False
        for line in code.splitlines():
            s = line.strip()
            if "/-" in s and "-/" not in s:
                in_block = True
                continue
            if "-/" in s:
                in_block = False
                continue
            if in_block:
                continue
            n += len(re.findall(r"\bsorry\b", s.split("--")[0]))
        return n

    def _cpl_extract_stmt(code: str) -> Optional[str]:  # type: ignore
        return _fallback_extract_statement(code)


def _fallback_extract_statement(lean_text: str) -> Optional[str]:
    """Local theorem-statement extractor (used if statement_diff and
    codex_proof_loop are both unavailable). First theorem/lemma header up to
    `:=` / `where`, whitespace-normalized."""
    collecting = False
    parts: list[str] = []
    for line in lean_text.splitlines():
        s = line.strip()
        if not collecting:
            if re.match(r"^(theorem|lemma)\s+", s):
                collecting = True
                parts = [s]
                if ":=" in s or " where" in s:
                    return re.split(r":=|where", s)[0].strip()
        else:
            parts.append(s)
            if ":=" in s or " where" in s:
                return re.split(r":=|where", " ".join(parts))[0].strip()
    return " ".join(parts).strip() if parts else None


# statement_diff (G2-L1) — built in parallel. Code to its contract; fall back to
# a conservative structural diff if not importable yet.
def _load_statement_diff():
    try:
        import statement_diff  # type: ignore

        compare = getattr(statement_diff, "compare_statements", None)
        extract = getattr(statement_diff, "extract_theorem_statement", None)
        if callable(compare):
            return compare, (extract if callable(extract) else _cpl_extract_stmt), True
    except Exception:
        pass
    return None, _cpl_extract_stmt, False


# biblio_gate (G3) — built in parallel. Code to its contract; fall back to a
# fail-CLOSED UNKNOWN if not importable yet.
def _load_biblio_gate():
    try:
        import biblio_gate  # type: ignore

        check = getattr(biblio_gate, "check_literature", None)
        if callable(check):
            return check, True
    except Exception:
        pass
    return None, False


# ── G1: MACHINE-CHECK (real lake build + axioms + failure modes) ─────────────

_LAKEFILE = f"""name = "gauntlet_check"
defaultTargets = ["GauntletCheck"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "{FC_MATHLIB_REV}"

[[lean_lib]]
name = "GauntletCheck"
"""


def _make_build_project(lean_text: str) -> Path:
    """Create an isolated Lean project that symlinks the formal-conjectures
    mathlib cache, with the candidate written as GauntletCheck.lean."""
    if not FC_LAKE_PACKAGES.exists():
        raise FileNotFoundError(
            f"formal-conjectures .lake/packages not found at {FC_LAKE_PACKAGES}. "
            "Run `lake build` in formal-conjectures/ first."
        )
    tmp = Path(tempfile.mkdtemp(prefix="gauntlet_g1_"))
    (tmp / "lakefile.toml").write_text(_LAKEFILE)
    # Toolchain (symlink → pins lean4 v4.22.0 to match the mathlib cache).
    if FC_TOOLCHAIN.exists():
        os.symlink(FC_TOOLCHAIN, tmp / "lean-toolchain")
    # Manifest (copy — lake mutates it).
    if FC_MANIFEST.exists():
        shutil.copy2(FC_MANIFEST, tmp / "lake-manifest.json")
    lake_dir = tmp / ".lake"
    lake_dir.mkdir()
    os.symlink(FC_LAKE_PACKAGES, lake_dir / "packages")
    (tmp / "GauntletCheck.lean").write_text(lean_text)
    return tmp


def _strip_comments(text: str) -> str:
    code = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    code = re.sub(r"--.*$", "", code, flags=re.MULTILINE)
    return code


def _declared_names(lean_text: str) -> list[str]:
    """All theorem/lemma names declared in the file, in order."""
    code = _strip_comments(lean_text)
    return re.findall(r"\b(?:theorem|lemma)\s+([A-Za-z_][\w'.]*)", code)


def _user_axiom_names(lean_text: str) -> list[str]:
    code = _strip_comments(lean_text)
    return re.findall(r"^\s*axiom\s+([A-Za-z_][\w'.]*)", code, re.MULTILINE)


def _run_lake_build(project_dir: Path, timeout: int) -> tuple[bool, str]:
    try:
        r = subprocess.run(
            ["lake", "build"],
            cwd=str(project_dir),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return (r.returncode == 0, (r.stdout or "") + (r.stderr or ""))
    except subprocess.TimeoutExpired:
        return (False, f"BUILD TIMED OUT after {timeout}s (fail-closed)")
    except FileNotFoundError:
        return (False, "lake not found in PATH (fail-closed)")
    except Exception as e:  # pragma: no cover - defensive
        return (False, f"build error: {e} (fail-closed)")


def _check_axioms(project_dir: Path, names: list[str], timeout: int) -> dict:
    """Run `#print axioms <name>` for each declared theorem against the built
    library. Returns {clean: bool, per_decl: {name: [axioms]},
    disallowed: {name: [bad-axioms]}, error: str|None}.

    Fail-closed: if the axiom check cannot run, clean=False.
    """
    if not names:
        return {"clean": True, "per_decl": {}, "disallowed": {}, "error": None,
                "note": "no theorem/lemma declarations to check"}

    lines = ["import Mathlib", "import GauntletCheck"]
    for n in names:
        lines.append(f"#print axioms {n}")
    check_file = project_dir / "AxCheck.lean"
    check_file.write_text("\n".join(lines) + "\n")

    try:
        r = subprocess.run(
            ["lake", "env", "lean", str(check_file)],
            cwd=str(project_dir),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        out = (r.stdout or "") + "\n" + (r.stderr or "")
    except subprocess.TimeoutExpired:
        return {"clean": False, "per_decl": {}, "disallowed": {},
                "error": f"#print axioms timed out after {timeout}s (fail-closed)"}
    except Exception as e:  # pragma: no cover - defensive
        return {"clean": False, "per_decl": {}, "disallowed": {},
                "error": f"#print axioms failed: {e} (fail-closed)"}

    # Parse Lean's two reply shapes:
    #   "'name' depends on axioms: [a, b, c]"
    #   "'name' does not depend on any axioms"
    per_decl: dict[str, list[str]] = {}
    for m in re.finditer(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", out):
        nm = m.group(1)
        axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
        per_decl[nm] = axs
    for m in re.finditer(r"'([^']+)'\s+does not depend on any axioms", out):
        per_decl.setdefault(m.group(1), [])

    disallowed: dict[str, list[str]] = {}
    for nm, axs in per_decl.items():
        bad = [a for a in axs if a not in SAFE_AXIOMS]
        if bad:
            disallowed[nm] = bad

    # sorryAx is the kernel marker for an unproven `sorry`; treat as disallowed
    # even if it slipped past the regex sorry counter.
    has_sorry_ax = any("sorryAx" in axs for axs in per_decl.values())

    # If we got NO axiom report at all for a file that has declarations, the
    # check effectively failed — fail closed.
    if not per_decl:
        return {"clean": False, "per_decl": {}, "disallowed": {},
                "error": "no axiom report parsed from `#print axioms` (fail-closed)"}

    clean = (not disallowed) and (not has_sorry_ax)
    return {"clean": clean, "per_decl": per_decl, "disallowed": disallowed,
            "has_sorry_ax": has_sorry_ax, "error": None}


def run_g1(lean_text: str, filename: str = "",
           build_timeout: int = DEFAULT_BUILD_TIMEOUT,
           axiom_timeout: int = DEFAULT_AXIOM_TIMEOUT,
           skip_build: bool = False) -> dict:
    """G1 — machine-check.

    Returns dict:
      {build_clean: bool, build_ok: bool, axioms_clean: bool,
       sorry_count: int, user_axioms: list, failure_modes: list,
       has_critical_failure_mode: bool, declarations: list,
       axiom_report: dict, build_log: str (truncated), reasons: list}

    `build_clean` (the single boolean G4 reads) is True IFF the file builds,
    has zero sorry, declares no user axioms, the `#print axioms` closure is
    within SAFE_AXIOMS, and no CRITICAL failure mode fired. Fail-closed: any
    sub-failure -> build_clean=False.
    """
    reasons: list[str] = []
    sorry_count = _cpl_count_sorries(lean_text)
    user_axioms = _user_axiom_names(lean_text)
    decls = _declared_names(lean_text)

    # Inline failure-mode library (F1/F3/F4/F6/F9 + em-tautology shapes).
    fmodes = _detect_failure_modes(lean_text, filename=filename)
    fmode_records = [{"code": c, "severity": s, "message": m} for (c, s, m) in fmodes]
    critical_modes = [r for r in fmode_records if r["severity"] == "CRITICAL"]
    has_critical = len(critical_modes) > 0

    if sorry_count > 0:
        reasons.append(f"G1: {sorry_count} sorry present")
    if user_axioms:
        reasons.append(f"G1: user axiom declarations: {user_axioms}")
    for r in critical_modes:
        reasons.append(f"G1: CRITICAL failure mode {r['code']}: {r['message'][:120]}")

    build_ok = False
    build_log = ""
    axiom_report: dict = {"clean": False, "per_decl": {}, "disallowed": {},
                          "error": "build not run"}

    if skip_build:
        reasons.append("G1: build skipped (skip_build=True) -> fail-closed, not clean")
        return {
            "build_clean": False, "build_ok": False, "axioms_clean": False,
            "sorry_count": sorry_count, "user_axioms": user_axioms,
            "failure_modes": fmode_records, "has_critical_failure_mode": has_critical,
            "declarations": decls, "axiom_report": axiom_report,
            "build_log": "", "reasons": reasons,
        }

    project_dir: Optional[Path] = None
    try:
        project_dir = _make_build_project(lean_text)
        build_ok, build_log = _run_lake_build(project_dir, build_timeout)
        if not build_ok:
            reasons.append("G1: lake build FAILED")
        else:
            axiom_report = _check_axioms(project_dir, decls, axiom_timeout)
            if axiom_report.get("error"):
                reasons.append(f"G1: {axiom_report['error']}")
            elif not axiom_report.get("clean"):
                bad = axiom_report.get("disallowed", {})
                reasons.append(f"G1: disallowed axioms in closure: {bad}")
                if axiom_report.get("has_sorry_ax"):
                    reasons.append("G1: sorryAx in axiom closure (hidden sorry)")
    except FileNotFoundError as e:
        reasons.append(f"G1: {e}")
        build_ok = False
    except Exception as e:  # pragma: no cover - defensive
        reasons.append(f"G1: unexpected build error: {e} (fail-closed)")
        build_ok = False
    finally:
        if project_dir is not None:
            shutil.rmtree(project_dir, ignore_errors=True)

    axioms_clean = bool(axiom_report.get("clean"))
    build_clean = (
        build_ok
        and sorry_count == 0
        and not user_axioms
        and axioms_clean
        and not has_critical
    )

    # Truncate build log for storage/printing.
    log_trunc = build_log if len(build_log) <= 4000 else (build_log[:2000] + "\n...[truncated]...\n" + build_log[-1500:])

    return {
        "build_clean": build_clean,
        "build_ok": build_ok,
        "axioms_clean": axioms_clean,
        "sorry_count": sorry_count,
        "user_axioms": user_axioms,
        "failure_modes": fmode_records,
        "has_critical_failure_mode": has_critical,
        "declarations": decls,
        "axiom_report": axiom_report,
        "build_log": log_trunc,
        "reasons": reasons,
    }


# ── G2: STATEMENT-FAITHFULNESS ───────────────────────────────────────────────

def _extract_proved_signature(lean_text: str) -> Optional[str]:
    compare, extractor, _ = _load_statement_diff()
    try:
        sig = extractor(lean_text)
        if sig:
            return sig.strip()
    except Exception:
        pass
    return _fallback_extract_statement(lean_text)


def _run_g2_cross_model(lean_path: Path, proved_sig: str,
                        intended_sig: str) -> dict:
    """G2-L2 adversary: invoke multi_agent_audit (Gemini + Claude; Grok dead)
    only when L1 is ambiguous. multi_agent_audit is owned/edited by this agent
    in the same phase (dead grok-4 -> Gemini+Claude). We invoke it as a
    subprocess so its own dependency graph (validate_submission.sh etc.) is
    self-contained; parse its exit code as the adversary verdict.

    Returns {ran: bool, agree_faithful: bool|None, detail: str}.
    Fail-closed: if the adversary cannot run or disagrees, agree_faithful is
    not True.
    """
    audit_script = SCRIPTS_DIR / "multi_agent_audit.py"
    if not audit_script.exists():
        return {"ran": False, "agree_faithful": None,
                "detail": "multi_agent_audit.py not found (fail-closed)"}
    try:
        r = subprocess.run(
            [sys.executable, str(audit_script), str(lean_path)],
            cwd=str(MATH_DIR),
            capture_output=True,
            text=True,
            timeout=400,
        )
        # multi_agent_audit exits 0 only when all cross-model checks pass.
        agree = (r.returncode == 0)
        tail = (r.stdout or "")[-600:]
        return {"ran": True, "agree_faithful": agree,
                "detail": f"multi_agent_audit exit={r.returncode}; {tail}"}
    except subprocess.TimeoutExpired:
        return {"ran": True, "agree_faithful": None,
                "detail": "multi_agent_audit timed out (fail-closed)"}
    except Exception as e:
        return {"ran": True, "agree_faithful": None,
                "detail": f"multi_agent_audit error: {e} (fail-closed)"}


def run_g2(lean_text: str, lean_path: Optional[Path], source_conjecture: Optional[str],
           structural_only: bool = False) -> dict:
    """G2 — statement-faithfulness.

    - L1: statement_diff.compare_statements(proved_sig, intended_sig).
    - L2: cross-model adversary (Gemini+Claude) on ambiguity (severity=='minor'
          or compare unavailable), only if not structural_only and we have a path.

    Returns {faithful: bool, issue: str|None, severity: 'none'|'minor'|'fatal',
             proved_signature: str|None, intended_signature: str|None,
             l1: dict, l2: dict|None, structural_only: bool, reasons: list}.

    Fail-closed: when no source_conjecture is available (structural_only) we
    perform only the proved-signature sanity check and report
    faithful=None-equivalent (severity 'minor', faithful=False) so G4 cannot
    promote. A proved signature that is itself degenerate (em-tautology /
    `True` / `answer ↔ …` shape) is 'fatal' regardless of source.
    """
    reasons: list[str] = []
    proved_sig = _extract_proved_signature(lean_text)

    # Degenerate proved-statement guards (apply even without a source).
    if proved_sig:
        norm = re.sub(r"\s+", " ", proved_sig)
        if re.search(r":\s*True\b\s*$", norm) or re.fullmatch(r".*:\s*True", norm.strip()):
            reasons.append("G2: proved statement is `: True` (vacuous)")
            return {"faithful": False, "issue": "vacuous statement (`: True`)",
                    "severity": "fatal", "proved_signature": proved_sig,
                    "intended_signature": source_conjecture, "l1": {}, "l2": None,
                    "structural_only": structural_only, "reasons": reasons}

    intended_sig = None
    if source_conjecture:
        intended_sig = _extract_proved_signature(source_conjecture) or source_conjecture.strip()

    # No source → structural-only: we cannot affirm faithfulness. Fail-closed.
    if structural_only or not intended_sig:
        reasons.append("G2: no source_conjecture -> structural-only, faithfulness UNAFFIRMED (fail-closed)")
        return {"faithful": False, "issue": "no source statement to compare against",
                "severity": "minor", "proved_signature": proved_sig,
                "intended_signature": intended_sig, "l1": {}, "l2": None,
                "structural_only": True, "reasons": reasons}

    # L1 deterministic diff via the statement_diff contract.
    compare, _extractor, have_sd = _load_statement_diff()
    l1: dict
    if have_sd and compare is not None:
        try:
            l1 = compare(proved_sig or "", intended_sig)
        except Exception as e:
            l1 = {"faithful": False, "issue": f"compare_statements error: {e}",
                  "severity": "minor"}
            reasons.append(f"G2-L1: compare_statements raised ({e}) -> ambiguous")
    else:
        # statement_diff not yet importable — conservative structural fallback.
        l1 = _structural_diff_fallback(proved_sig or "", intended_sig)
        reasons.append("G2-L1: statement_diff unavailable -> conservative structural fallback")

    sev = l1.get("severity", "minor")
    faithful_l1 = bool(l1.get("faithful"))

    # Fatal L1 mismatch → reject outright.
    if sev == "fatal" or (not faithful_l1 and sev != "minor"):
        reasons.append(f"G2-L1: fatal/structural mismatch: {l1.get('issue')}")
        return {"faithful": False, "issue": l1.get("issue") or "fatal statement mismatch",
                "severity": "fatal" if sev == "fatal" else sev,
                "proved_signature": proved_sig, "intended_signature": intended_sig,
                "l1": l1, "l2": None, "structural_only": False, "reasons": reasons}

    # Clear L1 pass → faithful (no need for the expensive adversary).
    if faithful_l1 and sev == "none":
        return {"faithful": True, "issue": None, "severity": "none",
                "proved_signature": proved_sig, "intended_signature": intended_sig,
                "l1": l1, "l2": None, "structural_only": False, "reasons": reasons}

    # Ambiguous (severity 'minor') → escalate to L2 cross-model adversary.
    l2 = None
    if not structural_only and lean_path is not None:
        reasons.append("G2-L1 ambiguous -> escalating to L2 cross-model adversary")
        l2 = _run_g2_cross_model(lean_path, proved_sig or "", intended_sig)
        if l2.get("agree_faithful") is True:
            return {"faithful": True, "issue": None, "severity": "none",
                    "proved_signature": proved_sig, "intended_signature": intended_sig,
                    "l1": l1, "l2": l2, "structural_only": False, "reasons": reasons}
        reasons.append("G2-L2: adversary did not unanimously affirm faithful (fail-closed)")
    else:
        reasons.append("G2-L2: skipped (structural_only or no path) -> fail-closed")

    return {"faithful": False, "issue": l1.get("issue") or "ambiguous; adversary did not affirm",
            "severity": "minor", "proved_signature": proved_sig,
            "intended_signature": intended_sig, "l1": l1, "l2": l2,
            "structural_only": False, "reasons": reasons}


def _structural_diff_fallback(proved: str, intended: str) -> dict:
    """Conservative deterministic diff used ONLY when statement_diff.py is not
    yet importable. Errs toward 'minor' (ambiguous → escalate), never 'none'
    unless byte-identical after normalization. This mirrors the statement_diff
    contract shape: {faithful, issue, severity}.
    """
    def norm(s: str) -> str:
        s = re.sub(r"\s+", " ", s).strip()
        return s

    np, ni = norm(proved), norm(intended)
    if not np or not ni:
        return {"faithful": False, "issue": "empty signature", "severity": "minor"}
    if np == ni:
        return {"faithful": True, "issue": None, "severity": "none"}

    # Cheap weaker-conclusion / hypothesis-strip heuristics (extends F9 spirit).
    # Bound injection: proved adds a numeric ceiling the intended lacks.
    bound_pat = r"(≤\s*\d+|<\s*\d+|Finset\.Icc\s+\d+|Finset\.range\s+\d+)"
    if re.search(bound_pat, np) and not re.search(bound_pat, ni):
        return {"faithful": False,
                "issue": "bound-injection: proved statement adds a numeric ceiling absent from source",
                "severity": "fatal"}
    # Quantifier flip: source ∀ but proved ∃ (or vice-versa) at the head.
    p_head = np.split(",")[0]
    i_head = ni.split(",")[0]
    if ("∀" in i_head and "∃" in p_head and "∀" not in p_head) or \
       ("∃" in i_head and "∀" in p_head and "∃" not in p_head):
        return {"faithful": False,
                "issue": "quantifier-flip between source and proved statement",
                "severity": "fatal"}
    # Otherwise: differs but not provably-weaker by these heuristics → ambiguous.
    return {"faithful": False,
            "issue": "signatures differ (normalized); structural fallback cannot certify",
            "severity": "minor"}


# ── G3: LITERATURE (fail-closed) ─────────────────────────────────────────────

def run_g3(statement: str, problem_id: Optional[str] = None,
           named_conjecture: Optional[str] = None) -> dict:
    """G3 — literature disentanglement via biblio_gate.check_literature.

    Contract: returns {status: 'CLEAR'|'CLOSED'|'AMBIGUOUS'|'UNKNOWN',
                       evidence: str, sources: list}.
    Fail-closed: any exception / biblio_gate unavailable -> 'UNKNOWN'
    (never 'CLEAR'). Only 'CLEAR' permits promotion in G4.
    """
    check, have_bg = _load_biblio_gate()
    if not have_bg or check is None:
        return {"status": "UNKNOWN",
                "evidence": "biblio_gate.check_literature unavailable (built in parallel) -> fail-closed UNKNOWN",
                "sources": []}
    try:
        res = check(statement, problem_id=problem_id, named_conjecture=named_conjecture)
        # Defensive: coerce to the contract shape, fail-closed on anything odd.
        status = (res or {}).get("status")
        if status not in ("CLEAR", "CLOSED", "AMBIGUOUS", "UNKNOWN"):
            return {"status": "UNKNOWN",
                    "evidence": f"biblio_gate returned non-contract status {status!r} -> fail-closed",
                    "sources": (res or {}).get("sources", []) if isinstance(res, dict) else []}
        return {"status": status,
                "evidence": (res or {}).get("evidence", ""),
                "sources": (res or {}).get("sources", [])}
    except Exception as e:
        return {"status": "UNKNOWN",
                "evidence": f"biblio_gate.check_literature raised: {e} -> fail-closed UNKNOWN",
                "sources": []}


# ── G4: PROMOTION + metrics ──────────────────────────────────────────────────

def _aristotle_wallclock_cost_usd(uuid: Optional[str]) -> Optional[float]:
    """Directional Aristotle cost = wall-clock (completed - submitted) × RATE.
    No SDK cost field exists (verified). Returns None if rate unset or times
    missing. Read-only on the DB."""
    if not uuid or ARISTOTLE_USD_PER_HOUR <= 0 or not DB_PATH.exists():
        return None
    try:
        import sqlite3
        conn = sqlite3.connect(str(DB_PATH))
        row = conn.execute(
            "SELECT submitted_at, completed_at FROM submissions WHERE uuid=?",
            (uuid,),
        ).fetchone()
        conn.close()
        if not row or not row[0] or not row[1]:
            return None
        from datetime import datetime

        def _parse(s: str):
            for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S",
                        "%Y-%m-%d %H:%M:%S.%f"):
                try:
                    return datetime.strptime(s.split("+")[0].strip()[:26], fmt)
                except ValueError:
                    continue
            return None

        a, b = _parse(row[0]), _parse(row[1])
        if not a or not b:
            return None
        hours = max(0.0, (b - a).total_seconds() / 3600.0)
        return round(hours * ARISTOTLE_USD_PER_HOUR, 4)
    except Exception:
        return None


def _mathematical_content_score(g1: dict, g2: dict, advanced: bool) -> Optional[int]:
    """Heuristic 0-10 mcs for an ADVANCE (audit may overwrite). Only meaningful
    when promoted; for non-advances we return None so the column stays honest
    pending real audit. The score penalizes brute-force shapes (F9 bound /
    native_decide) per the plan's regression-candidate definition (mcs<=2)."""
    if not advanced:
        return None
    score = 6  # baseline for a faithful, literature-clear, machine-checked advance
    fm_codes = {r["code"] for r in g1.get("failure_modes", [])}
    if "F9" in fm_codes:
        score = min(score, 2)  # bounded native_decide → brute force
    # Reward a fully axiom-clean closure (only the safe trio).
    per = g1.get("axiom_report", {}).get("per_decl", {})
    if per and all(set(axs) <= SAFE_AXIOMS for axs in per.values()):
        score += 1
    return max(0, min(10, score))


# ── Orchestration: run_gauntlet ──────────────────────────────────────────────

def _resolve_lean_text(lean_path: Path) -> str:
    return Path(lean_path).read_text(errors="replace")


def _negation_detected(text: str) -> bool:
    return bool(re.search(
        r"(?:negated|counterexample|The following was negated|disprov)",
        text, re.IGNORECASE))


def run_gauntlet(uuid: str,
                 lean_path,
                 summary_path=None,
                 source_conjecture: Optional[str] = None,
                 problem_id: Optional[str] = None,
                 build_timeout: int = DEFAULT_BUILD_TIMEOUT,
                 skip_build: bool = False,
                 named_conjecture: Optional[str] = None) -> dict:
    """Run the full fail-closed gauntlet. SINGLE entry point + EXCLUSIVE writer
    of compiled_advance / target_resolved=1.

    Args:
        uuid:               Aristotle project UUID (for cost wall-clock lookup).
        lean_path:          Path to the result .lean (the built artifact).
        summary_path:       Optional ARISTOTLE_SUMMARY.md (negation detection).
        source_conjecture:  Path to / text of the canonical source statement.
                            If absent, G1+G2-structural only; NEVER promotes.
        problem_id:         Problem id for G3 literature lookup.
        build_timeout:      G1 lake-build cap (seconds).
        skip_build:         If True, G1 build is skipped (fail-closed, no advance).
                            Used only by callers that cannot afford a build.
        named_conjecture:   Optional named-conjecture key for G3.

    Returns (per contract):
        {verdict, target_resolved, g1, g2, g3, cost_usd,
         mathematical_content_score, reasons}
    """
    reasons: list[str] = []
    lean_path = Path(lean_path)

    # Load artifact text (fail-closed: unreadable → compile_failed).
    try:
        lean_text = _resolve_lean_text(lean_path)
    except Exception as e:
        return {
            "verdict": ST_COMPILE_FAILED, "target_resolved": 0,
            "g1": {"build_clean": False, "reasons": [f"cannot read {lean_path}: {e}"]},
            "g2": {}, "g3": {}, "cost_usd": None,
            "mathematical_content_score": None,
            "reasons": [f"artifact unreadable: {e} (fail-closed)"],
        }

    # Resolve source-conjecture text (path or literal).
    source_text: Optional[str] = None
    if source_conjecture:
        sc_path = Path(source_conjecture)
        if sc_path.exists():
            try:
                source_text = sc_path.read_text(errors="replace")
            except Exception:
                source_text = None
        else:
            source_text = source_conjecture  # treat as literal statement
    have_source = bool(source_text) or bool(problem_id) or bool(named_conjecture)

    # Negation / disproof short-circuit (summary or artifact says counterexample).
    summary_text = ""
    if summary_path:
        sp = Path(summary_path)
        if sp.exists():
            try:
                summary_text = sp.read_text(errors="replace")
            except Exception:
                summary_text = ""
    if _negation_detected(lean_text) or _negation_detected(summary_text):
        reasons.append("disproof/negation detected -> verdict=disproven (not an advance)")
        # A disproof is a valid outcome but NOT a target_resolved=1 advance here.
        return {
            "verdict": ST_DISPROVEN, "target_resolved": 0,
            "g1": {}, "g2": {}, "g3": {}, "cost_usd": _aristotle_wallclock_cost_usd(uuid),
            "mathematical_content_score": None, "reasons": reasons,
        }

    # ── G1 ──
    g1 = run_g1(lean_text, filename=str(lean_path), build_timeout=build_timeout,
                skip_build=skip_build)
    reasons.extend(g1.get("reasons", []))

    # ── G2 ── (structural-only when no source)
    structural_only = not (bool(source_text))
    g2 = run_g2(lean_text, lean_path, source_text, structural_only=structural_only)
    reasons.extend(g2.get("reasons", []))

    # ── G3 ── (literature, fail-closed). Only meaningful with a statement.
    g3_statement = (g2.get("proved_signature") or
                    (source_text or "")[:2000] or
                    _fallback_extract_statement(lean_text) or "")
    if have_source and g3_statement:
        g3 = run_g3(g3_statement, problem_id=problem_id, named_conjecture=named_conjecture)
    else:
        g3 = {"status": "UNKNOWN",
              "evidence": "no source/problem_id/statement for literature check -> fail-closed UNKNOWN",
              "sources": []}
    reasons.extend([f"G3: {g3.get('evidence','')[:160]}"] if g3.get("evidence") else [])

    # ── G4: promotion decision ──
    g1_clean = bool(g1.get("build_clean"))
    g2_faithful = bool(g2.get("faithful"))
    g3_clear = (g3.get("status") == "CLEAR")

    # Determine the pre-gauntlet ceiling (what the row drops to if not promoted).
    if not g1.get("build_ok"):
        ceiling = ST_COMPILE_FAILED
    elif g1.get("sorry_count", 0) > 0 or g1.get("user_axioms"):
        ceiling = ST_COMPILED_PARTIAL
    elif g1.get("has_critical_failure_mode") or not g1.get("axioms_clean"):
        # Compiles but a critical failure mode / dirty axiom closure → no advance.
        ceiling = ST_COMPILED_NO_ADVANCE
    else:
        ceiling = ST_COMPILED_NO_ADVANCE

    advanced = g1_clean and g2_faithful and g3_clear and have_source and not skip_build

    if advanced:
        verdict = ST_COMPILED_ADVANCE
        target_resolved = 1
        reasons.append("G4: PROMOTED -> compiled_advance (G1 clean ∧ G2 faithful ∧ G3 CLEAR)")
    else:
        verdict = ceiling
        target_resolved = 0
        if not have_source:
            reasons.append("G4: not promoted — no source_conjecture/problem_id (structural-only, never advance)")
        elif skip_build:
            reasons.append("G4: not promoted — build skipped")
        elif not g1_clean:
            reasons.append("G4: not promoted — G1 not clean")
        elif not g2_faithful:
            reasons.append("G4: not promoted — G2 not faithful")
        elif not g3_clear:
            reasons.append(f"G4: not promoted — G3 status={g3.get('status')} (need CLEAR)")

    cost_usd = _aristotle_wallclock_cost_usd(uuid)
    mcs = _mathematical_content_score(g1, g2, advanced)

    return {
        "verdict": verdict,
        "target_resolved": target_resolved,
        "g1": g1,
        "g2": g2,
        "g3": g3,
        "cost_usd": cost_usd,
        "mathematical_content_score": mcs,
        "reasons": reasons,
    }


# ── CLI ──────────────────────────────────────────────────────────────────────

def _print_human(res: dict) -> None:
    print("=" * 72)
    print("VERIFICATION GAUNTLET")
    print("=" * 72)
    g1 = res.get("g1", {})
    g2 = res.get("g2", {})
    g3 = res.get("g3", {})
    print(f"G1 machine-check : build_ok={g1.get('build_ok')} "
          f"build_clean={g1.get('build_clean')} sorry={g1.get('sorry_count')} "
          f"axioms_clean={g1.get('axioms_clean')} "
          f"crit_fmode={g1.get('has_critical_failure_mode')}")
    if g1.get("user_axioms"):
        print(f"   user axioms     : {g1['user_axioms']}")
    if g1.get("axiom_report", {}).get("disallowed"):
        print(f"   bad axioms      : {g1['axiom_report']['disallowed']}")
    for fm in g1.get("failure_modes", []):
        print(f"   failure mode    : [{fm['severity']}] {fm['code']}: {fm['message'][:90]}")
    print(f"G2 faithfulness  : faithful={g2.get('faithful')} severity={g2.get('severity')} "
          f"structural_only={g2.get('structural_only')}")
    if g2.get("issue"):
        print(f"   issue           : {g2['issue']}")
    print(f"G3 literature    : status={g3.get('status')}")
    if g3.get("evidence"):
        print(f"   evidence        : {g3['evidence'][:120]}")
    print("-" * 72)
    print(f"VERDICT          : {res.get('verdict')}")
    print(f"target_resolved  : {res.get('target_resolved')}")
    print(f"cost_usd         : {res.get('cost_usd')}")
    print(f"mcs              : {res.get('mathematical_content_score')}")
    print("reasons:")
    for r in res.get("reasons", []):
        print(f"  - {r}")
    print("=" * 72)


def main():
    ap = argparse.ArgumentParser(
        description="Fail-closed verification gauntlet (G1→G4). EXCLUSIVE writer of compiled_advance.",
    )
    ap.add_argument("lean_file", help="Path to the Aristotle result .lean")
    ap.add_argument("--uuid", default="", help="Aristotle project UUID (for cost wall-clock)")
    ap.add_argument("--source-conjecture", default=None,
                    help="Path to or literal text of the canonical source statement")
    ap.add_argument("--problem-id", default=None, help="Problem id (for G3 literature lookup)")
    ap.add_argument("--named-conjecture", default=None, help="Named conjecture key (G3)")
    ap.add_argument("--summary", default=None, help="ARISTOTLE_SUMMARY.md (negation detection)")
    ap.add_argument("--build-timeout", type=int, default=DEFAULT_BUILD_TIMEOUT)
    ap.add_argument("--g1-only", action="store_true",
                    help="Run G1 only and print its result (no DB write, no promotion)")
    ap.add_argument("--skip-build", action="store_true",
                    help="Skip G1 lake build (fail-closed: cannot promote)")
    ap.add_argument("--json", action="store_true", help="Emit JSON")
    args = ap.parse_args()

    lean_path = Path(args.lean_file)
    if not lean_path.exists():
        print(f"ERROR: file not found: {lean_path}", file=sys.stderr)
        sys.exit(2)

    if args.g1_only:
        g1 = run_g1(lean_path.read_text(errors="replace"), filename=str(lean_path),
                    build_timeout=args.build_timeout, skip_build=args.skip_build)
        if args.json:
            print(json.dumps(g1, indent=2))
        else:
            print(json.dumps({k: g1[k] for k in (
                "build_clean", "build_ok", "axioms_clean", "sorry_count",
                "user_axioms", "has_critical_failure_mode", "declarations")},
                indent=2))
            if g1.get("reasons"):
                print("reasons:")
                for r in g1["reasons"]:
                    print(f"  - {r}")
        sys.exit(0 if g1.get("build_clean") else 1)

    res = run_gauntlet(
        uuid=args.uuid or "",
        lean_path=lean_path,
        summary_path=args.summary,
        source_conjecture=args.source_conjecture,
        problem_id=args.problem_id,
        build_timeout=args.build_timeout,
        skip_build=args.skip_build,
        named_conjecture=args.named_conjecture,
    )
    if args.json:
        print(json.dumps(res, indent=2))
    else:
        _print_human(res)
    sys.exit(0 if res.get("target_resolved") == 1 else 1)


if __name__ == "__main__":
    main()
