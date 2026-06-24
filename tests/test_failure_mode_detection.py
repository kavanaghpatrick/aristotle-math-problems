"""Unit tests for F-mode detectors (S7, 2026-05-30).

Tests both:
  - Pre-submission F-mode warnings in safe_aristotle_submit.check_gap_targeting()
  - Post-audit F-mode detectors in audit_proven.detect_failure_modes()
  - Closure-axis consistency rules (F-coherence) in check_closure_axis()

Run: pytest tests/test_failure_mode_detection.py -v

Reference:
  docs/failure_mode_prevention.md
  analysis/failure_dna_may30.md
"""
from __future__ import annotations

import importlib.util
import json
import os
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"

# Make scripts/ importable
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

# safe_aristotle_submit imports aristotlelib at module-load time. We need a
# dummy API key so that import succeeds without monkey-patching.
os.environ.setdefault("ARISTOTLE_API_KEY", "dummy-for-test")


def _load_module(name: str, path: Path):
    """Load a module by file path (works for top-level scripts in scripts/)."""
    spec = importlib.util.spec_from_file_location(name, str(path))
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def sas():
    """Loaded safe_aristotle_submit module."""
    return _load_module("safe_aristotle_submit",
                        SCRIPTS_DIR / "safe_aristotle_submit.py")


@pytest.fixture(scope="module")
def auditmod():
    """Loaded audit_proven module."""
    return _load_module("audit_proven", SCRIPTS_DIR / "audit_proven.py")


# ---------------------------------------------------------------------------
# Pre-submission F-mode warnings
# ---------------------------------------------------------------------------

class TestPreSubmissionF1:
    """F1 — Iff.rfl trap on undecidable wrappers."""

    def test_irrational_without_finite_range_rejects(self, sas, tmp_path):
        sketch = tmp_path / "slot999_f1.txt"
        sketch.write_text(
            "OPEN GAP: Test F1 detection\n"
            "Source: test fixture\n"
            "Domain: nt\n\n"
            "Is e + pi irrational?\n\n"
            "theorem foo : Irrational (Real.exp 1 + Real.pi) := by sorry\n\n"
            "Status: OPEN.\n"
        )
        with pytest.raises(sas.GapTargetingError) as excinfo:
            sas.check_gap_targeting(sketch)
        assert "F1" in str(excinfo.value) and "Irrational" in str(excinfo.value)

    def test_tendsto_without_finite_range_rejects(self, sas, tmp_path):
        sketch = tmp_path / "slot999_f1_tendsto.txt"
        sketch.write_text(
            "OPEN GAP: Test F1 tendsto\n"
            "Source: test fixture\n"
            "Domain: analysis\n\n"
            "Does the sequence tend to zero?\n\n"
            "theorem foo (f : ℕ → ℝ) : Tendsto f Filter.atTop (nhds 0) := by sorry\n\n"
            "Status: OPEN.\n"
        )
        with pytest.raises(sas.GapTargetingError) as excinfo:
            sas.check_gap_targeting(sketch)
        assert "F1" in str(excinfo.value)

    def test_irrational_with_finset_range_passes(self, sas, tmp_path):
        sketch = tmp_path / "slot999_f1_safe.txt"
        sketch.write_text(
            "OPEN GAP: F1 with rescue\n"
            "Source: test fixture\n"
            "Domain: nt\n\n"
            "Bounded variant.\n\n"
            "theorem foo (n : ℕ) (hn : n ∈ Finset.range 100) :\n"
            "  Irrational (Real.sqrt n) := by sorry\n\n"
            "Status: OPEN.\n"
        )
        # Finset.range rescues F1 — should pass without raising.
        result = sas.check_gap_targeting(sketch)
        assert result["pass"] is True

    def test_set_infinite_rejects(self, sas, tmp_path):
        sketch = tmp_path / "slot999_f1_setinfinite.txt"
        sketch.write_text(
            "OPEN GAP: Set.Infinite\n"
            "Source: test fixture\n"
            "Domain: nt\n\n"
            "Are there infinitely many?\n\n"
            "theorem foo : Set.Infinite {p : ℕ | Nat.Prime p} := by sorry\n\n"
            "Status: OPEN.\n"
        )
        with pytest.raises(sas.GapTargetingError) as excinfo:
            sas.check_gap_targeting(sketch)
        assert "F1" in str(excinfo.value)


class TestPreSubmissionF3:
    """F3 — infrastructure-overgrowth hand-wave detection."""

    def test_reduces_to_warns(self, sas, tmp_path):
        sketch = tmp_path / "slot999_f3.txt"
        sketch.write_text(
            "OPEN GAP: Test F3 reduces-to\n"
            "Source: test fixture\n"
            "Domain: nt\n\n"
            "This reduces to a Pell equation argument.\n\n"
            "theorem foo (n : ℕ) (hn : n ≤ 100) : True := by sorry\n\n"
            "Status: OPEN.\n"
        )
        result = sas.check_gap_targeting(sketch)
        warnings = [code for code, _ in result.get("f_mode_warnings", [])]
        assert "F3" in warnings

    def test_clean_sketch_no_f3_warning(self, sas, tmp_path):
        sketch = tmp_path / "slot999_clean.txt"
        sketch.write_text(
            "OPEN GAP: Clean sketch\n"
            "Source: test fixture\n"
            "Domain: nt\n\n"
            "A bounded statement.\n\n"
            "theorem foo (n : ℕ) (hn : n ≤ 100) : True := by sorry\n\n"
            "Status: OPEN.\n"
        )
        result = sas.check_gap_targeting(sketch)
        warnings = [code for code, _ in result.get("f_mode_warnings", [])]
        assert "F3" not in warnings


class TestPreSubmissionF4:
    """F4 — axiomatize-the-hard hand-defer detection."""

    def test_by_classical_warns(self, sas, tmp_path):
        sketch = tmp_path / "slot999_f4.txt"
        sketch.write_text(
            "OPEN GAP: Test F4\n"
            "Source: test fixture\n"
            "Domain: nt\n\n"
            "Follows from a well-known result of Erdos.\n\n"
            "theorem foo (n : ℕ) (hn : n ≤ 100) : True := by sorry\n\n"
            "Status: OPEN.\n"
        )
        result = sas.check_gap_targeting(sketch)
        warnings = [code for code, _ in result.get("f_mode_warnings", [])]
        assert "F4" in warnings


class TestPreSubmissionF10:
    """F10 — local definition detection."""

    def test_local_def_warns(self, sas, tmp_path):
        sketch = tmp_path / "slot999_f10.txt"
        sketch.write_text(
            "OPEN GAP: Test F10\n"
            "Source: test fixture\n"
            "Domain: nt\n\n"
            "Custom predicate.\n\n"
            "def MyPredicate (n : ℕ) : Prop := n = 0\n\n"
            "theorem foo (n : ℕ) (hn : n ≤ 100) : True := by sorry\n\n"
            "Status: OPEN.\n"
        )
        # Note: this also triggers Lean-code-line-count (def + theorem = 2 lines).
        # Both warnings are acceptable.
        try:
            result = sas.check_gap_targeting(sketch)
            warnings = [code for code, _ in result.get("f_mode_warnings", [])]
            assert "F10" in warnings
        except sas.GapTargetingError as e:
            # If the gate's lean-line-count rejects it first, F10 still applies;
            # accept that as a stricter detection.
            assert "lean code" in str(e).lower() or "F10" in str(e)


# ---------------------------------------------------------------------------
# Closure-axis consistency (F-coherence)
# ---------------------------------------------------------------------------

class TestClosureAxisConsistency:
    """F-coherence checks in _check_closure_axis_consistency."""

    def _make_companion(self, tmp_path: Path, axis: dict) -> Path:
        sketch = tmp_path / "fixture.txt"
        sketch.write_text("OPEN GAP: fixture\n\ntheorem foo : True := by sorry\n")
        comp = sketch.with_suffix(".closure.json")
        comp.write_text(json.dumps(axis))
        return sketch

    def test_f7_bounded_with_real_closure_rejects(self, sas, tmp_path):
        """F7: CS=bounded_version_closure + real_closure_candidate=true → REJECT."""
        sketch = self._make_companion(tmp_path, {
            "CS": "bounded_version_closure",
            "CM": "witness_table_chunked",
            "CR": "clean_decidable",
            "HM": "journal_partial",
            "real_closure_candidate": True,
            "rationale": "Should be rejected: bounded version cannot be real closure.",
        })
        with pytest.raises(sas.ClosureAxisError) as excinfo:
            sas.check_closure_axis(sketch, rubric_points=False)
        assert "F7" in str(excinfo.value) or "bounded_version_closure" in str(excinfo.value)
        assert "internally inconsistent" in str(excinfo.value)

    def test_f1_iff_rfl_with_real_closure_rejects(self, sas, tmp_path):
        """F1: CR=iff_rfl_trap + real_closure_candidate=true → REJECT."""
        sketch = self._make_companion(tmp_path, {
            "CS": "full_closure",
            "CM": "explicit_witness",
            "CR": "iff_rfl_trap",
            "HM": "journal_clean",
            "real_closure_candidate": True,
            "rationale": "Should be rejected: iff_rfl_trap is a failure mode.",
        })
        with pytest.raises(sas.ClosureAxisError) as excinfo:
            sas.check_closure_axis(sketch, rubric_points=False)
        assert "F1" in str(excinfo.value) or "iff_rfl_trap" in str(excinfo.value)

    def test_f3_overgrowth_with_real_closure_rejects(self, sas, tmp_path):
        sketch = self._make_companion(tmp_path, {
            "CS": "full_closure",
            "CM": "explicit_witness",
            "CR": "infrastructure_overgrowth",
            "HM": "journal_clean",
            "real_closure_candidate": True,
            "rationale": "Should be rejected: infrastructure_overgrowth is a failure mode.",
        })
        with pytest.raises(sas.ClosureAxisError) as excinfo:
            sas.check_closure_axis(sketch, rubric_points=False)
        assert "F3" in str(excinfo.value) or "infrastructure_overgrowth" in str(excinfo.value)

    def test_f10_def_mismatch_with_real_closure_rejects(self, sas, tmp_path):
        sketch = self._make_companion(tmp_path, {
            "CS": "full_closure",
            "CM": "explicit_witness",
            "CR": "definition_mismatch",
            "HM": "journal_clean",
            "real_closure_candidate": True,
            "rationale": "Should be rejected: definition_mismatch is a failure mode.",
        })
        with pytest.raises(sas.ClosureAxisError) as excinfo:
            sas.check_closure_axis(sketch, rubric_points=False)
        assert "F10" in str(excinfo.value) or "definition_mismatch" in str(excinfo.value)

    def test_hm_infrastructure_only_with_real_closure_rejects(self, sas, tmp_path):
        sketch = self._make_companion(tmp_path, {
            "CS": "full_closure",
            "CM": "explicit_witness",
            "CR": "clean_decidable",
            "HM": "infrastructure_only",
            "real_closure_candidate": True,
            "rationale": "Should be rejected: infrastructure-only is not journal-grade closure.",
        })
        with pytest.raises(sas.ClosureAxisError) as excinfo:
            sas.check_closure_axis(sketch, rubric_points=False)
        assert "infrastructure_only" in str(excinfo.value)

    def test_consistent_real_closure_passes(self, sas, tmp_path):
        """Sanity: a fully consistent real-closure axis still passes."""
        sketch = self._make_companion(tmp_path, {
            "CS": "disproof_closure",
            "CM": "explicit_witness",
            "CR": "clean_decidable",
            "HM": "journal_clean",
            "real_closure_candidate": True,
            "rationale": "Consistent fixture — should pass.",
        })
        result = sas.check_closure_axis(sketch, rubric_points=False)
        assert result["real_closure_candidate"] is True

    def test_bounded_with_real_closure_false_passes_with_rubric(self, sas, tmp_path):
        """Sanity: bounded + real_closure_candidate=false is legitimate (rubric-points lane)."""
        sketch = self._make_companion(tmp_path, {
            "CS": "bounded_version_closure",
            "CM": "witness_table_chunked",
            "CR": "clean_decidable",
            "HM": "journal_partial",
            "real_closure_candidate": False,
            "rationale": "Bounded extension; not real closure.",
        })
        result = sas.check_closure_axis(sketch, rubric_points=True)
        assert result["real_closure_candidate"] is False
        assert result["override"] is True


# ---------------------------------------------------------------------------
# Post-audit detectors
# ---------------------------------------------------------------------------

class TestPostAuditF1:
    """F1/F8 — Iff.rfl trap detection in compiled output."""

    def test_iff_rfl_direct_detected(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "def answer : Prop := ∃ n, Nat.Prime n\n\n"
            "theorem foo : answer ↔ ∃ n, Nat.Prime n := Iff.rfl\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot697_erdos470.lean")
        codes = [code for code, _, _ in detections]
        assert "F1" in codes

    def test_by_rfl_detected(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "def answer : Prop := True\n\n"
            "theorem foo : answer ↔ True := by rfl\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot697.lean")
        codes = [code for code, _, _ in detections]
        assert "F1" in codes

    def test_clean_file_no_f1(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "theorem foo (n : ℕ) : n + 0 = n := by rfl\n"
        )
        # This is `n + 0 = n` proven by rfl — legitimate, not Iff.rfl on answer.
        detections = auditmod.detect_failure_modes(content, "slot999.lean")
        codes = [code for code, _, _ in detections]
        assert "F1" not in codes


class TestPostAuditF3:
    """F3 — side-lemma proliferation detection."""

    def test_many_lemmas_no_target_detects(self, auditmod):
        lemmas = "\n\n".join(
            f"lemma helper_{i} : True := trivial" for i in range(20)
        )
        content = f"import Mathlib\n\n{lemmas}\n"
        detections = auditmod.detect_failure_modes(content, "slot703_erdos672_ap.lean")
        codes = [code for code, _, _ in detections]
        assert "F3" in codes

    def test_few_lemmas_no_f3(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "lemma a : True := trivial\n\n"
            "lemma b : True := trivial\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot1.lean")
        codes = [code for code, _, _ in detections]
        assert "F3" not in codes

    def test_many_lemmas_with_matching_name_no_f3(self, auditmod):
        lemmas = "\n\n".join(
            f"lemma helper_{i} : True := trivial" for i in range(20)
        )
        content = (
            f"import Mathlib\n\n{lemmas}\n\n"
            "theorem erdos672_main : True := trivial\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot703_erdos672.lean")
        codes = [code for code, _, _ in detections]
        assert "F3" not in codes


class TestPostAuditF4:
    """F4 — exact?/apply?/rewrite? trail detection."""

    def test_exact_query_detected(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "theorem foo : True := by\n"
            "  have h : True := trivial\n"
            "  exact?\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot698.lean")
        codes = [code for code, _, _ in detections]
        assert "F4" in codes

    def test_apply_query_detected(self, auditmod):
        content = "import Mathlib\n\ntheorem foo : True := by apply?\n"
        detections = auditmod.detect_failure_modes(content, "slot1.lean")
        codes = [code for code, _, _ in detections]
        assert "F4" in codes

    def test_no_query_no_f4(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "theorem foo : True := by exact trivial\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot1.lean")
        codes = [code for code, _, _ in detections]
        assert "F4" not in codes


class TestPostAuditF6:
    """F6 — Aristotle meta-failure + sorry detection."""

    def test_meta_failure_with_sorry_detected(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "-- Aristotle took a wrong turn (reason code: 9)\n"
            "theorem tuza_nu4 : True := by sorry\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot327_tau_le_8.lean")
        codes = [code for code, _, _ in detections]
        assert "F6" in codes

    def test_failed_to_find_proof_detected(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "-- Aristotle failed to find a proof.\n"
            "theorem foo : True := by sorry\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot1.lean")
        codes = [code for code, _, _ in detections]
        assert "F6" in codes

    def test_sorry_without_meta_no_f6(self, auditmod):
        content = "import Mathlib\n\ntheorem foo : True := by sorry\n"
        detections = auditmod.detect_failure_modes(content, "slot1.lean")
        codes = [code for code, _, _ in detections]
        assert "F6" not in codes


class TestPostAuditF9:
    """F9 — bounded native_decide passed off as unbounded."""

    def test_bounded_native_decide_detected(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "theorem lemoine_upto_1000 (n : ℕ) (hn : n ≤ 1000) :\n"
            "    True := by native_decide\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot650_lemoine.lean")
        codes = [code for code, _, _ in detections]
        assert "F9" in codes

    def test_native_decide_without_bound_no_f9(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "theorem foo (n : ℕ) : n + 0 = n := by native_decide\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot1.lean")
        codes = [code for code, _, _ in detections]
        assert "F9" not in codes

    def test_bounded_without_native_decide_no_f9(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "theorem foo (n : ℕ) (hn : n ≤ 100) : True := by trivial\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot1.lean")
        codes = [code for code, _, _ in detections]
        assert "F9" not in codes


class TestDetectFailureModesIntegration:
    """End-to-end: detect_failure_modes returns the right shape."""

    def test_returns_tuple_format(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "def answer : Prop := True\n\n"
            "theorem foo : answer ↔ True := Iff.rfl\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot999.lean")
        assert len(detections) >= 1
        for entry in detections:
            assert isinstance(entry, tuple) and len(entry) == 3
            code, severity, message = entry
            assert code.startswith("F")
            assert severity in ("CRITICAL", "HIGH", "LOW")
            assert isinstance(message, str) and message

    def test_clean_file_no_detections(self, auditmod):
        content = (
            "import Mathlib\n\n"
            "theorem foo : 1 + 1 = 2 := by rfl\n"
        )
        detections = auditmod.detect_failure_modes(content, "slot1.lean")
        # `1 + 1 = 2 := by rfl` is not an `answer ↔ X` shape, so no F1.
        # Single lemma, so no F3. No exact?, no meta-failure, no native_decide.
        codes = [code for code, _, _ in detections]
        assert codes == []
