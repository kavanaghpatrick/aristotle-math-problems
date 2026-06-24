"""Tests for safe_aristotle_submit.decide_lane() — U1 auto-routing.

Per U1 (2026-05-30), the default lane for novel structural problems is
FUSION whenever a .fusion.json companion sits adjacent to the sketch.
The W8 / I9 audit confirmed that BARE-prompt submissions route to
Aristotle's MCGS-only subsystem, while informal-shape prompts engage the
lemma-based reasoner that produced all 4 known Erdős wins. Making FUSION
the default when a companion exists is the lever for routing novel
structural problems to subsystem #2.

This test module covers the decision logic itself; the existing
fusion-gate tests (tests/fusion_gate/run_gate_test.py) cover the
companion validation. The I9 informal-routing wiring is exercised by
the existing test there. Here we only verify decide_lane() returns the
right shape for each combination of companions and flags.

The four required cases:
  1. Sketch with .fusion.json present              -> FUSION (auto)
  2. Sketch with .closure.json (structural_finite_reduction) -> BARE + recommend
  3. Sketch with no companion                       -> BARE silent
  4. Sketch with .fusion.json + --bare-only         -> BARE with override log

Plus regression coverage:
  5. Explicit --fusion-lane still routes FUSION even without companion
  6. Closure-only without structural_finite_reduction -> BARE without recommend
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import pytest


def _ensure_api_key():
    """safe_aristotle_submit raises on import without ARISTOTLE_API_KEY set."""
    os.environ.setdefault("ARISTOTLE_API_KEY", "test-dummy-key")


@pytest.fixture
def patched_submit_module(
    tmp_path,
    monkeypatch,
    mock_aristotlelib_module,
    import_patched_script,
):
    """Import safe_aristotle_submit with MATH_DIR redirected to tmp_path.

    decide_lane() itself does no DB I/O, but log_transaction() does, and
    decide_lane() calls log_transaction("BARE_OVERRIDE", ...) on case 4.
    Redirecting MATH_DIR isolates the log file under tmp_path.
    """
    _ensure_api_key()
    sas = import_patched_script("safe_aristotle_submit")
    monkeypatch.setattr(sas, "MATH_DIR", tmp_path)
    monkeypatch.setattr(sas, "TRANSACTION_LOG", tmp_path / "aristotle_submission_log.jsonl")
    return sas, tmp_path


def _write_sketch(tmp_path: Path, stem: str = "slot999_test") -> Path:
    """Write a minimal bare-gap sketch and return its path."""
    sketch_dir = tmp_path / "submissions" / "sketches"
    sketch_dir.mkdir(parents=True, exist_ok=True)
    p = sketch_dir / f"{stem}.txt"
    p.write_text(
        "OPEN GAP: Test problem (decide_lane test fixture)\n"
        "Source: tests/test_auto_routing\n"
        "Domain: nt\n"
        "\n"
        "Conjecture statement for testing the decide_lane router only.\n"
        "\n"
        "theorem t_auto_routing_fixture (n : Nat) (h : 0 < n) : 0 < n := by sorry\n"
        "\n"
        "Status: OPEN. Test placeholder.\n"
    )
    return p


def _write_fusion_companion(sketch_path: Path) -> Path:
    """Write a minimal valid .fusion.json adjacent to the sketch."""
    companion = sketch_path.with_suffix(".fusion.json")
    companion.write_text(json.dumps({
        "problem_id": "test_problem",
        "stage_outputs": {
            "literature_path": "x/01.md",
            "analogies_path": "x/02.md",
            "techniques_path": "x/03.md",
        },
        "named_technique": "Modularity lift (test fixture)",
        "seminal_paper_arxiv": "https://arxiv.org/abs/0707.4035",
        "fit_score": 0.5,
        "bridge_lemma": "If a counterexample exists, X.",
        "informal_proof_outline": (
            "Suppose a counterexample exists. By X, derive Y. Apply Z. "
            "Contradiction. Therefore the conjecture holds."
        ),
        "candidate_lemmas": [
            "lemma_one: dummy.",
            "lemma_two: dummy.",
        ],
        "honest_disclaimer": "Test fixture; technique fit is fabricated.",
    }, indent=2))
    return companion


def _write_closure_companion(
    sketch_path: Path,
    cm: str = "structural_finite_reduction",
) -> Path:
    """Write a minimal valid .closure.json adjacent to the sketch."""
    companion = sketch_path.with_suffix(".closure.json")
    companion.write_text(json.dumps({
        "CS": "sub_claim_closure",
        "CM": cm,
        "CR": "clean_decidable",
        "HM": "journal_clean",
        "real_closure_candidate": True,
        "rationale": (
            f"Test fixture: CM={cm} classification for the decide_lane router."
        ),
    }, indent=2))
    return companion


# -----------------------------------------------------------------------
# The four required cases.
# -----------------------------------------------------------------------

def test_case1_fusion_companion_auto_routes_to_fusion(patched_submit_module):
    """Case 1: sketch with .fusion.json present -> auto-routes to FUSION."""
    sas, tmp_path = patched_submit_module
    sketch = _write_sketch(tmp_path)
    _write_fusion_companion(sketch)

    result = sas.decide_lane(sketch)

    assert result["lane"] == "fusion"
    assert result["auto_detected"] is True
    assert result["fusion_lane"] is True
    assert result["informal_mode"] is False
    assert result["override"] is None
    assert result["closure_recommend"] is False
    assert "auto-detected" in result["reason"].lower()
    assert sketch.with_suffix(".fusion.json").name in result["reason"]


def test_case2_closure_structural_finite_reduction_recommends(patched_submit_module):
    """Case 2: sketch with .closure.json (CM=structural_finite_reduction)
    -> BARE lane plus a recommendation flag (not an auto-promote)."""
    sas, tmp_path = patched_submit_module
    sketch = _write_sketch(tmp_path)
    _write_closure_companion(sketch, cm="structural_finite_reduction")

    result = sas.decide_lane(sketch)

    assert result["lane"] == "bare"
    assert result["auto_detected"] is True
    assert result["fusion_lane"] is False
    assert result["informal_mode"] is False
    assert result["override"] is None
    assert result["closure_recommend"] is True
    # Reason must mention the closure companion explicitly so the banner
    # users see in stdout is unambiguous.
    assert "closure" in result["reason"].lower()
    assert "structural_finite_reduction" in result["reason"]


def test_case3_no_companion_silent_bare(patched_submit_module):
    """Case 3: sketch with no companion -> BARE silent."""
    sas, tmp_path = patched_submit_module
    sketch = _write_sketch(tmp_path)
    # No companion files.

    result = sas.decide_lane(sketch)

    assert result["lane"] == "bare"
    assert result["auto_detected"] is False
    assert result["fusion_lane"] is False
    assert result["informal_mode"] is False
    assert result["override"] is None
    assert result["closure_recommend"] is False
    assert "no companion" in result["reason"].lower()


def test_case4_bare_only_override_logs_event(patched_submit_module):
    """Case 4: sketch with .fusion.json + --bare-only -> BARE with override log."""
    sas, tmp_path = patched_submit_module
    sketch = _write_sketch(tmp_path)
    fusion_path = _write_fusion_companion(sketch)

    result = sas.decide_lane(sketch, bare_only=True)

    assert result["lane"] == "bare"
    assert result["auto_detected"] is False
    assert result["fusion_lane"] is False
    assert result["override"] == "BARE_OVERRIDE"
    assert fusion_path.name in result["reason"]

    # Verify the BARE_OVERRIDE event was written to the transaction log
    log_path = tmp_path / "aristotle_submission_log.jsonl"
    assert log_path.exists(), "BARE_OVERRIDE should produce a log entry"
    entries = [json.loads(l) for l in log_path.read_text().strip().splitlines() if l.strip()]
    bare_overrides = [e for e in entries if e["action"] == "BARE_OVERRIDE"]
    assert len(bare_overrides) == 1, (
        f"Expected exactly 1 BARE_OVERRIDE entry, got {len(bare_overrides)}: {entries}"
    )
    assert bare_overrides[0]["details"]["fusion_companion"].endswith(".fusion.json")


# -----------------------------------------------------------------------
# Regression coverage: explicit flags must still work and closure-only
# without structural_finite_reduction must NOT trip the recommendation.
# -----------------------------------------------------------------------

def test_explicit_fusion_lane_flag_still_works_without_companion(
    patched_submit_module,
):
    """Backward compat: --fusion-lane explicit override must still route to
    FUSION even when no companion exists (the explicit pipeline owns its
    own lane decision; the fusion-companion gate will fail downstream)."""
    sas, tmp_path = patched_submit_module
    sketch = _write_sketch(tmp_path)
    # No companion.

    result = sas.decide_lane(sketch, fusion_lane_explicit=True)

    assert result["lane"] == "fusion"
    assert result["auto_detected"] is False  # explicit, not auto
    assert result["fusion_lane"] is True
    assert "explicit" in result["reason"].lower()


def test_closure_without_structural_finite_reduction_no_recommend(
    patched_submit_module,
):
    """Closure companion with a different CM enum -> BARE without recommend."""
    sas, tmp_path = patched_submit_module
    sketch = _write_sketch(tmp_path)
    _write_closure_companion(sketch, cm="explicit_witness")

    result = sas.decide_lane(sketch)

    assert result["lane"] == "bare"
    assert result["auto_detected"] is True
    assert result["closure_recommend"] is False
    assert "closure" in result["reason"].lower()
    assert "explicit_witness" in result["reason"]


def test_fusion_takes_precedence_over_closure_when_both_present(
    patched_submit_module,
):
    """Defensive: if both companions exist, FUSION wins (it's the stronger
    signal). The closure-recommend flag should NOT fire because we already
    chose FUSION."""
    sas, tmp_path = patched_submit_module
    sketch = _write_sketch(tmp_path)
    _write_fusion_companion(sketch)
    _write_closure_companion(sketch, cm="structural_finite_reduction")

    result = sas.decide_lane(sketch)

    assert result["lane"] == "fusion"
    assert result["auto_detected"] is True
    assert result["closure_recommend"] is False


def test_explicit_informal_mode_flag_routes_to_informal(
    patched_submit_module,
):
    """Explicit --informal-mode flag forwards through decide_lane."""
    sas, tmp_path = patched_submit_module
    sketch = _write_sketch(tmp_path)
    # No companion files.

    result = sas.decide_lane(sketch, informal_mode_explicit=True)

    assert result["lane"] == "informal"
    assert result["auto_detected"] is False
    assert result["fusion_lane"] is False
    assert result["informal_mode"] is True
    assert "explicit" in result["reason"].lower()
