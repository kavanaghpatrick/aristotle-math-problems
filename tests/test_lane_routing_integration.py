"""Integration tests for U1 auto-routing — `safe_aristotle_submit.decide_lane()`.

These cross-cutting tests verify the auto-detection logic that makes a
sibling `.fusion.json` companion automatically promote a submission from
BARE to FUSION/informal mode (the W8 lever, May 30 2026).

Coverage:
  1. Auto-detect FUSION when sibling .fusion.json present
  2. FUSION wins over .closure.json when both present
  3. BARE when no companions
  4. --bare-only override + BARE_OVERRIDE log entry
  5. Explicit --fusion-lane with no .fusion.json (graceful — gate detects
     missing companion when it runs)
  6. Explicit --informal-mode beats auto-detection
  7. closure-only with CM=structural_finite_reduction → BARE + recommend
  8. Submit pipeline end-to-end smoke (Project.create mocked)

Reference:
  scripts/safe_aristotle_submit.py :: decide_lane()
  docs/infrastructure_changes_may30/U1_auto_routing.md
  docs/infrastructure_changes_may30/I9_informal_mode.md
"""
from __future__ import annotations

import importlib.util
import json
import os
import sys
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, patch

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

os.environ.setdefault("ARISTOTLE_API_KEY", "dummy-for-test")


def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, str(path))
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def sas():
    """safe_aristotle_submit loaded once per module."""
    return _load_module(
        "safe_aristotle_submit",
        SCRIPTS_DIR / "safe_aristotle_submit.py",
    )


# ---------------------------------------------------------------------------
# Helpers — build sketch + companion files on tmp_path.
# ---------------------------------------------------------------------------

_VALID_FUSION_JSON = {
    "problem_id": "erdos_routing",
    "stage_outputs": {
        "literature_path": "research_fusion/runs/erdos_routing/01_literature.md",
        "analogies_path":  "research_fusion/runs/erdos_routing/02_analogies.md",
        "techniques_path": "research_fusion/runs/erdos_routing/03_techniques.md",
    },
    "named_technique": "Modularity descent via Galois representation",
    "seminal_paper_arxiv": "https://arxiv.org/abs/1234.5678",
    "fit_score": 0.65,
    "bridge_lemma": (
        "A test bridge lemma for routing verification. The auxiliary structure "
        "associated to the conjecture admits a known reduction to a finite "
        "computation. The reduction is the bridge between the open gap and "
        "the closed sub-problem."
    ),
    "informal_proof_outline": (
        "Suppose the conjecture fails for some integer n. Then by the auxiliary "
        "structure, there exists a bounded witness W of size O(log n). Enumerate "
        "all witnesses of that size; show none satisfies the required identity. "
        "This contradicts the assumption and proves the conjecture."
    ),
    "candidate_lemmas": [
        "aux_struct_bound: the auxiliary structure has size O(log n).",
        "enumerate_witnesses: a finite set of witnesses covers all cases.",
        "no_witness_satisfies: no witness in the finite set works.",
    ],
    "honest_disclaimer": (
        "Test dossier for U1 auto-routing verification. NOT a real research "
        "fusion artifact. Used only to exercise decide_lane() and the airlock. "
        "All claims here are placeholder content for the test harness."
    ),
}


def _bare_sketch_text(problem: str = "erdos_routing") -> str:
    """A minimal bare-gap sketch that passes gap-targeting + airlock.

    Keep this free of any tokens that appear in `_VALID_FUSION_JSON`
    (`named_technique`, capitalised first words, etc.) — otherwise the
    airlock will (correctly) reject it as a strategy leak."""
    return (
        f"OPEN GAP: {problem.replace('_', ' ').title()} (illustrative)\n"
        f"Source: formal-conjectures/{problem}\n"
        f"Domain: nt\n"
        f"\n"
        f"The conjecture states that for all integers n in [1, 10^9], there is "
        f"no nontrivial witness of size O(log n) that satisfies the auxiliary "
        f"identity. We make no claim about the proof path.\n"
        f"\n"
        f"theorem {problem}_claim (n : Nat) (hn : 1 ≤ n) : True := by sorry\n"
        f"\n"
        f"Status: OPEN. Range 1 ≤ n ≤ 10^9.\n"
    )


def _write_sketch(dir_: Path, name: str = "erdos_routing.txt",
                  content: str | None = None) -> Path:
    dir_.mkdir(parents=True, exist_ok=True)
    p = dir_ / name
    p.write_text(content or _bare_sketch_text())
    return p


def _write_fusion_companion(sketch: Path, payload: dict | None = None) -> Path:
    p = sketch.with_suffix(".fusion.json")
    p.write_text(json.dumps(payload or _VALID_FUSION_JSON, indent=2))
    return p


def _write_closure_companion(
    sketch: Path,
    cm: str = "structural_finite_reduction",
    real: bool = True,
) -> Path:
    p = sketch.with_suffix(".closure.json")
    p.write_text(json.dumps({
        "CM": cm,
        "real_closure_candidate": real,
        "rationale": "test closure companion (U1 routing test)",
    }, indent=2))
    return p


# ---------------------------------------------------------------------------
# Cross-cutting decide_lane() tests.
# ---------------------------------------------------------------------------

class TestDecideLane:
    """Direct unit tests of safe_aristotle_submit.decide_lane()."""

    def test_fusion_companion_alone_auto_routes_to_fusion(self, sas, tmp_path):
        """Cross-cutting #1: sketch + sibling .fusion.json => FUSION + auto_detected."""
        sketch = _write_sketch(tmp_path)
        _write_fusion_companion(sketch)

        decision = sas.decide_lane(sketch)

        assert decision["lane"] == "fusion"
        assert decision["auto_detected"] is True
        assert decision["fusion_lane"] is True
        assert decision["override"] is None
        assert "FUSION" in decision["reason"]
        assert "auto-detected" in decision["reason"]

    def test_fusion_wins_over_closure_when_both_present(self, sas, tmp_path):
        """Cross-cutting #2: both companions present => FUSION takes precedence."""
        sketch = _write_sketch(tmp_path)
        _write_fusion_companion(sketch)
        _write_closure_companion(sketch, cm="structural_finite_reduction")

        decision = sas.decide_lane(sketch)

        # Precedence is documented in decide_lane(): fusion wins over closure.
        assert decision["lane"] == "fusion"
        assert decision["fusion_lane"] is True
        assert decision["auto_detected"] is True
        # closure_recommend MUST be False when fusion wins — we already promoted.
        assert decision["closure_recommend"] is False

    def test_no_companions_routes_to_bare(self, sas, tmp_path):
        """Cross-cutting #3: no companion file => BARE (historical default)."""
        sketch = _write_sketch(tmp_path)

        decision = sas.decide_lane(sketch)

        assert decision["lane"] == "bare"
        assert decision["auto_detected"] is False
        assert decision["fusion_lane"] is False
        assert decision["informal_mode"] is False
        assert decision["override"] is None
        assert "no companion" in decision["reason"].lower()

    def test_bare_only_override_logs_when_fusion_companion_present(
        self, sas, tmp_path, monkeypatch
    ):
        """Cross-cutting #4: --bare-only with sibling .fusion.json => BARE +
        BARE_OVERRIDE log entry (audit trail)."""
        sketch = _write_sketch(tmp_path)
        _write_fusion_companion(sketch)

        # Capture log_transaction calls.
        logged: list[tuple[str, dict]] = []
        monkeypatch.setattr(
            sas, "log_transaction",
            lambda action, details: logged.append((action, details)),
        )

        decision = sas.decide_lane(sketch, bare_only=True)

        assert decision["lane"] == "bare"
        assert decision["override"] == "BARE_OVERRIDE"
        assert decision["fusion_lane"] is False
        assert "--bare-only" in decision["reason"]
        # Audit log fired.
        assert any(action == "BARE_OVERRIDE" for action, _ in logged), (
            f"Expected BARE_OVERRIDE log entry, got {[a for a, _ in logged]}"
        )

    def test_explicit_fusion_lane_without_companion_returns_fusion(
        self, sas, tmp_path
    ):
        """Cross-cutting #5: --fusion-lane explicit + no companion =>
        decide_lane still returns 'fusion' (legacy explicit override). The
        fusion-companion gate downstream (check_fusion_companion) is what
        rejects missing companions — decide_lane only does the routing
        decision and trusts the user when they pass the explicit flag."""
        sketch = _write_sketch(tmp_path)
        # NO companion written.

        decision = sas.decide_lane(sketch, fusion_lane_explicit=True)

        assert decision["lane"] == "fusion"
        assert decision["fusion_lane"] is True
        assert decision["auto_detected"] is False  # NOT auto — explicit flag
        assert decision["override"] is None
        assert "explicit" in decision["reason"].lower()

        # And verify check_fusion_companion still rejects it when called
        # downstream — graceful error, not silent pass.
        with pytest.raises(sas.FusionCompanionError) as exc_info:
            sas.check_fusion_companion(sketch)
        assert "requires a companion" in str(exc_info.value)

    def test_explicit_informal_mode_beats_auto_detection(self, sas, tmp_path):
        """Cross-cutting #6: --informal-mode explicit takes precedence over
        a fusion companion (legacy explicit semantics)."""
        sketch = _write_sketch(tmp_path)
        _write_fusion_companion(sketch)  # would auto-route to FUSION

        decision = sas.decide_lane(sketch, informal_mode_explicit=True)

        # informal_mode_explicit fires BEFORE auto-detect (rule 3).
        assert decision["lane"] == "informal"
        assert decision["informal_mode"] is True
        assert decision["fusion_lane"] is False
        assert decision["auto_detected"] is False

    def test_closure_only_with_structural_reduction_recommends_fusion(
        self, sas, tmp_path
    ):
        """Cross-cutting #7: closure companion (no fusion) with
        CM=structural_finite_reduction => BARE + closure_recommend=True.
        Conservative: we don't auto-promote without an informal outline."""
        sketch = _write_sketch(tmp_path)
        _write_closure_companion(sketch, cm="structural_finite_reduction")

        decision = sas.decide_lane(sketch)

        assert decision["lane"] == "bare"
        assert decision["auto_detected"] is True   # closure JSON was detected
        assert decision["fusion_lane"] is False
        assert decision["closure_recommend"] is True

    def test_closure_only_with_other_cm_no_recommendation(self, sas, tmp_path):
        """When closure CM is anything OTHER than structural_finite_reduction
        (e.g. journal_clean, disproof), we still go BARE but DO NOT print
        the recommendation banner."""
        sketch = _write_sketch(tmp_path)
        _write_closure_companion(sketch, cm="journal_clean")

        decision = sas.decide_lane(sketch)

        assert decision["lane"] == "bare"
        assert decision["closure_recommend"] is False

    def test_bare_only_with_no_companion_no_override_logged(
        self, sas, tmp_path, monkeypatch
    ):
        """--bare-only without any companion => BARE, no BARE_OVERRIDE log
        (no auto-detection was suppressed)."""
        sketch = _write_sketch(tmp_path)

        logged: list[tuple[str, dict]] = []
        monkeypatch.setattr(
            sas, "log_transaction",
            lambda action, details: logged.append((action, details)),
        )

        decision = sas.decide_lane(sketch, bare_only=True)

        assert decision["lane"] == "bare"
        assert decision["override"] is None
        assert not any(action == "BARE_OVERRIDE" for action, _ in logged)


# ---------------------------------------------------------------------------
# End-to-end smoke: simulated submission with Project.create mocked.
# ---------------------------------------------------------------------------

class TestAutoRoutingSmoke:
    """Smoke test: invoke safe_submit() end-to-end with the auto-routing
    decision in place + Project.create mocked. Verifies the lane banner
    fires + the resolved flags propagate through the pipeline + the
    informal-mode routing kicks in when a fusion.json companion exists."""

    @pytest.mark.asyncio
    async def test_end_to_end_auto_route_with_fusion_companion(
        self, sas, tmp_path, capsys, monkeypatch
    ):
        """The full smoke fixture: bare .txt + valid .fusion.json. Expected:
          - decide_lane chooses FUSION + auto_detected=True
          - lane banner printed
          - Project.create called once with the informal prompt (longer
            than the bare prompt thanks to the I9 informal-mode adapter)
          - lane recorded as 'informal' in the DB call
        """
        # Build the smoke fixture (sketch + companion).
        sketch = tmp_path / "erdos_routing.txt"
        sketch.write_text(_bare_sketch_text())
        _write_fusion_companion(sketch)

        # Redirect transaction log + lockfile to tmp_path (avoid polluting
        # the real log). Leave MATH_DIR pointing at the real repo so the
        # I9 informal-mode adapter can still be loaded from scripts/.
        monkeypatch.setattr(sas, "TRANSACTION_LOG",
                            tmp_path / "aristotle_submission_log.jsonl")
        monkeypatch.setattr(sas, "LOCKFILE",
                            tmp_path / ".aristotle_submit.lock")

        # Mock literature check (network-dependent) to ALWAYS pass.
        monkeypatch.setattr(
            sas, "check_literature_freshness",
            lambda *a, **kw: {
                "status": "OPEN", "problem_id": None, "citations": [],
                "blocked": False, "reason": "test-stub",
            },
        )

        # Mock gather_context to return empty (avoid DB read).
        monkeypatch.setattr(sas, "gather_context", lambda *a, **kw: [])

        # Mock _record_closure_axis / _record_lane_metadata to capture lane.
        recorded_lane = {}

        def _fake_record_lane(uuid, filename, lane, informal_mode_used,
                              paired_llm, fusion_json=None, problem_id=None):
            # problem_id kwarg added by the G4 metadata-propagation fix
            # (2026-06-10): safe_submit now persists problem_id at insert.
            recorded_lane["uuid"] = uuid
            recorded_lane["lane"] = lane
            recorded_lane["informal_mode_used"] = informal_mode_used
            recorded_lane["fusion_json_present"] = fusion_json is not None
            recorded_lane["problem_id"] = problem_id

        monkeypatch.setattr(sas, "_record_lane_metadata", _fake_record_lane)
        monkeypatch.setattr(sas, "_record_closure_axis", lambda *a, **kw: None)

        # Mock capacity check — always show capacity available.
        async def _fake_capacity(window_minutes=10):
            return {
                "in_progress": 0,
                "slots_available": 5,
                "has_capacity": True,
                "recent_count": 0,
            }

        monkeypatch.setattr(sas, "check_rate_limit_and_capacity", _fake_capacity)

        # Mock Project.create — record the prompt + return fake project.
        captured_prompt = {}

        async def _fake_create(prompt: str, tar_file_path=None):
            captured_prompt["text"] = prompt
            captured_prompt["tar"] = tar_file_path
            p = MagicMock()
            p.project_id = "smoke-test-project-uuid"
            return p

        monkeypatch.setattr(sas.Project, "create", _fake_create)

        # Mock set_api_key (no-op).
        monkeypatch.setattr(sas, "set_api_key", lambda *a, **kw: None)

        id_file = tmp_path / "smoke_ID.txt"

        project_id = await sas.safe_submit(
            input_file=sketch,
            project_id_file=id_file,
            description="erdos_routing_smoke",
            batch=True,  # skip interactive rate-limit dance
        )

        captured = capsys.readouterr().out

        # Assert: lane decision fired + banner appeared.
        assert "Lane:" in captured, (
            f"Lane banner missing from output. Got:\n{captured[:500]}"
        )
        assert "FUSION" in captured or "auto-detected" in captured

        # Assert: Project.create was actually called.
        assert "text" in captured_prompt, "Project.create was not invoked"
        # Assert: the prompt was rewritten by the I9 informal adapter — it
        # should be LONGER than the raw bare sketch (the adapter prepends
        # the strategy outline).
        assert len(captured_prompt["text"]) > len(_bare_sketch_text()), (
            "Prompt was not rewritten by informal-mode adapter — auto-routing "
            "to FUSION did not engage the I9 wiring."
        )

        # Assert: lane recorded as 'informal' (I9 wiring upgrades fusion ->
        # informal when the companion carries a strategy outline).
        assert recorded_lane.get("lane") == "informal", (
            f"Expected lane='informal' (I9 routing), got lane={recorded_lane.get('lane')}"
        )
        assert recorded_lane.get("informal_mode_used") is True
        assert recorded_lane.get("fusion_json_present") is True

        # Assert: project_id propagates.
        assert project_id == "smoke-test-project-uuid"


# ---------------------------------------------------------------------------
# Regression guard: companion-path helpers behave as documented.
# ---------------------------------------------------------------------------

def test_companion_fusion_path_convention(sas, tmp_path):
    """`<stem>.txt` -> `<stem>.fusion.json` (sibling, same parent)."""
    sketch = tmp_path / "erdos99_fusion.txt"
    sketch.write_text("placeholder")
    expected = tmp_path / "erdos99_fusion.fusion.json"
    assert sas._companion_fusion_path(sketch) == expected


def test_companion_closure_path_convention(sas, tmp_path):
    """`<stem>.txt` -> `<stem>.closure.json` (sibling, same parent)."""
    sketch = tmp_path / "erdos99_bare.txt"
    sketch.write_text("placeholder")
    expected = tmp_path / "erdos99_bare.closure.json"
    assert sas._companion_closure_path(sketch) == expected
