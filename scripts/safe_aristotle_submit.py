#!/usr/bin/env python3
"""
Safe Aristotle submission with multiple safety checks to prevent duplicates.

Defense-in-depth approach:
1. Pre-flight checks (queue status, recent submissions, lockfile)
2. Atomic submission with immediate ID save
3. Post-flight verification
4. Transaction logging
"""

import asyncio
import json
import hashlib
import os
import re
import time
from pathlib import Path
from datetime import datetime, timedelta
from aristotlelib import Project, ProjectStatus, set_api_key

# Configuration
ARISTOTLE_API_KEY = os.environ.get("ARISTOTLE_API_KEY")
if not ARISTOTLE_API_KEY:
    raise ValueError("ARISTOTLE_API_KEY environment variable not set")

# Auto-detect repository root (works from any subdirectory)
MATH_DIR = Path(__file__).resolve().parent.parent
TRANSACTION_LOG = MATH_DIR / "aristotle_submission_log.jsonl"
LOCKFILE = MATH_DIR / ".aristotle_submit.lock"


class SubmissionError(Exception):
    """Raised when submission should be aborted."""
    pass


class GapTargetingError(SubmissionError):
    """Raised when a submission fails gap-targeting validation."""
    pass


class ClosureAxisError(SubmissionError):
    """Raised when the closure-axis companion file fails validation or
    classifies the submission outside the real-closure lane without
    an explicit --rubric-points override.

    Reference: docs/closure_axis_companion_spec.md, docs/closure_taxonomy_may30.md.
    """
    pass


class LiteratureStaleError(SubmissionError):
    """Raised when the literature-check finds the problem has already been
    closed (by AI or by literature) and no `--force-literature-stale` override
    is in effect.

    Reference: docs/infrastructure_changes_may30/I4_literature_check.md.
    """
    pass


class FusionCompanionError(SubmissionError):
    """Raised when the FUSION-lane companion file (.fusion.json) fails
    schema validation, exceeds the 80-line budget, or when the airlock
    detects strategy leakage in the bare .txt sketch.

    The FUSION gate has NO override (other than the global --force, which is
    reserved for the orchestrator pipeline). The airlock pattern is what
    protects bare-gap discipline on the fusion lane.

    Reference: docs/fusion_axis_companion_spec.md,
    docs/infrastructure_changes_may30/I8_fusion_lane.md.
    """
    pass


# Fusion-axis companion schema (verbatim from docs/fusion_axis_companion_spec.md).
FUSION_REQUIRED_FIELDS = {
    "problem_id",
    "stage_outputs",
    "named_technique",
    "seminal_paper_arxiv",
    "fit_score",
    "bridge_lemma",
    "informal_proof_outline",
    "candidate_lemmas",
    "honest_disclaimer",
}
FUSION_STAGE_OUTPUT_FIELDS = {
    "literature_path",
    "analogies_path",
    "techniques_path",
}
FUSION_MAX_LINES = 80                 # hard cap on non-blank lines
FUSION_MAX_OUTLINE_WORDS = 500
FUSION_MAX_OUTLINE_CHARS = 4000
FUSION_MAX_BRIDGE_SENTENCES = 3
FUSION_MAX_BRIDGE_CHARS = 600
FUSION_MAX_NAMED_TECHNIQUE_CHARS = 120
FUSION_MAX_CANDIDATE_LEMMAS = 10
FUSION_MIN_CANDIDATE_LEMMAS = 1


# Closure-axis enum sets (verbatim from docs/closure_taxonomy_may30.md).
# Keep in lock-step with docs/closure_axis_companion_spec.md.
CLOSURE_AXIS_CS_VALUES = {
    "full_closure",
    "direction_closure",
    "disproof_closure",
    "bounded_version_closure",
    "sub_claim_closure",
    "formalization_only",
}
CLOSURE_AXIS_CM_VALUES = {
    "explicit_witness",
    "bounded_to_infinite_lift",
    "structural_finite_reduction",
    "disproof_construction",
    "witness_table_chunked",
    "density_sieve_closure",
    "induction_template",
    "none_known",
}
CLOSURE_AXIS_CR_VALUES = {
    "clean_decidable",
    "partial_result_only",
    "iff_rfl_trap",
    "witness_search_explosion",
    "definition_mismatch",
    "em_tautology",
    "infrastructure_overgrowth",
    "recursive_falsification",
}
CLOSURE_AXIS_HM_VALUES = {
    "journal_clean",
    "journal_partial",
    "journal_subclaim",
    "infrastructure_only",
}
CLOSURE_AXIS_REQUIRED_FIELDS = {"CS", "CM", "CR", "HM", "real_closure_candidate", "rationale"}


def compute_task_hash(input_file: Path) -> str:
    """Compute SHA256 hash of task input for deduplication."""
    with open(input_file, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()[:16]


def log_transaction(action: str, details: dict):
    """Append to transaction log."""
    entry = {
        "timestamp": datetime.now().isoformat(),
        "action": action,
        "details": details
    }
    with open(TRANSACTION_LOG, 'a') as f:
        f.write(json.dumps(entry) + '\n')


def acquire_lock() -> bool:
    """Try to acquire lockfile. Returns True if acquired, False if already locked."""
    if LOCKFILE.exists():
        # Check if lock is stale (>5 minutes old)
        lock_age = time.time() - LOCKFILE.stat().st_mtime
        if lock_age > 300:  # 5 minutes
            print("⚠️  Removing stale lockfile")
            LOCKFILE.unlink()
        else:
            return False

    # Create lockfile
    LOCKFILE.write_text(f"{datetime.now().isoformat()}\n")
    return True


def release_lock():
    """Release lockfile."""
    if LOCKFILE.exists():
        LOCKFILE.unlink()


def check_duplicate(task_hash: str, window_minutes: int = 10) -> bool:
    """Check local transaction log for duplicate submission. No API call."""
    if not TRANSACTION_LOG.exists():
        return False
    recent_cutoff = datetime.now() - timedelta(minutes=window_minutes)
    with open(TRANSACTION_LOG) as f:
        for line in f:
            try:
                entry = json.loads(line)
            except json.JSONDecodeError:
                continue
            timestamp = datetime.fromisoformat(entry['timestamp']).replace(tzinfo=None)
            if timestamp > recent_cutoff:
                if entry.get('details', {}).get('task_hash') == task_hash:
                    return True
    return False


# Self-imposed concurrent-submission cap. Aristotle (Harmonic) does NOT publish a hard
# server-side limit; aristotlelib only caps pagination (1-100). This guardrail prevents
# runaway parallel campaigns from saturating our own attention. Override via env var
# ARISTOTLE_MAX_CONCURRENT (e.g., export ARISTOTLE_MAX_CONCURRENT=50). See
# docs/infrastructure_changes_may30/U1_auto_routing.md for context.
DEFAULT_MAX_CONCURRENT = 25
MAX_CONCURRENT = int(os.environ.get('ARISTOTLE_MAX_CONCURRENT', str(DEFAULT_MAX_CONCURRENT)))


async def check_rate_limit_and_capacity(window_minutes: int = 10) -> dict:
    """Single API call to check both rate limit and queue capacity.

    The concurrent-submission cap is MAX_CONCURRENT (default 25; configurable via
    ARISTOTLE_MAX_CONCURRENT env var). This is a project-side guardrail, not an
    Aristotle server-side limit (aristotlelib 0.7.0 has no documented hard cap).

    Returns:
        {
            'recent_count': int,     # submissions in last window_minutes
            'in_progress': int,      # queued + in_progress count
            'has_capacity': bool,    # in_progress < MAX_CONCURRENT
            'slots_available': int,  # max(0, MAX_CONCURRENT - in_progress)
            'max_concurrent': int,   # the active cap
        }
    """
    set_api_key(ARISTOTLE_API_KEY)
    # aristotlelib 2.0: server-side filter on ProjectStatus.RUNNING (was QUEUED/IN_PROGRESS in 0.7).
    # Pull up to MAX_CONCURRENT+5 to avoid undercounting if we ever push close to the cap.
    page_limit = min(100, MAX_CONCURRENT + 5)
    projects, _ = await Project.list_projects(limit=page_limit, status=ProjectStatus.RUNNING)
    recent_projects, _ = await Project.list_projects(limit=page_limit)
    now = datetime.now()

    recent_count = 0
    for p in recent_projects:
        created = datetime.fromisoformat(str(p.created_at).replace('Z', '+00:00'))
        age_minutes = (now - created.replace(tzinfo=None)).total_seconds() / 60
        if age_minutes < window_minutes:
            recent_count += 1

    in_progress = len(projects)

    return {
        'recent_count': recent_count,
        'in_progress': in_progress,
        'has_capacity': in_progress < MAX_CONCURRENT,
        'slots_available': max(0, MAX_CONCURRENT - in_progress),
        'max_concurrent': MAX_CONCURRENT,
    }


STRATEGY_PATTERNS = [
    re.compile(r'(?i)^#+\s*(proof\s+strategy|proposed\s+(strategy|approach)|key\s+lemma)'),
    re.compile(r'(?i)^#+\s*(main\s+proof|proof\s+assembly|proof\s+outline)'),
    re.compile(r'(?i)^APPROACH\s+\d'),
    re.compile(r'(?i)^FALLBACK\s+\d'),
    re.compile(r'(?i)^(PRIMARY|SECONDARY):\s'),
    re.compile(r'(?i)^###?\s+Lemma\s+\d'),
    re.compile(r'(?i)^\s*Proposed\s+proof:'),
    re.compile(r'(?i)^=+\s*(PROOF|WHAT TO PROVE|APPROACH)'),
]

FALSIFICATION_PATTERNS = [
    re.compile(r'(?i)\b(falsif|disprove|counterexample|negat)'),
    re.compile(r'(?i)\bis\s+this\s+(true|false|real)'),
    re.compile(r'(?i)\btest\s+(whether|if)'),
]

MAX_SKETCH_LINES = 30
MAX_LEAN_LINES_IN_SKETCH = 5


# F-mode pre-submission patterns (S7, 2026-05-30 — failure_mode_prevention.md).
# Each catalog entry pairs an F-code with one or more compiled regex patterns
# that, when present in a bare sketch, indicate elevated risk. The patterns are
# heuristic — they fire warnings, not hard rejects, EXCEPT where the F-mode is
# already known to be unrecoverable (F1 in conjunction with no finite range).
#
# References:
#   docs/failure_mode_prevention.md (master mapping)
#   analysis/failure_dna_may30.md (F1-F10 catalog)
#   docs/closure_taxonomy_may30.md (CR enum mapping)

# F1 — undecidable wrapper red flags. If the theorem statement uses any of
# these predicates AND no finite range constraint appears anywhere in the file,
# Aristotle is overwhelmingly likely to produce an Iff.rfl trap.
F1_UNDECIDABLE_WRAPPERS = [
    re.compile(r'\bIrrational\b'),
    re.compile(r'\bTendsto\b'),
    re.compile(r'\bIsEquivalent\b'),
    re.compile(r'\bHasDensity\b'),
    re.compile(r'\bSet\.(?:Finite|Infinite)\b'),
    re.compile(r'\bFilter\.(?:atTop|atBot)\b'),
    re.compile(r'\bCardinal\.aleph\b'),
]
# A finite-range constraint that rescues an undecidable wrapper from F1.
F1_FINITE_RANGE_HINTS = [
    re.compile(r'\bFinset\.(?:range|Icc|Ico|Ioc|Ioo)\b'),
    re.compile(r'\b∀\s+\w+\s*≤\s*\d+'),
    re.compile(r'\b∃\s+\w+\s*≤\s*\d+'),
    re.compile(r'\b≤\s*\d+'),                  # generic "≤ N" with a literal N
    re.compile(r'\bn\.(?:val|toNat)\b'),
    re.compile(r'\bDecidable\b'),
]

# F3 — infrastructure-overgrowth red flags. Sketches that hand-wave "reduces
# to" / "follows from infinite descent / Pell / sieve" without naming the
# precise finite obstruction tend to produce 1000-line side-lemma towers.
F3_HANDWAVE_PATTERNS = [
    re.compile(r'(?i)\breduces\s+to\b'),
    re.compile(r'(?i)\bfollows\s+from\s+(?:a\s+)?(?:well[\s-]known|standard|classical)\b'),
    re.compile(r'(?i)\binfinite\s+descent\b'),
    re.compile(r'(?i)\bsieve\s+method\b'),
    re.compile(r'(?i)\bPell\s+(?:equation|sequence|theory)\b'),
]

# F4 — axiomatize-the-hard red flags. Sketches that defer to "classical X" or
# "standard Y" without naming the exact Mathlib lemma invite Aristotle to leave
# exact? stubs.
F4_HARD_DEFER_PATTERNS = [
    re.compile(r'(?i)\bby\s+classical\b'),
    re.compile(r'(?i)\bby\s+standard\b'),
    re.compile(r'(?i)(?:well[\s-]known|classical|standard)\s+(?:result|fact|theorem|lemma)\b'),
]

# F10 — definition-mismatch red flag. Sketches that define new `def` / `class`
# / `structure` / `instance` (≥1 line of definition) instead of importing from
# formal-conjectures are at risk of Aristotle producing a definitionally
# disconnected proof.
F10_LOCAL_DEF_PATTERNS = [
    re.compile(r'^\s*def\s+\w+\s'),
    re.compile(r'^\s*class\s+\w+\s'),
    re.compile(r'^\s*structure\s+\w+\s'),
    re.compile(r'^\s*instance\s+\w+\s*:'),
    re.compile(r'^\s*abbrev\s+\w+\s'),
]


def _check_f_modes_pre_submission(content: str, theorem_body: str = "") -> list[tuple[str, str]]:
    """Scan a sketch for pre-submission F-mode red flags.

    Returns a list of (F-code, human-readable warning) tuples. EMPTY list
    means no red flags detected. Callers turn warnings into stdout messages
    (and optionally a hard reject for F7).

    The check is intentionally heuristic — false positives are acceptable
    when the cost is a single line of stdout noise. False negatives are the
    real worry, because they let known-bad shapes through.

    Args:
        content: the full sketch text (.txt body).
        theorem_body: optional pre-extracted theorem body. If empty, the
            function extracts it from `content`.
    """
    warnings: list[tuple[str, str]] = []

    # Extract theorem body if not provided
    if not theorem_body:
        m = re.search(r'theorem\s+\w+[^:]*:(?P<body>.*?):=\s*by\b', content, re.DOTALL)
        if not m:
            m = re.search(r'theorem\s+\w+[^:]*:(?P<body>.*?):=\s*sorry\b', content, re.DOTALL)
        if m:
            theorem_body = re.sub(r'\s+', ' ', m.group('body')).strip()

    # ---- F1: undecidable wrapper ----------------------------------------
    # Trigger only when the theorem body uses an undecidable wrapper AND
    # the WHOLE sketch has no finite-range constraint.
    if theorem_body:
        f1_hit = next((p.pattern for p in F1_UNDECIDABLE_WRAPPERS if p.search(theorem_body)), None)
        if f1_hit:
            f1_rescue = any(p.search(content) for p in F1_FINITE_RANGE_HINTS)
            if not f1_rescue:
                warnings.append((
                    "F1",
                    f"Theorem uses undecidable wrapper '{f1_hit}' with no finite-range constraint.\n"
                    "  Aristotle will likely define `answer := <Statement>` and prove "
                    "`answer ↔ Statement := Iff.rfl`. To avoid F1/F8:\n"
                    "    1) restrict to `∀ n ∈ Finset.range N, ...` with explicit N, OR\n"
                    "    2) state a structural sub-claim that IS decidable, OR\n"
                    "    3) skip this problem (it requires asymptotic analysis we can't formalize).\n"
                    "  Reference: docs/failure_mode_prevention.md F1."
                ))

    # ---- F3: hand-wave hints --------------------------------------------
    f3_hits = [p.pattern for p in F3_HANDWAVE_PATTERNS if p.search(content)]
    if f3_hits:
        warnings.append((
            "F3",
            "Sketch hand-waves a reduction (matched: " + ", ".join(f3_hits[:3]) + ").\n"
            "  Aristotle will likely produce 30-100 helper lemmas WITHOUT closing the main theorem.\n"
            "  Fix: name the precise finite obstruction OR remove the hand-wave from the sketch.\n"
            "  Reference: docs/failure_mode_prevention.md F3."
        ))

    # ---- F4: axiomatize-the-hard ----------------------------------------
    f4_hits = [p.pattern for p in F4_HARD_DEFER_PATTERNS if p.search(content)]
    if f4_hits:
        warnings.append((
            "F4",
            "Sketch defers to 'classical/standard' result without naming Mathlib lemma "
            "(matched: " + ", ".join(f4_hits[:2]) + ").\n"
            "  Aristotle will likely leave `exact?` stubs that compile but axiomatize the deferred step.\n"
            "  Fix: name the exact Mathlib name (e.g. `Nat.Prime.factorization`).\n"
            "  Reference: docs/failure_mode_prevention.md F4."
        ))

    # ---- F10: local def / structure -------------------------------------
    f10_hits: list[str] = []
    for line in content.splitlines():
        for p in F10_LOCAL_DEF_PATTERNS:
            if p.match(line):
                f10_hits.append(line.strip()[:80])
                break
    if f10_hits:
        warnings.append((
            "F10",
            "Sketch contains local definition(s) (e.g. " + repr(f10_hits[0]) + ").\n"
            "  Aristotle may produce a proof against this LOCAL def that disconnects from "
            "the upstream formal-conjectures statement (F10 mismatch).\n"
            "  Fix: import the statement from `formal-conjectures` instead of redefining it.\n"
            "  Reference: docs/failure_mode_prevention.md F10."
        ))

    return warnings


def _check_closure_axis_consistency(axis: dict) -> list[str]:
    """Schema-level consistency checks across closure-axis fields.

    Returns a list of human-readable error strings. EMPTY list = consistent.
    A non-empty list MUST cause check_closure_axis to REJECT — these are
    contradictions inside the agent's own classification, not gate decisions.

    The rules encode the verbatim definitions from docs/closure_taxonomy_may30.md.

    Currently checks:
      F7-coherence:  CS=bounded_version_closure → real_closure_candidate=false.
                     (The taxonomy says bounded version is publishable but never closure.)
      F2-coherence:  CR=em_tautology            → real_closure_candidate=false.
                     (em-tautology is hard-blocked at gate C6 anyway; this is belt-and-suspenders.)
      F1-coherence:  CR=iff_rfl_trap            → real_closure_candidate=false.
      F3-coherence:  CR=infrastructure_overgrowth → real_closure_candidate=false.
      F5-coherence:  CR=recursive_falsification → real_closure_candidate=false.
      F10-coherence: CR=definition_mismatch     → real_closure_candidate=false.
      HM-coherence:  HM=infrastructure_only     → real_closure_candidate=false.
      Formalization-only: CS=formalization_only → real_closure_candidate=false.
    """
    errors: list[str] = []
    cs = axis.get("CS")
    cr = axis.get("CR")
    hm = axis.get("HM")
    rcc = axis.get("real_closure_candidate")

    if rcc is True:
        # All contradictions only fire when the author claims real-closure.
        if cs == "bounded_version_closure":
            errors.append(
                "F7-coherence: CS=bounded_version_closure cannot coexist with "
                "real_closure_candidate=true. Bounded version is, by taxonomy "
                "definition, NOT real closure (docs/closure_taxonomy_may30.md §CS)."
            )
        if cs == "formalization_only":
            errors.append(
                "Formalization-only cannot coexist with real_closure_candidate=true. "
                "Formalization-only is, by taxonomy definition, NOT closure "
                "(docs/closure_taxonomy_may30.md §CS)."
            )
        bad_crs = {
            "em_tautology": "F2",
            "iff_rfl_trap": "F1",
            "infrastructure_overgrowth": "F3",
            "recursive_falsification": "F5",
            "definition_mismatch": "F10",
        }
        if cr in bad_crs:
            errors.append(
                f"{bad_crs[cr]}-coherence: CR={cr} cannot coexist with "
                "real_closure_candidate=true. This risk class is a failure "
                "mode, not a closure mechanism (docs/closure_taxonomy_may30.md §CR)."
            )
        if hm == "infrastructure_only":
            errors.append(
                "HM=infrastructure_only cannot coexist with real_closure_candidate=true. "
                "Infrastructure-only is, by definition, NOT a journal-grade closure "
                "(docs/closure_taxonomy_may30.md §HM)."
            )

    return errors


def _looks_like_em_tautology(text: str) -> bool:
    """True if the theorem body has the structural shape (X) ∨ ¬ (X).

    We extract the part of the file between `theorem ... :` and `:= by`/`:= sorry`,
    normalize whitespace, then check whether it matches a disjunction whose right
    side is the negation of its left side. Conservative: returns False if no
    theorem block is found, so it never blocks files that don't contain a Lean
    statement at all.
    """
    import re as _re
    m = _re.search(r'theorem\s+\w+[^:]*:(?P<body>.*?):=\s*by\b', text, _re.DOTALL)
    if not m:
        m = _re.search(r'theorem\s+\w+[^:]*:(?P<body>.*?):=\s*sorry\b', text, _re.DOTALL)
    if not m:
        return False
    body = _re.sub(r'\s+', ' ', m.group('body')).strip()
    # Look for disjunction with negation on right
    parts = _re.split(r'∨\s*¬', body, maxsplit=1)
    if len(parts) != 2:
        return False
    # Normalize both sides: strip whitespace AND all parens — parens are syntactic
    # noise; the question is whether the two propositions are equal as logical content.
    def _norm(s: str) -> str:
        return _re.sub(r'[\s()]+', '', s)
    left = _norm(parts[0])
    right = _norm(parts[1])
    if not left or not right:
        return False
    return left == right


def check_gap_targeting(input_file: Path) -> dict:
    """Validate that input_file targets an open gap. Hard block, no override.

    Returns:
        {"pass": True, "submission_type": "gap_targeting"|"falsification",
         "gap_statement": str, "line_count": int}

    Raises:
        GapTargetingError with actionable fix message.
    """
    suffix = input_file.suffix.lower()

    # C1: Reject .lean files
    if suffix == '.lean':
        raise GapTargetingError(
            "Gap-targeting requires INFORMAL (.txt). Convert to bare conjecture sketch.\n"
            "  Sketch format: OPEN GAP / English statement / Lean statement / Status\n"
            "  Max 30 lines. No proof strategy."
        )

    # C2: Empty file
    content = input_file.read_text()
    if not content.strip():
        raise GapTargetingError("Sketch is empty. Write the bare conjecture statement.")

    lines = content.splitlines()
    non_blank = [l for l in lines if l.strip() and not l.strip().startswith('---')]

    # C3: Line count
    if len(non_blank) > MAX_SKETCH_LINES:
        raise GapTargetingError(
            f"Sketch has {len(non_blank)} non-blank lines (max {MAX_SKETCH_LINES}).\n"
            "  Strip proof strategy — state only the open gap.\n"
            "  Format: OPEN GAP / English / Lean / Status"
        )

    # Check falsification BEFORE strategy (falsification may look strategy-like)
    is_falsification = any(
        p.search(line) for line in lines for p in FALSIFICATION_PATTERNS
    )

    # C4: Strategy keywords (skip if falsification)
    if not is_falsification:
        for line in lines:
            for pattern in STRATEGY_PATTERNS:
                if pattern.search(line):
                    matched = line.strip()[:60]
                    raise GapTargetingError(
                        f"Sketch contains proof guidance: '{matched}'\n"
                        "  Remove all strategy — let Aristotle find the path.\n"
                        "  Keep only: OPEN GAP / English statement / Lean statement / Status"
                    )

    # C5: Extended Lean code blocks
    lean_indicators = [
        'theorem ', 'def ', 'lemma ', 'import ', ':= by', 'where', '  sorry',
        '| ', 'instance ', 'class ', 'structure '
    ]
    lean_lines = sum(1 for l in lines if any(ind in l for ind in lean_indicators))
    if lean_lines > MAX_LEAN_LINES_IN_SKETCH:
        raise GapTargetingError(
            f"Sketch contains {lean_lines} lines of Lean code (max {MAX_LEAN_LINES_IN_SKETCH}).\n"
            "  Use only 1-3 lines for the formal theorem statement."
        )

    # C6: em-tautology guard (added 2026-05-28 after PILOT_ERDOS850 found this pathology).
    # A theorem statement of the form `(P) ∨ ¬ (P)` is the law of excluded middle —
    # Aristotle discharges it with `exact em _` in one line without engaging the math.
    # We detect this by looking for a disjunction whose two clauses are textually
    # identical modulo the leading `¬ `. Falsifications are exempt (they intentionally
    # negate a claim).
    if not is_falsification and _looks_like_em_tautology(content):
        raise GapTargetingError(
            "Theorem statement looks like (P) ∨ ¬ (P) — the law of excluded middle.\n"
            "  Aristotle will discharge this with `exact em _` and resolve nothing.\n"
            "  Rewrite as one direction:\n"
            "    existence:    theorem ... : ∃ x y, P x y := by sorry\n"
            "    impossibility: theorem ... : ¬ ∃ x y, P x y := by sorry\n"
            "  Submit one (or both, as separate files). Never the disjunction.\n"
            "  Reference: docs/research/PILOT_ERDOS850.md"
        )

    # Extract gap statement (first non-blank, non-comment line)
    gap_statement = ""
    for line in lines:
        stripped = line.strip().lstrip('#').lstrip('-').strip()
        if stripped:
            gap_statement = stripped[:200]
            break

    submission_type = "falsification" if is_falsification else "gap_targeting"

    # C7: F-mode pre-submission warnings (S7, 2026-05-30).  These do NOT
    # block the submission — they print a warning to stdout so the operator
    # can decide whether to bail. The exception is F1 with no finite range,
    # which is upgraded to a hard reject because Iff.rfl is unrecoverable.
    # See docs/failure_mode_prevention.md.
    f_mode_warnings = _check_f_modes_pre_submission(content)
    f1_hits = [w for code, w in f_mode_warnings if code == "F1"]
    if f1_hits and not is_falsification:
        # F1 without a finite-range rescue is unrecoverable — Aristotle's
        # only path is Iff.rfl on an undecidable wrapper. Hard reject.
        raise GapTargetingError(
            "Pre-submission F1 check failed: "
            "undecidable wrapper without finite-range constraint.\n"
            f"  {f1_hits[0]}"
        )

    return {
        "pass": True,
        "submission_type": submission_type,
        "gap_statement": gap_statement,
        "line_count": len(non_blank),
        "f_mode_warnings": f_mode_warnings,
    }


def check_literature_freshness(
    input_file: Path,
    *,
    force_stale: bool = False,
    literature_ack: str | None = None,
) -> dict:
    """Run literature_check.py against the sketch's problem_id and decide
    whether the submission may proceed.

    Decision table:
      status                 | gate behavior
      ---------------------- + ------------------------------------------------
      AI_CLOSED              | REJECT unless force_stale=True
      RECENTLY_SOLVED        | REJECT unless force_stale=True
      AMBIGUOUS              | REJECT unless literature_ack is a non-empty string
      POSSIBLY_SOLVED        | REJECT unless literature_ack is a non-empty string
      CLEAR                  | pass silently
      UNKNOWN                | pass with a soft notice (no problem_id detected)

    Returns a dict {status, problem_id, citations, ack_required, blocked, reason}.
    """
    # Import lazily so callers that don't need this aren't penalised on import.
    try:
        from literature_check import status_for_sketch  # type: ignore
    except ImportError:
        # When invoked from elsewhere, fall back to a path-based import.
        import importlib.util
        lit_path = MATH_DIR / "scripts" / "literature_check.py"
        if not lit_path.exists():
            return {
                "status": "UNKNOWN",
                "problem_id": None,
                "citations": [],
                "blocked": False,
                "reason": "literature_check.py not found",
            }
        spec = importlib.util.spec_from_file_location("literature_check", lit_path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)  # type: ignore
        status_for_sketch = mod.status_for_sketch  # type: ignore

    try:
        report = status_for_sketch(input_file)
    except Exception as e:
        # Never let a literature-check failure block a submission — degrade gracefully.
        print(f"   ⚠️  literature-check failed ({type(e).__name__}: {e}); proceeding")
        return {"status": "UNKNOWN", "problem_id": None, "citations": [],
                "blocked": False, "reason": f"check raised {type(e).__name__}"}

    status = report.get("status", "UNKNOWN")
    pid = report.get("problem_id")
    citations = report.get("citations") or []

    print(f"   problem_id: {pid or '(none detected)'}")
    print(f"   literature status: {status}")
    for c in citations[:3]:
        ev = c.get("evidence", "")
        src = c.get("source", "")
        print(f"     - [{src}] {ev}")

    if status in ("AI_CLOSED", "RECENTLY_SOLVED"):
        if force_stale:
            print(f"   ⚠️  Literature gate BYPASSED (--force-literature-stale)")
            log_transaction("LITERATURE_STALE_BYPASS", {
                "problem_id": pid, "status": status,
                "citations": citations,
            })
            return {"status": status, "problem_id": pid, "citations": citations,
                    "blocked": False, "reason": "bypassed via --force-literature-stale"}
        return {"status": status, "problem_id": pid, "citations": citations,
                "blocked": True,
                "reason": f"problem closed in literature ({status}); see citations"}

    if status in ("AMBIGUOUS", "POSSIBLY_SOLVED"):
        if literature_ack and literature_ack.strip():
            print(f"   ✅ Literature ack: {literature_ack[:80]}")
            log_transaction("LITERATURE_ACK_RECORDED", {
                "problem_id": pid, "status": status,
                "ack": literature_ack, "citations": citations,
            })
            return {"status": status, "problem_id": pid, "citations": citations,
                    "blocked": False, "ack": literature_ack,
                    "reason": "ack provided"}
        return {"status": status, "problem_id": pid, "citations": citations,
                "blocked": True,
                "reason": f"literature status {status}; pass --literature-ack \"<comment>\""}

    # CLEAR / UNKNOWN
    return {"status": status, "problem_id": pid, "citations": citations,
            "blocked": False, "reason": "clear"}


def _companion_closure_path(input_file: Path) -> Path:
    """Return the companion .closure.json path for a sketch.

    Convention (docs/closure_axis_companion_spec.md): strip the input file's
    suffix and append `.closure.json` adjacent to it.
    """
    return input_file.with_suffix('.closure.json')


def check_closure_axis(
    input_file: Path,
    rubric_points: bool = False,
) -> dict:
    """Validate the closure-axis companion file and decide whether to allow submission.

    Behavior (matches docs/closure_axis_companion_spec.md gate table):

      - Missing companion: WARN + log MISSING_CLOSURE_AXIS, ALLOW.
      - Invalid JSON / bad schema: REJECT (ClosureAxisError).
      - Valid, real_closure_candidate=True: PASS.
      - Valid, real_closure_candidate=False, rubric_points=False: REJECT.
      - Valid, real_closure_candidate=False, rubric_points=True: PASS, log RUBRIC_POINTS_OVERRIDE.

    Returns:
        {"present": bool,
         "axis": dict | None,           # the parsed closure_axis_json (or None if missing)
         "real_closure_candidate": bool | None,
         "override": bool}              # True iff rubric_points was used to permit a non-candidate
    """
    companion = _companion_closure_path(input_file)
    if not companion.exists():
        log_transaction("MISSING_CLOSURE_AXIS", {
            "input_file": str(input_file),
            "expected_companion": str(companion),
        })
        print(f"   ⚠️  WARN: no closure-axis companion at {companion.name} — submission allowed (transition period)")
        return {
            "present": False,
            "axis": None,
            "real_closure_candidate": None,
            "override": False,
        }

    # Parse JSON
    try:
        text = companion.read_text()
        axis = json.loads(text)
    except (OSError, json.JSONDecodeError) as e:
        raise ClosureAxisError(
            f"Closure-axis companion is unreadable or invalid JSON: {companion.name}\n"
            f"  Error: {e}\n"
            f"  Fix: ensure {companion.name} is valid JSON per docs/closure_axis_companion_spec.md."
        )

    if not isinstance(axis, dict):
        raise ClosureAxisError(
            f"Closure-axis companion must be a JSON object: {companion.name}\n"
            f"  Got: {type(axis).__name__}"
        )

    # Schema check: all 6 fields present
    missing = CLOSURE_AXIS_REQUIRED_FIELDS - set(axis.keys())
    if missing:
        raise ClosureAxisError(
            f"Closure-axis companion missing required field(s): {sorted(missing)}\n"
            f"  File: {companion.name}\n"
            f"  Required: {sorted(CLOSURE_AXIS_REQUIRED_FIELDS)}\n"
            f"  Reference: docs/closure_axis_companion_spec.md"
        )

    extra = set(axis.keys()) - CLOSURE_AXIS_REQUIRED_FIELDS
    if extra:
        raise ClosureAxisError(
            f"Closure-axis companion has unexpected field(s): {sorted(extra)}\n"
            f"  File: {companion.name}\n"
            f"  Only allowed: {sorted(CLOSURE_AXIS_REQUIRED_FIELDS)}\n"
            f"  Reference: docs/closure_axis_companion_spec.md"
        )

    # Enum validation
    enum_checks = [
        ("CS", CLOSURE_AXIS_CS_VALUES),
        ("CM", CLOSURE_AXIS_CM_VALUES),
        ("CR", CLOSURE_AXIS_CR_VALUES),
        ("HM", CLOSURE_AXIS_HM_VALUES),
    ]
    for field, allowed in enum_checks:
        value = axis[field]
        if not isinstance(value, str) or value not in allowed:
            raise ClosureAxisError(
                f"Closure-axis field '{field}' has invalid value: {value!r}\n"
                f"  File: {companion.name}\n"
                f"  Allowed: {sorted(allowed)}\n"
                f"  Reference: docs/closure_taxonomy_may30.md"
            )

    if not isinstance(axis["real_closure_candidate"], bool):
        raise ClosureAxisError(
            f"Closure-axis 'real_closure_candidate' must be true|false (bool).\n"
            f"  File: {companion.name}\n"
            f"  Got: {axis['real_closure_candidate']!r} ({type(axis['real_closure_candidate']).__name__})"
        )

    if not isinstance(axis["rationale"], str) or not axis["rationale"].strip():
        raise ClosureAxisError(
            f"Closure-axis 'rationale' must be a non-empty string.\n"
            f"  File: {companion.name}"
        )

    # F-mode coherence checks (S7, 2026-05-30). Reject combinations that the
    # taxonomy declares structurally impossible — e.g. CS=bounded_version_closure
    # with real_closure_candidate=true (the F7 contradiction).
    consistency_errors = _check_closure_axis_consistency(axis)
    if consistency_errors:
        bullet_list = "\n  - ".join(consistency_errors)
        raise ClosureAxisError(
            f"Closure-axis classification is internally inconsistent:\n"
            f"  File: {companion.name}\n"
            f"  - {bullet_list}\n"
            f"  Fix: either flip real_closure_candidate to false, or pick a CS/CR/HM "
            f"that is consistent with closure (see docs/closure_taxonomy_may30.md)."
        )

    rcc = axis["real_closure_candidate"]
    if rcc:
        print(f"   ✅ Closure axis: real_closure_candidate=true ({axis['CS']}/{axis['HM']})")
        return {
            "present": True,
            "axis": axis,
            "real_closure_candidate": True,
            "override": False,
        }

    # rcc is False
    if not rubric_points:
        raise ClosureAxisError(
            "Closure-axis classification: real_closure_candidate=false.\n"
            f"  CS={axis['CS']}  CM={axis['CM']}  CR={axis['CR']}  HM={axis['HM']}\n"
            f"  Rationale: {axis['rationale']}\n"
            "  This submission is NOT in the real-closure lane.\n"
            "  To submit anyway (mechanical extension / engineering port), pass --rubric-points.\n"
            "  Reference: docs/closure_axis_companion_spec.md gate table, MEMORY.md directive #4."
        )

    log_transaction("RUBRIC_POINTS_OVERRIDE", {
        "input_file": str(input_file),
        "axis": axis,
    })
    print(f"   ⚠️  Closure axis: real_closure_candidate=false; --rubric-points override applied")
    return {
        "present": True,
        "axis": axis,
        "real_closure_candidate": False,
        "override": True,
    }


def _companion_fusion_path(input_file: Path) -> Path:
    """Return the companion .fusion.json path for a sketch.

    Convention (docs/fusion_axis_companion_spec.md): strip the input file's
    suffix and append `.fusion.json` adjacent to it.
    """
    return input_file.with_suffix('.fusion.json')


def _count_sentences(s: str) -> int:
    """Rough sentence count for the bridge_lemma length check.

    Splits on `.`, `?`, `!` followed by whitespace or end-of-string. Used
    only for the bridge_lemma ≤3 sentence cap.
    """
    if not s.strip():
        return 0
    parts = re.split(r'[.!?](?:\s+|$)', s.strip())
    return len([p for p in parts if p.strip()])


def check_fusion_companion(
    input_file: Path,
    sketch_lines: int | None = None,
    blocklist_path: Path | None = None,
) -> dict:
    """Validate the FUSION-lane companion file and run the airlock.

    Triggered when `--fusion-lane` is passed to `safe_submit()`. Always
    REJECTS on any failure — no override. The only bypass is the global
    `--force` flag (reserved for the orchestrator pipeline).

    Decision table (matches docs/fusion_axis_companion_spec.md):

      - Companion missing                        → REJECT (FusionCompanionError)
      - Companion invalid JSON / non-object       → REJECT
      - Missing required field                    → REJECT
      - Extra unexpected field                    → REJECT
      - Non-blank line count > 80                 → REJECT
      - `fit_score` outside [0.0, 1.0]            → REJECT
      - `informal_proof_outline` > 500 words OR > 4000 chars → REJECT
      - `bridge_lemma` > 3 sentences OR > 600 chars          → REJECT
      - `candidate_lemmas` empty or > 10 entries  → REJECT
      - `stage_outputs` missing literature/analogies/techniques path → REJECT
      - Airlock detects strategy leak in .txt    → REJECT
      - All checks pass                           → PASS

    Args:
        input_file: the .txt sketch.
        sketch_lines: ignored, accepted for caller-symmetry with check_gap_targeting.
        blocklist_path: optional explicit static blocklist file; defaults to
            scripts/airlock_blocklist.txt.

    Returns:
        {"present": True,
         "fusion": dict,           # the parsed companion
         "non_blank_lines": int,
         "airlock_passed": True}

    Raises:
        FusionCompanionError on any validation failure.
    """
    companion_path = _companion_fusion_path(input_file)
    if not companion_path.exists():
        raise FusionCompanionError(
            "FUSION lane requires a companion .fusion.json file.\n"
            f"  Expected at: {companion_path}\n"
            "  Author the companion per docs/fusion_axis_companion_spec.md\n"
            "  (9 required fields, ≤80 non-blank lines, paired-LLM dossier metadata)."
        )

    # Parse JSON
    try:
        raw = companion_path.read_text()
        fusion = json.loads(raw)
    except (OSError, json.JSONDecodeError) as e:
        raise FusionCompanionError(
            f"Fusion companion is unreadable or invalid JSON: {companion_path.name}\n"
            f"  Error: {e}\n"
            f"  Fix: ensure {companion_path.name} is valid JSON per "
            "docs/fusion_axis_companion_spec.md."
        )

    if not isinstance(fusion, dict):
        raise FusionCompanionError(
            f"Fusion companion must be a JSON object: {companion_path.name}\n"
            f"  Got: {type(fusion).__name__}"
        )

    # Line budget
    non_blank = [ln for ln in raw.splitlines() if ln.strip()]
    if len(non_blank) > FUSION_MAX_LINES:
        raise FusionCompanionError(
            f"Fusion companion has {len(non_blank)} non-blank lines "
            f"(max {FUSION_MAX_LINES}).\n"
            f"  File: {companion_path.name}\n"
            "  Trim. The companion is METADATA pointing to the dossier "
            "(stage_outputs.*_path); it is NOT the dossier itself."
        )

    # Required fields
    missing = FUSION_REQUIRED_FIELDS - set(fusion.keys())
    if missing:
        raise FusionCompanionError(
            f"Fusion companion missing required field(s): {sorted(missing)}\n"
            f"  File: {companion_path.name}\n"
            f"  Required: {sorted(FUSION_REQUIRED_FIELDS)}\n"
            "  Reference: docs/fusion_axis_companion_spec.md"
        )
    extra = set(fusion.keys()) - FUSION_REQUIRED_FIELDS
    if extra:
        raise FusionCompanionError(
            f"Fusion companion has unexpected field(s): {sorted(extra)}\n"
            f"  File: {companion_path.name}\n"
            f"  Only allowed: {sorted(FUSION_REQUIRED_FIELDS)}\n"
            "  Reference: docs/fusion_axis_companion_spec.md"
        )

    # problem_id
    pid = fusion["problem_id"]
    if not isinstance(pid, str) or not re.fullmatch(r"[a-z0-9_]+", pid):
        raise FusionCompanionError(
            "Fusion 'problem_id' must be a string matching ^[a-z0-9_]+$.\n"
            f"  File: {companion_path.name}\n  Got: {pid!r}"
        )

    # stage_outputs sub-schema
    so = fusion["stage_outputs"]
    if not isinstance(so, dict):
        raise FusionCompanionError(
            "Fusion 'stage_outputs' must be a JSON object.\n"
            f"  File: {companion_path.name}"
        )
    so_missing = FUSION_STAGE_OUTPUT_FIELDS - set(so.keys())
    if so_missing:
        raise FusionCompanionError(
            f"Fusion 'stage_outputs' missing field(s): {sorted(so_missing)}\n"
            f"  File: {companion_path.name}\n"
            f"  Required: {sorted(FUSION_STAGE_OUTPUT_FIELDS)}"
        )
    so_extra = set(so.keys()) - FUSION_STAGE_OUTPUT_FIELDS
    if so_extra:
        raise FusionCompanionError(
            f"Fusion 'stage_outputs' has unexpected field(s): {sorted(so_extra)}\n"
            f"  File: {companion_path.name}"
        )
    for sub in FUSION_STAGE_OUTPUT_FIELDS:
        v = so[sub]
        if not isinstance(v, str) or not v.strip():
            raise FusionCompanionError(
                f"Fusion 'stage_outputs.{sub}' must be a non-empty string path.\n"
                f"  File: {companion_path.name}  Got: {v!r}"
            )

    # named_technique
    nt = fusion["named_technique"]
    if not isinstance(nt, str) or not nt.strip():
        raise FusionCompanionError(
            "Fusion 'named_technique' must be a non-empty string.\n"
            f"  File: {companion_path.name}"
        )
    if len(nt) > FUSION_MAX_NAMED_TECHNIQUE_CHARS:
        raise FusionCompanionError(
            f"Fusion 'named_technique' too long: {len(nt)} chars "
            f"(max {FUSION_MAX_NAMED_TECHNIQUE_CHARS}).\n"
            f"  File: {companion_path.name}"
        )

    # seminal_paper_arxiv — URL string or "none"
    sp = fusion["seminal_paper_arxiv"]
    if not isinstance(sp, str) or not sp.strip():
        raise FusionCompanionError(
            "Fusion 'seminal_paper_arxiv' must be a URL string or 'none'.\n"
            f"  File: {companion_path.name}"
        )

    # fit_score
    fs = fusion["fit_score"]
    if not isinstance(fs, (int, float)) or isinstance(fs, bool):
        raise FusionCompanionError(
            "Fusion 'fit_score' must be a number in [0.0, 1.0].\n"
            f"  File: {companion_path.name}  Got: {fs!r}"
        )
    if not (0.0 <= float(fs) <= 1.0):
        raise FusionCompanionError(
            f"Fusion 'fit_score' out of range: {fs} (must be in [0.0, 1.0]).\n"
            f"  File: {companion_path.name}"
        )

    # bridge_lemma
    bl = fusion["bridge_lemma"]
    if not isinstance(bl, str) or not bl.strip():
        raise FusionCompanionError(
            "Fusion 'bridge_lemma' must be a non-empty string (1-3 sentences).\n"
            f"  File: {companion_path.name}"
        )
    if len(bl) > FUSION_MAX_BRIDGE_CHARS:
        raise FusionCompanionError(
            f"Fusion 'bridge_lemma' too long: {len(bl)} chars "
            f"(max {FUSION_MAX_BRIDGE_CHARS}).\n"
            f"  File: {companion_path.name}"
        )
    sentence_count = _count_sentences(bl)
    if sentence_count > FUSION_MAX_BRIDGE_SENTENCES:
        raise FusionCompanionError(
            f"Fusion 'bridge_lemma' too long: {sentence_count} sentences "
            f"(max {FUSION_MAX_BRIDGE_SENTENCES}).\n"
            f"  File: {companion_path.name}"
        )

    # informal_proof_outline
    out = fusion["informal_proof_outline"]
    if not isinstance(out, str) or not out.strip():
        raise FusionCompanionError(
            "Fusion 'informal_proof_outline' must be a non-empty string.\n"
            f"  File: {companion_path.name}"
        )
    if len(out) > FUSION_MAX_OUTLINE_CHARS:
        raise FusionCompanionError(
            f"Fusion 'informal_proof_outline' too long: {len(out)} chars "
            f"(max {FUSION_MAX_OUTLINE_CHARS}).\n"
            f"  File: {companion_path.name}"
        )
    word_count = len(out.split())
    if word_count > FUSION_MAX_OUTLINE_WORDS:
        raise FusionCompanionError(
            f"Fusion 'informal_proof_outline' too long: {word_count} words "
            f"(max {FUSION_MAX_OUTLINE_WORDS}).\n"
            f"  File: {companion_path.name}"
        )

    # candidate_lemmas
    lemmas = fusion["candidate_lemmas"]
    if not isinstance(lemmas, list):
        raise FusionCompanionError(
            "Fusion 'candidate_lemmas' must be an array of strings.\n"
            f"  File: {companion_path.name}  Got: {type(lemmas).__name__}"
        )
    if not (FUSION_MIN_CANDIDATE_LEMMAS <= len(lemmas) <= FUSION_MAX_CANDIDATE_LEMMAS):
        raise FusionCompanionError(
            f"Fusion 'candidate_lemmas' has {len(lemmas)} entries "
            f"(need {FUSION_MIN_CANDIDATE_LEMMAS}-{FUSION_MAX_CANDIDATE_LEMMAS}).\n"
            f"  File: {companion_path.name}"
        )
    for i, entry in enumerate(lemmas):
        if not isinstance(entry, str) or not entry.strip():
            raise FusionCompanionError(
                f"Fusion 'candidate_lemmas[{i}]' must be a non-empty string.\n"
                f"  File: {companion_path.name}  Got: {entry!r}"
            )

    # honest_disclaimer
    hd = fusion["honest_disclaimer"]
    if not isinstance(hd, str) or not hd.strip():
        raise FusionCompanionError(
            "Fusion 'honest_disclaimer' must be a non-empty string.\n"
            f"  File: {companion_path.name}"
        )

    # Airlock check on the .txt
    try:
        from airlock_check import run_airlock, AirlockError  # type: ignore
    except ImportError:
        # Path-based import for use outside scripts/ cwd
        import importlib.util
        airlock_path = MATH_DIR / "scripts" / "airlock_check.py"
        if not airlock_path.exists():
            raise FusionCompanionError(
                f"FUSION gate cannot find airlock script at {airlock_path}.\n"
                "  Install scripts/airlock_check.py or set PYTHONPATH."
            )
        spec = importlib.util.spec_from_file_location("airlock_check", airlock_path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)  # type: ignore
        run_airlock = mod.run_airlock  # type: ignore
        AirlockError = mod.AirlockError  # type: ignore

    try:
        airlock_result = run_airlock(
            input_file,
            companion_path=companion_path,
            blocklist_path=blocklist_path,
            quiet=True,
        )
    except AirlockError as e:
        raise FusionCompanionError(
            "FUSION airlock REJECTED: strategy term leaked into bare .txt.\n"
            f"  {e}\n"
            "  Move strategy content into the .fusion.json companion; keep "
            "the .txt bare per docs/fusion_axis_companion_spec.md."
        )

    print(
        f"   ✅ Fusion companion: {companion_path.name} "
        f"(nblines={len(non_blank)}/{FUSION_MAX_LINES}, "
        f"technique={nt[:50]!r}, fit={fs}, "
        f"airlock static={airlock_result['static_tokens']} "
        f"dynamic={airlock_result['dynamic_tokens']})"
    )
    return {
        "present": True,
        "fusion": fusion,
        "non_blank_lines": len(non_blank),
        "airlock_passed": True,
    }


def extract_problem_id(input_file: Path) -> str | None:
    """Extract problem ID from sketch filename or content."""
    import re as re_mod

    # From filename: strip slot prefix and extension
    stem = input_file.stem
    m = re_mod.match(r'slot\d+_(.+?)(?:_v\d+)?$', stem)
    if m:
        problem_id = m.group(1).lower().replace(' ', '_')
        return problem_id[:50] if problem_id else None

    # From content: look for OPEN GAP: line
    try:
        content = input_file.read_text()
        for line in content.splitlines()[:5]:
            m2 = re_mod.match(r'(?i)OPEN\s+GAP:\s*(.+)', line)
            if m2:
                problem_id = m2.group(1).strip().lower()
                problem_id = re_mod.sub(r'[^a-z0-9]+', '_', problem_id)
                return problem_id[:50] if problem_id else None
    except Exception:
        pass

    return None


def gather_context(problem_id: str, verbose: bool = False) -> list[Path]:
    """Find all prior _result.lean files for this problem from tracking.db.

    Schema-aware: queries by (output_file IS NOT NULL) rather than a fixed
    status enum, so it stays correct as new status values are added. We do
    still bias toward statuses that imply a useful artifact, but we do not
    exclude rows on status alone — `output_file IS NOT NULL` is the primary
    gate, with `verified != 0` ruling out artifacts already audited as bad.

    History:
      - Pre-2026-05-30: filtered on status IN ('compiled_clean','near_miss',
        'completed') — none of which exist in the current schema, so this
        function returned 0 rows for 1166 submissions. See
        docs/infrastructure_changes_may30/I1_gather_context_fix.md.

    Args:
        problem_id: substring to match against `problem_id` or `filename`.
        verbose: if True, print every attached path and skipped row to stdout.

    Returns:
        List of existing absolute paths to prior result .lean files,
        ordered most-recent-first. Empty on any DB/IO error or when no
        prior artifacts exist.
    """
    import sqlite3

    tracking_db = MATH_DIR / "submissions" / "tracking.db"
    if not tracking_db.exists():
        if verbose:
            print(f"   [gather_context] tracking.db not found at {tracking_db}")
        return []

    try:
        conn = sqlite3.connect(str(tracking_db))
        try:
            # Verify the submissions table has expected columns before querying
            cursor = conn.execute("PRAGMA table_info(submissions)")
            columns = {row[1] for row in cursor.fetchall()}
            required = {'problem_id', 'filename', 'output_file', 'status', 'submitted_at'}
            if not required.issubset(columns):
                if verbose:
                    missing = required - columns
                    print(f"   [gather_context] schema missing columns: {sorted(missing)}")
                conn.close()
                return []
            has_verified = 'verified' in columns

            # Future-proof query: gate primarily on artifact presence, not status.
            # We exclude rows whose audit explicitly marked them invalid
            # (verified=0); NULL verified is allowed (pending audit, but the
            # artifact may still be useful as context). We also exclude
            # compile_failed because by definition there is no useful Lean
            # artifact to attach — output_file would be NULL anyway, but we
            # belt-and-suspenders it.
            verified_clause = " AND (verified IS NULL OR verified != 0)" if has_verified else ""
            sql = (
                "SELECT id, status, output_file, submitted_at, verified "
                "FROM submissions "
                "WHERE (problem_id LIKE ? OR filename LIKE ?) "
                "  AND output_file IS NOT NULL "
                "  AND output_file != '' "
                "  AND status != 'compile_failed'"
                f"{verified_clause}"
                " ORDER BY submitted_at DESC"
            )
            cursor = conn.execute(sql, (f'%{problem_id}%', f'%{problem_id}%'))
            rows = cursor.fetchall()

            # Safety check: if 0 rows but the problem has *any* submissions, warn.
            # This is the canary that catches future schema drift like the
            # pre-2026-05-30 bug.
            if not rows:
                anycur = conn.execute(
                    "SELECT COUNT(*) FROM submissions "
                    "WHERE problem_id LIKE ? OR filename LIKE ?",
                    (f'%{problem_id}%', f'%{problem_id}%'),
                )
                total = anycur.fetchone()[0]
                if total > 0 and verbose:
                    print(
                        f"   [gather_context] WARN: 0 prior artifacts for "
                        f"'{problem_id}' but {total} prior submissions exist "
                        f"(all compile_failed or output_file=NULL?)"
                    )
                elif total > 0:
                    # Visible warning even without --verbose-context: this is
                    # the smoking-gun pattern from the May-30 audit.
                    print(
                        f"   ⚠️  [gather_context] 0 artifacts attached for "
                        f"'{problem_id}' despite {total} prior submission(s). "
                        f"Re-run with --verbose-context to investigate."
                    )
        finally:
            conn.close()
    except (sqlite3.Error, OSError) as e:
        if verbose:
            print(f"   [gather_context] DB error: {e}")
        return []

    if not rows:
        return []

    context_paths = []
    skipped_missing = 0
    for (row_id, status, filepath, submitted_at, verified) in rows:
        p = Path(filepath)
        if not p.is_absolute():
            p = MATH_DIR / p
        if p.exists():
            context_paths.append(p)
            if verbose:
                print(
                    f"   [gather_context] +attach id={row_id} status={status} "
                    f"verified={verified} submitted_at={submitted_at} path={p}"
                )
        else:
            skipped_missing += 1
            if verbose:
                print(
                    f"   [gather_context] -skip  id={row_id} status={status} "
                    f"path missing on disk: {p}"
                )

    if skipped_missing and not verbose:
        print(
            f"   ⚠️  [gather_context] {skipped_missing} prior result file(s) "
            f"referenced in DB but missing on disk"
        )

    return context_paths


def _record_closure_axis(uuid: str, filename: str, closure_axis: dict) -> None:
    """Upsert submissions.closure_axis_json keyed by uuid.

    - If a row with this uuid exists: UPDATE closure_axis_json only.
    - If not: INSERT a minimal row with (uuid, filename, status='submitted',
      closure_axis_json). Subsequent /fetch updates fill in audit fields.

    Silently no-ops if the closure_axis_json column is missing (pre-migration DB).
    """
    import sqlite3

    tracking_db = MATH_DIR / "submissions" / "tracking.db"
    if not tracking_db.exists():
        return

    payload = json.dumps(closure_axis, separators=(",", ":"), sort_keys=True)

    conn = sqlite3.connect(str(tracking_db))
    try:
        cols = {row[1] for row in conn.execute("PRAGMA table_info(submissions)")}
        if "closure_axis_json" not in cols:
            return  # migration not applied; nothing to write

        row = conn.execute(
            "SELECT id FROM submissions WHERE uuid = ?", (uuid,)
        ).fetchone()
        if row is not None:
            conn.execute(
                "UPDATE submissions SET closure_axis_json = ? WHERE uuid = ?",
                (payload, uuid),
            )
        else:
            conn.execute(
                "INSERT INTO submissions (uuid, filename, status, submitted_at, closure_axis_json) "
                "VALUES (?, ?, 'submitted', datetime('now'), ?)",
                (uuid, filename, payload),
            )
        conn.commit()
    finally:
        conn.close()


def _record_lane_metadata(
    uuid: str,
    filename: str,
    lane: str,
    informal_mode_used: bool,
    paired_llm: str | None,
    fusion_json: dict | None = None,
    problem_id: str | None = None,
) -> None:
    """Upsert lane / informal_mode_used / paired_llm / fusion_json keyed by uuid.

    Added 2026-05-30 by I2 alongside `migrate_add_lane_columns_may30.py`.

    - If a row with this uuid exists: UPDATE the four lane-axis columns.
    - If not: INSERT a minimal row carrying the lane metadata.

    G4 fix (2026-06-10): also persists problem_id on the row when provided.
    Row 1345 (method1:erdos_100_piepmeyer) landed with problem_id=NULL because
    this insert omitted it, stranding the fetch-time gauntlet at
    "structural-only, never advance" (no source_conjecture/problem_id).

    Silently no-ops if any of the new columns are missing (pre-migration DB).
    """
    import sqlite3

    tracking_db = MATH_DIR / "submissions" / "tracking.db"
    if not tracking_db.exists():
        return

    fusion_payload = (
        json.dumps(fusion_json, separators=(",", ":"), sort_keys=True)
        if fusion_json is not None else None
    )
    informal_int = 1 if informal_mode_used else 0
    paired = paired_llm if paired_llm else "none"

    conn = sqlite3.connect(str(tracking_db))
    try:
        cols = {row[1] for row in conn.execute("PRAGMA table_info(submissions)")}
        required = {"lane", "informal_mode_used", "paired_llm", "fusion_json"}
        if not required.issubset(cols):
            return  # migration not applied; nothing to write

        row = conn.execute(
            "SELECT id FROM submissions WHERE uuid = ?", (uuid,)
        ).fetchone()
        if row is not None:
            conn.execute(
                "UPDATE submissions SET lane = ?, informal_mode_used = ?, "
                "paired_llm = ?, fusion_json = ?, "
                "problem_id = COALESCE(NULLIF(?, ''), problem_id) "
                "WHERE uuid = ?",
                (lane, informal_int, paired, fusion_payload,
                 (problem_id or "").strip(), uuid),
            )
        else:
            conn.execute(
                "INSERT INTO submissions "
                "(uuid, filename, status, submitted_at, lane, informal_mode_used, "
                " paired_llm, fusion_json, problem_id) "
                "VALUES (?, ?, 'submitted', datetime('now'), ?, ?, ?, ?, ?)",
                (uuid, filename, lane, informal_int, paired, fusion_payload,
                 (problem_id or "").strip() or None),
            )
        conn.commit()
    finally:
        conn.close()


def decide_lane(
    input_file: Path,
    fusion_lane_explicit: bool = False,
    informal_mode_explicit: bool = False,
    bare_only: bool = False,
) -> dict:
    """Decide which Aristotle lane to use for a submission.

    Auto-routing logic (U1, 2026-05-30):

      1. If `bare_only=True` (explicit --bare-only flag) → force BARE.
         Logged as BARE_OVERRIDE if a .fusion.json was present.
      2. If `fusion_lane_explicit=True` (explicit --fusion-lane flag) → FUSION
         (preserves legacy explicit override semantics).
      3. If `informal_mode_explicit=True` (explicit --informal-mode flag) →
         INFORMAL (legacy explicit override).
      4. Otherwise, check for companions adjacent to the sketch:
           - <stem>.fusion.json present → FUSION (auto-detected). Routes to
             Aristotle subsystem #2 (lemma-based informal reasoner) via the
             I9 informal-mode wiring downstream.
           - <stem>.closure.json present with CM=structural_finite_reduction →
             BARE + recommendation banner (closure-only is conservative; we
             don't auto-promote to informal without a strategy outline).
           - Anything else → BARE (current historical default).

    The motivation: empirical evidence (I9 smoke test, UUID 8d500201 on
    Euclid, May 30 2026) confirmed that BARE-prompt submissions route to
    Aristotle's MCGS-only subsystem, while informal-shape prompts route to
    the lemma-based reasoner that produced all 4 known Erdős wins (E124,
    E728, E1026, E481). Making FUSION the default when a companion exists
    is the W8 lever for routing novel structural problems to subsystem #2.

    Reference:
      docs/infrastructure_changes_may30/I9_informal_mode.md
      docs/infrastructure_changes_may30/U1_auto_routing.md (this change)

    Args:
        input_file: the .txt sketch path.
        fusion_lane_explicit: True if --fusion-lane was explicitly passed.
        informal_mode_explicit: True if --informal-mode was explicitly passed.
        bare_only: True if --bare-only was explicitly passed.

    Returns:
        dict with:
          "lane": one of {"fusion", "informal", "bare"}
          "auto_detected": bool — True iff companion file drove the choice
          "fusion_lane": bool — flag value to forward to safe_submit
          "informal_mode": bool — flag value to forward to safe_submit
          "reason": str — human-readable explanation for the banner
          "override": str | None — "BARE_OVERRIDE" if --bare-only suppressed
              an auto-detected FUSION companion; None otherwise.
          "closure_recommend": bool — True iff a .closure.json with
              CM=structural_finite_reduction was found and we chose BARE.
    """
    fusion_companion = _companion_fusion_path(input_file)
    closure_companion = _companion_closure_path(input_file)
    fusion_present = fusion_companion.exists()
    closure_present = closure_companion.exists()

    # 1. --bare-only forces BARE regardless of companions.
    if bare_only:
        if fusion_present:
            log_transaction("BARE_OVERRIDE", {
                "input_file": str(input_file),
                "fusion_companion": str(fusion_companion),
                "reason": "--bare-only flag suppressed auto-detected FUSION lane",
            })
            return {
                "lane": "bare",
                "auto_detected": False,
                "fusion_lane": False,
                "informal_mode": False,
                "reason": (
                    "BARE (forced by --bare-only; auto-detected "
                    f"{fusion_companion.name} suppressed)"
                ),
                "override": "BARE_OVERRIDE",
                "closure_recommend": False,
            }
        return {
            "lane": "bare",
            "auto_detected": False,
            "fusion_lane": False,
            "informal_mode": False,
            "reason": "BARE (forced by --bare-only)",
            "override": None,
            "closure_recommend": False,
        }

    # 2. Explicit --fusion-lane wins (legacy semantics).
    if fusion_lane_explicit:
        return {
            "lane": "fusion",
            "auto_detected": False,
            "fusion_lane": True,
            "informal_mode": informal_mode_explicit,
            "reason": "FUSION (explicit --fusion-lane flag)",
            "override": None,
            "closure_recommend": False,
        }

    # 3. Explicit --informal-mode wins (legacy semantics).
    if informal_mode_explicit:
        return {
            "lane": "informal",
            "auto_detected": False,
            "fusion_lane": False,
            "informal_mode": True,
            "reason": "INFORMAL (explicit --informal-mode flag)",
            "override": None,
            "closure_recommend": False,
        }

    # 4. Auto-detection by companion presence.
    if fusion_present:
        return {
            "lane": "fusion",
            "auto_detected": True,
            "fusion_lane": True,
            "informal_mode": False,
            "reason": (
                f"FUSION (auto-detected via {fusion_companion.name} "
                "companion). Override with --bare-only."
            ),
            "override": None,
            "closure_recommend": False,
        }

    if closure_present:
        # Closure-only is conservative — recommend but don't auto-promote.
        # Read the closure JSON to check CM; if CM=structural_finite_reduction,
        # surface a recommendation that the user *consider* authoring a
        # .fusion.json companion to engage the informal reasoner.
        cm_value = None
        try:
            text = closure_companion.read_text()
            axis = json.loads(text)
            if isinstance(axis, dict):
                cm_value = axis.get("CM")
        except (OSError, json.JSONDecodeError):
            cm_value = None

        closure_recommend = (cm_value == "structural_finite_reduction")
        return {
            "lane": "bare",
            "auto_detected": True,
            "fusion_lane": False,
            "informal_mode": False,
            "reason": (
                f"BARE (closure-only companion {closure_companion.name} "
                f"present; CM={cm_value or 'unknown'})"
            ),
            "override": None,
            "closure_recommend": closure_recommend,
        }

    # 5. No companion → BARE (historical default, fine for long-tail
    #    Tao snipes and mechanical extensions).
    return {
        "lane": "bare",
        "auto_detected": False,
        "fusion_lane": False,
        "informal_mode": False,
        "reason": "BARE (no companion file detected)",
        "override": None,
        "closure_recommend": False,
    }


async def safe_submit(
    input_file: Path,
    project_id_file: Path,
    description: str,
    force: bool = False,
    context_files: list[Path] | None = None,
    batch: bool = False,
    rubric_points: bool = False,
    verbose_context: bool = False,
    fusion_lane: bool = False,
    informal_mode: bool = False,
    paired_llm: str | None = None,
    force_literature_stale: bool = False,
    literature_ack: str | None = None,
    bare_only: bool = False,
    problem_id: str | None = None,
) -> str:
    """
    Safely submit to Aristotle with multiple safety checks.

    Args:
        input_file: Path to input file (.txt sketch)
        project_id_file: Where to save the project ID
        description: Human-readable description for logging
        force: Skip safety checks (use with caution!)
        problem_id: Canonical problem id for the submissions row (G4 fix,
            2026-06-10). Orchestrator pipelines (method1_loop) pass this
            explicitly; when absent we fall back to extract_problem_id() and
            then the fusion companion's problem_id. Without it the fetch-time
            verification gauntlet cannot run G2/G3 and the row is stranded
            "structural-only, never advance" (DB row 1345).
        context_files: Optional list of additional context files (.lean, .md, .txt, .tex)
        rubric_points: If True, allow submission even when the closure-axis
            companion classifies the sketch as real_closure_candidate=false.
            See docs/closure_axis_companion_spec.md.
        verbose_context: If True, gather_context() prints per-row attach/skip
            diagnostics. Use when investigating whether prior artifacts are
            being picked up correctly.
        fusion_lane: If True, this submission is on the research-fusion lane.
            Sets DB.lane='fusion'. See I2 schema spec (May 30 2026).
            EXPLICIT override of auto-routing — used when caller already knows
            the lane (e.g. orchestrator pipelines).
        informal_mode: If True, Aristotle's informal reasoner was invoked.
            Sets DB.lane='informal' and DB.informal_mode_used=1.
        paired_llm: Name of the strategy LLM that produced the sketch
            ('gpt-5.2-pro', 'codex', 'none', etc.). Stored on DB.paired_llm.
            Defaults to 'none' when not provided.
        bare_only: If True (explicit --bare-only), force BARE lane even if
            a .fusion.json companion is present. Logs BARE_OVERRIDE.
            See decide_lane() and U1_auto_routing.md.

    Returns:
        Project ID string

    Raises:
        SubmissionError: If submission should be aborted
    """

    # AUTO-ROUTING DECISION (U1, 2026-05-30). Runs before any gate so the
    # chosen lane is printed up front and downstream gates (fusion-companion
    # gate, informal-mode routing) trigger on the resolved flags. Auto-routing
    # is a no-op when --force is set: the orchestrator pipeline owns its own
    # lane decisions.
    if not force:
        lane_decision = decide_lane(
            input_file,
            fusion_lane_explicit=fusion_lane,
            informal_mode_explicit=informal_mode,
            bare_only=bare_only,
        )
        # Visible banner — every submission now declares its lane up front.
        print(f"🚦 Lane: {lane_decision['reason']}")
        if lane_decision.get("closure_recommend"):
            print(
                "   💡 Recommendation: this problem has a structural_finite_reduction "
                "classification.\n"
                "      Consider authoring a .fusion.json companion (with "
                "informal_proof_outline)\n"
                "      to engage Aristotle's lemma-based reasoner (subsystem #2). "
                "Closure-only\n"
                "      auto-routes to BARE; the recommendation does NOT promote the lane."
            )
        if lane_decision.get("override"):
            print(f"   ⚠️  {lane_decision['override']} logged for audit.")
        print()
        # Forward resolved flags to the rest of safe_submit().
        fusion_lane = lane_decision["fusion_lane"]
        informal_mode = lane_decision["informal_mode"]

    # Compute task hash for deduplication
    task_hash = compute_task_hash(input_file)

    print("🔒 SAFE SUBMISSION PROTOCOL")
    print("=" * 70)
    print(f"Task: {description}")
    print(f"Input: {input_file.name}")
    print(f"Hash: {task_hash}")
    print()

    # GAP-TARGETING GATE (runs before all other checks)
    if force:
        # --force bypasses gap-targeting gate (for informal proof pipeline)
        content = input_file.read_text()
        lines = content.splitlines()
        non_blank = [l for l in lines if l.strip() and not l.strip().startswith('---')]
        gap_statement = ""
        for line in lines:
            stripped = line.strip().lstrip('#').lstrip('-').strip()
            if stripped:
                gap_statement = stripped[:200]
                break
        gap_info = {
            "pass": True,
            "submission_type": "informal_proof",
            "gap_statement": gap_statement,
            "line_count": len(non_blank),
        }
        print("   ⚠️  Gap-targeting gate BYPASSED (--force)")
    else:
        gap_info = check_gap_targeting(input_file)
    print(f"   Gap: {gap_info['gap_statement'][:60]}")
    print(f"   Type: {gap_info['submission_type']}")
    print(f"   Lines: {gap_info['line_count']}")
    # S7 (2026-05-30): F-mode warnings — non-blocking advisory output.
    # F1-no-range was already escalated to a hard reject upstream; what
    # surfaces here are F3/F4/F10 advisories.
    for code, msg in gap_info.get("f_mode_warnings", []):
        if code == "F1":
            continue  # already a hard reject when no range present
        print(f"   ⚠️  {code} WARNING: {msg.splitlines()[0]}")
        log_transaction(f"{code}_WARNING", {
            "input_file": str(input_file),
            "message": msg,
        })
    print()

    # LITERATURE FRESHNESS GATE (May 30 2026): runs after gap-targeting and
    # before the closure-axis check.  Calls scripts/literature_check.py and
    # rejects submissions whose problem is already closed in the wiki / by
    # erdosproblems.com.  See docs/infrastructure_changes_may30/I4_literature_check.md.
    # --force preserves the legacy informal-proof bypass.
    if force:
        lit_info = {"status": "UNKNOWN", "problem_id": None, "citations": [],
                    "blocked": False, "reason": "bypassed via --force"}
        print("📚 Literature freshness gate BYPASSED (--force)")
    else:
        print("📚 Literature freshness check...")
        lit_info = check_literature_freshness(
            input_file,
            force_stale=force_literature_stale,
            literature_ack=literature_ack,
        )
        if lit_info["blocked"]:
            log_transaction("LITERATURE_GATE_REJECT", {
                "problem_id": lit_info.get("problem_id"),
                "status": lit_info.get("status"),
                "citations": lit_info.get("citations", []),
                "input_file": str(input_file),
            })
            raise LiteratureStaleError(
                f"Literature gate REJECTED submission for "
                f"'{lit_info.get('problem_id')}' — status={lit_info.get('status')}. "
                f"{lit_info.get('reason')}"
            )
    print()

    # FUSION-LANE GATE (May 30 2026, I8): runs only when --fusion-lane is passed.
    # Reads the companion .fusion.json, validates schema (9 required fields, ≤80
    # non-blank lines), and runs the airlock to verify no strategy term has
    # leaked into the bare .txt. NO OVERRIDE (other than --force).
    # See docs/fusion_axis_companion_spec.md and
    # docs/infrastructure_changes_may30/I8_fusion_lane.md.
    fusion_info: dict | None = None
    if fusion_lane:
        if force:
            print("   ⚠️  Fusion-companion gate BYPASSED (--force)")
        else:
            print("🔬 Fusion-companion gate (--fusion-lane)...")
            fusion_info = check_fusion_companion(input_file)
        print()

    # CLOSURE-AXIS GATE (May 30 2026): runs after gap-targeting, before queue checks.
    # See docs/closure_axis_companion_spec.md for the gate's decision table.
    # --force preserves the legacy informal-proof bypass for the orchestrator pipeline.
    if force:
        closure_info = {"present": False, "axis": None, "real_closure_candidate": None, "override": False}
        print("   ⚠️  Closure-axis gate BYPASSED (--force)")
    else:
        closure_info = check_closure_axis(input_file, rubric_points=rubric_points)
    print()

    # Auto-context: gather prior results.
    # G4 fix (2026-06-10): an explicitly-passed problem_id wins; the filename/
    # content heuristic is the fallback.
    problem_id = (problem_id or "").strip() or extract_problem_id(input_file)
    if problem_id:
        auto_context = gather_context(problem_id, verbose=verbose_context)
        if auto_context:
            if context_files is None:
                context_files = []
            # Merge auto-context with explicit context (no duplicates)
            existing = set(str(p) for p in context_files)
            for ctx in auto_context:
                if str(ctx) not in existing:
                    context_files.append(ctx)
            print(f"   Auto-context: {len(auto_context)} prior result(s) for '{problem_id}'")
            if verbose_context:
                for ctx in auto_context:
                    print(f"      - {ctx}")
        elif verbose_context:
            print(f"   Auto-context: 0 prior result(s) for '{problem_id}'")

    # SAFETY CHECK 1: Acquire lockfile
    if not force:
        print("1️⃣  Checking lockfile...")
        if not acquire_lock():
            raise SubmissionError("Another submission is in progress (lockfile exists)")
        print("   ✅ Lock acquired")

    try:
        # SAFETY CHECK 2: Check for duplicate (local log only, no API call)
        if not force:
            print("2️⃣  Checking for recent duplicates...")
            if check_duplicate(task_hash, window_minutes=10):
                raise SubmissionError(
                    "Task already submitted in last 10 minutes! "
                    "Found matching hash in transaction log."
                )
            print("   ✅ No recent duplicates found")

        # SAFETY CHECK 3: Check rate limit + queue capacity (single API call)
        if not force and not batch:
            print("3️⃣  Checking rate limit and queue capacity...")
            queue = await check_rate_limit_and_capacity(window_minutes=10)
            if not queue['has_capacity']:
                raise SubmissionError(
                    f"Queue is full ({queue['in_progress']}/{queue['max_concurrent']} slots used). "
                    f"Wait for a slot to free up, or raise the cap via "
                    f"ARISTOTLE_MAX_CONCURRENT env var (default {DEFAULT_MAX_CONCURRENT})."
                )
            print(f"   ✅ Queue has capacity ({queue['slots_available']}/{queue['max_concurrent']} slots available)")
        elif batch:
            print("3️⃣  Batch mode: skipping interactive rate-limit check")

        # SAFETY CHECK 4: Confirm file exists and is readable
        print("4️⃣  Validating input file...")
        if not input_file.exists():
            raise SubmissionError(f"Input file does not exist: {input_file}")
        file_size = input_file.stat().st_size
        if file_size == 0:
            raise SubmissionError("Input file is empty")
        if file_size > 100_000_000:  # 100MB limit
            raise SubmissionError(f"Input file too large: {file_size:,} bytes")
        print(f"   ✅ File valid ({file_size:,} bytes)")

        # ALL CHECKS PASSED - SUBMIT
        print()
        print("🚀 All safety checks passed! Submitting to Aristotle...")
        print()

        set_api_key(ARISTOTLE_API_KEY)

        # Log pre-submission
        log_transaction("pre_submit", {
            "task_hash": task_hash,
            "description": description,
            "input_file": str(input_file),
            "file_size": file_size
        })

        # Read sketch content as prompt
        prompt_text = input_file.read_text()

        # INFORMAL-MODE ROUTING (I9, 2026-05-30).
        # When --fusion-lane is set AND a sibling <sketch>.fusion.json exists
        # AND that JSON carries a non-empty strategy_outline (or alias
        # informal_proof_outline), route through aristotle_informal.py so
        # Aristotle's informal reasoner subsystem is invoked rather than the
        # MCGS formalize-only path. This is the W8 lever: we have historically
        # NEVER used the informal reasoner. See
        # docs/infrastructure_changes_may30/I9_informal_mode.md.
        fusion_companion_data: dict | None = None
        if fusion_lane or informal_mode:
            companion_path = input_file.with_suffix('.fusion.json')
            if not companion_path.exists():
                # Try alternate naming: <stem>.fusion.json adjacent to the
                # sketch (e.g. erdos124_fusion.txt -> erdos124_fusion.fusion.json)
                alt = input_file.parent / (input_file.stem + ".fusion.json")
                if alt.exists():
                    companion_path = alt
            if companion_path.exists():
                try:
                    # Import locally so we never hard-depend on the adapter at
                    # module-load time. The adapter is intentionally minimal
                    # and safe to import.
                    import importlib.util
                    spec = importlib.util.spec_from_file_location(
                        "aristotle_informal",
                        MATH_DIR / "scripts" / "aristotle_informal.py",
                    )
                    if spec is not None and spec.loader is not None:
                        mod = importlib.util.module_from_spec(spec)
                        spec.loader.exec_module(mod)  # type: ignore
                        fusion_companion_data = mod.load_fusion_companion(companion_path)
                        # Only rewrite the prompt if the companion actually
                        # carries an informal proof outline. Otherwise we keep
                        # the BARE prompt and let the user know we did NOT
                        # invoke informal mode (this preserves backward
                        # compatibility with --fusion-lane submissions that
                        # only carry analogy/technique fields).
                        has_outline = bool(
                            mod._first_present(fusion_companion_data,
                                               mod.STRATEGY_OUTLINE_FIELDS)
                        )
                        if has_outline:
                            informal_prompt = mod.build_informal_prompt(
                                sketch_text=prompt_text,
                                fusion=fusion_companion_data,
                                paired_llm=paired_llm,
                            )
                            print(f"   🧠 Informal-mode routing: companion "
                                  f"{companion_path.name} -> informal prompt "
                                  f"({len(informal_prompt)} chars, was "
                                  f"{len(prompt_text)} chars BARE)")
                            prompt_text = informal_prompt
                            informal_mode = True  # ensure DB.lane='informal'
                        else:
                            print(f"   ℹ️  Companion {companion_path.name} has "
                                  f"no strategy_outline; keeping BARE prompt.")
                except Exception as e:
                    # Never let an informal-routing failure block the
                    # submission — fall back to BARE.
                    print(f"   ⚠️  Informal-mode routing failed ({e}); "
                          f"falling back to BARE prompt.")
                    log_transaction("INFORMAL_ROUTING_FAILED", {
                        "input_file": str(input_file),
                        "companion": str(companion_path),
                        "error": str(e),
                    })

        # If context files exist, bundle them into a tar.gz
        tar_path = None
        if context_files:
            import tarfile
            import tempfile
            tar_path = Path(tempfile.mktemp(suffix='.tar.gz'))
            with tarfile.open(tar_path, 'w:gz') as tar:
                for ctx in context_files:
                    tar.add(ctx, arcname=ctx.name)
            print(f"   📎 {len(context_files)} context file(s) bundled")

        # Submit via new Project.create API
        try:
            project = await Project.create(
                prompt=prompt_text,
                tar_file_path=tar_path,
            )
        finally:
            # Clean up temp tar
            if tar_path and tar_path.exists():
                tar_path.unlink()

        project_id = project.project_id

        # IMMEDIATELY save project ID (before anything else can fail)
        with open(project_id_file, 'w') as f:
            f.write(f"{project_id}\n")
            f.write(f"# Task: {description}\n")
            f.write(f"# Hash: {task_hash}\n")
            f.write(f"# Submitted: {datetime.now().isoformat()}\n")

        # Log successful submission
        log_transaction("submitted", {
            "project_id": project_id,
            "task_hash": task_hash,
            "description": description,
            "id_file": str(project_id_file),
            "closure_axis_present": closure_info.get("present"),
            "rubric_points_override": closure_info.get("override"),
        })

        # Persist closure_axis_json on the DB row keyed by uuid. Idempotent upsert:
        # if the row already exists (rare — usually inserted later by aristotle_fetch),
        # we update only closure_axis_json without touching status/audit fields.
        if closure_info.get("axis") is not None:
            try:
                _record_closure_axis(
                    uuid=project_id,
                    filename=description,
                    closure_axis=closure_info["axis"],
                )
            except Exception as e:
                # Never let a DB write failure block the submission record.
                print(f"   ⚠️  Failed to persist closure_axis_json to DB: {e}")
                log_transaction("CLOSURE_AXIS_DB_WRITE_FAILED", {
                    "project_id": project_id,
                    "error": str(e),
                })

        # Persist lane / informal_mode_used / paired_llm / fusion_json metadata
        # (I2 May 30 2026). Lane resolution precedence:
        #   1. informal_mode  -> 'informal'  (Aristotle informal reasoner invoked)
        #   2. fusion_lane    -> 'fusion'    (research-fusion lane)
        #   3. real_closure_candidate=True (from closure_info) -> 'closure'
        #   4. default        -> 'bare'      (bare-gap sketch, the historical default)
        if informal_mode:
            resolved_lane = "informal"
        elif fusion_lane:
            resolved_lane = "fusion"
        elif closure_info.get("real_closure_candidate") is True:
            resolved_lane = "closure"
        else:
            resolved_lane = "bare"

        try:
            _record_lane_metadata(
                uuid=project_id,
                filename=description,
                lane=resolved_lane,
                informal_mode_used=informal_mode,
                paired_llm=paired_llm,
                # I9 (2026-05-30): when informal-mode routing fired, persist
                # the actual companion JSON we used so the audit trail can
                # reconstruct exactly what was sent.
                fusion_json=fusion_companion_data,
                # G4 fix (2026-06-10): persist problem_id at insert so the
                # fetch-time gauntlet can adjudicate G2/G3 (row 1345 landed
                # NULL here and could never be promoted).
                problem_id=problem_id or (fusion_companion_data or {}).get("problem_id"),
            )
            print(f"   📊 Lane recorded: {resolved_lane}  paired_llm={paired_llm or 'none'}  "
                  f"informal_mode={'yes' if informal_mode else 'no'}")
        except Exception as e:
            print(f"   ⚠️  Failed to persist lane metadata to DB: {e}")
            log_transaction("LANE_METADATA_DB_WRITE_FAILED", {
                "project_id": project_id,
                "error": str(e),
            })

        print("✅ SUBMISSION SUCCESSFUL!")
        print(f"   Project ID: {project_id}")
        print(f"   ID saved to: {project_id_file.name}")
        print()

        return project_id

    finally:
        # Always release lock, even if submission failed
        if not force:
            release_lock()


async def submit_with_retry(
    input_file: Path,
    project_id_file: Path,
    description: str,
    max_retries: int = 3,
    retry_delay: int = 30,
    context_files: list[Path] | None = None,
    force: bool = False,
    batch: bool = False,
    rubric_points: bool = False,
    verbose_context: bool = False,
    fusion_lane: bool = False,
    informal_mode: bool = False,
    paired_llm: str | None = None,
    force_literature_stale: bool = False,
    literature_ack: str | None = None,
    bare_only: bool = False,
) -> str:
    """
    Submit with exponential backoff retry on transient failures.

    Does NOT retry on:
    - Duplicate submissions
    - Full queue
    - Invalid input files

    Only retries on:
    - Network errors
    - API timeouts
    """

    for attempt in range(max_retries):
        try:
            return await safe_submit(
                input_file, project_id_file, description,
                force=force, context_files=context_files,
                batch=batch, rubric_points=rubric_points,
                verbose_context=verbose_context,
                fusion_lane=fusion_lane,
                informal_mode=informal_mode,
                paired_llm=paired_llm,
                force_literature_stale=force_literature_stale,
                literature_ack=literature_ack,
                bare_only=bare_only,
            )

        except SubmissionError as e:
            # Don't retry on safety check failures
            print(f"❌ Submission aborted: {e}")
            raise

        except Exception as e:
            # Retry on other errors (network, API, etc.)
            if attempt < max_retries - 1:
                wait = retry_delay * (2 ** attempt)  # Exponential backoff
                print(f"⚠️  Attempt {attempt + 1} failed: {e}")
                print(f"   Retrying in {wait}s...")
                await asyncio.sleep(wait)
            else:
                print(f"❌ All {max_retries} attempts failed")
                raise


# CLI interface
if __name__ == "__main__":
    import sys
    import re as re_mod

    # Separate flags (--xyz) and flag-arguments (--context <file>) from positional args
    all_args = sys.argv[1:]
    positional = []
    flags = set()
    context_files = []
    paired_llm_arg: str | None = None
    literature_ack_arg: str | None = None
    i = 0
    while i < len(all_args):
        arg = all_args[i]
        if arg == '--context' and i + 1 < len(all_args):
            context_files.append(Path(all_args[i + 1]))
            i += 2
        elif arg == '--codex-context' and i + 1 < len(all_args):
            codex_problem_id = all_args[i + 1]
            best_path = MATH_DIR / "codex_proofs" / codex_problem_id / "best.lean"
            if best_path.exists():
                context_files.append(best_path.resolve())
                print(f"   Codex context: {best_path}")
            else:
                print(f"WARNING: No Codex best proof found for '{codex_problem_id}'")
            i += 2
        elif arg == '--paired-llm' and i + 1 < len(all_args):
            paired_llm_arg = all_args[i + 1]
            i += 2
        elif arg == '--literature-ack' and i + 1 < len(all_args):
            literature_ack_arg = all_args[i + 1]
            i += 2
        elif arg.startswith('--'):
            flags.add(arg)
            i += 1
        else:
            positional.append(arg)
            i += 1

    batch_mode = '--batch' in flags
    force = '--force' in flags
    rubric_points = '--rubric-points' in flags
    verbose_context = '--verbose-context' in flags
    fusion_lane = '--fusion-lane' in flags
    informal_mode = '--informal-mode' in flags
    force_literature_stale = '--force-literature-stale' in flags
    bare_only = '--bare-only' in flags

    if len(positional) < 1:
        print("Usage: python3 safe_aristotle_submit.py <input_file> [slot_number] [options]")
        print("       python3 safe_aristotle_submit.py --batch <file1> <file2> ... [options]")
        print()
        print("Auto-routing (U1, 2026-05-30):")
        print("  By default the submitter inspects companion files adjacent to the sketch:")
        print("    <stem>.fusion.json present  -> FUSION lane (engages Aristotle subsystem #2,")
        print("                                   the lemma-based informal reasoner).")
        print("    <stem>.closure.json present -> BARE lane + recommendation banner if")
        print("                                   CM=structural_finite_reduction.")
        print("    no companion                -> BARE lane (historical default; suits")
        print("                                   long-tail Tao snipes and mechanical extensions).")
        print("  The CHOSEN LANE is always printed as the first line of submission output.")
        print()
        print("Options:")
        print("  --force              Skip safety checks (also bypasses closure-axis gate and")
        print("                       auto-routing; caller owns lane decision).")
        print("  --context <file>     Add context file (can repeat)")
        print("  --codex-context <id> Auto-locate best Codex proof as context")
        print("  --batch              Submit multiple files (skips interactive prompts)")
        print("  --rubric-points      Permit submission when closure-axis classifies it")
        print("                       as real_closure_candidate=false (mechanical extension,")
        print("                       formalization-only port). Logged for audit.")
        print("                       See docs/closure_axis_companion_spec.md.")
        print("  --verbose-context    Print every prior-result file considered for auto-context")
        print("                       (which attached, which skipped, why). Use when prior")
        print("                       artifacts seem to be missing from a submission.")
        print("  --fusion-lane        EXPLICIT override: tag as research-fusion lane regardless")
        print("                       of companion detection (DB.lane='fusion').")
        print("                       Triggers check_fusion_companion gate: validates the")
        print("                       sibling <name>.fusion.json (9 required fields, ≤80 lines)")
        print("                       and runs the airlock — REJECTS if strategy from the JSON")
        print("                       leaks into the bare .txt. NO override (other than --force).")
        print("                       See docs/fusion_axis_companion_spec.md,")
        print("                       docs/infrastructure_changes_may30/I8_fusion_lane.md.")
        print("                       (Auto-routing already picks this lane whenever the")
        print("                       companion exists; --fusion-lane is for explicit pipelines.)")
        print("  --bare-only          EXPLICIT override: force BARE lane even if a .fusion.json")
        print("                       companion is present. Logs BARE_OVERRIDE for audit.")
        print("                       See docs/infrastructure_changes_may30/U1_auto_routing.md.")
        print("  --informal-mode      EXPLICIT override: tag as Aristotle informal-reasoner lane")
        print("                       (DB.lane='informal', DB.informal_mode_used=1). Auto-routing")
        print("                       picks this implicitly via FUSION when the companion has a")
        print("                       strategy_outline; --informal-mode is the legacy explicit flag.")
        print("  --paired-llm <name>  Record the strategy LLM that produced the sketch")
        print("                       (e.g. 'gpt-5.2-pro', 'codex'). Stored on DB.paired_llm.")
        print("  --literature-ack \"<note>\"")
        print("                       Acknowledge a literature-check WARN (AMBIGUOUS or")
        print("                       POSSIBLY_SOLVED).  Required to submit when the gate")
        print("                       finds partial AI work or a literature-search hit.")
        print("  --force-literature-stale")
        print("                       Submit anyway when the gate flags AI_CLOSED or")
        print("                       RECENTLY_SOLVED.  Logged for audit.  Use only when")
        print("                       you've manually re-verified the gap is still open.")
        print()
        print("Examples:")
        print("  # Single file (auto-detect slot AND lane):")
        print("  python3 safe_aristotle_submit.py submissions/sketches/erdos850.txt")
        print()
        print("  # Force BARE even though a .fusion.json sits next to the sketch:")
        print("  python3 safe_aristotle_submit.py --bare-only sketches/erdos850.txt")
        print()
        print("  # Batch submit:")
        print("  python3 safe_aristotle_submit.py --batch sketch1.txt sketch2.txt")
        sys.exit(1)

    def resolve_file(filepath_str: str) -> tuple[Path, Path, str]:
        """Resolve input file -> (input_path, id_file, description)."""
        input_path = Path(filepath_str)
        m = re_mod.match(r'slot(\d+)', input_path.stem)
        slot_num = m.group(1) if m else None
        if slot_num:
            id_path = input_path.parent / f"slot{slot_num}_ID.txt"
            desc = input_path.stem
        else:
            id_path = input_path.with_suffix('.ID.txt')
            desc = input_path.stem
        return input_path, id_path, desc

    if batch_mode:
        # Batch: all positional args are input files
        input_files = positional
        print(f"📦 BATCH MODE: {len(input_files)} file(s)")
        print()

        succeeded = 0
        failed = 0
        for filepath_str in input_files:
            input_file, id_file, description = resolve_file(filepath_str)
            print(f"{'─' * 70}")
            print(f"📁 Input: {input_file}")
            print(f"📋 ID file: {id_file}")
            print(f"📝 Description: {description}")
            print()

            try:
                project_id = asyncio.run(submit_with_retry(
                    input_file, id_file, description,
                    context_files=context_files or None,
                    force=force,
                    batch=True,
                    rubric_points=rubric_points,
                    verbose_context=verbose_context,
                    fusion_lane=fusion_lane,
                    informal_mode=informal_mode,
                    paired_llm=paired_llm_arg,
                    force_literature_stale=force_literature_stale,
                    literature_ack=literature_ack_arg,
                    bare_only=bare_only,
                ))
                print(f"✅ Success! Project ID: {project_id}")
                succeeded += 1
            except SubmissionError as e:
                print(f"❌ {e}")
                failed += 1
            except Exception as e:
                print(f"❌ Unexpected error: {e}")
                failed += 1
            print()

        print(f"{'═' * 70}")
        print(f"Batch complete: {succeeded} succeeded, {failed} failed")

    else:
        # Single file mode (original behavior)
        input_file = Path(positional[0])

        if len(positional) >= 2 and positional[1].isdigit():
            slot_num = positional[1]
        else:
            m = re_mod.match(r'slot(\d+)', input_file.stem)
            slot_num = m.group(1) if m else None

        if slot_num:
            id_file = input_file.parent / f"slot{slot_num}_ID.txt"
            description = input_file.stem
        elif len(positional) >= 3:
            id_file = Path(positional[1])
            description = positional[2]
        else:
            id_file = input_file.with_suffix('.ID.txt')
            description = input_file.stem

        print(f"📁 Input: {input_file}")
        print(f"📋 ID file: {id_file}")
        print(f"📝 Description: {description}")
        print()

        try:
            project_id = asyncio.run(submit_with_retry(
                input_file, id_file, description,
                context_files=context_files or None,
                force=force,
                batch=False,
                rubric_points=rubric_points,
                verbose_context=verbose_context,
                fusion_lane=fusion_lane,
                informal_mode=informal_mode,
                paired_llm=paired_llm_arg,
                force_literature_stale=force_literature_stale,
                literature_ack=literature_ack_arg,
                bare_only=bare_only,
            ))
            print(f"✅ Success! Project ID: {project_id}")
        except SubmissionError as e:
            print(f"❌ {e}")
            sys.exit(1)
        except Exception as e:
            print(f"❌ Unexpected error: {e}")
            import traceback
            traceback.print_exc()
            sys.exit(2)
