#!/usr/bin/env python3
"""
advance_dashboard.py — Method-1 throughput-governance surface (read-only).

The single observability surface over `submissions/tracking.db` for the
Method-1 / Recipe-B scale-up campaign. It answers the questions the plan
(`analysis/method1_scaleup_plan.md` §4–§5) says a campaign MUST be able to
answer, and it asserts the three self-enforcing invariants that keep the
gauntlet honest:

  1. ADVANCE-RATE  — per lane and per author (paired_llm / sketch model).
  2. COST-PER-ADVANCE — directional $/advance per lane and per author.
  3. FAITHFULNESS / LITERATURE REJECT BREAKDOWN — derived from the signals
     the gauntlet actually persists (status enum + closure_axis_json +
     contribution_statement heuristics). Honest about being a persisted-signal
     read, not a live re-run of G2/G3.
  4. MISLABELED-ADVANCE ALARM — any `compiled_advance` row that does NOT look
     like a genuine, gauntlet-passed advance (target_resolved=0,
     axiomatizes_prior_work=1, "does NOT resolve"-style contribution text,
     cost/mcs missing). The two historical rows (Brocard id1254,
     Feit-Thompson id1255) MUST light up here.

THREE SELF-ENFORCING INVARIANTS (assert these continuously):
  I1. target_resolved=1  ⟺  status == 'compiled_advance'  (the gauntlet G4 rule:
      promotion happens IFF G1∧G2∧G3 passed, and that promotion is the *only*
      writer of both target_resolved=1 and compiled_advance — so the two must
      agree on every row; either side without the other is a CRITICAL
      regression). Source of truth: verification_gauntlet G4 (lines 18-19).
  I2. cost_usd AND mathematical_content_score are non-NULL on 100% of
      compiled_* rows. Today: 0/937 and 7/937 — the completeness alarm.
  I3. The two existing compiled_advance rows are flagged for re-audit: under a
      fail-closed gauntlet G2 bound-injection check they WILL be downgraded
      (Brocard: n≤500 finite verification; Feit-Thompson: q≤1000 finite family).

SAFETY: READ-ONLY on `submissions`. Opens the DB in immutable mode (uri=ro)
by default; never writes, never migrates, never re-runs a gauntlet build, never
fires an Aristotle call. Pure SELECT + Python aggregation.

Usage:
    python3 scripts/advance_dashboard.py                 # full dashboard, real DB
    python3 scripts/advance_dashboard.py --json          # machine-readable
    python3 scripts/advance_dashboard.py --days 7        # window submissions
    python3 scripts/advance_dashboard.py --db /tmp/x.db  # alternate DB
    python3 scripts/advance_dashboard.py --invariants-only
    python3 scripts/advance_dashboard.py --self-test     # tiny synthetic DB

Exit code: 0 if all three invariants hold, 1 if any invariant is violated
(so the dashboard can gate a campaign in CI / a cron pre-check). On the real DB
today this exits 1 (I1 + I2 both violated) — that is the alarm working.
"""

import argparse
import json
import os
import sqlite3
import sys
from datetime import datetime, timezone
from pathlib import Path

# ── Paths ────────────────────────────────────────────────────────────────────
SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
DEFAULT_DB = REPO_ROOT / "submissions" / "tracking.db"

# ── Status enum (single source of truth = verification_gauntlet) ──────────────
# Import the canonical constants so the dashboard's invariant cannot drift from
# the gauntlet's G4 promotion rule. Fall back to literals if the module cannot
# be imported (the dashboard is read-only and must never crash on import).
sys.path.insert(0, str(SCRIPT_DIR))
try:
    import verification_gauntlet as _vg  # type: ignore

    ST_SUBMITTED = _vg.ST_SUBMITTED
    ST_COMPILE_FAILED = _vg.ST_COMPILE_FAILED
    ST_COMPILED_PARTIAL = _vg.ST_COMPILED_PARTIAL
    ST_COMPILED_NO_ADVANCE = _vg.ST_COMPILED_NO_ADVANCE
    ST_COMPILED_ADVANCE = _vg.ST_COMPILED_ADVANCE
    ST_DISPROVEN = _vg.ST_DISPROVEN
    _GAUNTLET_IMPORTED = True
except Exception:  # pragma: no cover - defensive; literals match CLAUDE.md enum
    ST_SUBMITTED = "submitted"
    ST_COMPILE_FAILED = "compile_failed"
    ST_COMPILED_PARTIAL = "compiled_partial"
    ST_COMPILED_NO_ADVANCE = "compiled_no_advance"
    ST_COMPILED_ADVANCE = "compiled_advance"
    ST_DISPROVEN = "disproven"
    _GAUNTLET_IMPORTED = False

COMPILED_STATUSES = (
    ST_COMPILE_FAILED,
    ST_COMPILED_PARTIAL,
    ST_COMPILED_NO_ADVANCE,
    ST_COMPILED_ADVANCE,
)

# Directional Aristotle $/hr (no SDK cost field exists; matches gauntlet §4).
ARISTOTLE_USD_PER_HOUR = float(os.environ.get("ARISTOTLE_USD_PER_HOUR", "0") or "0")

# Heuristic phrases that mark a "does NOT actually resolve the gap" contribution.
# Used ONLY for the mislabeled-advance alarm and the faithfulness reject signal;
# never to promote anything (dashboard is read-only).
_NON_RESOLUTION_MARKERS = (
    "does not resolve",
    "does not close",
    "not the full",
    "not full closure",
    "bounded extension",
    "finite verification",
    "native_decide",
    "small-n gap",
    "sub-claim",
    "subclaim",
    "partial result",
)


# ── DB access (READ-ONLY) ─────────────────────────────────────────────────────
def connect_ro(db_path):
    """Open the DB strictly read-only via SQLite immutable URI.

    Falls back to a normal connection only if the file URI cannot be used
    (e.g. an in-memory test DB handle passed directly). Never issues writes.
    """
    p = Path(db_path)
    if not p.exists():
        raise FileNotFoundError(f"DB not found: {db_path}")
    uri = f"file:{p}?mode=ro"
    conn = sqlite3.connect(uri, uri=True)
    conn.row_factory = sqlite3.Row
    return conn


def _table_columns(conn, table):
    try:
        return {r[1] for r in conn.execute(f"PRAGMA table_info({table})").fetchall()}
    except sqlite3.Error:
        return set()


def _safe_float(v):
    try:
        return float(v) if v is not None else None
    except (TypeError, ValueError):
        return None


# ── Cost model ────────────────────────────────────────────────────────────────
def _row_cost(row, usd_per_hour):
    """Best-available cost for one row, in USD.

    Priority:
      1. Persisted cost_usd (authored token cost or prior estimate) — authoritative.
      2. Directional Aristotle wall-clock estimate (completed_at - created_at) *
         usd_per_hour, ONLY when usd_per_hour > 0. Plan §4 labels this directional.
    Returns (cost: float|None, source: 'persisted'|'wallclock_est'|None).
    """
    persisted = _safe_float(row["cost_usd"]) if "cost_usd" in row.keys() else None
    if persisted is not None:
        return persisted, "persisted"
    if usd_per_hour and usd_per_hour > 0:
        secs = _wallclock_seconds(row)
        if secs is not None and secs > 0:
            return (secs / 3600.0) * usd_per_hour, "wallclock_est"
    return None, None


def _parse_ts(s):
    if not s:
        return None
    s = str(s).strip()
    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d %H:%M:%S.%f",
                "%Y-%m-%dT%H:%M:%S.%f", "%Y-%m-%d"):
        try:
            return datetime.strptime(s.split("+")[0].strip(), fmt)
        except ValueError:
            continue
    return None


def _wallclock_seconds(row):
    keys = row.keys()
    start = _parse_ts(row["created_at"]) if "created_at" in keys else None
    end = _parse_ts(row["completed_at"]) if "completed_at" in keys else None
    if start and end and end >= start:
        return (end - start).total_seconds()
    return None


# ── Core fetch ────────────────────────────────────────────────────────────────
def fetch_rows(conn, days=None):
    """Return all submission rows (optionally windowed to last N days)."""
    cols = _table_columns(conn, "submissions")
    # Only select columns that exist (defensive against schema drift / test DBs).
    wanted = [
        "id", "uuid", "filename", "problem_id", "status", "status_legacy",
        "lane", "informal_mode_used", "paired_llm", "sketch_model_primary",
        "sketch_model_secondary", "target_resolved", "axiomatizes_prior_work",
        "axiom_count", "cost_usd", "mathematical_content_score",
        "contribution_statement", "closure_axis_json", "fusion_json",
        "created_at", "submitted_at", "completed_at",
    ]
    sel = [c for c in wanted if c in cols]
    sql = f"SELECT {', '.join(sel)} FROM submissions"
    params = []
    if days is not None:
        # Window on submitted_at when present, else created_at.
        ts_col = "submitted_at" if "submitted_at" in cols else "created_at"
        sql += f" WHERE COALESCE({ts_col}, created_at) >= datetime('now', ?)"
        params.append(f"-{int(days)} days")
    return [dict(r) for r in conn.execute(sql, params).fetchall()]


# ── Classifiers ───────────────────────────────────────────────────────────────
def _author_label(row):
    """The author dimension. paired_llm is the rich strategy-LLM field; fall back
    to sketch_model_primary; else '(unattributed)'."""
    pl = (row.get("paired_llm") or "").strip()
    if pl and pl.lower() != "none":
        return pl
    sm = (row.get("sketch_model_primary") or "").strip()
    if sm:
        return sm
    return "(unattributed)"


def _lane_label(row):
    lane = (row.get("lane") or "").strip()
    return lane if lane else "(none)"


def _is_compiled(row):
    return row.get("status") in COMPILED_STATUSES


def _is_genuine_advance(row):
    """A `compiled_advance` row that ALSO looks like a real, gauntlet-passed
    advance. This is the read-only proxy for "G4 actually promoted it":
      - status == compiled_advance
      - target_resolved == 1   (G4's co-written flag)
      - axiomatizes_prior_work != 1 (didn't cheat by axiomatizing)
      - contribution_statement does not contain a non-resolution marker
    Anything failing these while still labeled compiled_advance is MISLABELED.
    """
    if row.get("status") != ST_COMPILED_ADVANCE:
        return False
    if int(row.get("target_resolved") or 0) != 1:
        return False
    if int(row.get("axiomatizes_prior_work") or 0) == 1:
        return False
    contrib = (row.get("contribution_statement") or "").lower()
    if any(m in contrib for m in _NON_RESOLUTION_MARKERS):
        return False
    return True


def _literature_signal(row):
    """Persisted literature/closure-axis signal for the reject breakdown.

    Read-only derivation (NOT a live biblio_gate call):
      - disproven                                  -> 'disproven' (counterexample)
      - closure_axis_json.real_closure_candidate False -> 'held_not_real_closure'
      - closure_axis_json present & True               -> 'closure_claimed'
      - else                                           -> 'unscreened'
    """
    if row.get("status") == ST_DISPROVEN:
        return "disproven"
    caj = row.get("closure_axis_json")
    if caj:
        try:
            obj = json.loads(caj)
            rcc = obj.get("real_closure_candidate")
            if rcc is False:
                return "held_not_real_closure"
            if rcc is True:
                return "closure_claimed"
        except (json.JSONDecodeError, AttributeError, TypeError):
            return "closure_axis_unparseable"
    return "unscreened"


def _faithfulness_signal(row):
    """Persisted faithfulness signal for the reject breakdown.

    Read-only derivation (NOT a live statement_diff call):
      - compile_failed                       -> 'g1_build_reject'  (never reached G2)
      - axiomatizes_prior_work == 1          -> 'axiomatized_prior_work'
      - non-resolution markers in contribution-> 'bounded_or_weaker' (the Rivin trap)
      - compiled_partial (residual sorry)    -> 'residual_sorry'
      - genuine advance                      -> 'faithful_advance'
      - else (compiled_no_advance, clean)    -> 'clean_no_advance'
    """
    status = row.get("status")
    if status == ST_COMPILE_FAILED:
        return "g1_build_reject"
    if int(row.get("axiomatizes_prior_work") or 0) == 1:
        return "axiomatized_prior_work"
    contrib = (row.get("contribution_statement") or "").lower()
    if any(m in contrib for m in _NON_RESOLUTION_MARKERS):
        return "bounded_or_weaker"
    if status == ST_COMPILED_PARTIAL:
        return "residual_sorry"
    if _is_genuine_advance(row):
        return "faithful_advance"
    return "clean_no_advance"


# ── Aggregations ──────────────────────────────────────────────────────────────
def _bucketize_advance_rate(rows, key_fn):
    """Per-key: attempts, genuine advances, mislabeled-advance count, advance-rate."""
    out = {}
    for r in rows:
        k = key_fn(r)
        b = out.setdefault(k, {
            "attempts": 0, "compiled": 0, "advance_labeled": 0,
            "genuine_advance": 0, "mislabeled_advance": 0,
        })
        b["attempts"] += 1
        if _is_compiled(r):
            b["compiled"] += 1
        if r.get("status") == ST_COMPILED_ADVANCE:
            b["advance_labeled"] += 1
            if _is_genuine_advance(r):
                b["genuine_advance"] += 1
            else:
                b["mislabeled_advance"] += 1
    for b in out.values():
        b["advance_rate"] = (b["genuine_advance"] / b["attempts"]) if b["attempts"] else 0.0
    return out


def _cost_per_advance(rows, key_fn, usd_per_hour):
    """Per-key: total cost (persisted+est), genuine advances, cost-per-advance,
    and how many rows actually carried a cost."""
    out = {}
    for r in rows:
        k = key_fn(r)
        b = out.setdefault(k, {
            "total_cost_usd": 0.0, "rows_with_cost": 0, "rows_total": 0,
            "genuine_advance": 0, "est_used": 0,
        })
        b["rows_total"] += 1
        cost, src = _row_cost(r, usd_per_hour)
        if cost is not None:
            b["total_cost_usd"] += cost
            b["rows_with_cost"] += 1
            if src == "wallclock_est":
                b["est_used"] += 1
        if _is_genuine_advance(r):
            b["genuine_advance"] += 1
    for b in out.values():
        if b["genuine_advance"] > 0:
            b["cost_per_advance_usd"] = b["total_cost_usd"] / b["genuine_advance"]
        else:
            b["cost_per_advance_usd"] = None  # undefined: no genuine advance yet
    return out


def _reject_breakdown(rows):
    """Counts of literature & faithfulness signals across all rows."""
    lit, faith = {}, {}
    for r in rows:
        lit[_literature_signal(r)] = lit.get(_literature_signal(r), 0) + 1
        faith[_faithfulness_signal(r)] = faith.get(_faithfulness_signal(r), 0) + 1
    return {"literature": lit, "faithfulness": faith}


def _mislabeled_advances(rows):
    """Every compiled_advance row that is NOT a genuine gauntlet-passed advance.
    Returns a detailed record per row with the specific reasons."""
    flagged = []
    for r in rows:
        if r.get("status") != ST_COMPILED_ADVANCE:
            continue
        reasons = []
        if int(r.get("target_resolved") or 0) != 1:
            reasons.append("target_resolved=0 (G4 never promoted; IFF violation)")
        if int(r.get("axiomatizes_prior_work") or 0) == 1:
            reasons.append("axiomatizes_prior_work=1")
        contrib = (r.get("contribution_statement") or "")
        low = contrib.lower()
        hit = [m for m in _NON_RESOLUTION_MARKERS if m in low]
        if hit:
            reasons.append(f"non-resolution markers in contribution: {hit}")
        if _safe_float(r.get("cost_usd")) is None:
            reasons.append("cost_usd NULL")
        if r.get("mathematical_content_score") is None:
            reasons.append("mathematical_content_score NULL")
        if reasons:
            flagged.append({
                "id": r.get("id"),
                "filename": r.get("filename"),
                "problem_id": r.get("problem_id"),
                "lane": _lane_label(r),
                "author": _author_label(r),
                "mcs": r.get("mathematical_content_score"),
                "reasons": reasons,
                "contribution_excerpt": contrib[:160] + ("…" if len(contrib) > 160 else ""),
            })
    return flagged


# ── The three invariants ──────────────────────────────────────────────────────
def check_invariants(rows):
    """Assert the three self-enforcing invariants. Returns a dict with per-
    invariant {ok, detail, offenders}."""
    # I1: target_resolved=1  ⟺  status == compiled_advance.
    tr1_not_adv = [r for r in rows
                   if int(r.get("target_resolved") or 0) == 1
                   and r.get("status") != ST_COMPILED_ADVANCE]
    adv_not_tr1 = [r for r in rows
                   if r.get("status") == ST_COMPILED_ADVANCE
                   and int(r.get("target_resolved") or 0) != 1]
    i1_ok = not tr1_not_adv and not adv_not_tr1
    i1 = {
        "name": "I1: target_resolved=1 ⟺ status=compiled_advance (gauntlet G4 IFF)",
        "ok": i1_ok,
        "detail": (
            "All rows agree."
            if i1_ok else
            f"{len(adv_not_tr1)} compiled_advance row(s) with target_resolved=0 "
            f"(promotion without G1∧G2∧G3); "
            f"{len(tr1_not_adv)} target_resolved=1 row(s) not labeled compiled_advance."
        ),
        "offenders": (
            [{"id": r.get("id"), "status": r.get("status"),
              "target_resolved": r.get("target_resolved"),
              "issue": "compiled_advance but target_resolved=0"} for r in adv_not_tr1]
            + [{"id": r.get("id"), "status": r.get("status"),
                "target_resolved": r.get("target_resolved"),
                "issue": "target_resolved=1 but status!=compiled_advance"} for r in tr1_not_adv]
        ),
    }

    # I2: cost_usd AND mcs non-NULL on 100% of compiled_* rows.
    compiled = [r for r in rows if _is_compiled(r)]
    n = len(compiled)
    cost_missing = [r for r in compiled if _safe_float(r.get("cost_usd")) is None]
    mcs_missing = [r for r in compiled if r.get("mathematical_content_score") is None]
    i2_ok = (not cost_missing) and (not mcs_missing)
    i2 = {
        "name": "I2: cost_usd AND mathematical_content_score non-NULL on 100% of compiled_* rows",
        "ok": i2_ok,
        "detail": (
            f"All {n} compiled_* rows complete."
            if i2_ok else
            f"compiled_* rows={n}; cost_usd missing on {len(cost_missing)} "
            f"({_pct(len(cost_missing), n)}), mathematical_content_score missing on "
            f"{len(mcs_missing)} ({_pct(len(mcs_missing), n)}). COMPLETENESS ALARM."
        ),
        "cost_missing": len(cost_missing),
        "mcs_missing": len(mcs_missing),
        "compiled_total": n,
        # cap offender ids for sanity in JSON
        "cost_missing_ids": [r.get("id") for r in cost_missing[:50]],
        "mcs_missing_ids": [r.get("id") for r in mcs_missing[:50]],
    }

    # I3: the two existing compiled_advance rows flagged for re-audit.
    # We define the re-audit set as every compiled_advance row that is NOT a
    # genuine advance under the read-only proxy. On the real DB that is exactly
    # {1254 Brocard, 1255 Feit-Thompson}.
    flagged = _mislabeled_advances(rows)
    all_adv = [r for r in rows if r.get("status") == ST_COMPILED_ADVANCE]
    # I3 "holds" when every currently-labeled compiled_advance that is mislabeled
    # is surfaced for re-audit (i.e. the alarm is doing its job). It is a WARN,
    # not a hard failure of data integrity by itself — but it FAILS the exit
    # gate because a mislabeled advance must block a campaign until re-audited.
    i3_ok = (len(flagged) == 0)
    i3 = {
        "name": "I3: the existing compiled_advance rows are flagged for re-audit "
                "(fail-closed gauntlet would downgrade them)",
        "ok": i3_ok,
        "detail": (
            f"No mislabeled advances; all {len(all_adv)} compiled_advance row(s) "
            f"are genuine."
            if i3_ok else
            f"{len(flagged)} of {len(all_adv)} compiled_advance row(s) FLAGGED FOR "
            f"RE-AUDIT (mislabeled). Re-run verification_gauntlet.run_gauntlet on "
            f"each; expect downgrade to compiled_no_advance."
        ),
        "flagged_ids": [f["id"] for f in flagged],
        "flagged": flagged,
    }

    all_ok = i1_ok and i2_ok and i3_ok
    return {"all_ok": all_ok, "I1": i1, "I2": i2, "I3": i3}


def _pct(num, den):
    if not den:
        return "0%"
    return f"{100.0 * num / den:.1f}%"


# ── Full report assembly ──────────────────────────────────────────────────────
def build_report(conn, days=None, usd_per_hour=ARISTOTLE_USD_PER_HOUR):
    rows = fetch_rows(conn, days=days)
    by_lane_rate = _bucketize_advance_rate(rows, _lane_label)
    by_author_rate = _bucketize_advance_rate(rows, _author_label)
    by_lane_cost = _cost_per_advance(rows, _lane_label, usd_per_hour)
    by_author_cost = _cost_per_advance(rows, _author_label, usd_per_hour)
    rejects = _reject_breakdown(rows)
    mislabeled = _mislabeled_advances(rows)
    invariants = check_invariants(rows)

    status_counts = {}
    for r in rows:
        status_counts[r.get("status")] = status_counts.get(r.get("status"), 0) + 1

    total_genuine = sum(1 for r in rows if _is_genuine_advance(r))
    total_attempts = len(rows)

    return {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "gauntlet_constants_imported": _GAUNTLET_IMPORTED,
        "window_days": days,
        "aristotle_usd_per_hour": usd_per_hour,
        "totals": {
            "submissions_in_window": total_attempts,
            "genuine_advances": total_genuine,
            "advance_labeled": status_counts.get(ST_COMPILED_ADVANCE, 0),
            "overall_advance_rate": (total_genuine / total_attempts) if total_attempts else 0.0,
        },
        "status_counts": status_counts,
        "advance_rate_by_lane": by_lane_rate,
        "advance_rate_by_author": by_author_rate,
        "cost_per_advance_by_lane": by_lane_cost,
        "cost_per_advance_by_author": by_author_cost,
        "reject_breakdown": rejects,
        "mislabeled_advances": mislabeled,
        "invariants": invariants,
    }


# ── Text rendering ────────────────────────────────────────────────────────────
def _fmt_cost(v):
    return "—" if v is None else f"${v:,.2f}"


def render_text(rep):
    L = []
    A = L.append
    A("=" * 78)
    A("METHOD-1 ADVANCE DASHBOARD  (read-only governance surface)")
    A("=" * 78)
    src = "verification_gauntlet" if rep["gauntlet_constants_imported"] else "literal fallback"
    win = f"last {rep['window_days']} days" if rep["window_days"] else "all time"
    A(f"generated {rep['generated_at']}  |  status enum from: {src}  |  window: {win}")
    rate = rep["aristotle_usd_per_hour"]
    A(f"Aristotle directional cost rate: ${rate:.2f}/hr"
      + ("" if rate else "  (0 → wall-clock cost estimate DISABLED; set ARISTOTLE_USD_PER_HOUR)"))
    A("")

    t = rep["totals"]
    A("-" * 78)
    A("TOTALS")
    A("-" * 78)
    A(f"  submissions in window     : {t['submissions_in_window']}")
    A(f"  compiled_advance (labeled): {t['advance_labeled']}")
    A(f"  GENUINE advances          : {t['genuine_advances']}   "
      f"(target_resolved=1 ∧ not-axiomatized ∧ not bounded/weaker)")
    A(f"  overall advance-rate      : {t['overall_advance_rate']*100:.3f}%")
    A("  status counts             : "
      + ", ".join(f"{k}={v}" for k, v in sorted(rep["status_counts"].items(),
                                                 key=lambda kv: -kv[1])))
    A("")

    # Advance-rate per lane
    A("-" * 78)
    A("ADVANCE-RATE BY LANE")
    A("-" * 78)
    A(f"  {'lane':<16}{'attempts':>9}{'compiled':>9}{'adv*':>6}{'genuine':>8}{'mislabel':>9}{'rate':>9}")
    for lane, b in sorted(rep["advance_rate_by_lane"].items(), key=lambda kv: -kv[1]["attempts"]):
        A(f"  {lane:<16}{b['attempts']:>9}{b['compiled']:>9}{b['advance_labeled']:>6}"
          f"{b['genuine_advance']:>8}{b['mislabeled_advance']:>9}{b['advance_rate']*100:>8.2f}%")
    A("  (adv* = rows labeled compiled_advance; genuine = passed read-only proxy)")
    A("")

    # Advance-rate per author
    A("-" * 78)
    A("ADVANCE-RATE BY AUTHOR (paired_llm / sketch model)")
    A("-" * 78)
    items = sorted(rep["advance_rate_by_author"].items(), key=lambda kv: -kv[1]["attempts"])
    A(f"  {'author':<46}{'attempts':>9}{'genuine':>8}{'mislabel':>9}")
    for author, b in items[:25]:
        nm = author if len(author) <= 44 else author[:43] + "…"
        A(f"  {nm:<46}{b['attempts']:>9}{b['genuine_advance']:>8}{b['mislabeled_advance']:>9}")
    if len(items) > 25:
        A(f"  … and {len(items) - 25} more authors")
    A("")

    # Cost per advance
    A("-" * 78)
    A("COST-PER-ADVANCE BY LANE  (directional)")
    A("-" * 78)
    A(f"  {'lane':<16}{'rows':>7}{'w/cost':>8}{'est':>6}{'total$':>12}{'genuine':>8}{'$/advance':>12}")
    for lane, b in sorted(rep["cost_per_advance_by_lane"].items(), key=lambda kv: -kv[1]["rows_total"]):
        A(f"  {lane:<16}{b['rows_total']:>7}{b['rows_with_cost']:>8}{b['est_used']:>6}"
          f"{_fmt_cost(b['total_cost_usd']):>12}{b['genuine_advance']:>8}"
          f"{_fmt_cost(b['cost_per_advance_usd']):>12}")
    A("  ($/advance = '—' when no genuine advance yet, i.e. undefined — the honest state today)")
    A("")
    # Cost per advance by author (only authors that carried cost or produced advances)
    auth_cost = {k: v for k, v in rep["cost_per_advance_by_author"].items()
                 if v["rows_with_cost"] > 0 or v["genuine_advance"] > 0}
    if auth_cost:
        A("  COST-PER-ADVANCE BY AUTHOR (rows with cost or advances only):")
        for author, b in sorted(auth_cost.items(), key=lambda kv: -kv[1]["total_cost_usd"])[:15]:
            nm = author if len(author) <= 40 else author[:39] + "…"
            A(f"    {nm:<42}total={_fmt_cost(b['total_cost_usd'])}  "
              f"genuine={b['genuine_advance']}  $/adv={_fmt_cost(b['cost_per_advance_usd'])}")
    else:
        A("  COST-PER-ADVANCE BY AUTHOR: no rows carry cost yet (cost_usd 0/all).")
    A("")

    # Reject breakdown
    A("-" * 78)
    A("FAITHFULNESS / LITERATURE REJECT BREAKDOWN  (persisted-signal derived, read-only)")
    A("-" * 78)
    A("  Derived from status enum + closure_axis_json + contribution_statement —")
    A("  NOT a live re-run of statement_diff / biblio_gate. Labels are signals, not verdicts.")
    A("  FAITHFULNESS signal:")
    for k, v in sorted(rep["reject_breakdown"]["faithfulness"].items(), key=lambda kv: -kv[1]):
        A(f"     {k:<28}{v:>6}")
    A("  LITERATURE / closure-axis signal:")
    for k, v in sorted(rep["reject_breakdown"]["literature"].items(), key=lambda kv: -kv[1]):
        A(f"     {k:<28}{v:>6}")
    A("")

    # Mislabeled-advance alarm
    A("=" * 78)
    ml = rep["mislabeled_advances"]
    if ml:
        A(f"  *** MISLABELED-ADVANCE ALARM: {len(ml)} compiled_advance row(s) are NOT genuine ***")
        A("=" * 78)
        for f in ml:
            A(f"  [id {f['id']}] {f['problem_id']}  ({f['lane']} lane, author={f['author']}, mcs={f['mcs']})")
            A(f"     file: {f['filename']}")
            for r in f["reasons"]:
                A(f"       - {r}")
            if f["contribution_excerpt"]:
                A(f"     contribution: {f['contribution_excerpt']}")
        A("  ACTION: re-run verification_gauntlet.run_gauntlet(...) on each; expect downgrade.")
    else:
        A("  MISLABELED-ADVANCE ALARM: clear — every compiled_advance row is genuine.")
        A("=" * 78)
    A("")

    # Invariants
    inv = rep["invariants"]
    A("=" * 78)
    A(f"SELF-ENFORCING INVARIANTS  →  {'ALL HOLD ✅' if inv['all_ok'] else 'VIOLATION(S) ✗'}")
    A("=" * 78)
    for key in ("I1", "I2", "I3"):
        iv = inv[key]
        mark = "PASS" if iv["ok"] else "FAIL"
        A(f"  [{mark}] {iv['name']}")
        A(f"         {iv['detail']}")
        if not iv["ok"]:
            if key == "I1" and iv.get("offenders"):
                for o in iv["offenders"][:10]:
                    A(f"           offender id={o['id']}: {o['issue']}")
            if key == "I2":
                A(f"           cost_usd missing ids (≤50): {iv['cost_missing_ids']}")
                A(f"           mcs missing ids (≤50): {iv['mcs_missing_ids']}")
            if key == "I3":
                A(f"           flagged ids: {iv['flagged_ids']}")
        A("")
    A("Exit code: 0 if ALL invariants hold, else 1 (gate a campaign on this).")
    A("=" * 78)
    return "\n".join(L)


# ── Self-test (synthetic temp DB; no real-DB writes) ──────────────────────────
def _build_self_test_db(path):
    """Create a tiny synthetic DB exercising every classifier/invariant branch."""
    conn = sqlite3.connect(path)
    conn.execute("""
        CREATE TABLE submissions (
            id INTEGER PRIMARY KEY, uuid TEXT, filename TEXT, problem_id TEXT,
            status TEXT, status_legacy TEXT, lane TEXT, informal_mode_used INTEGER,
            paired_llm TEXT, sketch_model_primary TEXT, sketch_model_secondary TEXT,
            target_resolved INTEGER, axiomatizes_prior_work INTEGER, axiom_count INTEGER,
            cost_usd REAL, mathematical_content_score INTEGER, contribution_statement TEXT,
            closure_axis_json TEXT, fusion_json TEXT,
            created_at TEXT, submitted_at TEXT, completed_at TEXT
        )""")
    rows = [
        # 1: genuine advance (should pass everything; complete cost+mcs)
        (1, "u1", "good.txt", "p1", ST_COMPILED_ADVANCE, None, "informal", 1,
         "codex+gemini", None, None, 1, 0, 0, 2.50, 7,
         "Resolves the gap: full closure proven.", None, None,
         "2026-05-01 00:00:00", "2026-05-01 00:00:00", "2026-05-01 01:00:00"),
        # 2: MISLABELED advance — target_resolved=0 + non-resolution text + cost NULL (Brocard-like)
        (2, "u2", "brocard.txt", "brocard", ST_COMPILED_ADVANCE, None, "bare", 0,
         "none", "claude", None, 0, 0, 0, None, 3,
         "STRUCTURAL: proved for n in [2,500] via native_decide. Does NOT resolve Brocard.",
         None, None, "2026-05-02 00:00:00", "2026-05-02 00:00:00", "2026-05-02 02:00:00"),
        # 3: compiled_no_advance, clean, has cost+mcs
        (3, "u3", "noadv.txt", "p3", ST_COMPILED_NO_ADVANCE, None, "fusion", 1,
         "gemini", None, None, 0, 0, 0, 1.10, 5, "Clean compile, goal untouched.",
         None, None, "2026-05-03 00:00:00", "2026-05-03 00:00:00", "2026-05-03 00:30:00"),
        # 4: compile_failed (G1 reject), cost NULL, mcs NULL -> I2 offender
        (4, "u4", "fail.txt", "p4", ST_COMPILE_FAILED, None, "bare", 0,
         "none", None, None, 0, 0, 0, None, None, None, None, None,
         "2026-05-04 00:00:00", None, None),
        # 5: disproven (literature/faithfulness counterexample signal)
        (5, "u5", "dis.txt", "p5", ST_DISPROVEN, None, "informal", 1,
         "codex", None, None, 0, 0, 0, 0.40, 2, None, None, None,
         "2026-05-05 00:00:00", "2026-05-05 00:00:00", "2026-05-05 00:10:00"),
        # 6: closure-axis held (real_closure_candidate false)
        (6, "u6", "held.txt", "p6", ST_COMPILED_NO_ADVANCE, None, "closure", 0,
         "none", None, None, 0, 0, 0, 0.90, 4, "partial result only",
         '{"real_closure_candidate": false, "CR": "partial_result_only"}', None,
         "2026-05-06 00:00:00", "2026-05-06 00:00:00", "2026-05-06 00:20:00"),
        # 7: compiled_partial (residual sorry), cost+mcs present
        (7, "u7", "part.txt", "p7", ST_COMPILED_PARTIAL, None, "informal", 1,
         "gemini", None, None, 0, 0, 0, 0.75, 6, None, None, None,
         "2026-05-07 00:00:00", "2026-05-07 00:00:00", "2026-05-07 00:25:00"),
    ]
    conn.executemany(
        "INSERT INTO submissions VALUES (" + ",".join("?" * 22) + ")", rows)
    conn.commit()
    conn.close()


def run_self_test():
    import tempfile
    failures = []
    with tempfile.TemporaryDirectory() as d:
        dbp = os.path.join(d, "selftest.db")
        _build_self_test_db(dbp)
        conn = connect_ro(dbp)
        rep = build_report(conn, usd_per_hour=10.0)  # enable wall-clock estimate
        conn.close()

    inv = rep["invariants"]
    # I1 must FAIL: row 2 is compiled_advance with target_resolved=0.
    if inv["I1"]["ok"]:
        failures.append("I1 should FAIL (row2 compiled_advance target_resolved=0)")
    if 2 not in [o["id"] for o in inv["I1"]["offenders"]]:
        failures.append("I1 offenders should include id=2")
    # I2 must FAIL: rows 2 (cost NULL) and 4 (cost+mcs NULL) are compiled_*.
    if inv["I2"]["ok"]:
        failures.append("I2 should FAIL (rows 2,4 missing cost/mcs)")
    if inv["I2"]["cost_missing"] < 2:
        failures.append(f"I2 cost_missing should be >=2, got {inv['I2']['cost_missing']}")
    # I3 must FAIL: row 2 is a mislabeled advance.
    if inv["I3"]["ok"]:
        failures.append("I3 should FAIL (row2 mislabeled)")
    if 2 not in inv["I3"]["flagged_ids"]:
        failures.append("I3 flagged_ids should include id=2")
    # Genuine advance count must be exactly 1 (row 1).
    if rep["totals"]["genuine_advances"] != 1:
        failures.append(f"genuine_advances should be 1, got {rep['totals']['genuine_advances']}")
    # Mislabeled alarm must contain exactly row 2.
    ml_ids = [f["id"] for f in rep["mislabeled_advances"]]
    if ml_ids != [2]:
        failures.append(f"mislabeled_advances should be [2], got {ml_ids}")
    # Faithfulness breakdown must include the bounded_or_weaker (row 2) bucket.
    if rep["reject_breakdown"]["faithfulness"].get("bounded_or_weaker", 0) < 1:
        failures.append("faithfulness 'bounded_or_weaker' should be >=1")
    # Literature breakdown must include disproven (row 5) and held (row 6).
    lit = rep["reject_breakdown"]["literature"]
    if lit.get("disproven", 0) != 1:
        failures.append("literature 'disproven' should be 1")
    if lit.get("held_not_real_closure", 0) != 1:
        failures.append("literature 'held_not_real_closure' should be 1")
    # Cost-per-advance for the genuine-advance lane (informal) must be defined,
    # and the wall-clock estimate must have kicked in for row 4? row4 has no
    # completed_at so est skipped — just assert informal lane $/advance is set.
    informal_cost = rep["cost_per_advance_by_lane"].get("informal", {})
    if informal_cost.get("cost_per_advance_usd") is None:
        failures.append("informal lane cost_per_advance should be defined (row1 genuine)")

    print(render_text(rep))
    print()
    if failures:
        print("SELF-TEST FAILED:")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("SELF-TEST PASSED — all classifier + invariant branches verified on synthetic DB.")
    return 0


# ── CLI ───────────────────────────────────────────────────────────────────────
def main():
    ap = argparse.ArgumentParser(
        description="Method-1 advance dashboard (read-only governance surface over tracking.db).")
    ap.add_argument("--db", default=str(DEFAULT_DB),
                    help=f"SQLite DB path (default: {DEFAULT_DB})")
    ap.add_argument("--days", type=int, default=None,
                    help="Window: only submissions in the last N days")
    ap.add_argument("--usd-per-hour", type=float, default=ARISTOTLE_USD_PER_HOUR,
                    help="Directional Aristotle $/hr for wall-clock cost estimate "
                         "(default from ARISTOTLE_USD_PER_HOUR env, else 0 = disabled)")
    ap.add_argument("--json", action="store_true", help="Emit machine-readable JSON")
    ap.add_argument("--invariants-only", action="store_true",
                    help="Print only the three invariants + exit code")
    ap.add_argument("--self-test", action="store_true",
                    help="Run the synthetic-DB self-test (no real-DB access)")
    args = ap.parse_args()

    if args.self_test:
        sys.exit(run_self_test())

    try:
        conn = connect_ro(args.db)
    except FileNotFoundError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(2)

    try:
        rep = build_report(conn, days=args.days, usd_per_hour=args.usd_per_hour)
    finally:
        conn.close()

    if args.json:
        print(json.dumps(rep, indent=2, default=str))
    elif args.invariants_only:
        inv = rep["invariants"]
        for key in ("I1", "I2", "I3"):
            iv = inv[key]
            print(f"[{'PASS' if iv['ok'] else 'FAIL'}] {iv['name']}")
            print(f"        {iv['detail']}")
        print(f"\nALL INVARIANTS HOLD: {inv['all_ok']}")
    else:
        print(render_text(rep))

    # Exit nonzero if any invariant is violated → gates a campaign.
    sys.exit(0 if rep["invariants"]["all_ok"] else 1)


if __name__ == "__main__":
    main()
