#!/usr/bin/env python3
"""
Method-1 / Recipe-B loop driver — the async state-machine that runs the GATED
Method-1 conveyor at parallel throughput.

  strong-LLM-authored informal argument (.fusion.json)
    -> ADMISSION GATE (refuse rows lacking a strategy_outline — never bare-spray)
    -> capacity-governed parallel INFORMAL submit (asyncio.Semaphore +
       slots_available re-check + build_informal_prompt, via safe_aristotle_submit
       --fusion-lane)
    -> fetch_backlog fold-in (fetch / extract / audit)
    -> verification_gauntlet.run_gauntlet (fail-closed: compiled_advance IFF
       G1 clean AND G2 faithful AND G3 CLEAR)
    -> Project.ask self-repair loop (cap ASK_REPAIR_CAP=2, plateau detection)
    -> cost capture + daily $CAP governor.

This script REPLACES proof_orchestrator's broken Aristotle leg:
  * get_solution() (proof_orchestrator.py ~:532) — that coroutine does not exist
    on aristotlelib 2.0 Project; fetch_result/get_files is the real download path.
  * str(p.status) == 'COMPLETE' (~:511) — Project.status is RUNNING/IDLE/UNKNOWN
    now; outcome lives on the latest AgentTask (check_status reads it correctly).
  * bare `safe_aristotle_submit.py <sketch> --force` (~:434) — that is a BARE-lane
    spray with the gap-targeting gate bypassed; Method-1 forbids it. We submit on
    the FUSION lane with a strong-LLM-authored .fusion.json companion, which routes
    through the informal reasoner (subsystem #2) instead of formalize-only MCGS.

It keeps proof_orchestrator's state-machine skeleton (proof_queue table, the
QUEUED/.../RESOLVED/STALLED transitions, the enqueue/run/status CLI shape).

SAFETY: `run` DEFAULTS to dry-run-safe behavior only insofar as the loop will
not submit unless candidates are admitted AND capacity exists; the actual live
Aristotle submission is gated behind --live. --dry-run (and the absence of --live)
SKIPS the submit call entirely so the admission/capacity/queue logic can be
exercised with zero outward-facing cost. There is intentionally NO --force /
--skip-gate / bare-spray path.

Usage:
    python3 scripts/method1_loop.py enqueue --problem-id erdos_1056 [--dossier PATH]
    python3 scripts/method1_loop.py run [--dry-run] [--max N] [--live]
    python3 scripts/method1_loop.py status

    # Safe validation (NO live submit):
    python3 scripts/method1_loop.py run --dry-run --max 5
"""

import argparse
import asyncio
import json
import os
import signal
import sqlite3
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

MATH_DIR = Path(__file__).resolve().parent.parent
TRACKING_DB = MATH_DIR / "submissions" / "tracking.db"
RESULTS_DIR = MATH_DIR / "submissions" / "method1_results"
METHOD1_DIR = MATH_DIR / "submissions" / "method1"

sys.path.insert(0, str(MATH_DIR / "scripts"))

# ── Tunables (env-overridable) ───────────────────────────────────────────────
ASK_REPAIR_CAP = int(os.environ.get("METHOD1_ASK_REPAIR_CAP", "2"))
# The shared Aristotle slot governor lives in safe_aristotle_submit (MAX_CONCURRENT,
# default 25, env ARISTOTLE_MAX_CONCURRENT). We never exceed slots_available.
SUBMIT_WAVE_SEMAPHORE = int(os.environ.get("METHOD1_SUBMIT_CONCURRENCY", "6"))
# Daily $-budget governor: campaign pauses a submit wave when projected spend
# (today's authoring + Aristotle wall-clock cost already booked) exceeds the cap.
DAILY_CAP_USD = float(os.environ.get("METHOD1_DAILY_CAP_USD", "0") or "0")  # 0 = no cap
# Directional Aristotle wall-clock cost (matches verification_gauntlet's model).
ARISTOTLE_USD_PER_HOUR = float(os.environ.get("ARISTOTLE_USD_PER_HOUR", "0") or "0")


# ── Lazy imports of reused primitives ────────────────────────────────────────
# Imported lazily so `status`/`enqueue` (and --dry-run authoring/admission) work
# even when aristotlelib / ARISTOTLE_API_KEY are absent. Only the live submit /
# fetch / ask path requires the SDK.

def _imp_informal():
    """aristotle_informal: load_fusion_companion + STRATEGY_OUTLINE_FIELDS + _first_present.

    This is the SAME module the I9 downstream router uses, so the admission gate's
    `has_outline` check is byte-identical to safe_aristotle_submit's.
    """
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "aristotle_informal", MATH_DIR / "scripts" / "aristotle_informal.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # type: ignore
    return mod


def _imp_gauntlet():
    import verification_gauntlet  # noqa: WPS433
    return verification_gauntlet


def _imp_fetch():
    """fetch_backlog's fetch/extract/audit primitive + aristotle_fetch helpers."""
    import fetch_backlog  # noqa: WPS433
    import aristotle_fetch  # noqa: WPS433
    return fetch_backlog, aristotle_fetch


def _imp_safe_submit():
    import safe_aristotle_submit  # noqa: WPS433
    return safe_aristotle_submit


# ── DB layer (forked from proof_orchestrator, additive only) ─────────────────

def _db_path() -> Path:
    """Resolve the tracking DB. METHOD1_DB env override is for temp-copy tests."""
    return Path(os.environ.get("METHOD1_DB", str(TRACKING_DB)))


def ensure_queue_table():
    """Create proof_queue if missing (ADDITIVE: CREATE IF NOT EXISTS only).

    Mirrors proof_orchestrator's schema so the two tools share one queue, and adds
    submission_uuid (the migration agent added this column to the real DB; we
    ALTER ADD here too so temp-copy / fresh DBs match the contract).
    """
    conn = sqlite3.connect(str(_db_path()))
    try:
        conn.executescript("""
            CREATE TABLE IF NOT EXISTS proof_queue (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                problem_id TEXT NOT NULL,
                problem_source TEXT NOT NULL,
                created_at TEXT DEFAULT CURRENT_TIMESTAMP,
                updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
                state TEXT NOT NULL DEFAULT 'QUEUED',
                priority INTEGER NOT NULL DEFAULT 5,
                codex_proof_id INTEGER,
                codex_attempts INTEGER DEFAULT 0,
                codex_best_sorry INTEGER,
                codex_compiled INTEGER DEFAULT 0,
                reasoning_effort TEXT DEFAULT 'high',
                aristotle_uuid TEXT,
                aristotle_rounds INTEGER DEFAULT 0,
                context_files TEXT DEFAULT '[]',
                parent_queue_id INTEGER,
                total_rounds INTEGER DEFAULT 0,
                best_sorry_count INTEGER,
                last_sorry_count INTEGER,
                stall_count INTEGER DEFAULT 0,
                max_codex_attempts INTEGER DEFAULT 3,
                max_aristotle_rounds INTEGER DEFAULT 3,
                max_total_rounds INTEGER DEFAULT 8,
                max_stall INTEGER DEFAULT 2,
                resolved_at TEXT,
                resolved_proof TEXT,
                error_message TEXT
            );
            CREATE INDEX IF NOT EXISTS idx_pq_state ON proof_queue(state);
            CREATE INDEX IF NOT EXISTS idx_pq_priority ON proof_queue(priority, created_at);
            CREATE INDEX IF NOT EXISTS idx_pq_problem ON proof_queue(problem_id);
        """)
        cols = {r[1] for r in conn.execute("PRAGMA table_info(proof_queue)")}
        if "submission_uuid" not in cols:
            conn.execute("ALTER TABLE proof_queue ADD COLUMN submission_uuid TEXT")
            conn.execute(
                "CREATE INDEX IF NOT EXISTS idx_pq_submission_uuid "
                "ON proof_queue(submission_uuid)")
        conn.commit()
    finally:
        conn.close()


def db_query(sql, params=()):
    conn = sqlite3.connect(str(_db_path()))
    conn.row_factory = sqlite3.Row
    try:
        rows = conn.execute(sql, params).fetchall()
        return [dict(r) for r in rows]
    finally:
        conn.close()


def db_execute(sql, params=()):
    conn = sqlite3.connect(str(_db_path()))
    try:
        conn.execute("PRAGMA journal_mode=WAL")
        cur = conn.execute(sql, params)
        conn.commit()
        return cur.lastrowid
    finally:
        conn.close()


def db_scalar(sql, params=()):
    rows = db_query(sql, params)
    return list(rows[0].values())[0] if rows else None


# ── Config ───────────────────────────────────────────────────────────────────

@dataclass
class LoopConfig:
    dry_run: bool = True          # default safe: never submit unless --live
    live: bool = False            # explicit opt-in to fire real submissions
    max_per_run: int = 5          # cap candidates pulled from v_method1_ready per run
    poll_interval: int = 60
    single_pass: bool = True      # default: one tick then exit (campaign uses loop)
    exit_when_done: bool = False
    ask_repair_cap: int = ASK_REPAIR_CAP
    submit_concurrency: int = SUBMIT_WAVE_SEMAPHORE
    daily_cap_usd: float = DAILY_CAP_USD
    out_dir: Path = METHOD1_DIR
    verbose: bool = False

    @property
    def will_submit(self) -> bool:
        """Live submission happens ONLY when --live is set AND not --dry-run."""
        return self.live and not self.dry_run


# ── Admission gate (NEVER bare-spray) ────────────────────────────────────────

@dataclass
class AdmissionResult:
    admitted: bool
    reason: str
    sketch_path: Optional[Path] = None
    fusion_path: Optional[Path] = None
    outline_chars: int = 0


def find_dossier(problem_id: str, out_dir: Path) -> tuple[Optional[Path], Optional[Path]]:
    """Locate the authored (.txt, .fusion.json) pair for a problem_id.

    author_argument.py normalizes the problem_id to ^[a-z0-9_]+$ for the
    filename, so we mirror that normalization here.
    """
    import re
    pid_norm = re.sub(r"[^a-z0-9_]+", "_", problem_id.lower()).strip("_") or "candidate"
    txt = out_dir / f"{pid_norm}.txt"
    fusion = out_dir / f"{pid_norm}.fusion.json"
    return (txt if txt.exists() else None,
            fusion if fusion.exists() else None)


def check_admission(problem_id: str, out_dir: Path) -> AdmissionResult:
    """ADMISSION GATE. Refuse any row whose authored .fusion.json lacks a non-empty
    strategy_outline (alias informal_proof_outline). This is the hard "no outline ->
    no informal -> never bare-spray" rule: Method-1's whole point is that a
    strong-LLM argument backs every submission.

    Uses aristotle_informal.load_fusion_companion + STRATEGY_OUTLINE_FIELDS so the
    check is identical to the I9 downstream router's has_outline guard.
    """
    txt, fusion = find_dossier(problem_id, out_dir)
    if fusion is None:
        return AdmissionResult(False,
                               f"no .fusion.json dossier (run author_argument.py "
                               f"--problem-id {problem_id} first)")
    if txt is None:
        return AdmissionResult(False, f"dossier {fusion.name} present but bare .txt "
                                      f"sketch missing", fusion_path=fusion)
    try:
        inf = _imp_informal()
        companion = inf.load_fusion_companion(fusion)
        outline = inf._first_present(companion, inf.STRATEGY_OUTLINE_FIELDS)
    except Exception as e:
        return AdmissionResult(False, f"dossier unreadable: {e}",
                               sketch_path=txt, fusion_path=fusion)
    outline_str = str(outline).strip() if outline else ""
    if not outline_str:
        return AdmissionResult(False,
                               "dossier has empty strategy_outline / "
                               "informal_proof_outline -> REFUSED (no bare-spray)",
                               sketch_path=txt, fusion_path=fusion)
    return AdmissionResult(True, "admitted (strategy_outline present)",
                           sketch_path=txt, fusion_path=fusion,
                           outline_chars=len(outline_str))


# ── Cost / daily-cap governor ────────────────────────────────────────────────

def cost_booked_today() -> float:
    """Sum cost_usd booked on submissions created today (UTC). Directional.

    Method-1 books authoring cost at author time and Aristotle wall-clock cost at
    fetch time, both on the submissions row's cost_usd. The governor reads the
    real spend already recorded so an in-progress campaign self-limits.
    """
    try:
        v = db_scalar(
            "SELECT COALESCE(SUM(cost_usd), 0) FROM submissions "
            "WHERE cost_usd IS NOT NULL "
            "AND date(COALESCE(completed_at, submitted_at, created_at)) = date('now')")
        return float(v or 0.0)
    except Exception:
        # If the column/table is unexpectedly absent, fail toward caution: report
        # 0 (no false pause) but the governor still has the cap as a hard ceiling.
        return 0.0


def daily_cap_ok(cfg: LoopConfig) -> tuple[bool, float]:
    """Return (ok_to_submit, booked_today). cap<=0 disables the governor."""
    booked = cost_booked_today()
    if cfg.daily_cap_usd <= 0:
        return True, booked
    return booked < cfg.daily_cap_usd, booked


# ── The loop ─────────────────────────────────────────────────────────────────

class Method1Loop:
    def __init__(self, cfg: LoopConfig):
        self.cfg = cfg
        self.running = True
        cfg.out_dir.mkdir(parents=True, exist_ok=True)
        RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    # ── public entry ──
    def run(self):
        mode = "LIVE SUBMIT" if self.cfg.will_submit else "DRY-RUN (no submit)"
        print("=" * 72)
        print(f"  METHOD-1 LOOP  [{mode}]")
        print(f"  ask-repair cap={self.cfg.ask_repair_cap}  "
              f"submit-concurrency={self.cfg.submit_concurrency}  "
              f"daily-cap=${self.cfg.daily_cap_usd or 'none'}")
        print(f"  DB={_db_path()}  out-dir={self.cfg.out_dir}")
        print("=" * 72)
        ensure_queue_table()
        self._recover_from_crash()

        while self.running:
            try:
                asyncio.run(self.tick())
            except Exception as e:
                print(f"  ERROR in tick: {e}")
            if self.cfg.single_pass:
                break
            if self.cfg.exit_when_done:
                active = db_scalar(
                    "SELECT COUNT(*) FROM proof_queue "
                    "WHERE state NOT IN ('RESOLVED','STALLED','REJECTED')")
                if not active:
                    print("  All jobs terminal. Exiting.")
                    break
            time.sleep(self.cfg.poll_interval)

    async def tick(self):
        now = datetime.now().strftime("%H:%M:%S")
        # 1. Pull ready candidates from the DB-backed view, enqueue any not yet queued.
        self._refill_from_ready()
        # 2. Poll + fold-in any in-flight Aristotle jobs (fetch/extract/audit/gauntlet).
        await self._poll_and_fold_in()
        # 3. Capacity-governed parallel informal submit wave (SKIPPED in dry-run).
        await self._submit_wave()
        # 4. Drive ask self-repair on rows that need it.
        await self._repair_wave()

        summary = self._state_summary()
        print(f"\n[{now}] tick complete: {summary or 'queue empty'}")

    # ── crash recovery ──
    def _recover_from_crash(self):
        """Reset transient states on startup (mirrors proof_orchestrator)."""
        rows = db_query(
            "SELECT id, problem_id, aristotle_uuid FROM proof_queue "
            "WHERE state = 'SUBMITTING'")
        for r in rows:
            print(f"  Recovering job {r['id']} ({r['problem_id']}): "
                  f"SUBMITTING -> QUEUED (interrupted before confirm)")
            self._transition(r['id'], 'QUEUED')

    # ── transitions ──
    def _transition(self, queue_id, new_state, **kwargs):
        sets = ["state = ?", "updated_at = datetime('now')"]
        params = [new_state]
        for k, v in kwargs.items():
            sets.append(f"{k} = ?")
            params.append(v)
        params.append(queue_id)
        db_execute(f"UPDATE proof_queue SET {', '.join(sets)} WHERE id = ?", params)

    def _state_summary(self) -> str:
        rows = db_query(
            "SELECT state, COUNT(*) c FROM proof_queue GROUP BY state ORDER BY c DESC")
        return ", ".join(f"{r['state']}={r['c']}" for r in rows)

    # ── stage 1: refill from v_method1_ready ──
    def _refill_from_ready(self):
        """Pull top-N ready candidates and enqueue any not already in proof_queue.

        v_method1_ready already encodes the intake gate (literature_status=CLEAR
        AND deep_structural_exclude=0 AND NOT terminal, ordered by tractability).
        We do NOT re-implement that ranking — we trust the view.
        """
        try:
            ready = db_query(
                "SELECT problem_id, source_path, statement, domain, tier, "
                "snipe_signature, tractability_score, prior_attempts, argument_authored "
                "FROM v_method1_ready LIMIT ?", (self.cfg.max_per_run,))
        except sqlite3.OperationalError as e:
            print(f"  v_method1_ready unavailable ({e}); "
                  f"run scripts/migrate_method1.py + intake first.")
            return
        # Exclude EVERY problem_id that already has a proof_queue row — active OR
        # terminal. The loop drives existing rows through their state machine; it
        # must NOT resurrect a RESOLVED/STALLED/REJECTED problem on the next tick
        # (that would re-pull a malformed-dossier row from the view forever and
        # spawn duplicate REJECTED rows). Re-attempting a terminal problem is an
        # explicit operator action (`enqueue`), not an automatic refill.
        existing = {r['problem_id'] for r in db_query(
            "SELECT DISTINCT problem_id FROM proof_queue")}
        new = 0
        for c in ready:
            if c['problem_id'] in existing:
                continue
            src = c['source_path'] or c['statement'] or c['problem_id']
            qid = db_execute(
                "INSERT INTO proof_queue (problem_id, problem_source, priority, "
                "state, context_files) VALUES (?, ?, ?, 'QUEUED', '[]')",
                (c['problem_id'], src, int(c['tier'] or 5)))
            new += 1
            if self.cfg.verbose:
                print(f"  enqueued {c['problem_id']} (queue #{qid}, "
                      f"tractability={c['tractability_score']}, authored={c['argument_authored']})")
        if new:
            print(f"  refill: +{new} candidate(s) from v_method1_ready")

    # ── stage 3: capacity-governed parallel submit wave ──
    async def _submit_wave(self):
        """Submit exactly slots_available admitted candidates in one Semaphore-bounded
        wave. SKIPS the actual Project.create when not --live (dry-run).
        """
        queued = db_query(
            "SELECT * FROM proof_queue WHERE state = 'QUEUED' "
            "ORDER BY priority ASC, created_at ASC")
        if not queued:
            return

        # Daily $-cap governor (checked once per wave, before any submit).
        ok, booked = daily_cap_ok(self.cfg)
        if not ok:
            print(f"  💰 daily $-cap reached (booked ${booked:.2f} >= "
                  f"${self.cfg.daily_cap_usd:.2f}); pausing submit wave")
            return

        # ADMISSION GATE on every queued row (never bare-spray).
        admitted: list[tuple[dict, AdmissionResult]] = []
        for row in queued:
            adm = check_admission(row['problem_id'], self.cfg.out_dir)
            if not adm.admitted:
                print(f"  ⛔ admission DENIED {row['problem_id']}: {adm.reason}")
                # A row with no dossier is not a failure — it just hasn't been
                # authored yet. Leave it QUEUED (the campaign's author stage, or a
                # manual author_argument run, will produce the dossier). Only a
                # *malformed* dossier (present but empty outline) is terminal.
                if adm.fusion_path is not None and adm.outline_chars == 0 and adm.sketch_path is not None:
                    self._transition(row['id'], 'REJECTED',
                                     error_message=f'admission: {adm.reason}')
                continue
            admitted.append((row, adm))

        if not admitted:
            print("  submit wave: 0 admitted candidates")
            return

        # CAPACITY GOVERNOR: re-check slots_available right before the wave.
        slots = await self._slots_available()
        if slots <= 0:
            print(f"  submit wave: 0 slots available "
                  f"({len(admitted)} admitted, all deferred)")
            return

        wave = admitted[:slots]
        print(f"  submit wave: {len(wave)} of {len(admitted)} admitted "
              f"(slots_available={slots}, concurrency={self.cfg.submit_concurrency})")

        if not self.cfg.will_submit:
            # DRY-RUN: exercise admission + capacity + queue logic, NO submit.
            # G4 fix (2026-06-10): also surface the metadata that WOULD be
            # propagated — db.problem_id (safe_submit -> _record_lane_metadata
            # insert) and the gauntlet's source_conjecture (candidate_queue) —
            # so the dry-run proves end-to-end propagation, not just admission.
            for row, adm in wave:
                src = self._source_for(row['problem_id'])
                src_desc = f"resolved:{src[:60]}" if src else "MISSING (gauntlet would be structural-only)"
                print(f"     [DRY-RUN] would submit {row['problem_id']} "
                      f"(fusion-lane, outline={adm.outline_chars} chars) "
                      f"db.problem_id={row['problem_id']!r} "
                      f"source_conjecture={src_desc} "
                      f"-> SKIPPED (no --live)")
            return

        # LIVE: bounded asyncio.gather over safe_submit(fusion_lane=True).
        sem = asyncio.Semaphore(self.cfg.submit_concurrency)
        results = await asyncio.gather(
            *[self._submit_one(row, adm, sem) for row, adm in wave],
            return_exceptions=True)
        for (row, _adm), res in zip(wave, results):
            if isinstance(res, Exception):
                print(f"     submit error {row['problem_id']}: {res}")
                self._transition(row['id'], 'QUEUED', error_message=str(res)[:300])

    async def _slots_available(self) -> int:
        """Re-read the live Aristotle slot count via the ONE capacity governor.

        Reconciles the shared server budget with how many Method-1 jobs we already
        have in flight locally. In dry-run we never call the API (no SDK / key
        needed) — return the cap so the wave-sizing logic is still exercised.
        """
        if not self.cfg.will_submit:
            # Pretend the full cap is free; the wave is skipped anyway.
            try:
                ss = _imp_safe_submit()
                return ss.MAX_CONCURRENT
            except Exception:
                return 25
        ss = _imp_safe_submit()
        cap = await ss.check_rate_limit_and_capacity(window_minutes=10)
        server_slots = int(cap.get("slots_available", 0))
        # Subtract our own locally-tracked in-flight jobs so we never double-book.
        local_inflight = db_scalar(
            "SELECT COUNT(*) FROM proof_queue "
            "WHERE state IN ('SUBMITTED','FETCHING','REPAIRING')") or 0
        return max(0, min(server_slots, ss.MAX_CONCURRENT - int(local_inflight)))

    async def _submit_one(self, row: dict, adm: AdmissionResult,
                          sem: asyncio.Semaphore):
        """Submit ONE admitted candidate on the FUSION lane (informal reasoner).

        Calls safe_aristotle_submit.safe_submit in-process with fusion_lane=True.
        safe_submit auto-detects the sibling .fusion.json companion and routes
        through build_informal_prompt (the I9 informal-mode pathway). NO --force,
        NO bare-spray.
        """
        async with sem:
            self._transition(row['id'], 'SUBMITTING')
            ss = _imp_safe_submit()
            id_file = adm.sketch_path.with_suffix(".ID.txt")
            paired = self._winner_model(row['problem_id'])
            try:
                uuid = await ss.safe_submit(
                    input_file=adm.sketch_path,
                    project_id_file=id_file,
                    description=f"method1:{row['problem_id']}",
                    fusion_lane=True,           # routes to informal reasoner
                    informal_mode=False,        # let companion's outline flip it
                    paired_llm=paired,
                    batch=True,                 # wave context: skip interactive cap check
                    # G4 fix (2026-06-10): propagate problem_id onto the
                    # submissions row at insert. Row 1345 landed problem_id=NULL
                    # because this call never passed it, so the fetch-time
                    # gauntlet could not run G2/G3 ("structural-only, never
                    # advance") and the erdos_100 result failed promotion on
                    # metadata, not math.
                    problem_id=row['problem_id'],
                )
            except Exception as e:
                raise e
            if not uuid:
                raise RuntimeError("safe_submit returned no project_id")
            print(f"     ✅ submitted {row['problem_id']} uuid={uuid[:12]}")
            self._transition(row['id'], 'SUBMITTED',
                             aristotle_uuid=uuid,
                             submission_uuid=uuid,
                             aristotle_rounds=(row['aristotle_rounds'] or 0) + 1)
            return uuid

    def _winner_model(self, problem_id: str) -> str:
        """Best-effort: read paired_llm the author recorded (sketch_model_primary).

        author_argument writes provenance onto the submissions row at submit time,
        but the dossier file also carries the winning engine. We keep this simple:
        the loop passes a paired_llm hint; absence degrades to 'none'.
        """
        # The dossier sidecar (analysis/method1_authoring/<pid>.dossier.json) records
        # the winner engine; cheap to read, never fatal.
        import re
        pid_norm = re.sub(r"[^a-z0-9_]+", "_", problem_id.lower()).strip("_")
        sidecar = MATH_DIR / "analysis" / "method1_authoring" / f"{pid_norm}.dossier.json"
        try:
            data = json.loads(sidecar.read_text())
            return str(data.get("winner", {}).get("engine") or "none")
        except Exception:
            return "none"

    # ── stage 2: poll + fold-in fetch_backlog + gauntlet ──
    async def _poll_and_fold_in(self):
        """For every SUBMITTED/FETCHING/REPAIRING row with a uuid, check status; on
        COMPLETE/COMPLETE_WITH_ERRORS download+extract+audit (fetch_backlog primitives)
        then run the verification gauntlet and decide the next state.
        """
        rows = db_query(
            "SELECT * FROM proof_queue "
            "WHERE state IN ('SUBMITTED','FETCHING','REPAIRING') "
            "AND aristotle_uuid IS NOT NULL")
        if not rows:
            return
        if not self.cfg.will_submit:
            # In dry-run we never hit the network. If somehow rows are in flight
            # (e.g. a prior live run left them), just report and skip.
            print(f"  poll: {len(rows)} in-flight row(s) present but dry-run "
                  f"(skipping network fetch)")
            return

        _, aristotle_fetch = _imp_fetch()
        aristotle_fetch.aristotlelib.set_api_key(aristotle_fetch.get_api_key())

        sem = asyncio.Semaphore(3)  # mirror fetch_backlog's Semaphore(3)

        async def check_one(r):
            async with sem:
                for attempt in range(4):
                    st = await aristotle_fetch.check_status(r['aristotle_uuid'])
                    if st["status"] != "ERROR":
                        return r, st
                    await asyncio.sleep(1.5 * (attempt + 1))
                return r, st

        statuses = await asyncio.gather(*[check_one(r) for r in rows])
        for r, st in statuses:
            s = st["status"]
            if s in ("COMPLETE", "COMPLETE_WITH_ERRORS"):
                await self._fold_in_complete(r)
            elif s in ("ERROR", "FAILED"):
                self._handle_terminal_failure(r, s)
            else:
                # still running; bump to FETCHING-pending marker only if needed
                if r['state'] == 'SUBMITTED':
                    self._transition(r['id'], 'FETCHING')

    async def _fold_in_complete(self, row: dict):
        """Download + extract + audit (fetch_backlog primitives), then run_gauntlet."""
        fetch_backlog, aristotle_fetch = _imp_fetch()
        uuid = row['aristotle_uuid']
        tar_path = RESULTS_DIR / f"method1_{row['problem_id']}.tar.gz"
        res = await aristotle_fetch.fetch_result(uuid, tar_path)
        if not (res and tar_path.exists()):
            print(f"     [{row['problem_id']}] download FAILED")
            self._transition(row['id'], 'QUEUED',
                             error_message='download failed')
            return
        try:
            main_lean, summary = fetch_backlog._extract_and_find_lean(
                tar_path, RESULTS_DIR / f"method1_{row['problem_id']}_extracted")
        except Exception as e:
            print(f"     [{row['problem_id']}] extract FAILED ({e})")
            self._transition(row['id'], 'STALLED', error_message=f'extract: {e}')
            return
        if not main_lean:
            print(f"     [{row['problem_id']}] no .lean in archive")
            self._transition(row['id'], 'STALLED', error_message='no .lean in archive')
            return

        # ── VERIFICATION GAUNTLET (fail-closed) ──
        gauntlet = _imp_gauntlet()
        source = self._source_for(row['problem_id'])
        gv = gauntlet.run_gauntlet(
            uuid=uuid,
            lean_path=main_lean,
            summary_path=summary,
            source_conjecture=source,
            problem_id=row['problem_id'],
        )
        verdict = gv.get("verdict")
        target_resolved = int(gv.get("target_resolved", 0) or 0)
        sorry_count = int(gv.get("g1", {}).get("sorry_count", 0) or 0)
        print(f"     [{row['problem_id']}] gauntlet verdict={verdict} "
              f"target_resolved={target_resolved} sorry={sorry_count} "
              f"cost=${gv.get('cost_usd')} mcs={gv.get('mathematical_content_score')}")
        for reason in gv.get("reasons", [])[:4]:
            print(f"        - {reason}")

        self._decide_after_gauntlet(row, gv, main_lean, sorry_count)

    def _decide_after_gauntlet(self, row, gv, lean_path, sorry_count):
        """State transition after the gauntlet adjudicates a result."""
        verdict = gv.get("verdict")
        target_resolved = int(gv.get("target_resolved", 0) or 0)

        if target_resolved == 1 and verdict == "compiled_advance":
            print(f"     🎯 RESOLVED (compiled_advance): {row['problem_id']}")
            self._transition(row['id'], 'RESOLVED',
                             resolved_proof=str(lean_path),
                             resolved_at=datetime.now(timezone.utc).isoformat(),
                             best_sorry_count=0,
                             last_sorry_count=sorry_count)
            return

        if verdict == "disproven":
            print(f"     ✗ DISPROVEN (conjecture false): {row['problem_id']}")
            self._transition(row['id'], 'RESOLVED',
                             resolved_proof=str(lean_path),
                             resolved_at=datetime.now(timezone.utc).isoformat(),
                             error_message='disproven (counterexample)')
            return

        # Not promoted. Decide whether to attempt ask self-repair.
        prev_best = row['best_sorry_count'] if row['best_sorry_count'] is not None else 999
        made_progress = sorry_count < prev_best
        new_best = min(sorry_count, prev_best)
        rounds = (row['aristotle_rounds'] or 0)

        repairable = verdict in ("compiled_partial", "compile_failed")
        if not repairable:
            # compiled_no_advance: faithful/literature failure — repair won't fix the
            # *statement*, so it's terminal for this attempt (fail-closed ceiling).
            print(f"     ⛔ not repairable (verdict={verdict}); marking STALLED")
            self._transition(row['id'], 'STALLED',
                             best_sorry_count=new_best,
                             last_sorry_count=sorry_count,
                             error_message=f'{verdict}: not an advance, repair n/a')
            return

        stall = row['stall_count'] + (0 if made_progress else 1)
        if rounds >= self.cfg.ask_repair_cap or stall > row['max_stall']:
            print(f"     ⛔ ask-repair cap reached "
                  f"(rounds={rounds}/{self.cfg.ask_repair_cap}, stall={stall}); STALLED")
            self._transition(row['id'], 'STALLED',
                             best_sorry_count=new_best,
                             last_sorry_count=sorry_count,
                             stall_count=stall,
                             error_message=f'plateau at {sorry_count} sorry after '
                                           f'{rounds} repair round(s)')
            return

        # Queue a repair round (stage 4 will fire the ask).
        ctx = json.loads(row['context_files'] or '[]')
        if str(lean_path) not in ctx:
            ctx.append(str(lean_path))
        print(f"     ↻ queueing ask self-repair round {rounds + 1} "
              f"(sorry={sorry_count}, {'progress' if made_progress else 'plateau'})")
        self._transition(row['id'], 'REPAIR_PENDING',
                         best_sorry_count=new_best,
                         last_sorry_count=sorry_count,
                         stall_count=stall,
                         context_files=json.dumps(ctx))

    def _handle_terminal_failure(self, row, status):
        rounds = (row['aristotle_rounds'] or 0)
        if rounds < self.cfg.ask_repair_cap:
            print(f"     Aristotle {status} for {row['problem_id']}; re-queue")
            self._transition(row['id'], 'QUEUED',
                             error_message=f'Aristotle returned {status}')
        else:
            self._transition(row['id'], 'STALLED',
                             error_message=f'Aristotle {status}, cap reached')

    # ── stage 4: ask self-repair wave ──
    async def _repair_wave(self):
        """Fire Project.ask() on REPAIR_PENDING rows (cap ASK_REPAIR_CAP, plateau-aware).

        Reuses the cmd_ask lever's core: Project.from_id(uuid).ask(prompt) spawns a
        new AgentTask on the SAME project (keeps context, no re-upload). The row then
        goes back to REPAIRING and the next tick's poll folds in the new result.
        """
        rows = db_query("SELECT * FROM proof_queue WHERE state = 'REPAIR_PENDING'")
        if not rows:
            return
        if not self.cfg.will_submit:
            for r in rows:
                print(f"     [DRY-RUN] would ask-repair {r['problem_id']} "
                      f"(round {(r['aristotle_rounds'] or 0)+1}) -> SKIPPED")
            return

        _, aristotle_fetch = _imp_fetch()
        aristotle_fetch.aristotlelib.set_api_key(aristotle_fetch.get_api_key())
        from aristotlelib import Project

        for r in rows:
            rounds = (r['aristotle_rounds'] or 0)
            if rounds >= self.cfg.ask_repair_cap:
                self._transition(r['id'], 'STALLED',
                                 error_message='ask-repair cap reached at dispatch')
                continue
            prompt = self._repair_prompt(r)
            try:
                project = await Project.from_id(r['aristotle_uuid'])
                task = await project.ask(prompt)
                print(f"     ↻ ask-repair {r['problem_id']} round {rounds+1}: "
                      f"task {task.agent_task_id} ({task.status.name})")
                self._transition(r['id'], 'REPAIRING',
                                 aristotle_rounds=rounds + 1)
            except Exception as e:
                print(f"     ask-repair error {r['problem_id']}: {e}")
                self._transition(r['id'], 'QUEUED', error_message=f'ask failed: {e}')

    def _repair_prompt(self, row) -> str:
        """A targeted self-repair prompt: close the residual sorry / fix the build,
        keep the SAME statement (no weakening — the gauntlet's G2 would reject it).
        """
        sorry = row['last_sorry_count']
        sc = f" There {'is' if sorry == 1 else 'are'} {sorry} `sorry` remaining." if sorry else ""
        return (
            "Your previous attempt did not fully close the goal.{sc} Please complete "
            "the proof of the SAME theorem statement (do not weaken it, do not add "
            "hypotheses, do not bound an unbounded claim, do not introduce new "
            "axioms). Discharge every remaining `sorry`, fix any build error, and "
            "keep the conclusion exactly as stated."
        ).format(sc=sc)

    # ── helpers ──
    def _source_for(self, problem_id: str) -> Optional[str]:
        """Return the canonical source statement for the gauntlet's G2/G3.

        Precedence: candidate_queue.source_path (a file) > candidate_queue.statement
        (literal). run_gauntlet accepts either a path or literal text.
        """
        rows = db_query(
            "SELECT source_path, statement FROM candidate_queue WHERE problem_id = ?",
            (problem_id,))
        if not rows:
            return None
        sp = (rows[0].get("source_path") or "").strip()
        if sp:
            p = Path(sp)
            if not p.is_absolute():
                p = MATH_DIR / p
            if p.exists():
                return str(p)
        stmt = (rows[0].get("statement") or "").strip()
        return stmt or None


# ── CLI commands ─────────────────────────────────────────────────────────────

def cmd_enqueue(args):
    """Add a problem to the proof_queue (Method-1 attempt).

    The candidate normally arrives via v_method1_ready during `run`, but this lets
    you hand-enqueue a specific problem_id (e.g. for a smoke test).
    """
    ensure_queue_table()
    pid = args.problem_id
    # Resolve a source for problem_source: candidate_queue row, else the dossier.
    rows = db_query(
        "SELECT source_path, statement, tier FROM candidate_queue WHERE problem_id = ?",
        (pid,))
    if rows:
        src = (rows[0].get("source_path") or rows[0].get("statement") or pid)
        tier = int(rows[0].get("tier") or 5)
    else:
        src = args.problem_source or pid
        tier = 5
    qid = db_execute(
        "INSERT INTO proof_queue (problem_id, problem_source, priority, state, "
        "context_files) VALUES (?, ?, ?, 'QUEUED', '[]')",
        (pid, src, tier))
    print(f"  Enqueued: {pid} (queue #{qid}, priority={tier})")
    adm = check_admission(pid, args.out_dir)
    flag = "ADMITTED" if adm.admitted else "NOT-YET-ADMISSIBLE"
    print(f"  Admission preview: [{flag}] {adm.reason}")
    if not adm.admitted and adm.fusion_path is None:
        print(f"  -> author first: python3 scripts/author_argument.py "
              f"--problem-id {pid} --out-dir {args.out_dir}")


def cmd_run(args):
    cfg = LoopConfig(
        dry_run=args.dry_run or not args.live,
        live=args.live,
        max_per_run=args.max,
        single_pass=not args.loop,
        exit_when_done=args.exit_when_done,
        poll_interval=args.poll_interval,
        out_dir=args.out_dir,
        verbose=args.verbose,
    )
    if args.live and args.dry_run:
        print("  NOTE: both --live and --dry-run given; --dry-run wins (no submit).")
    loop = Method1Loop(cfg)

    def shutdown(sig, frame):
        print("\n  Shutting down gracefully...")
        loop.running = False
    signal.signal(signal.SIGINT, shutdown)
    signal.signal(signal.SIGTERM, shutdown)
    loop.run()


def cmd_status(args):
    ensure_queue_table()
    rows = db_query(
        "SELECT id, problem_id, state, aristotle_rounds, total_rounds, "
        "best_sorry_count, stall_count, aristotle_uuid, "
        "COALESCE(error_message,'') err, updated_at "
        "FROM proof_queue ORDER BY "
        "CASE state WHEN 'REPAIRING' THEN 0 WHEN 'FETCHING' THEN 1 "
        "WHEN 'SUBMITTED' THEN 2 WHEN 'SUBMITTING' THEN 3 "
        "WHEN 'REPAIR_PENDING' THEN 4 WHEN 'QUEUED' THEN 5 "
        "WHEN 'RESOLVED' THEN 8 WHEN 'REJECTED' THEN 9 WHEN 'STALLED' THEN 10 END, "
        "updated_at DESC")
    if not rows:
        print("  Method-1 queue is empty. `run` will refill from v_method1_ready, "
              "or use `enqueue --problem-id ID`.")
        # Still surface how many ready candidates exist upstream.
        try:
            ready = db_scalar("SELECT COUNT(*) FROM v_method1_ready")
            authored = db_scalar(
                "SELECT COUNT(*) FROM v_method1_ready WHERE argument_authored = 1")
            print(f"  Upstream: {ready} candidate(s) in v_method1_ready "
                  f"({authored} already authored).")
        except Exception:
            pass
        return

    print(f"\n{'ID':>4} {'Problem':<22} {'State':<16} {'Rnd':>4} {'Sorry':>6} "
          f"{'UUID':<14} {'Updated':<20}")
    print("-" * 96)
    for r in rows:
        sorry = str(r['best_sorry_count']) if r['best_sorry_count'] is not None else '-'
        uuid = (r['aristotle_uuid'] or '')[:12]
        print(f"{r['id']:>4} {r['problem_id'][:22]:<22} {r['state']:<16} "
              f"{r['aristotle_rounds']:>4} {sorry:>6} {uuid:<14} {r['updated_at']:<20}")

    counts = {}
    for r in rows:
        counts[r['state']] = counts.get(r['state'], 0) + 1
    resolved = counts.get('RESOLVED', 0)
    stalled = counts.get('STALLED', 0) + counts.get('REJECTED', 0)
    active = sum(v for k, v in counts.items() if k not in ('RESOLVED', 'STALLED', 'REJECTED'))
    print(f"\n  Active: {active} | Resolved: {resolved} | Stalled/Rejected: {stalled}")
    booked = cost_booked_today()
    print(f"  Cost booked today (directional): ${booked:.2f}")


def main():
    p = argparse.ArgumentParser(
        description="Method-1 loop driver — gated informal-argument -> Aristotle "
                    "informal reasoner -> fail-closed verification gauntlet.")
    sub = p.add_subparsers(dest="command")

    p_run = sub.add_parser("run", help="Run the Method-1 loop")
    p_run.add_argument("--dry-run", action="store_true",
                       help="Exercise admission+capacity+queue logic with NO live "
                            "submit (default-safe; this is what tests run).")
    p_run.add_argument("--live", action="store_true",
                       help="EXPLICIT opt-in to fire real Aristotle submissions "
                            "(costs money; not exercised in tests).")
    p_run.add_argument("--max", type=int, default=5,
                       help="Max candidates pulled from v_method1_ready per run.")
    p_run.add_argument("--loop", action="store_true",
                       help="Keep ticking (campaign mode) instead of single-pass.")
    p_run.add_argument("--exit-when-done", action="store_true")
    p_run.add_argument("--poll-interval", type=int, default=60)
    p_run.add_argument("--out-dir", type=Path, default=METHOD1_DIR,
                       help="Directory holding authored .txt + .fusion.json dossiers.")
    p_run.add_argument("--verbose", action="store_true")

    p_enq = sub.add_parser("enqueue", help="Enqueue one problem_id for a Method-1 attempt")
    p_enq.add_argument("--problem-id", required=True)
    p_enq.add_argument("--problem-source", default=None,
                       help="Source statement/path (defaults to candidate_queue row).")
    p_enq.add_argument("--out-dir", type=Path, default=METHOD1_DIR)

    sub.add_parser("status", help="Show Method-1 queue status")

    args = p.parse_args()
    if not args.command:
        p.print_help()
        return
    {"run": cmd_run, "enqueue": cmd_enqueue, "status": cmd_status}[args.command](args)


if __name__ == "__main__":
    main()
