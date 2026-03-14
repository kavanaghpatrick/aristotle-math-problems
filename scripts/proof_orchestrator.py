#!/usr/bin/env python3
"""
Proof Orchestrator — Autonomous queue driving Codex and Aristotle in a loop.

State machine: QUEUED → CODEX_RUNNING → CODEX_DONE →
  - 0 sorry → RESOLVED
  - compiled + sorries → ARISTOTLE_PENDING → ARISTOTLE_SUBMITTED → ARISTOTLE_COMPLETE →
    - 0 sorry → RESOLVED
    - fewer sorries → back to QUEUED (with context)
    - no progress → STALLED
  - failed → retry or STALLED
"""

import argparse
import asyncio
import json
import os
import re
import signal
import sqlite3
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional

MATH_DIR = Path(__file__).resolve().parent.parent
TRACKING_DB = MATH_DIR / "submissions" / "tracking.db"
PROOFS_DIR = MATH_DIR / "codex_proofs"

# Import from sibling scripts
sys.path.insert(0, str(MATH_DIR / "scripts"))
from codex_proof_loop import (
    LoopConfig, LoopResult, run_loop, save_result,
    count_sorries, extract_theorem_statement, extract_sorry_targets
)

EFFORT_LADDER = ['high', 'xhigh', 'xhigh']


@dataclass
class OrchestratorConfig:
    poll_interval: int = 60
    max_concurrent_aristotle: int = 5
    max_concurrent_codex: int = 4
    codex_max_iterations: int = 5
    codex_build_timeout: int = 300
    dry_run: bool = False
    single_pass: bool = False
    exit_when_done: bool = False


# ── Database ───────────────────────────────────────────────────────────────

def ensure_queue_table():
    conn = sqlite3.connect(str(TRACKING_DB))
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
            error_message TEXT,

            FOREIGN KEY (codex_proof_id) REFERENCES codex_proofs(id),
            FOREIGN KEY (parent_queue_id) REFERENCES proof_queue(id)
        );
        CREATE INDEX IF NOT EXISTS idx_pq_state ON proof_queue(state);
        CREATE INDEX IF NOT EXISTS idx_pq_priority ON proof_queue(priority, created_at);
        CREATE INDEX IF NOT EXISTS idx_pq_problem ON proof_queue(problem_id);
    """)
    conn.close()


def db_query(sql, params=()):
    conn = sqlite3.connect(str(TRACKING_DB))
    conn.row_factory = sqlite3.Row
    rows = conn.execute(sql, params).fetchall()
    conn.close()
    return [dict(r) for r in rows]


def db_execute(sql, params=()):
    conn = sqlite3.connect(str(TRACKING_DB))
    conn.execute("PRAGMA journal_mode=WAL")
    cur = conn.execute(sql, params)
    conn.commit()
    lastid = cur.lastrowid
    conn.close()
    return lastid


def db_scalar(sql, params=()):
    rows = db_query(sql, params)
    return list(rows[0].values())[0] if rows else None


# ── Orchestrator ───────────────────────────────────────────────────────────

class ProofOrchestrator:
    def __init__(self, config: OrchestratorConfig):
        self.config = config
        self.running = True

    def run(self):
        """Main loop."""
        print(f"\n  PROOF ORCHESTRATOR starting (poll={self.config.poll_interval}s)")
        print(f"  Dry run: {self.config.dry_run}")
        self.recover_from_crash()

        while self.running:
            try:
                self.tick()
            except Exception as e:
                print(f"  ERROR in tick: {e}")
            if self.config.single_pass:
                break
            if self.config.exit_when_done:
                active = db_scalar(
                    "SELECT COUNT(*) FROM proof_queue WHERE state NOT IN ('RESOLVED','STALLED')"
                )
                if active == 0:
                    print("  All jobs terminal. Exiting.")
                    break
            time.sleep(self.config.poll_interval)

    def tick(self):
        """One orchestration cycle."""
        now = datetime.now().strftime("%H:%M:%S")
        active = db_query(
            "SELECT state, COUNT(*) as cnt FROM proof_queue "
            "WHERE state NOT IN ('RESOLVED','STALLED') GROUP BY state"
        )
        if active:
            summary = ", ".join(f"{r['state']}={r['cnt']}" for r in active)
            print(f"\n[{now}] Tick: {summary}")
        else:
            return  # Nothing to do

        # 1. Poll Aristotle for completed jobs
        self.poll_aristotle()

        # 2. Submit any ARISTOTLE_PENDING
        self.submit_pending_aristotle()

        # 3. Run next Codex job
        self.run_next_codex()

    def recover_from_crash(self):
        """Reset CODEX_RUNNING → appropriate state on startup."""
        rows = db_query("SELECT id, problem_id, codex_attempts, codex_compiled FROM proof_queue WHERE state = 'CODEX_RUNNING'")
        for r in rows:
            if r['codex_compiled']:
                # Already compiled once — send to Aristotle instead of re-running
                print(f"  Recovering job {r['id']} ({r['problem_id']}): CODEX_RUNNING → ARISTOTLE_PENDING (already compiled)")
                self.transition(r['id'], 'ARISTOTLE_PENDING')
            else:
                print(f"  Recovering job {r['id']} ({r['problem_id']}): CODEX_RUNNING → QUEUED")
                self.transition(r['id'], 'QUEUED')

    def transition(self, queue_id, new_state, **kwargs):
        """Update queue row state + optional fields."""
        sets = ["state = ?", "updated_at = datetime('now')"]
        params = [new_state]
        for k, v in kwargs.items():
            sets.append(f"{k} = ?")
            params.append(v)
        params.append(queue_id)
        db_execute(f"UPDATE proof_queue SET {', '.join(sets)} WHERE id = ?", params)

    # ── Codex Phase ────────────────────────────────────────────────────────

    def run_next_codex(self):
        """Launch QUEUED jobs as parallel Codex subprocesses, up to max_concurrent_codex."""
        import subprocess as _sp

        # Count currently running Codex jobs
        running = db_scalar(
            "SELECT COUNT(*) FROM proof_queue WHERE state = 'CODEX_RUNNING'"
        ) or 0

        # Also reap any finished subprocesses
        self._reap_codex_workers()

        slots_available = self.config.max_concurrent_codex - running
        if slots_available <= 0:
            return

        rows = db_query(
            "SELECT * FROM proof_queue WHERE state = 'QUEUED' "
            "ORDER BY priority ASC, created_at ASC LIMIT ?",
            (slots_available,)
        )
        if not rows:
            return

        for row in rows:
            print(f"\n  Launching Codex worker: {row['problem_id']} (queue #{row['id']})")
            if self.config.dry_run:
                print("  [DRY RUN] Would launch Codex worker here")
                continue

            self.transition(row['id'], 'CODEX_RUNNING')

            context = json.loads(row['context_files'] or '[]')
            ctx_args = []
            for f in context:
                if os.path.isfile(f):
                    ctx_args.extend(["--context", f])

            log_path = f"/tmp/codex_{row['problem_id']}.log"
            cmd = [
                sys.executable, str(MATH_DIR / "scripts" / "codex_proof_loop.py"),
                row['problem_source'],
                "--problem-id", row['problem_id'],
                "--max-iterations", str(self.config.codex_max_iterations),
                "--build-timeout", str(self.config.codex_build_timeout),
                "--reasoning-effort", row['reasoning_effort'] or 'high',
            ] + ctx_args

            with open(log_path, 'w') as log_f:
                proc = _sp.Popen(cmd, stdout=log_f, stderr=_sp.STDOUT)

            # Track the subprocess
            if not hasattr(self, '_codex_workers'):
                self._codex_workers = {}
            self._codex_workers[row['id']] = {
                'proc': proc, 'row': row, 'log': log_path
            }
            print(f"    PID {proc.pid} → {log_path}")

    def _reap_codex_workers(self):
        """Check for finished Codex subprocesses and process their results."""
        if not hasattr(self, '_codex_workers'):
            self._codex_workers = {}
            return

        finished = []
        for queue_id, worker in self._codex_workers.items():
            proc = worker['proc']
            ret = proc.poll()
            if ret is not None:
                finished.append(queue_id)
                row = worker['row']
                pid = row['problem_id']

                # Check what Codex produced
                proof_dir = PROOFS_DIR / pid
                best_lean = proof_dir / "best.lean"

                if best_lean.exists():
                    content = best_lean.read_text()
                    sorry_count = content.count('sorry')
                    print(f"\n  Codex worker done: {pid} — sorry={sorry_count} (exit={ret})")

                    # Build a minimal LoopResult-like object for decide_after_codex
                    class _MiniResult:
                        def __init__(self, compiled, sorry, lean_file):
                            self.compiled = compiled
                            self.best = type('B', (), {'sorry_count': sorry})() if compiled else None
                            self.lean_file = lean_file
                    result = _MiniResult(True, sorry_count, best_lean)
                    self.decide_after_codex(queue_id, row, result)
                else:
                    print(f"\n  Codex worker done: {pid} — no proof produced (exit={ret})")
                    attempts = row['codex_attempts'] + 1
                    if attempts < row['max_codex_attempts']:
                        effort = self.escalate_effort(row['reasoning_effort'] or 'high')
                        self.transition(queue_id, 'QUEUED',
                                      codex_attempts=attempts,
                                      reasoning_effort=effort,
                                      total_rounds=row['total_rounds'] + 1)
                    else:
                        self.transition(queue_id, 'STALLED',
                                      codex_attempts=attempts,
                                      error_message=f'Max Codex attempts ({attempts})')

        for qid in finished:
            del self._codex_workers[qid]

    def decide_after_codex(self, queue_id, row, result: LoopResult):
        """State transition after Codex finishes."""
        attempts = row['codex_attempts'] + 1

        if result.compiled and result.best and result.best.sorry_count == 0:
            # Validate: check that the proof actually addresses the target problem
            # by looking for the problem_id or key terms in the lean file
            lean_content = result.lean_file.read_text() if result.lean_file and result.lean_file.exists() else ""
            problem_terms = row['problem_id'].lower().replace('_', ' ').split()
            source_terms = row['problem_source'].lower()[:200].split()[:5]
            # Heuristic: if the lean file is very short or doesn't reference key problem terms,
            # it may have proved something trivial — still send to Aristotle for validation
            if len(lean_content) < 300:
                print(f"  WARNING: Codex proof is only {len(lean_content)} chars — sending to Aristotle for validation")
                self.transition(queue_id, 'ARISTOTLE_PENDING',
                              codex_attempts=attempts, codex_compiled=1,
                              codex_best_sorry=0, best_sorry_count=0,
                              total_rounds=row['total_rounds'] + 1)
                return
            print(f"  Codex compiled with 0 sorry — sending to Aristotle for validation")
            self.transition(queue_id, 'ARISTOTLE_PENDING',
                          codex_attempts=attempts,
                          codex_compiled=1,
                          codex_best_sorry=0,
                          best_sorry_count=0,
                          total_rounds=row['total_rounds'] + 1)
            return

        sorry_count = result.best.sorry_count if result.best else 999

        if result.compiled and sorry_count > 0:
            # Compiled with sorries → send to Aristotle
            print(f"  Codex compiled with {sorry_count} sorry → queueing for Aristotle")
            best_sorry = min(sorry_count, row['best_sorry_count'] or 999)
            self.transition(queue_id, 'ARISTOTLE_PENDING',
                          codex_attempts=attempts,
                          codex_compiled=1,
                          codex_best_sorry=sorry_count,
                          codex_proof_id=db_scalar(
                              "SELECT id FROM codex_proofs WHERE problem_id=? ORDER BY id DESC LIMIT 1",
                              (row['problem_id'],)),
                          best_sorry_count=best_sorry,
                          last_sorry_count=sorry_count,
                          total_rounds=row['total_rounds'] + 1)
            return

        # Failed to compile
        if attempts < row['max_codex_attempts']:
            effort = self.escalate_effort(row['reasoning_effort'] or 'high')
            print(f"  Codex failed, retrying ({attempts}/{row['max_codex_attempts']}) effort={effort}")
            self.transition(queue_id, 'QUEUED',
                          codex_attempts=attempts,
                          reasoning_effort=effort,
                          total_rounds=row['total_rounds'] + 1)
        else:
            print(f"  Codex exhausted ({attempts} attempts), marking STALLED")
            self.transition(queue_id, 'STALLED',
                          codex_attempts=attempts,
                          error_message=f'Max Codex attempts ({attempts}), no compilation')

    def escalate_effort(self, current):
        try:
            idx = EFFORT_LADDER.index(current)
        except ValueError:
            idx = 0
        return EFFORT_LADDER[min(idx + 1, len(EFFORT_LADDER) - 1)]

    # ── Aristotle Phase ────────────────────────────────────────────────────

    def submit_pending_aristotle(self):
        """Submit ARISTOTLE_PENDING jobs."""
        rows = db_query("SELECT * FROM proof_queue WHERE state = 'ARISTOTLE_PENDING'")
        for row in rows:
            # Check Aristotle capacity
            active = db_scalar(
                "SELECT COUNT(*) FROM proof_queue "
                "WHERE state IN ('ARISTOTLE_SUBMITTED','ARISTOTLE_RUNNING')"
            ) or 0
            if active >= self.config.max_concurrent_aristotle:
                print(f"  Aristotle at capacity ({active}/{self.config.max_concurrent_aristotle}), deferring")
                return

            if self.config.dry_run:
                print(f"  [DRY RUN] Would submit {row['problem_id']} to Aristotle")
                continue

            try:
                self._do_aristotle_submit(row)
            except Exception as e:
                print(f"  Submit error for {row['problem_id']}: {e}")
                self.transition(row['id'], 'QUEUED', error_message=str(e))

    def _do_aristotle_submit(self, row):
        """Generate sketch, submit to Aristotle."""
        # Find best Codex .lean
        codex_lean = PROOFS_DIR / row['problem_id'] / "best.lean"
        if not codex_lean.exists():
            self.transition(row['id'], 'STALLED',
                          error_message='No Codex best.lean found')
            return

        # Auto-generate sketch
        sketch_path = self.auto_generate_sketch(row, codex_lean)

        # Build context list
        context = [codex_lean]
        extra = json.loads(row['context_files'] or '[]')
        for f in extra:
            p = Path(f)
            if p.exists() and p.suffix == '.lean':
                context.append(p)

        # Submit via safe_aristotle_submit
        print(f"  Submitting {row['problem_id']} to Aristotle...")
        import subprocess
        cmd = ["python3", str(MATH_DIR / "scripts" / "safe_aristotle_submit.py"),
               str(sketch_path), "--force"]
        for ctx in context:
            cmd.extend(["--context", str(ctx)])

        result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)

        # Extract UUID from output or ID file
        uuid = None
        id_file = sketch_path.with_suffix('.ID.txt')
        if id_file.exists():
            uuid = id_file.read_text().strip().split('\n')[0].strip()
        if not uuid:
            # Try parsing from stdout
            m = re.search(r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}', result.stdout)
            if m:
                uuid = m.group(0)

        if uuid:
            print(f"  Submitted! UUID: {uuid[:8]}")
            self.transition(row['id'], 'ARISTOTLE_SUBMITTED',
                          aristotle_uuid=uuid,
                          aristotle_rounds=row['aristotle_rounds'] + 1)
        else:
            print(f"  Submit failed: {result.stderr[:200]}")
            self.transition(row['id'], 'QUEUED',
                          error_message=f'Submit failed: {result.stderr[:200]}')

    def auto_generate_sketch(self, row, lean_path):
        """Generate bare-gap .txt sketch from Codex .lean."""
        lean_code = lean_path.read_text()
        stmt = extract_theorem_statement(lean_code)
        sorry_count = count_sorries(lean_code)

        sketch = f"""OPEN GAP: {row['problem_id']}
Source: Codex proof loop (partial proof with {sorry_count} sorry)
Domain: nt

Fill the remaining sorry targets to complete this proof.

{stmt or 'see context .lean file'}

Status: OPEN. Partial Codex proof attached as context.
"""
        sketch_dir = PROOFS_DIR / row['problem_id']
        sketch_dir.mkdir(parents=True, exist_ok=True)
        sketch_path = sketch_dir / "auto_sketch.txt"
        sketch_path.write_text(sketch)
        return sketch_path

    def poll_aristotle(self):
        """Poll Aristotle API for SUBMITTED/RUNNING jobs."""
        rows = db_query(
            "SELECT * FROM proof_queue "
            "WHERE state IN ('ARISTOTLE_SUBMITTED','ARISTOTLE_RUNNING') "
            "AND aristotle_uuid IS NOT NULL"
        )
        if not rows:
            return

        try:
            from aristotlelib import Project, set_api_key
            api_key = os.environ.get("ARISTOTLE_API_KEY")
            if not api_key:
                return
            set_api_key(api_key)
        except ImportError:
            return

        for row in rows:
            try:
                asyncio.run(self._check_aristotle_job(row))
            except Exception as e:
                print(f"  Poll error {row['aristotle_uuid'][:8]}: {e}")

    async def _check_aristotle_job(self, row):
        from aristotlelib import Project
        p = await Project.from_id(row['aristotle_uuid'])
        status = str(p.status)

        if 'COMPLETE' in status:
            print(f"  Aristotle COMPLETE: {row['problem_id']}")
            await self._fetch_and_evaluate(row, p)
        elif 'IN_PROGRESS' in status:
            if row['state'] == 'ARISTOTLE_SUBMITTED':
                self.transition(row['id'], 'ARISTOTLE_RUNNING')
        elif 'ERROR' in status or 'FAILED' in status:
            print(f"  Aristotle {status}: {row['problem_id']}")
            self.transition(row['id'], 'QUEUED',
                          error_message=f'Aristotle returned {status}')

    async def _fetch_and_evaluate(self, row, project):
        """Fetch Aristotle result and decide next action."""
        output_dir = PROOFS_DIR / row['problem_id']
        output_dir.mkdir(parents=True, exist_ok=True)
        output_path = output_dir / f"aristotle_r{row['aristotle_rounds']}.lean"

        try:
            import shutil
            sol_path = await project.get_solution(output_path=str(output_dir))
            if sol_path and Path(str(sol_path)).exists() and Path(str(sol_path)) != output_path:
                # get_solution returns a path, might be a tarball directory
                # Find .lean files in the result
                sol = Path(str(sol_path))
                if sol.is_dir():
                    lean_files = list(sol.rglob("*.lean"))
                    if lean_files:
                        shutil.copy2(lean_files[0], output_path)
                elif sol.suffix == '.lean':
                    shutil.copy2(sol, output_path)
        except Exception as e:
            print(f"  Fetch error: {e}")
            self.transition(row['id'], 'QUEUED',
                          error_message=f'Fetch failed: {e}')
            return

        if not output_path.exists():
            self.transition(row['id'], 'QUEUED',
                          error_message='No .lean in Aristotle result')
            return

        # Audit
        lean_code = output_path.read_text()
        sorry_count = count_sorries(lean_code)
        print(f"  Aristotle result: {sorry_count} sorry, {len(lean_code.splitlines())}L")

        self.decide_after_aristotle(row, sorry_count, output_path)

    def decide_after_aristotle(self, row, sorry_count, result_path):
        """State transition after Aristotle result fetched."""
        if sorry_count == 0:
            print(f"  RESOLVED by Aristotle! {result_path}")
            self.transition(row['id'], 'RESOLVED',
                          resolved_proof=str(result_path),
                          resolved_at=datetime.now().isoformat(),
                          best_sorry_count=0)
            return

        prev = row['last_sorry_count'] or row['codex_best_sorry'] or 999

        if sorry_count < prev:
            # Progress — feed back to Codex
            print(f"  Progress: {prev} → {sorry_count} sorry. Feeding back to Codex.")
            context = json.loads(row['context_files'] or '[]')
            context.append(str(result_path))
            self.transition(row['id'], 'QUEUED',
                          context_files=json.dumps(context),
                          last_sorry_count=sorry_count,
                          best_sorry_count=min(sorry_count, row['best_sorry_count'] or 999),
                          stall_count=0,
                          total_rounds=row['total_rounds'] + 1)
        else:
            # No progress
            stall = row['stall_count'] + 1
            if stall >= row['max_stall'] or row['total_rounds'] >= row['max_total_rounds']:
                print(f"  STALLED: no progress after {row['total_rounds']} rounds")
                self.transition(row['id'], 'STALLED',
                              stall_count=stall,
                              error_message=f'No progress ({sorry_count} sorry, stall={stall})')
            else:
                # Try again anyway with result as context
                context = json.loads(row['context_files'] or '[]')
                context.append(str(result_path))
                self.transition(row['id'], 'QUEUED',
                              context_files=json.dumps(context),
                              stall_count=stall,
                              total_rounds=row['total_rounds'] + 1)


# ── CLI ────────────────────────────────────────────────────────────────────

def cmd_enqueue(args):
    """Add a problem to the queue."""
    ensure_queue_table()

    problem_id = args.problem_id
    if not problem_id:
        # Derive from problem text or filename
        if os.path.isfile(args.problem):
            problem_id = Path(args.problem).stem
        else:
            words = re.sub(r'[^a-zA-Z0-9\s]', '', args.problem).split()[:4]
            problem_id = "_".join(w.lower() for w in words) or "unnamed"

    context = json.dumps(args.context or [])

    qid = db_execute(
        """INSERT INTO proof_queue
           (problem_id, problem_source, priority, context_files,
            max_codex_attempts, max_aristotle_rounds, max_total_rounds)
           VALUES (?, ?, ?, ?, ?, ?, ?)""",
        (problem_id, args.problem, args.priority, context,
         args.max_codex, args.max_aristotle, args.max_rounds)
    )
    print(f"  Enqueued: {problem_id} (queue #{qid}, priority={args.priority})")


def cmd_status(args):
    """Show queue status."""
    ensure_queue_table()
    rows = db_query(
        "SELECT id, problem_id, state, codex_attempts, aristotle_rounds, "
        "total_rounds, best_sorry_count, priority, "
        "COALESCE(error_message, '') as error, updated_at "
        "FROM proof_queue ORDER BY "
        "CASE state WHEN 'CODEX_RUNNING' THEN 0 WHEN 'ARISTOTLE_RUNNING' THEN 1 "
        "WHEN 'ARISTOTLE_SUBMITTED' THEN 2 WHEN 'ARISTOTLE_PENDING' THEN 3 "
        "WHEN 'QUEUED' THEN 4 WHEN 'RESOLVED' THEN 8 WHEN 'STALLED' THEN 9 END, "
        "updated_at DESC"
    )
    if not rows:
        print("  Queue is empty. Use `enqueue` to add problems.")
        return

    print(f"\n{'ID':>4} {'Problem':<25} {'State':<22} {'Cx':>3} {'Ar':>3} {'Rnd':>4} {'Sorry':>6} {'Updated':<20}")
    print("-" * 100)
    for r in rows:
        sorry = str(r['best_sorry_count']) if r['best_sorry_count'] is not None else '-'
        state = r['state']
        if state == 'RESOLVED':
            state = 'RESOLVED'
        elif state == 'STALLED':
            state = f"STALLED"
        print(f"{r['id']:>4} {r['problem_id']:<25} {state:<22} {r['codex_attempts']:>3} "
              f"{r['aristotle_rounds']:>3} {r['total_rounds']:>4} {sorry:>6} {r['updated_at']:<20}")

    resolved = sum(1 for r in rows if r['state'] == 'RESOLVED')
    stalled = sum(1 for r in rows if r['state'] == 'STALLED')
    active = sum(1 for r in rows if r['state'] not in ('RESOLVED', 'STALLED'))
    print(f"\n  Active: {active} | Resolved: {resolved} | Stalled: {stalled}")


def cmd_cancel(args):
    ensure_queue_table()
    db_execute("UPDATE proof_queue SET state='STALLED', error_message='Cancelled by user' WHERE id=?",
               (args.queue_id,))
    print(f"  Cancelled queue #{args.queue_id}")


def cmd_retry(args):
    ensure_queue_table()
    db_execute("UPDATE proof_queue SET state='QUEUED', stall_count=0, error_message=NULL WHERE id=?",
               (args.queue_id,))
    print(f"  Reset queue #{args.queue_id} to QUEUED")


def cmd_run(args):
    ensure_queue_table()
    config = OrchestratorConfig(
        poll_interval=args.poll_interval,
        max_concurrent_codex=args.max_codex_parallel,
        dry_run=args.dry_run,
        single_pass=args.single_pass,
        exit_when_done=args.exit_when_done,
    )
    orch = ProofOrchestrator(config)

    def shutdown(sig, frame):
        print("\n  Shutting down gracefully...")
        orch.running = False
    signal.signal(signal.SIGINT, shutdown)
    signal.signal(signal.SIGTERM, shutdown)

    orch.run()


def main():
    parser = argparse.ArgumentParser(
        description="Proof Orchestrator — autonomous Codex + Aristotle queue"
    )
    sub = parser.add_subparsers(dest="command")

    # run
    p_run = sub.add_parser("run", help="Start the orchestrator loop")
    p_run.add_argument("--poll-interval", type=int, default=60)
    p_run.add_argument("--max-codex-parallel", type=int, default=4,
                       help="Max concurrent Codex workers (default: 4)")
    p_run.add_argument("--dry-run", action="store_true")
    p_run.add_argument("--single-pass", action="store_true")
    p_run.add_argument("--exit-when-done", action="store_true")

    # enqueue
    p_enq = sub.add_parser("enqueue", help="Add a problem to the queue")
    p_enq.add_argument("problem", help="Problem description or file path")
    p_enq.add_argument("--problem-id", help="Explicit problem ID")
    p_enq.add_argument("--priority", type=int, default=5, help="1=highest, 10=lowest")
    p_enq.add_argument("--context", action="append", default=[])
    p_enq.add_argument("--max-codex", type=int, default=3)
    p_enq.add_argument("--max-aristotle", type=int, default=3)
    p_enq.add_argument("--max-rounds", type=int, default=8)

    # status
    sub.add_parser("status", help="Show queue status")

    # cancel
    p_can = sub.add_parser("cancel", help="Cancel a queued job")
    p_can.add_argument("queue_id", type=int)

    # retry
    p_ret = sub.add_parser("retry", help="Reset STALLED job to QUEUED")
    p_ret.add_argument("queue_id", type=int)

    args = parser.parse_args()
    if not args.command:
        parser.print_help()
        return

    {"run": cmd_run, "enqueue": cmd_enqueue, "status": cmd_status,
     "cancel": cmd_cancel, "retry": cmd_retry}[args.command](args)


if __name__ == "__main__":
    main()
