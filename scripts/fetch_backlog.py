#!/usr/bin/env python3
"""
DB-driven status sweep + fetch for backlog jobs that the slot-file-based
aristotle_fetch.py is blind to (e.g. the yolo_* submissions tracked only by
uuid in submissions/tracking.db).

Usage:
    python3 scripts/fetch_backlog.py status [filter]   # sweep status, no download
    python3 scripts/fetch_backlog.py fetch  [filter]   # download COMPLETE ones, audit, update DB

[filter] is an optional substring matched against filename (e.g. 938).
"""
import asyncio
import sqlite3
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import aristotlelib  # noqa: E402
from aristotle_fetch import check_status, fetch_result, audit_file, update_db, get_api_key  # noqa: E402

DB = Path("submissions/tracking.db")
OUT = Path("submissions/yolo_results")
OUT.mkdir(parents=True, exist_ok=True)


def load_rows(filt: str | None):
    con = sqlite3.connect(DB)
    q = ("SELECT id, filename, uuid, problem_id FROM submissions "
         "WHERE status='submitted' AND uuid IS NOT NULL AND uuid!=''")
    if filt:
        q += f" AND filename LIKE '%{filt}%'"
    q += " ORDER BY id DESC"
    rows = con.execute(q).fetchall()
    con.close()
    return rows


async def sweep(rows):
    sem = asyncio.Semaphore(3)

    async def one(r):
        # Retry on transient ERROR (API flakes under concurrency).
        for attempt in range(4):
            async with sem:
                st = await check_status(r[2])
            if st["status"] != "ERROR":
                return (r, st)
            await asyncio.sleep(1.5 * (attempt + 1))
        return (r, st)

    return await asyncio.gather(*[one(r) for r in rows])


def cmd_status(rows):
    results = asyncio.run(sweep(rows))
    tally = Counter()
    ready = []
    for (rid, fn, uuid, pid), st in sorted(results, key=lambda x: x[0][0], reverse=True):
        s = st["status"]
        tally[s] += 1
        pct = f" {st['percent']}%" if st.get("percent") is not None else ""
        flag = ""
        if s in ("COMPLETE", "COMPLETE_WITH_ERRORS"):
            ready.append((rid, fn, uuid))
            flag = "  <-- READY"
        print(f"  {rid:<5} {s:<22}{pct:<6} {fn[:42]:<42} {uuid[:13]}{flag}")
    print("\n=== STATUS TALLY ===")
    for s, n in tally.most_common():
        print(f"  {s:<24} {n}")
    print(f"\n  {len(ready)} ready to fetch. Run: python3 scripts/fetch_backlog.py fetch")
    return ready


def _extract_and_find_lean(tar_path: Path, dest: Path):
    """Extract the Aristotle tar.gz; return (main_lean_path, summary_path)."""
    import tarfile
    dest.mkdir(parents=True, exist_ok=True)
    with tarfile.open(tar_path, "r:gz") as tar:
        tar.extractall(dest)
    leans = list(dest.rglob("Main.lean")) or list(dest.rglob("*.lean"))
    # Prefer the RequestProject/Main.lean (the actual proof file)
    leans = [p for p in leans if "lakefile" not in p.name.lower()]
    main_lean = max(leans, key=lambda p: p.stat().st_size) if leans else None
    summaries = list(dest.rglob("ARISTOTLE_SUMMARY.md"))
    return main_lean, (summaries[0] if summaries else None)


def cmd_fetch(rows):
    fetched = 0
    verdicts = Counter()
    results = asyncio.run(sweep(rows))
    for (rid, fn, uuid, pid), st in sorted(results, key=lambda x: x[0][0]):
        if st["status"] not in ("COMPLETE", "COMPLETE_WITH_ERRORS"):
            continue
        tar_path = OUT / f"{fn}.tar.gz"
        res = asyncio.run(_dl(uuid, tar_path))
        if not (res and tar_path.exists()):
            print(f"  [{rid}] {fn}: download FAILED")
            continue
        try:
            main_lean, summary = _extract_and_find_lean(tar_path, OUT / f"{fn}_extracted")
        except Exception as e:
            print(f"  [{rid}] {fn}: extract FAILED ({e})")
            continue
        if not main_lean:
            print(f"  [{rid}] {fn}: no .lean found in archive")
            continue
        audit = audit_file(main_lean)
        v = audit["verdict"]
        verdicts[v] += 1
        fetched += 1
        # G4 fix (2026-06-10): forward the row's problem_id so update_db can
        # resolve source_conjecture (candidate_queue) and the gauntlet can run
        # G2/G3 instead of "structural-only, never advance" (row 1345).
        update_db(rid, uuid, audit, str(main_lean), task=fn, problem_id=pid)
        print(f"  [{rid}] {fn[:38]:<38} {v:<20} sorry={audit['sorry']} ax={audit['axioms']} lines={audit['lines']}")
    print(f"\n=== FETCHED {fetched} ===")
    for v, n in verdicts.most_common():
        print(f"  {v:<24} {n}")


async def _dl(uuid, out_path):
    return await fetch_result(uuid, out_path)


def main():
    aristotlelib.set_api_key(get_api_key())
    mode = sys.argv[1] if len(sys.argv) > 1 else "status"
    filt = sys.argv[2] if len(sys.argv) > 2 else None
    rows = load_rows(filt)
    print(f"Backlog rows matching filter={filt!r}: {len(rows)}\n")
    if not rows:
        return
    if mode == "status":
        cmd_status(rows)
    elif mode == "fetch":
        cmd_fetch(rows)
    else:
        print(f"Unknown mode: {mode}")


if __name__ == "__main__":
    main()
