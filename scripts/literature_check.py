#!/usr/bin/env python3
"""
literature_check.py — Bloom-debunker discipline as code.

Verifies whether a problem (typically an Erdős problem) has already been
closed in the literature or by another AI team before we waste Aristotle
compute on it.

Sources consulted, in order:
  1. teorth AI-contributions wiki (the gold standard for AI closures)
  2. erdosproblems.com per-problem page (Bloom-curated status indicator)
  3. arxiv recent papers (2024-2026) matching the problem keywords
  4. Local `mk failed <keyword>` for prior project history

Outputs a JSON report with:
  - status: AI_CLOSED | RECENTLY_SOLVED | AMBIGUOUS | POSSIBLY_SOLVED | CLEAR | UNKNOWN
  - citations: list of {source, url, evidence}
  - cache_age_days

Cache: submissions/literature_cache/<problem_id>.json with 7-day TTL.

Status semantics:
  AI_CLOSED         — full AI solution recorded in the wiki (section 1(a)/1(b)/1(c))
  RECENTLY_SOLVED   — erdosproblems.com marks the problem solved
  AMBIGUOUS         — partial / unverified AI work, or literature partial result
  POSSIBLY_SOLVED   — appears in wiki only via literature-search or rewriting tag
  CLEAR             — none of the above; safe to submit
  UNKNOWN           — cannot determine (e.g. problem isn't on erdosproblems.com)

CLI:
  python3 scripts/literature_check.py erdos_728
  python3 scripts/literature_check.py submissions/sketches/slot999_erdos_672.txt
  python3 scripts/literature_check.py --backfill   # process the kill-list

API (importable):
  check_literature(problem_id: str, *, use_cache: bool = True) -> dict
  status_for_sketch(sketch_path: Path) -> dict
"""
from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
PROJECT_ROOT = Path(__file__).resolve().parent.parent
CACHE_DIR = PROJECT_ROOT / "submissions" / "literature_cache"
REGISTRY_CSV = PROJECT_ROOT / "analysis" / "open_problems_registry_may30.csv"
KILL_LIST_CSV = PROJECT_ROOT / "analysis" / "literature_kill_list.csv"

CACHE_TTL_SECONDS = 7 * 24 * 3600  # 7 days

WIKI_URL = "https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems"
ERDOSPROBLEMS_BASE = "https://www.erdosproblems.com"

USER_AGENT = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
)

# ---------------------------------------------------------------------------
# Wiki snapshot (2026-05-30, manually verified against
# https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdős-problems)
#
# Why a static snapshot rather than scraping every call?
#   - GitHub wiki HTML is unstable to parse, the wiki updates roughly weekly,
#     and we run hundreds of submissions per day.  A snapshot keeps results
#     deterministic; the script can still fetch the live wiki via --refresh-wiki.
#
# To update for new AI teams entering the field: edit the sets below.  See
# docs/infrastructure_changes_may30/I4_literature_check.md "How to update".
# ---------------------------------------------------------------------------

# Section 1(a) AI Standalone — Fully Solved (green)
WIKI_AI_SOLVED_STANDALONE = {
    38, 90, 125, 205, 457, 694, 741, 960, 987, 990,
    1014, 1051, 1091, 1141, 1196, 1202, 1217,
}
# Section 1(a) AI Standalone — Partial/Other (yellow/white/red)
WIKI_AI_PARTIAL_STANDALONE = {
    11, 42, 51, 75, 124, 138, 233, 251, 263, 358, 477, 616, 647, 654,
    684, 783, 836, 872, 888, 949, 951, 963, 1039, 1040, 1041, 1044,
    1101, 1131, 1194,
}
# Section 1(b) AI alongside literature (typically full Lean solutions)
WIKI_AI_ALONGSIDE_LIT = {
    120, 152, 218, 281, 333, 366, 397, 543, 629, 635, 650, 659, 728,
    846, 851, 897, 935, 983, 997, 1026, 1077, 1082, 1089,
}
# Section 1(c) AI building on literature
WIKI_AI_BUILD_LIT = {
    12, 26, 36, 43, 75, 198, 224, 258, 264, 349, 379, 488, 493, 507,
    513, 524, 679, 729, 788, 848, 868, 871, 942, 951, 958, 966, 1004,
    1007, 1032, 1043, 1047, 1048, 1090, 1095, 1097, 1197,
}
# Section 1(d) AI + human collaboration
WIKI_AI_HUMAN = {
    7, 12, 25, 42, 52, 90, 138, 202, 283, 288, 326, 327, 330, 342, 345,
    347, 351, 352, 358, 367, 369, 374, 380, 388, 390, 393, 396, 401,
    411, 415, 423, 451, 456, 460, 488, 501, 503, 514, 521, 524, 535,
    598, 603, 610, 659, 675, 684, 686, 690, 696, 749, 750, 776, 819,
    848, 852, 856, 858, 863, 866, 870, 872, 873, 875, 888, 896, 906,
    931, 943, 951, 953, 956, 976, 995, 996, 1026, 1038, 1039, 1041,
    1062, 1092, 1095, 1132, 1133, 1138, 1141, 1143, 1148, 1151, 1153,
    1183, 1190, 1194, 1195, 1196, 1201, 1209,
}
# Section 2(a) literature search — AI surfaced existing literature (may be
# partial, may be a full pre-existing proof — semantics are ambiguous)
WIKI_LIT_SEARCH = {
    35, 66, 94, 120, 167, 188, 214, 223, 306, 325, 330, 333, 339, 347,
    354, 370, 387, 397, 481, 494, 515, 516, 524, 533, 559, 574, 575,
    591, 602, 621, 645, 650, 652, 659, 672, 705, 729, 737, 749, 750,
    788, 793, 811, 822, 827, 829, 847, 851, 871, 903, 915, 942, 965,
    971, 985, 990, 992, 1008, 1011, 1016, 1019, 1021, 1043, 1079, 1084,
    1099, 1105, 1123, 1124, 1129, 1130, 1147, 1150, 1154, 1161, 1198,
    1216,
}
# Section 2(c) "rewriting" — AI rewrote known solutions; problem is closed.
WIKI_REWRITING = {281, 392, 457, 543, 728, 783, 846, 1039, 1196}

WIKI_SNAPSHOT_DATE = "2026-05-30"


def _wiki_classify(erdos_n: int) -> tuple[str, list[str]]:
    """Classify by wiki sections.  Returns (status_tag, evidence_list)."""
    evidence = []
    # The strongest signals first: full solutions
    if erdos_n in WIKI_AI_SOLVED_STANDALONE:
        evidence.append("wiki 1(a): AI standalone — Full solution")
        return "AI_CLOSED", evidence
    if erdos_n in WIKI_AI_ALONGSIDE_LIT:
        evidence.append("wiki 1(b): AI alongside literature")
        return "AI_CLOSED", evidence
    if erdos_n in WIKI_AI_BUILD_LIT:
        evidence.append("wiki 1(c): AI building on literature")
        return "AI_CLOSED", evidence
    if erdos_n in WIKI_REWRITING:
        evidence.append("wiki 2(c): AI rewrote a known solution")
        return "AI_CLOSED", evidence
    # Weaker signals split into two tiers:
    #   - 1(a) Partial or 1(d) human-collab => AMBIGUOUS (active AI work).
    #   - 2(a) lit-search hit only          => POSSIBLY_SOLVED (lower severity —
    #                                          a paper exists but the problem
    #                                          itself may still be open).
    strong_weak = []
    if erdos_n in WIKI_AI_PARTIAL_STANDALONE:
        strong_weak.append("wiki 1(a) Partial/Other: partial AI progress")
    if erdos_n in WIKI_AI_HUMAN:
        strong_weak.append("wiki 1(d): AI + human collaboration")
    if strong_weak:
        # Surface any lit-search hit too, but the tier is set by the stronger signal.
        if erdos_n in WIKI_LIT_SEARCH:
            strong_weak.append("wiki 2(a): AI surfaced prior literature")
        return "AMBIGUOUS", strong_weak
    if erdos_n in WIKI_LIT_SEARCH:
        return "POSSIBLY_SOLVED", ["wiki 2(a): AI surfaced prior literature"]
    return "CLEAR", []


# ---------------------------------------------------------------------------
# Problem ID parsing
# ---------------------------------------------------------------------------
_ERDOS_RE = re.compile(r"erdos[_-]?(\d+)", re.IGNORECASE)


def parse_erdos_number(problem_id: str) -> int | None:
    """Return the Erdős number from a problem_id, or None if not Erdős."""
    if not problem_id:
        return None
    # Handle variants like "erdos_897.parts.i" or "erdos_42.constructive"
    head = problem_id.split(".")[0]
    m = _ERDOS_RE.match(head)
    if m:
        return int(m.group(1))
    return None


def problem_id_from_sketch(sketch_path: Path) -> str | None:
    """Pull the problem_id out of a sketch file (filename or content)."""
    stem = sketch_path.stem
    m = re.match(r"slot\d+_(.+?)(?:_v\d+)?$", stem, re.IGNORECASE)
    if m:
        return m.group(1).lower().replace(" ", "_")[:80]
    try:
        for line in sketch_path.read_text().splitlines()[:6]:
            mm = re.match(r"(?i)\s*OPEN\s+GAP\s*:\s*(.+)", line)
            if mm:
                pid = mm.group(1).strip().lower()
                pid = re.sub(r"[^a-z0-9]+", "_", pid).strip("_")
                return pid[:80] if pid else None
    except OSError:
        pass
    return stem.lower() if stem else None


# ---------------------------------------------------------------------------
# Cache I/O
# ---------------------------------------------------------------------------
def _cache_path(problem_id: str) -> Path:
    safe = re.sub(r"[^a-zA-Z0-9_.\-]", "_", problem_id)[:120]
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    return CACHE_DIR / f"{safe}.json"


def _read_cache(problem_id: str) -> dict | None:
    p = _cache_path(problem_id)
    if not p.exists():
        return None
    try:
        data = json.loads(p.read_text())
    except (json.JSONDecodeError, OSError):
        return None
    ts = data.get("_cache_ts", 0)
    age = time.time() - ts
    if age > CACHE_TTL_SECONDS:
        return None
    data["cache_age_days"] = round(age / 86400.0, 2)
    return data


def _write_cache(problem_id: str, payload: dict) -> None:
    out = dict(payload)
    out["_cache_ts"] = time.time()
    try:
        _cache_path(problem_id).write_text(
            json.dumps(out, indent=2, sort_keys=True, default=str)
        )
    except OSError as e:
        print(f"WARN: cache write failed for {problem_id}: {e}", file=sys.stderr)


# ---------------------------------------------------------------------------
# Network helpers
# ---------------------------------------------------------------------------
def _http_get(url: str, timeout: float = 15.0) -> str | None:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            charset = resp.headers.get_content_charset() or "utf-8"
            return resp.read().decode(charset, errors="replace")
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError) as e:
        return None
    except Exception as e:
        return None


def fetch_erdosproblems_status(erdos_n: int) -> tuple[str, str | None]:
    """Return (status, url).  status in {open, solved, partial, disproved, error, missing}."""
    url = f"{ERDOSPROBLEMS_BASE}/{erdos_n}"
    html = _http_get(url)
    if html is None:
        return "error", url
    if "404" in html[:200] or "Not Found" in html[:200]:
        return "missing", url
    # Bloom's site emits <div ... id="solved"> / id="open" / id="partial" / id="disproved"
    m = re.search(r'id="(solved|open|partial|disproved)"', html)
    if m:
        return m.group(1), url
    return "unknown", url


def search_arxiv(query: str, max_results: int = 5) -> list[dict]:
    """Search arxiv for recent (2024-) papers matching the query.

    Returns list of {title, authors, date, url, summary_snippet}.
    Limited to titles+abstracts, sorted by submitted-date desc.
    """
    base = "http://export.arxiv.org/api/query"
    # Restrict to recent submissions; arxiv supports date range via submittedDate
    q = f"all:{query}+AND+submittedDate:[202401010000+TO+202612312359]"
    url = f"{base}?search_query={q}&start=0&max_results={max_results}&sortBy=submittedDate&sortOrder=descending"
    xml = _http_get(url, timeout=20.0)
    if xml is None:
        return []
    entries = []
    # Lightweight regex parse (avoid bringing in feedparser)
    for entry in re.findall(r"<entry>(.*?)</entry>", xml, re.DOTALL)[:max_results]:
        title = re.search(r"<title>(.*?)</title>", entry, re.DOTALL)
        link = re.search(r'<id>(.*?)</id>', entry, re.DOTALL)
        published = re.search(r"<published>(.*?)</published>", entry)
        summary = re.search(r"<summary>(.*?)</summary>", entry, re.DOTALL)
        if not title:
            continue
        entries.append({
            "title": re.sub(r"\s+", " ", title.group(1)).strip(),
            "url": (link.group(1).strip() if link else ""),
            "date": (published.group(1)[:10] if published else ""),
            "snippet": (re.sub(r"\s+", " ", summary.group(1)).strip()[:240] if summary else ""),
        })
    return entries


def check_mk_failed(keyword: str) -> dict:
    """Call `mk failed <keyword>` and capture project history.  Returns
    {present: bool, lines: list[str]}.
    """
    try:
        r = subprocess.run(
            ["mk", "failed", keyword],
            capture_output=True, text=True, timeout=15,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return {"present": False, "lines": []}
    if r.returncode != 0:
        return {"present": False, "lines": []}
    out = r.stdout.strip()
    # mk emits a header + a warning footer even on empty results, so detect
    # actual content by looking for lines that aren't the boilerplate.
    body_lines = [
        l for l in out.splitlines()
        if l.strip()
        and not l.startswith("[math-forge]")
        and not l.startswith("WARNING:")
        and "---" not in l
        and "Do NOT repeat" not in l
    ]
    return {"present": bool(body_lines), "lines": body_lines[:10]}


# ---------------------------------------------------------------------------
# Main check
# ---------------------------------------------------------------------------
def check_literature(
    problem_id: str,
    *,
    use_cache: bool = True,
    skip_arxiv: bool = False,
    arxiv_keywords: str | None = None,
) -> dict:
    """Full literature check for a single problem_id.

    Returns a dict with keys:
        problem_id, erdos_n, status, citations, wiki_snapshot_date,
        erdosproblems_status, mk_failed, arxiv, cache_age_days, checked_at
    """
    if use_cache:
        cached = _read_cache(problem_id)
        if cached is not None:
            return cached

    erdos_n = parse_erdos_number(problem_id)
    citations: list[dict] = []
    wiki_status, wiki_evidence = ("CLEAR", [])
    if erdos_n is not None:
        wiki_status, wiki_evidence = _wiki_classify(erdos_n)
        for ev in wiki_evidence:
            citations.append({
                "source": "teorth-wiki",
                "url": WIKI_URL,
                "evidence": ev,
                "snapshot": WIKI_SNAPSHOT_DATE,
            })

    # erdosproblems.com — only meaningful for Erdős problems
    ep_status = None
    ep_url = None
    if erdos_n is not None:
        ep_status, ep_url = fetch_erdosproblems_status(erdos_n)
        if ep_status in ("solved", "partial", "disproved"):
            citations.append({
                "source": "erdosproblems.com",
                "url": ep_url,
                "evidence": f"status indicator: {ep_status}",
            })

    # arXiv recent papers
    arxiv_hits: list[dict] = []
    if not skip_arxiv:
        kw = arxiv_keywords or (
            f"Erdős problem {erdos_n}" if erdos_n is not None
            else problem_id.replace("_", " ")
        )
        arxiv_hits = search_arxiv(kw, max_results=5)
        for h in arxiv_hits[:3]:
            citations.append({
                "source": "arxiv",
                "url": h["url"],
                "evidence": f'{h["date"]} — {h["title"]}',
            })

    # mk failed
    mk_keyword = f"erdos_{erdos_n}" if erdos_n is not None else problem_id
    mk_result = check_mk_failed(mk_keyword)
    if mk_result["present"]:
        citations.append({
            "source": "mk-failed",
            "url": None,
            "evidence": f"{len(mk_result['lines'])} prior failed approach(es) on record",
        })

    # Resolve final status — strict priority order
    if wiki_status == "AI_CLOSED" or ep_status == "solved":
        status = "AI_CLOSED" if wiki_status == "AI_CLOSED" else "RECENTLY_SOLVED"
    elif ep_status == "disproved":
        status = "RECENTLY_SOLVED"
    elif wiki_status == "AMBIGUOUS" or ep_status == "partial":
        status = "AMBIGUOUS"
    elif wiki_status == "POSSIBLY_SOLVED":
        status = "POSSIBLY_SOLVED"
    elif erdos_n is None and not citations:
        status = "UNKNOWN"
    else:
        status = "CLEAR"

    payload = {
        "problem_id": problem_id,
        "erdos_n": erdos_n,
        "status": status,
        "wiki_status": wiki_status,
        "wiki_evidence": wiki_evidence,
        "wiki_snapshot_date": WIKI_SNAPSHOT_DATE,
        "erdosproblems_status": ep_status,
        "erdosproblems_url": ep_url,
        "arxiv_recent": arxiv_hits,
        "mk_failed": mk_result,
        "citations": citations,
        "checked_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }
    _write_cache(problem_id, payload)
    payload["cache_age_days"] = 0.0
    return payload


def status_for_sketch(sketch_path: Path) -> dict:
    """Convenience for safe_aristotle_submit.py:  given a sketch file, look up
    its problem_id and return the full literature report.
    """
    pid = problem_id_from_sketch(sketch_path)
    if not pid:
        return {
            "problem_id": None,
            "status": "UNKNOWN",
            "reason": "could not infer problem_id from sketch path/content",
            "citations": [],
        }
    return check_literature(pid)


# ---------------------------------------------------------------------------
# Backfill: process the POSSIBLY_SOLVED_SINCE rows from the registry
# ---------------------------------------------------------------------------
def backfill_kill_list(
    registry_csv: Path = REGISTRY_CSV,
    out_csv: Path = KILL_LIST_CSV,
    *,
    skip_arxiv: bool = True,
    use_cache: bool = True,
) -> dict:
    """Run literature_check on every POSSIBLY_SOLVED_SINCE row in the registry
    and emit the canonical kill-list CSV.

    Skips arxiv by default (38 rows * arxiv = slow + flaky in batch mode);
    wiki + erdosproblems.com is sufficient for backfill.
    """
    if not registry_csv.exists():
        raise FileNotFoundError(f"registry not found: {registry_csv}")

    rows_out: list[dict] = []
    seen_pids: set[str] = set()
    with registry_csv.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row.get("freshness_flag") != "POSSIBLY_SOLVED_SINCE":
                continue
            pid = row.get("problem_id", "").strip()
            if not pid or pid in seen_pids:
                # one entry per distinct problem_id; multiple theorem variants
                # collapse to a single kill-list row.
                continue
            seen_pids.add(pid)
            report = check_literature(
                pid, use_cache=use_cache, skip_arxiv=skip_arxiv,
            )
            top_cite = (report["citations"][0]["evidence"]
                        if report["citations"] else "")
            rows_out.append({
                "problem_id": pid,
                "erdos_n": report.get("erdos_n") or "",
                "registry_theorem": row.get("theorem_name", ""),
                "registry_file": row.get("file_path", ""),
                "literature_status": report["status"],
                "wiki_status": report.get("wiki_status", ""),
                "erdosproblems_status": report.get("erdosproblems_status") or "",
                "top_evidence": top_cite,
                "checked_at": report.get("checked_at", ""),
            })

    out_csv.parent.mkdir(parents=True, exist_ok=True)
    with out_csv.open("w", newline="") as f:
        if not rows_out:
            f.write("# no rows\n")
        else:
            writer = csv.DictWriter(f, fieldnames=list(rows_out[0].keys()))
            writer.writeheader()
            writer.writerows(rows_out)

    confirmed = sum(1 for r in rows_out if r["literature_status"] in ("AI_CLOSED", "RECENTLY_SOLVED"))
    ambiguous = sum(1 for r in rows_out if r["literature_status"] == "AMBIGUOUS")
    clear = sum(1 for r in rows_out if r["literature_status"] == "CLEAR")
    return {
        "total_processed": len(rows_out),
        "confirmed_kill": confirmed,
        "ambiguous": ambiguous,
        "clear": clear,
        "output_path": str(out_csv),
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def _cli() -> int:
    parser = argparse.ArgumentParser(
        description="Literature freshness check for math problem submissions.",
    )
    parser.add_argument("target", nargs="?",
                        help="problem_id (e.g. erdos_728) OR path to a sketch file")
    parser.add_argument("--backfill", action="store_true",
                        help="run literature check across the POSSIBLY_SOLVED_SINCE rows in the registry")
    parser.add_argument("--no-cache", action="store_true",
                        help="ignore cache, hit the network")
    parser.add_argument("--skip-arxiv", action="store_true",
                        help="skip arxiv search (faster)")
    parser.add_argument("--json", action="store_true",
                        help="emit raw JSON (no human-readable summary)")
    args = parser.parse_args()

    if args.backfill:
        summary = backfill_kill_list(skip_arxiv=args.skip_arxiv,
                                     use_cache=not args.no_cache)
        print(json.dumps(summary, indent=2))
        return 0

    if not args.target:
        parser.error("provide a problem_id, a sketch path, or --backfill")

    # Decide: is the target a path or a problem_id?
    target_path = Path(args.target)
    if target_path.exists() and target_path.is_file():
        report = status_for_sketch(target_path)
    else:
        report = check_literature(
            args.target,
            use_cache=not args.no_cache,
            skip_arxiv=args.skip_arxiv,
        )

    if args.json:
        print(json.dumps(report, indent=2, default=str))
        return 0

    # Human-readable summary
    status = report["status"]
    pid = report.get("problem_id", args.target)
    print(f"Problem:  {pid}")
    print(f"Status:   {status}")
    if report.get("erdos_n"):
        print(f"Erdős #:  {report['erdos_n']}")
    if report.get("erdosproblems_status"):
        print(f"erdosproblems.com: {report['erdosproblems_status']}")
    if report.get("wiki_evidence"):
        for ev in report["wiki_evidence"]:
            print(f"  wiki: {ev}")
    arxiv_hits = report.get("arxiv_recent") or []
    if arxiv_hits:
        print(f"arxiv (top {min(3, len(arxiv_hits))}):")
        for h in arxiv_hits[:3]:
            print(f"  - {h['date']}  {h['title'][:90]}")
    if report.get("mk_failed", {}).get("present"):
        print(f"mk failed:  {len(report['mk_failed']['lines'])} prior approach(es)")
    if "cache_age_days" in report:
        print(f"cache age: {report['cache_age_days']} days")
    # Exit code carries the decision (handy for shell pipelines):
    return {
        "AI_CLOSED": 2, "RECENTLY_SOLVED": 2,
        "AMBIGUOUS": 1, "POSSIBLY_SOLVED": 1,
        "CLEAR": 0, "UNKNOWN": 0,
    }.get(status, 0)


if __name__ == "__main__":
    sys.exit(_cli())
