#!/usr/bin/env python3
"""Re-score cached raw responses from a prior calibration run.

Usage:
  python3 research_fusion/calibration/rescore.py [--raw-dir DIR] [--suffix SUFFIX]

Reads research_fusion/calibration/raw/<id>__<model>.md files and rebuilds
the results_<date>.md + hit_rate.json without spending API dollars.

This is useful when:
  - You revise the alt_names / DOMAIN_TOKENS scoring lists.
  - You want a strict-only (1.0-required) view.
  - You want to add/remove models from the ensemble.
"""
from __future__ import annotations

import argparse
import datetime as dt
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from calibration_runner import (  # noqa: E402
    PROBLEMS,
    ProblemRun,
    ensemble_score,
    extract_proposals,
    score_proposals,
    write_hit_rate_json,
    write_results_markdown,
)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--raw-dir", default=str(HERE / "raw"))
    ap.add_argument("--suffix", default="rescored")
    args = ap.parse_args()

    raw_dir = Path(args.raw_dir)
    if not raw_dir.exists():
        print(f"ERROR: raw directory not found: {raw_dir}")
        return 2

    runs: list[ProblemRun] = []
    for problem in PROBLEMS:
        run = ProblemRun(problem_id=problem["id"], name=problem["name"], prompt="")
        for m in ("grok", "gemini", "codex"):
            f = raw_dir / f"{problem['id']}__{m}.md"
            if not f.exists():
                continue
            resp = f.read_text()
            run.responses[m] = resp
            run.proposals[m] = extract_proposals(resp)
            run.scores[m] = {"model": m, **score_proposals(problem, run.proposals[m], resp)}
        if run.scores:
            run.ensemble = ensemble_score(list(run.scores.values()))
        runs.append(run)

    hit_rate = sum(1 for r in runs if r.ensemble.get("hit"))
    verdict = "PASS" if hit_rate >= 4 else "FAIL"
    date = dt.date.today().isoformat()
    suffix = f"_{args.suffix}" if args.suffix else ""
    md = HERE / f"results_{date}{suffix}.md"
    js = HERE / f"hit_rate{suffix}.json"
    write_results_markdown(runs, md, hit_rate, verdict)
    write_hit_rate_json(runs, hit_rate, verdict, js)

    print(f"hit_rate={hit_rate}/10  verdict={verdict}")
    print(f"results: {md}")
    print(f"json:    {js}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
