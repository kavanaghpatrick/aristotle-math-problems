#!/usr/bin/env python3
"""gpt52pro_smoke.py — Smoke test GPT-5.2 Pro via OpenAI Responses API.

Verifies that gpt-5.2-pro is reachable as a paired strategist LLM for
Stage 4 fusion outlines. Compares against Codex CLI (gpt-5.5) on the
same prompt for qualitative differential.

WARNING: gpt-5.2-pro is exclusive to the Responses API (NOT Chat
Completions, NOT Codex CLI with ChatGPT-account auth). You must export
a real OPENAI_API_KEY (sk-...) bound to a developer account, not a
ChatGPT-Plus OAuth token.

Usage:
    export OPENAI_API_KEY=sk-...
    python3 scripts/gpt52pro_smoke.py --gap submissions/sketches/erdos938.txt
    python3 scripts/gpt52pro_smoke.py --gap <file> --compare-codex

Refs:
    - https://openai.com/index/introducing-gpt-5-2/
    - docs/gpt52pro_evaluation.md
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import urllib.request
import urllib.error


OUTLINE_PROMPT = """You are a research mathematician preparing an INFORMAL
strategy outline for an open conjecture. The prover (Aristotle) will receive:
  1. The bare gap statement (problem).
  2. Your informal outline (this output).

Your outline must contain:
  - Named technique (e.g. "Mertens-style upper bound on prime gaps", "Apex
    cover argument", "Bombieri-Vinogradov dyadic decomposition")
  - 3-5 candidate lemmas, each stated formally enough that a Lean prover
    can attempt them
  - Brief justification (1-2 sentences) for why this attack should work

DO NOT write Lean code. DO NOT write a complete proof. Just the strategist
outline. Be specific about the analytic / algebraic tool you would reach for.

------ OPEN GAP ------
{gap}
------ OUTLINE BELOW ------
"""


def call_responses_api(prompt: str, model: str = "gpt-5.2-pro",
                       reasoning_effort: str = "xhigh",
                       timeout: int = 600) -> dict:
    """Call OpenAI Responses API (the only endpoint gpt-5.2-pro is on)."""
    api_key = os.environ.get("OPENAI_API_KEY", "")
    if not api_key.startswith("sk-"):
        raise RuntimeError(
            "OPENAI_API_KEY missing or not a developer key. "
            "Codex OAuth tokens cannot reach the Responses API."
        )

    body = {
        "model": model,
        "input": prompt,
        "reasoning": {"effort": reasoning_effort},
    }
    req = urllib.request.Request(
        "https://api.openai.com/v1/responses",
        data=json.dumps(body).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    t0 = time.time()
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        err_body = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"Responses API HTTP {e.code}: {err_body}")
    dt = time.time() - t0

    # Responses API output shape: output[].content[].text
    text = ""
    for item in payload.get("output", []):
        for c in item.get("content", []):
            if c.get("type") in ("output_text", "text"):
                text += c.get("text", "")
    usage = payload.get("usage", {})
    return {
        "model": model,
        "text": text,
        "elapsed_s": round(dt, 1),
        "usage": usage,
        "raw_id": payload.get("id"),
    }


def call_codex_cli(prompt: str, model: str = "gpt-5.5",
                   timeout: int = 600) -> dict:
    """Call Codex CLI as the comparison baseline."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".txt", delete=False
    ) as f:
        f.write(prompt)
        prompt_file = f.name
    try:
        t0 = time.time()
        proc = subprocess.run(
            [
                "bash", "-c",
                f'codex exec --full-auto --sandbox read-only -m {model} '
                f'"$(cat \'{prompt_file}\')"',
            ],
            capture_output=True, text=True, timeout=timeout,
        )
        dt = time.time() - t0
    finally:
        try:
            os.unlink(prompt_file)
        except OSError:
            pass
    # Strip codex CLI banner lines
    out_lines = proc.stdout.splitlines()
    # Codex output sits between "codex" markers; cheap heuristic: drop
    # everything before the first "codex" marker line and "tokens used"
    # trailer.
    body = []
    in_body = False
    for line in out_lines:
        if line.strip() == "codex":
            in_body = True
            continue
        if line.strip().startswith("tokens used"):
            break
        if in_body:
            body.append(line)
    text = "\n".join(body).strip() or proc.stdout.strip()
    return {
        "model": f"codex-cli/{model}",
        "text": text,
        "elapsed_s": round(dt, 1),
        "usage": {},
        "raw_id": None,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--gap", type=Path, required=True,
                    help="Path to bare gap sketch .txt")
    ap.add_argument("--model", default="gpt-5.2-pro",
                    help="Responses-API model id (default gpt-5.2-pro)")
    ap.add_argument("--effort", default="xhigh",
                    choices=["minimal", "low", "medium", "high", "xhigh"])
    ap.add_argument("--compare-codex", action="store_true",
                    help="Also call codex CLI (gpt-5.5) and print both.")
    ap.add_argument("--out-dir", type=Path,
                    default=Path("docs/gpt52pro_smoke_runs"))
    args = ap.parse_args()

    gap = args.gap.read_text()
    prompt = OUTLINE_PROMPT.format(gap=gap)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    stem = args.gap.stem

    print(f"# Smoke test: {stem}\n")
    print(f"Gap file: {args.gap}")
    print(f"Gap bytes: {len(gap)}")
    print()

    try:
        r1 = call_responses_api(prompt, model=args.model,
                                reasoning_effort=args.effort)
    except RuntimeError as e:
        print(f"FAIL Responses API: {e}", file=sys.stderr)
        return 2
    out1 = args.out_dir / f"{stem}.{args.model}.md"
    out1.write_text(
        f"# {args.model} | effort={args.effort}\n"
        f"elapsed_s: {r1['elapsed_s']}\n"
        f"usage: {json.dumps(r1['usage'])}\n\n{r1['text']}\n"
    )
    print(f"[{args.model}] {r1['elapsed_s']}s, usage={r1['usage']}")
    print(f"  -> {out1}")
    print()

    if args.compare_codex:
        r2 = call_codex_cli(prompt)
        out2 = args.out_dir / f"{stem}.codex-gpt-5.5.md"
        out2.write_text(
            f"# codex-cli/gpt-5.5\n"
            f"elapsed_s: {r2['elapsed_s']}\n\n{r2['text']}\n"
        )
        print(f"[codex-cli/gpt-5.5] {r2['elapsed_s']}s")
        print(f"  -> {out2}")
        print()
        print("Compare with: diff -u "
              f"{out1} {out2}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
