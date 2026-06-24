#!/usr/bin/env python3
"""Standalone Gemini worker for EXP3."""

import json, os, subprocess, sys, time
from pathlib import Path

ROOT = Path("/Users/patrickkavanagh/math")
RAW_DIR = ROOT / "analysis" / "exp3_raw"
sys.path.insert(0, str(ROOT / "analysis"))
from exp3_runner import build_prompt, DOMAINS  # noqa: E402


def call_gemini(prompt: str) -> str:
    # Flash first (Pro is currently exhausted), then Pro as fallback.
    last_err = ""
    for attempt in range(4):
        model = "gemini-2.5-flash" if attempt < 3 else "gemini-2.5-pro"
        try:
            r = subprocess.run(
                ["gemini", "-m", model, "-p", prompt],
                capture_output=True, text=True, timeout=180
            )
        except subprocess.TimeoutExpired:
            last_err = f"timeout ({model})"
            time.sleep(30)
            continue
        body = r.stdout.strip()
        combined = (r.stderr or "") + body
        if "You have exhausted your capacity" in combined and not body:
            last_err = f"quota exhausted ({model})"
            time.sleep(30 * (attempt + 1))
            continue
        if r.returncode == 0 and body:
            return f"[model={model}]\n\n{body}"
        last_err = f"rc={r.returncode} body_len={len(body)} stderr_head={r.stderr[:150]} ({model})"
        time.sleep(20 * (attempt + 1))
    return f"GEMINI FAILED. Last: {last_err}"


def main():
    for p in ["E938", "E373"]:
        for d, _ in DOMAINS:
            out = RAW_DIR / f"{p}_{d}_gemini.md"
            if out.exists() and out.stat().st_size > 1500:
                body = out.read_text()
                if "GEMINI FAILED" not in body and "GEMINI ERROR" not in body[:300]:
                    print(f"SKIP {out.name}", flush=True)
                    continue
            prompt = build_prompt(p, d)
            t0 = time.time()
            body = call_gemini(prompt)
            elapsed = time.time() - t0
            hdr = f"# EXP3 — {p} × {d} × gemini\nPrompt date: 2026-05-31  Elapsed: {elapsed:.1f}s  Bytes: {len(body)}\n\n## Prompt\n\n```\n{prompt}\n```\n\n## Response\n\n"
            out.write_text(hdr + body)
            status = "OK" if "FAILED" not in body and "ERROR" not in body[:200] else "ERR"
            print(f"{status} {out.name} ({elapsed:.1f}s, {len(body)}B)", flush=True)
            time.sleep(30)  # be polite


if __name__ == "__main__":
    main()
