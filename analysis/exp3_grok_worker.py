#!/usr/bin/env python3
"""Standalone Grok worker for EXP3 — independent of the main runner.

Uses direct curl-style API calls with aggressive backoff. Skips any output
file already > 1500 bytes that doesn't contain a known error string.
"""

import json, os, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path("/Users/patrickkavanagh/math")
RAW_DIR = ROOT / "analysis" / "exp3_raw"
sys.path.insert(0, str(ROOT / "analysis"))
from exp3_runner import build_prompt, DOMAINS  # noqa: E402

api_key = os.environ.get("XAI_API_KEY", "")
if not api_key:
    print("No XAI_API_KEY; exit"); sys.exit(1)


def call_grok(prompt: str, max_tokens: int = 2000) -> str:
    last_err = ""
    for attempt in range(6):
        data = {
            "messages": [{"role": "user", "content": prompt}],
            "model": "grok-4",
            "max_tokens": max_tokens,
            "temperature": 0.3,
        }
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
            json.dump(data, f); fn = f.name
        try:
            r = subprocess.run(
                ["curl", "-s", "-X", "POST", "--max-time", "180",
                 "https://api.x.ai/v1/chat/completions",
                 "-H", f"Authorization: Bearer {api_key}",
                 "-H", "Content-Type: application/json",
                 "-d", f"@{fn}"],
                capture_output=True, text=True, timeout=200
            )
        finally:
            os.unlink(fn)
        if r.returncode != 0:
            last_err = f"curl rc={r.returncode}"
            time.sleep(45 * (attempt + 1))
            continue
        try:
            resp = json.loads(r.stdout)
        except Exception as e:
            last_err = f"json {e}"
            time.sleep(30 * (attempt + 1))
            continue
        if "choices" in resp:
            c = resp["choices"][0]["message"].get("content", "")
            if c.strip():
                return c
            last_err = "empty"
            time.sleep(30 * (attempt + 1))
            continue
        # error path
        err = resp.get("error", "?")
        if isinstance(err, dict): err = err.get("message", err)
        last_err = f"api: {err}"
        # Aggressive backoff on the 'team does not have access' transient
        time.sleep(60 * (attempt + 1))
    return f"GROK FAILED 6 attempts. Last: {last_err}"


def main():
    for p in ["E938", "E373"]:
        for d, _ in DOMAINS:
            out = RAW_DIR / f"{p}_{d}_grok.md"
            if out.exists() and out.stat().st_size > 1500:
                body = out.read_text()
                if "GROK FAILED" not in body and "ERROR" not in body[:300]:
                    print(f"SKIP {out.name}", flush=True)
                    continue
            prompt = build_prompt(p, d)
            t0 = time.time()
            body = call_grok(prompt)
            elapsed = time.time() - t0
            hdr = f"# EXP3 — {p} × {d} × grok\nPrompt date: 2026-05-31  Elapsed: {elapsed:.1f}s  Bytes: {len(body)}\n\n## Prompt\n\n```\n{prompt}\n```\n\n## Response\n\n"
            out.write_text(hdr + body)
            status = "OK" if "FAILED" not in body and "ERROR" not in body[:200] else "ERR"
            print(f"{status} {out.name} ({elapsed:.1f}s, {len(body)}B)", flush=True)
            time.sleep(20)  # be polite


if __name__ == "__main__":
    main()
