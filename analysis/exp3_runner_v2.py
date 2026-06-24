#!/usr/bin/env python3
"""
EXP3 runner v2 — rate-limit aware.

Strategy: model-by-model serial. Codex first (no observed rate limits), then
Gemini, then Grok. Per-model intra-batch sleep to be polite.
"""

import json
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path("/Users/patrickkavanagh/math")
SCRIPTS = ROOT / "scripts"
RAW_DIR = ROOT / "analysis" / "exp3_raw"
RAW_DIR.mkdir(parents=True, exist_ok=True)

# Import prompt machinery from v1
sys.path.insert(0, str(ROOT / "analysis"))
from exp3_runner import build_prompt, DOMAINS  # type: ignore  # noqa: E402


def call_grok(prompt: str) -> str:
    """Direct Grok-4 call with retries on rate-limit-style errors."""
    api_key = os.environ.get("XAI_API_KEY", "")
    if not api_key:
        return "ERROR: no XAI_API_KEY"
    import tempfile
    data = {
        "messages": [{"role": "user", "content": prompt}],
        "model": "grok-4",
        "max_tokens": 2000,
        "temperature": 0.3,
    }
    last_err = ""
    for attempt in range(6):
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
            json.dump(data, f)
            fn = f.name
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
            last_err = f"curl rc={r.returncode}: {r.stderr[:300]}"
            time.sleep(30 * (attempt + 1))
            continue
        try:
            resp = json.loads(r.stdout)
        except json.JSONDecodeError as e:
            last_err = f"JSON: {e}; raw: {r.stdout[:300]}"
            time.sleep(30 * (attempt + 1))
            continue
        if "choices" in resp:
            content = resp["choices"][0]["message"].get("content", "")
            if content.strip():
                return content
            last_err = f"empty content; finish={resp['choices'][0].get('finish_reason')}"
            time.sleep(30 * (attempt + 1))
            continue
        err = resp.get("error")
        if isinstance(err, dict):
            last_err = f"API: {err.get('message', err)}"
        else:
            last_err = f"API: {err}"
        # Increase backoff aggressively on the team-not-found error
        time.sleep(60 * (attempt + 1))
    return f"GROK FAILED 6 attempts. Last: {last_err}"


def call_gemini(prompt: str) -> str:
    last_err = ""
    for attempt in range(4):
        try:
            r = subprocess.run(
                ["gemini", "-m", "gemini-2.5-pro", "-p", prompt],
                capture_output=True, text=True, timeout=420
            )
        except subprocess.TimeoutExpired:
            last_err = "timeout"
            time.sleep(60)
            continue
        body = r.stdout.strip()
        # Gemini exit code can be 0 with quota-exhaustion text
        if "You have exhausted your capacity" in (r.stderr + r.stdout):
            last_err = "quota exhausted"
            time.sleep(120 * (attempt + 1))
            continue
        if r.returncode != 0 and not body:
            last_err = f"rc={r.returncode}: {r.stderr[:300]}"
            time.sleep(60 * (attempt + 1))
            continue
        if body:
            return body
        last_err = "empty body"
        time.sleep(60)
    return f"GEMINI FAILED. Last: {last_err}"


def call_codex(prompt: str) -> str:
    try:
        r = subprocess.run(
            ["codex", "exec", prompt],
            capture_output=True, text=True, timeout=600
        )
    except subprocess.TimeoutExpired:
        return "CODEX TIMEOUT 600s"
    if r.returncode != 0:
        return f"CODEX ERROR rc={r.returncode}: {r.stderr[:500]}"
    return r.stdout


def run_one(problem: str, domain: str, model: str, call_fn) -> dict:
    out = RAW_DIR / f"{problem}_{domain}_{model}.md"
    if out.exists() and out.stat().st_size > 1500 and "FAILED" not in out.read_text()[:3000] and "ERROR" not in out.read_text()[:300]:
        print(f"  SKIP {out.name}", flush=True)
        return {"problem": problem, "domain": domain, "model": model, "status": "cached"}
    prompt = build_prompt(problem, domain)
    t0 = time.time()
    body = call_fn(prompt)
    elapsed = time.time() - t0
    header = f"# EXP3 — {problem} × {domain} × {model}\nPrompt date: 2026-05-31  Elapsed: {elapsed:.1f}s  Bytes: {len(body)}\n\n## Prompt\n\n```\n{prompt}\n```\n\n## Response\n\n"
    out.write_text(header + body)
    status = "ok"
    if any(s in body[:300] for s in ("FAILED", "ERROR", "TIMEOUT")):
        status = "err"
    print(f"  {status.upper()} {out.name}  ({elapsed:.1f}s, {len(body)}B)", flush=True)
    return {"problem": problem, "domain": domain, "model": model, "status": status, "elapsed_s": elapsed, "bytes": len(body)}


def main():
    problems = ["E938", "E373"]
    domain_keys = [k for k, _ in DOMAINS]
    results = []

    # Run model-by-model. Codex first.
    for model_name, call_fn, intra_delay in [
        ("codex", call_codex, 5),
        ("gemini", call_gemini, 30),
        ("grok", call_grok, 30),
    ]:
        print(f"\n=== {model_name} batch (8 jobs) ===", flush=True)
        for p in problems:
            for d in domain_keys:
                results.append(run_one(p, d, model_name, call_fn))
                time.sleep(intra_delay)

    manifest = RAW_DIR / "manifest.json"
    manifest.write_text(json.dumps(results, indent=2))
    ok = sum(1 for r in results if r.get("status") in ("ok", "cached"))
    print(f"\nDone. {ok}/{len(results)} OK. Manifest: {manifest}")


if __name__ == "__main__":
    main()
