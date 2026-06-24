#!/usr/bin/env python3
"""
Extended thinking Grok-4 run for Erdős 938.
Uses grok-4-fast-reasoning with reasoning_effort=high and max_completion_tokens=64000.
"""

import os
import sys
import json
import time
import requests

API_KEY = os.environ.get("XAI_API_KEY") or os.environ.get("GROK_API_KEY")
if not API_KEY:
    print("ERROR: no XAI_API_KEY", file=sys.stderr)
    sys.exit(1)

PROMPT_PATH = "/Users/patrickkavanagh/math/analysis/exp1_outputs/prompt_extended.md"
OUT_PATH = "/Users/patrickkavanagh/math/analysis/exp1_outputs/grok_extended_output.md"
META_PATH = "/Users/patrickkavanagh/math/analysis/exp1_outputs/grok_extended_meta.json"

with open(PROMPT_PATH, "r") as f:
    prompt = f.read()

models_to_try = [
    "grok-4-fast-reasoning",
    "grok-4",
    "grok-4-0709",
]

start = time.time()
result = None
last_error = None

for model in models_to_try:
    print(f"[INFO] Trying model={model}", file=sys.stderr)
    payload = {
        "messages": [
            {"role": "system", "content": "You are a careful research mathematician. You have unlimited reasoning budget. Think deeply before answering. Use chain-of-thought reasoning extensively. Be technically precise, not hand-wavy. Avoid restating known content."},
            {"role": "user", "content": prompt},
        ],
        "model": model,
        "max_tokens": 64000,
        "temperature": 0.3,
    }
    # grok-4 reasoning models support reasoning_effort
    if "reasoning" in model or model == "grok-4":
        payload["reasoning_effort"] = "high"

    try:
        r = requests.post(
            "https://api.x.ai/v1/chat/completions",
            headers={
                "Authorization": f"Bearer {API_KEY}",
                "Content-Type": "application/json",
            },
            json=payload,
            timeout=900,  # 15 minutes max
        )
        if r.status_code == 200:
            data = r.json()
            print(f"[OK] model={model} returned {r.status_code}", file=sys.stderr)
            result = (model, data, time.time() - start)
            break
        else:
            last_error = f"{model} returned {r.status_code}: {r.text[:500]}"
            print(f"[WARN] {last_error}", file=sys.stderr)
    except Exception as e:
        last_error = f"{model} threw {type(e).__name__}: {e}"
        print(f"[WARN] {last_error}", file=sys.stderr)

if not result:
    print(f"[FATAL] all models failed; last_error={last_error}", file=sys.stderr)
    sys.exit(2)

model, data, elapsed = result
content = data["choices"][0]["message"]["content"]
usage = data.get("usage", {})

with open(OUT_PATH, "w") as f:
    f.write(content)

with open(META_PATH, "w") as f:
    json.dump({
        "model": model,
        "elapsed_seconds": elapsed,
        "usage": usage,
        "completion_tokens": usage.get("completion_tokens"),
        "prompt_tokens": usage.get("prompt_tokens"),
        "reasoning_tokens": usage.get("reasoning_tokens") or usage.get("completion_tokens_details", {}).get("reasoning_tokens"),
        "total_tokens": usage.get("total_tokens"),
        "finish_reason": data["choices"][0].get("finish_reason"),
    }, f, indent=2)

print(f"[DONE] model={model} elapsed={elapsed:.1f}s tokens={usage}", file=sys.stderr)
print(f"[DONE] output={OUT_PATH}", file=sys.stderr)
