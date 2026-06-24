#!/usr/bin/env python3
"""Run a single persona attack via Grok API or Codex CLI."""
import os, sys, json, subprocess, tempfile, argparse

def query_grok(prompt: str, max_tokens: int = 3500, timeout: int = 480) -> str:
    api_key = os.environ.get("XAI_API_KEY")
    if not api_key:
        return "ERROR: No XAI_API_KEY"
    data = {
        "messages": [{"role": "user", "content": prompt}],
        "model": "grok-4",
        "max_tokens": max_tokens,
        "temperature": 0.5,
    }
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        json.dump(data, f)
        tmp = f.name
    try:
        r = subprocess.run(
            ['curl', '-s', '-X', 'POST',
             '--max-time', str(timeout),
             'https://api.x.ai/v1/chat/completions',
             '-H', f'Authorization: Bearer {api_key}',
             '-H', 'Content-Type: application/json',
             '-d', f'@{tmp}'],
            capture_output=True, text=True, timeout=timeout + 30
        )
        os.unlink(tmp)
        if r.returncode != 0:
            return f"CURL ERR ({r.returncode}): {r.stderr[:500]}"
        resp = json.loads(r.stdout)
        if 'error' in resp:
            return f"API ERR: {resp['error']}"
        return resp['choices'][0]['message']['content']
    except Exception as e:
        if os.path.exists(tmp):
            os.unlink(tmp)
        return f"EXC: {e}"

def query_codex(prompt: str) -> str:
    """Call codex CLI in non-interactive mode."""
    try:
        # Codex expects prompt via argv, runs xhigh by default
        r = subprocess.run(
            ['codex', 'exec', '--skip-git-repo-check', prompt],
            capture_output=True, text=True, timeout=900
        )
        # Codex prints prompt header + final response; isolate the assistant content.
        out = r.stdout
        # Strip the header (everything up to and including the prompt block)
        # Codex output usually has a "codex" line after which assistant content begins.
        marker = "tokens used:"
        if marker in out:
            # All assistant text appears between the user prompt and the token-count footer.
            # Find the last occurrence of "codex" prior to "tokens used:".
            pass
        # Easier: return full stdout if non-trivial; the user can parse
        return out + ("\n--STDERR--\n" + r.stderr if r.stderr else "")
    except Exception as e:
        return f"EXC: {e}"

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--prompt-file", required=True)
    ap.add_argument("--engine", choices=["grok", "codex"], required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    with open(args.prompt_file) as f:
        prompt = f.read()
    if args.engine == "grok":
        out = query_grok(prompt)
    else:
        out = query_codex(prompt)
    with open(args.output, "w") as f:
        f.write(out)
    print(f"WROTE {args.output} ({len(out)} chars)")
