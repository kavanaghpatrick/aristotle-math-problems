#!/usr/bin/env python3
"""
Grok API helper for math problem analysis.
Uses curl internally with configurable timeout.
Usage: python3 grok_query.py "Your prompt here" [timeout_seconds]
Default timeout: 600 seconds (10 minutes)
"""

import os
import sys
import json
import subprocess
import tempfile

def query_grok(prompt: str, model: str = "grok-4", max_tokens: int = 4000, timeout: int = 600) -> str:
    """Query Grok API using curl and return response."""
    api_key = os.environ.get("GROK_API_KEY") or os.environ.get("XAI_API_KEY")
    if not api_key:
        return "ERROR: No GROK_API_KEY or XAI_API_KEY found in environment"

    data = {
        "messages": [{"role": "user", "content": prompt}],
        "model": model,
        "max_tokens": max_tokens,
        "temperature": 0.3
    }

    # Write JSON to temp file to handle escaping properly
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        json.dump(data, f)
        temp_file = f.name

    try:
        # Use curl with explicit timeout
        result = subprocess.run(
            [
                'curl', '-s', '-X', 'POST',
                '--max-time', str(timeout),
                'https://api.x.ai/v1/chat/completions',
                '-H', f'Authorization: Bearer {api_key}',
                '-H', 'Content-Type: application/json',
                '-d', f'@{temp_file}'
            ],
            capture_output=True,
            text=True,
            timeout=timeout + 30  # subprocess timeout slightly longer than curl
        )

        os.unlink(temp_file)

        if result.returncode != 0:
            return f"CURL ERROR (code {result.returncode}): {result.stderr}"

        if not result.stdout.strip():
            return "ERROR: Empty response from API"

        response = json.loads(result.stdout)
        if 'error' in response:
            return f"API ERROR: {response['error'].get('message', response['error'])}"

        return response['choices'][0]['message']['content']

    except subprocess.TimeoutExpired:
        if os.path.exists(temp_file):
            os.unlink(temp_file)
        return f"ERROR: Request timed out after {timeout}s"
    except json.JSONDecodeError as e:
        return f"JSON ERROR: {e}\nRaw response: {result.stdout[:1000]}"
    except Exception as e:
        if os.path.exists(temp_file):
            os.unlink(temp_file)
        return f"ERROR: {str(e)}"

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 grok_query.py 'Your prompt here' [timeout_seconds]")
        sys.exit(1)

    prompt = sys.argv[1]
    timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    print(query_grok(prompt, timeout=timeout))
