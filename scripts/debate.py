#!/usr/bin/env python3
"""
Multi-AI Debate Orchestrator

Runs structured debates between AI models with FULL context accumulation.
Every round, every model receives:
  1. The FULL original context (unchanged)
  2. ALL responses from ALL models in ALL prior rounds
  3. Round-specific instructions

This ensures genuine debate: each model can respond to specific points
made by others, revise positions, and build on prior analysis.

Usage:
  python3 scripts/debate.py \
    --context docs/context.md \
    --topic "Your debate topic" \
    --rounds 4 \
    --output docs/debate_output.md \
    --models grok,gemini,codex \
    --timeout 300

  # With custom per-round instructions:
  python3 scripts/debate.py \
    --context docs/context.md \
    --topic "Topic" \
    --rounds 3 \
    --output docs/debate.md \
    --models grok,gemini,codex \
    --round-instructions round_prompts.json

  # round_prompts.json format:
  # {"1": "Opening: state your position on X",
  #  "2": "Respond to others. What do you agree/disagree with?",
  #  "3": "Final recommendation with prioritized actions."}
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path


# ══════════════════════════════════════════════════════════════════
# MODEL CALLERS
# ══════════════════════════════════════════════════════════════════

def call_grok(prompt: str, timeout: int = 300) -> str:
    """Call Grok-4 via xAI API."""
    api_key = os.environ.get("GROK_API_KEY")
    if not api_key:
        return "[ERROR: GROK_API_KEY not set in environment]"

    request = {
        "messages": [{"role": "user", "content": prompt}],
        "model": "grok-4",
        "temperature": 0.3,
    }

    # Write request to temp file (avoids shell escaping issues)
    req_file = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".json", delete=False
        ) as f:
            json.dump(request, f)
            req_file = f.name

        result = subprocess.run(
            [
                "curl", "-s", "-X", "POST",
                "https://api.x.ai/v1/chat/completions",
                "-H", f"Authorization: Bearer {api_key}",
                "-H", "Content-Type: application/json",
                "--max-time", str(timeout),
                "-d", f"@{req_file}",
            ],
            capture_output=True,
            text=True,
            timeout=timeout + 30,
        )

        if result.returncode != 0:
            return f"[ERROR: curl failed with code {result.returncode}: {result.stderr[:500]}]"

        response = json.loads(result.stdout)
        if "error" in response:
            return f"[ERROR from Grok API: {response['error']}]"
        return response["choices"][0]["message"]["content"]

    except json.JSONDecodeError as e:
        return f"[ERROR: Failed to parse Grok response: {e}\nRaw: {result.stdout[:500]}]"
    except subprocess.TimeoutExpired:
        return f"[ERROR: Grok timed out after {timeout}s]"
    except Exception as e:
        return f"[ERROR calling Grok: {type(e).__name__}: {e}]"
    finally:
        if req_file and os.path.exists(req_file):
            os.unlink(req_file)


def call_gemini(prompt: str, timeout: int = 300) -> str:
    """Call Gemini via CLI. Writes prompt to temp file for long inputs."""
    prompt_file = None
    try:
        # Write prompt to temp file to avoid shell argument length limits
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", delete=False
        ) as f:
            f.write(prompt)
            prompt_file = f.name

        # Use shell to read from file (handles arbitrarily long prompts)
        result = subprocess.run(
            ["bash", "-c", f'gemini -p "$(cat \'{prompt_file}\')"'],
            capture_output=True,
            text=True,
            timeout=timeout,
        )

        output = result.stdout.strip()
        if not output and result.stderr:
            # Filter out common harmless warnings
            stderr = "\n".join(
                line for line in result.stderr.split("\n")
                if "DeprecationWarning" not in line
                and "punycode" not in line
                and "trace-deprecation" not in line
                and line.strip()
            )
            if stderr:
                return f"[Gemini stderr: {stderr[:1000]}]"
            return "[ERROR: Gemini returned empty response]"
        return output

    except FileNotFoundError:
        return "[ERROR: gemini CLI not found. Install with: npm install -g @anthropic-ai/gemini-cli]"
    except subprocess.TimeoutExpired:
        return f"[ERROR: Gemini timed out after {timeout}s]"
    except Exception as e:
        return f"[ERROR calling Gemini: {type(e).__name__}: {e}]"
    finally:
        if prompt_file and os.path.exists(prompt_file):
            os.unlink(prompt_file)


def call_codex(prompt: str, timeout: int = 300) -> str:
    """Call Codex/GPT-5.2 via CLI."""
    prompt_file = None
    try:
        # Write prompt to temp file
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", delete=False
        ) as f:
            f.write(prompt)
            prompt_file = f.name

        # codex exec with read-only sandbox for safety
        result = subprocess.run(
            [
                "bash", "-c",
                f'codex exec --full-auto --sandbox read-only "$(cat \'{prompt_file}\')"',
            ],
            capture_output=True,
            text=True,
            timeout=timeout,
        )

        output = result.stdout.strip()
        if not output and result.stderr:
            stderr = "\n".join(
                line for line in result.stderr.split("\n")
                if "DeprecationWarning" not in line
                and "punycode" not in line
                and line.strip()
            )
            if stderr:
                return f"[Codex stderr: {stderr[:1000]}]"
            return "[ERROR: Codex returned empty response]"
        return output

    except FileNotFoundError:
        return "[ERROR: codex CLI not found. Install with: npm install -g @openai/codex]"
    except subprocess.TimeoutExpired:
        return f"[ERROR: Codex timed out after {timeout}s]"
    except Exception as e:
        return f"[ERROR calling Codex: {type(e).__name__}: {e}]"
    finally:
        if prompt_file and os.path.exists(prompt_file):
            os.unlink(prompt_file)


# Model registry: name -> (display_name, caller_function)
MODEL_REGISTRY = {
    "grok": ("Grok-4 (xAI)", call_grok),
    "gemini": ("Gemini (Google)", call_gemini),
    "codex": ("Codex/GPT-5.2 (OpenAI)", call_codex),
}


# ══════════════════════════════════════════════════════════════════
# PROMPT BUILDING
# ══════════════════════════════════════════════════════════════════

def default_round_instructions(round_num: int, total_rounds: int) -> str:
    """Generate default instructions for a given round."""
    if round_num == 1:
        return (
            "Give your OPENING POSITION on the debate topic.\n"
            "- Be specific and cite evidence from the context above\n"
            "- Structure your response with clear numbered points\n"
            "- State your key claims explicitly so others can respond to them\n"
            "- Identify what you see as the most important questions/issues"
        )
    elif round_num == total_rounds:
        return (
            "This is the FINAL ROUND. Give your closing position:\n"
            "1. What positions have you REVISED based on this debate? Be specific about what changed your mind.\n"
            "2. Where do you STILL DISAGREE with other participants? Why?\n"
            "3. What is your FINAL RECOMMENDATION? Be concrete and actionable.\n"
            "4. Provide a PRIORITIZED list of next 3-5 actions.\n"
            "5. What is the single most important thing the team should do next?"
        )
    else:
        return (
            f"This is Round {round_num} of {total_rounds}. RESPOND TO THE OTHER PARTICIPANTS:\n"
            "1. Quote specific claims from other participants and state whether you agree or disagree, and WHY.\n"
            "2. Present NEW evidence or arguments that haven't been raised yet.\n"
            "3. Have you revised any of your positions? If so, explain what changed your mind.\n"
            "4. What questions do you want other participants to address in the next round?\n"
            "5. Where is genuine disagreement vs. miscommunication?"
        )


def build_prompt(
    original_context: str,
    topic: str,
    transcript: list,
    model_display_name: str,
    round_num: int,
    total_rounds: int,
    round_instructions: str = "",
) -> str:
    """Build the full prompt for a model in a given round.

    The prompt always includes:
    1. Role assignment and debate structure
    2. Full original context (unchanged every round)
    3. Complete debate transcript so far
    4. Round-specific instructions
    """
    parts = []

    # ── Header ──
    parts.append(
        f"You are {model_display_name}, participating in a structured "
        f"{total_rounds}-round multi-AI debate.\n"
        f"This is ROUND {round_num} of {total_rounds}.\n"
    )

    # ── Rules ──
    parts.append(
        "DEBATE RULES:\n"
        "- Respond to SPECIFIC points made by other participants (quote them)\n"
        "- If you change your mind, SAY SO explicitly and explain why\n"
        "- Distinguish between facts (verifiable) and opinions (judgment calls)\n"
        "- Be concrete: propose specific actions, not vague directions\n"
        "- If you disagree, explain what evidence would change your mind\n"
    )

    # ── Topic ──
    parts.append(f"## DEBATE TOPIC\n\n{topic}\n")

    # ── Full Context ──
    parts.append(
        "## FULL CONTEXT\n"
        "Below is the complete context for this debate. "
        "This is the SAME context given to all participants in every round.\n"
    )
    parts.append(original_context)
    parts.append("")

    # ── Accumulated Transcript ──
    if transcript:
        parts.append(
            "## COMPLETE DEBATE TRANSCRIPT\n"
            "Below are ALL responses from ALL participants in ALL prior rounds.\n"
            "Read them carefully. You MUST engage with specific points made by others.\n"
            "Do NOT repeat arguments already made — build on them or challenge them.\n"
        )
        current_round = 0
        for entry in transcript:
            if entry["round"] != current_round:
                current_round = entry["round"]
                parts.append(f"### ── Round {current_round} ──\n")
            parts.append(f"**{entry['model']}** (Round {entry['round']}):\n")
            parts.append(entry["response"])
            parts.append("")
    else:
        parts.append(
            "## DEBATE TRANSCRIPT\n"
            "No prior rounds. You are providing the opening position.\n"
        )

    # ── Round Instructions ──
    instructions = round_instructions or default_round_instructions(
        round_num, total_rounds
    )
    parts.append(f"## YOUR TASK FOR ROUND {round_num}\n")
    parts.append(instructions)
    parts.append("")
    parts.append(
        "Write your response now. Be thorough but focused. "
        "Do NOT include meta-commentary about the debate format."
    )

    return "\n".join(parts)


# ══════════════════════════════════════════════════════════════════
# DEBATE ORCHESTRATION
# ══════════════════════════════════════════════════════════════════

def run_debate(
    context_file: str,
    topic: str,
    rounds: int,
    output_file: str,
    models: list,
    round_instructions: dict = None,
    timeout: int = 300,
):
    """Run the full multi-round debate with context accumulation."""

    # Load context
    context_path = Path(context_file)
    if not context_path.exists():
        print(f"ERROR: Context file not found: {context_file}")
        sys.exit(1)
    context = context_path.read_text()

    # Validate models
    for m in models:
        if m not in MODEL_REGISTRY:
            print(
                f"ERROR: Unknown model '{m}'. "
                f"Available: {list(MODEL_REGISTRY.keys())}"
            )
            sys.exit(1)

    # State
    transcript = []  # List of {"round": int, "model": str, "response": str}

    # ── Build Output Header ──
    output_parts = []
    output_parts.append(f"# Multi-AI Debate: {topic}")
    output_parts.append(f"## {datetime.now().strftime('%B %d, %Y')}\n")
    output_parts.append("### Participants")
    for m in models:
        display_name, _ = MODEL_REGISTRY[m]
        output_parts.append(f"- **{display_name}**")
    output_parts.append("")
    output_parts.append(f"### Format")
    output_parts.append(f"- **{rounds} rounds** of structured debate")
    output_parts.append(
        "- **Full context accumulation**: every model receives the complete "
        "original context + ALL prior debate responses in every round"
    )
    output_parts.append(
        f"- **Context source**: `{context_file}` "
        f"({len(context)} chars, ~{len(context)//4} tokens)"
    )
    output_parts.append("")
    output_parts.append("---\n")

    # ── Run Rounds ──
    for round_num in range(1, rounds + 1):
        round_start = time.time()

        print(f"\n{'='*60}")
        print(f"  ROUND {round_num} of {rounds}")
        print(f"  Transcript so far: {len(transcript)} entries, "
              f"~{sum(len(e['response']) for e in transcript)} chars")
        print(f"{'='*60}")

        output_parts.append(f"## ROUND {round_num}\n")

        # Get round-specific instructions
        r_instructions = ""
        if round_instructions and round_num in round_instructions:
            r_instructions = round_instructions[round_num]

        # Build prompts for each model (can differ in role assignment)
        prompts = {}
        for m in models:
            display_name, _ = MODEL_REGISTRY[m]
            prompts[m] = build_prompt(
                original_context=context,
                topic=topic,
                transcript=transcript,
                model_display_name=display_name,
                round_num=round_num,
                total_rounds=rounds,
                round_instructions=r_instructions,
            )
            prompt_tokens = len(prompts[m]) // 4  # rough estimate
            print(f"  {display_name}: prompt ~{prompt_tokens} tokens")

        # Call all models in parallel
        responses = {}
        with ThreadPoolExecutor(max_workers=len(models)) as executor:
            futures = {}
            for m in models:
                display_name, caller = MODEL_REGISTRY[m]
                print(f"  >> Calling {display_name}...")
                futures[executor.submit(caller, prompts[m], timeout)] = m

            for future in as_completed(futures):
                m = futures[future]
                display_name, _ = MODEL_REGISTRY[m]
                try:
                    response = future.result()
                    responses[m] = response
                    resp_len = len(response)
                    is_error = response.startswith("[ERROR")
                    status = "FAIL" if is_error else "OK"
                    print(
                        f"  << {display_name}: {status} "
                        f"({resp_len} chars, ~{resp_len//4} tokens)"
                    )
                except Exception as e:
                    responses[m] = f"[ERROR: {type(e).__name__}: {e}]"
                    print(f"  << {display_name}: EXCEPTION — {e}")

        # Add responses to transcript and output
        for m in models:
            display_name, _ = MODEL_REGISTRY[m]
            response = responses.get(m, "[No response received]")

            # Add to accumulated transcript (will be included in future rounds)
            transcript.append(
                {"round": round_num, "model": display_name, "response": response}
            )

            # Add to output document
            output_parts.append(f"### {display_name}\n")
            output_parts.append(response)
            output_parts.append("")

        round_elapsed = time.time() - round_start
        output_parts.append(
            f"*Round {round_num} completed in {round_elapsed:.0f}s*\n"
        )
        output_parts.append("---\n")

        # Write incrementally after each round (don't lose progress on crash)
        Path(output_file).parent.mkdir(parents=True, exist_ok=True)
        Path(output_file).write_text("\n".join(output_parts))
        print(f"  -> Written to {output_file} (incremental)")

    # ── Final Summary ──
    output_parts.append("## DEBATE STATISTICS\n")
    output_parts.append(f"- **Rounds**: {rounds}")
    output_parts.append(f"- **Models**: {len(models)}")
    output_parts.append(f"- **Total responses**: {len(transcript)}")
    total_chars = sum(len(e["response"]) for e in transcript)
    output_parts.append(f"- **Total debate text**: {total_chars} chars (~{total_chars//4} tokens)")
    errors = sum(1 for e in transcript if e["response"].startswith("[ERROR"))
    if errors:
        output_parts.append(f"- **Errors**: {errors} responses failed")
    output_parts.append("")

    # Write final version
    Path(output_file).write_text("\n".join(output_parts))

    print(f"\n{'='*60}")
    print(f"  DEBATE COMPLETE")
    print(f"  {rounds} rounds, {len(models)} models, {len(transcript)} responses")
    print(f"  Total text: ~{total_chars//4} tokens")
    if errors:
        print(f"  Errors: {errors}")
    print(f"  Output: {output_file}")
    print(f"{'='*60}")


# ══════════════════════════════════════════════════════════════════
# CLI
# ══════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="Multi-AI Debate Orchestrator — full context accumulation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic 4-round debate
  python3 scripts/debate.py \\
    --context docs/progress.md \\
    --topic "Best proof strategy for Tuza tau<=8" \\
    --rounds 4 \\
    --output docs/debate_feb8.md

  # 2-round quick debate with custom instructions
  python3 scripts/debate.py \\
    --context docs/context.md \\
    --topic "Should we use approach A or B?" \\
    --rounds 2 \\
    --models grok,gemini \\
    --output docs/debate.md \\
    --round-instructions instructions.json

  # Single model deep analysis (no debate, just structured rounds)
  python3 scripts/debate.py \\
    --context docs/context.md \\
    --topic "Analyze the proof gaps" \\
    --rounds 2 \\
    --models grok \\
    --output docs/analysis.md
        """,
    )
    parser.add_argument(
        "--context", required=True, help="Path to context file (will be included in every prompt)"
    )
    parser.add_argument("--topic", required=True, help="Debate topic / question")
    parser.add_argument(
        "--rounds", type=int, default=4, help="Number of debate rounds (default: 4)"
    )
    parser.add_argument("--output", required=True, help="Output markdown file path")
    parser.add_argument(
        "--models",
        default="grok,gemini,codex",
        help="Comma-separated model list (default: grok,gemini,codex)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Per-model timeout in seconds (default: 300)",
    )
    parser.add_argument(
        "--round-instructions",
        type=str,
        default=None,
        help="JSON file with per-round instructions: {\"1\": \"...\", \"2\": \"...\"}",
    )

    args = parser.parse_args()

    models = [m.strip() for m in args.models.split(",")]

    round_instructions = None
    if args.round_instructions:
        ri_path = Path(args.round_instructions)
        if not ri_path.exists():
            print(f"ERROR: Round instructions file not found: {args.round_instructions}")
            sys.exit(1)
        with open(ri_path) as f:
            raw = json.load(f)
            round_instructions = {int(k): v for k, v in raw.items()}

    run_debate(
        context_file=args.context,
        topic=args.topic,
        rounds=args.rounds,
        output_file=args.output,
        models=models,
        round_instructions=round_instructions,
        timeout=args.timeout,
    )


if __name__ == "__main__":
    main()
