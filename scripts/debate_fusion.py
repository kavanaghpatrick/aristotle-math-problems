#!/usr/bin/env python3
"""
debate_fusion.py — wrapper around scripts/debate.py for cross-domain technique scouting.

Wires up a debate-templates/<template>.md prompt with a problem ID and any
existing Stage-1 literature context (analysis/research_fusion_<id>.md), then
calls scripts/debate.py with the right --context, --topic, --output.

Usage:
  python3 scripts/debate_fusion.py erdos_938 --template technique_scout --rounds 3
  python3 scripts/debate_fusion.py erdos_938 --template adjacent_analog --rounds 2
  python3 scripts/debate_fusion.py erdos_938 --template bias_flush --models grok,gemini

Templates live in research_fusion/prompts/debate_templates/.
Output lands in research_fusion/runs/<problem_id>/debates/<template>.md.
"""

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
DEBATE_SCRIPT = REPO_ROOT / "scripts" / "debate.py"
TEMPLATES_DIR = REPO_ROOT / "research_fusion" / "prompts" / "debate_templates"
RUNS_DIR = REPO_ROOT / "research_fusion" / "runs"


def find_problem_context(problem_id: str) -> Path:
    """Find an existing Stage-1 literature dossier for the problem, if any.

    Tries several common naming variants:
      - exact ``problem_id`` as given
      - underscore-normalised (e.g. ``erdos-938`` -> ``erdos_938``)
      - compact form, no separators (e.g. ``erdos_938`` -> ``erdos938``)
      - compact lowercase

    Across the standard dossier locations:
      1. analysis/research_fusion_<variant>.md
      2. docs/research/<variant>.md
      3. docs/debate_context_<variant>.md

    Returns the first match, or raises FileNotFoundError if none exist.
    """
    underscored = problem_id.replace("-", "_").lower()
    compact = underscored.replace("_", "")
    variants = []
    for v in [problem_id, underscored, compact]:
        if v not in variants:
            variants.append(v)

    locations = [
        ("analysis", "research_fusion_{}.md"),
        ("docs/research", "{}.md"),
        ("docs", "debate_context_{}.md"),
    ]

    candidates: list[Path] = []
    for v in variants:
        for subdir, pattern in locations:
            candidates.append(REPO_ROOT / subdir / pattern.format(v))

    for c in candidates:
        if c.exists():
            return c
    raise FileNotFoundError(
        f"No Stage-1 literature dossier found for {problem_id}. "
        f"Searched: {[str(c) for c in candidates]}"
    )


def extract_prompt_body(template_path: Path) -> str:
    """Extract the prompt body from a template file.

    Templates have a ``## Sample prompt body`` section with a fenced code block
    containing the actual prompt. We extract that block. If the template lacks
    that section, the entire file is used (legacy templates).
    """
    text = template_path.read_text()
    marker = "## Sample prompt body"
    if marker in text:
        body = text.split(marker, 1)[1]
        # Find first fenced code block
        if "```" in body:
            first_fence = body.index("```")
            after = body[first_fence + 3:]
            # Skip optional language tag
            if "\n" in after:
                after = after[after.index("\n") + 1:]
            end_fence = after.index("```")
            return after[:end_fence].strip()
    return text.strip()


def main():
    parser = argparse.ArgumentParser(
        description="Cross-domain technique-scouting debate wrapper.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Available templates (in research_fusion/prompts/debate_templates/):
  technique_scout       — 5 cross-domain techniques per AI
  adjacent_analog       — 3-5 structurally isomorphic closed problems
  tao_simulator         — Tao's first 3 moves (roleplay)
  bias_flush            — adversarial critique of our default toolkit
  bridge_lemma          — single bridge lemma to factor the problem
  obstruction_diagnosis — why has the problem resisted attack?

Examples:
  python3 scripts/debate_fusion.py erdos_938 --template technique_scout
  python3 scripts/debate_fusion.py erdos_938 --template bridge_lemma --rounds 2
  python3 scripts/debate_fusion.py erdos_938 --template tao_simulator --models gemini,codex
        """,
    )
    parser.add_argument(
        "problem_id",
        help="Problem ID (e.g. erdos_938, ft_p3, brocard). Used for context lookup and output path.",
    )
    parser.add_argument(
        "--template",
        required=True,
        help="Template name (without .md extension).",
    )
    parser.add_argument(
        "--rounds",
        type=int,
        default=3,
        help="Number of debate rounds (default: 3).",
    )
    parser.add_argument(
        "--models",
        default="grok,gemini,codex",
        help="Comma-separated model list (default: grok,gemini,codex).",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Per-model timeout (seconds, default: 300).",
    )
    parser.add_argument(
        "--context",
        default=None,
        help="Override context file path (default: auto-pull from analysis/ or docs/research/).",
    )
    parser.add_argument(
        "--output",
        default=None,
        help="Override output path (default: research_fusion/runs/<problem>/debates/<template>.md).",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print the command that would be run without executing.",
    )
    args = parser.parse_args()

    # Resolve template
    template_path = TEMPLATES_DIR / f"{args.template}.md"
    if not template_path.exists():
        available = sorted(p.stem for p in TEMPLATES_DIR.glob("*.md"))
        print(f"ERROR: Template not found: {template_path}", file=sys.stderr)
        print(f"Available templates: {available}", file=sys.stderr)
        sys.exit(1)

    # Resolve context
    if args.context:
        context_path = Path(args.context)
        if not context_path.exists():
            print(f"ERROR: Context file not found: {context_path}", file=sys.stderr)
            sys.exit(1)
    else:
        try:
            context_path = find_problem_context(args.problem_id)
            print(f"[debate_fusion] Auto-pulled context: {context_path}")
        except FileNotFoundError as e:
            print(f"[debate_fusion] WARNING: {e}", file=sys.stderr)
            print(
                "[debate_fusion] Proceeding with a minimal context stub. "
                "Consider running Stage-1 literature pull first for richer context.",
                file=sys.stderr,
            )
            # Write a minimal stub
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".md", delete=False
            ) as f:
                f.write(
                    f"# {args.problem_id}\n\n"
                    f"No Stage-1 literature dossier available. "
                    f"The LLMs should rely on their own knowledge of {args.problem_id}.\n"
                )
                context_path = Path(f.name)

    # Build prompt body from template, substituting {PROBLEM}
    prompt_body = extract_prompt_body(template_path)
    topic = prompt_body.replace("{PROBLEM}", args.problem_id)

    # Resolve output path
    if args.output:
        output_path = Path(args.output)
    else:
        output_path = RUNS_DIR / args.problem_id / "debates" / f"{args.template}.md"
    output_path.parent.mkdir(parents=True, exist_ok=True)

    # Build debate.py command
    # Note: --topic accepts a string; we pass the substituted prompt body.
    cmd = [
        "python3",
        str(DEBATE_SCRIPT),
        "--context", str(context_path),
        "--topic", topic,
        "--rounds", str(args.rounds),
        "--output", str(output_path),
        "--models", args.models,
        "--timeout", str(args.timeout),
    ]

    print(f"[debate_fusion] Problem:  {args.problem_id}")
    print(f"[debate_fusion] Template: {args.template} ({template_path})")
    print(f"[debate_fusion] Context:  {context_path}")
    print(f"[debate_fusion] Rounds:   {args.rounds}")
    print(f"[debate_fusion] Models:   {args.models}")
    print(f"[debate_fusion] Output:   {output_path}")

    if args.dry_run:
        print("[debate_fusion] DRY RUN — command would be:")
        print(" ".join(repr(x) if " " in x else x for x in cmd))
        return

    # Exec debate.py
    try:
        result = subprocess.run(cmd, check=False)
        sys.exit(result.returncode)
    except KeyboardInterrupt:
        print("\n[debate_fusion] Interrupted by user.", file=sys.stderr)
        sys.exit(130)


if __name__ == "__main__":
    main()
