"""research_fusion — Stages 1-3 of the F7 cross-domain pipeline.

Stages own:
    Stage 1 — Literature breadth     (stage1_literature.py)
    Stage 2 — Analogy mining         (stage2_analogy.py)
    Stage 3 — Technique transfer     (stage3_techniques.py)

I8 owns Stage 4 (fusion sketch) and Stage 5 (Aristotle + project.ask follow-up).

Conventions
-----------
- Per-problem dossiers live under research_fusion/runs/<problem_id>/
- All stages emit a markdown report + a JSON companion (matching schemas/).
- Cache hits are determined by problem_id + a 7-day TTL on the source markdown.
- Stages NEVER call safe_aristotle_submit.py — they only assemble context.
"""

__all__ = [
    "stage1_literature",
    "stage2_analogy",
    "stage3_techniques",
]

ROOT = __file__.rsplit("/", 1)[0]
RUNS_DIR = f"{ROOT}/runs"
PROMPTS_DIR = f"{ROOT}/prompts"
SCHEMAS_DIR = f"{ROOT}/schemas"
CACHE_DIR = f"{ROOT}/cache"

# 7 days in seconds — cache TTL for stage outputs and arXiv/forum fetches.
CACHE_TTL_SECONDS = 7 * 24 * 60 * 60
