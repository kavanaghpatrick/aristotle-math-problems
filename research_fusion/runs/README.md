# research_fusion/runs/ — per-problem dossier convention

Each problem gets a directory named after its canonical id (lowercased,
underscored), e.g. `erdos_938/`. Stages write the following artifacts:

```
runs/<problem_id>/
    problem_card.json       # Input — written once by stage0 (caller) or by
                            #         stage1 if absent.
    01_literature.md        # Stage 1 markdown report
    01_literature.json      # Stage 1 structured payload (matches the
                            # `literature` block in fusion_candidate.schema.json)
    02_analogies.md         # Stage 2 markdown — 3-AI debate transcript +
                            # consolidated top analog list
    02_analogies.json       # Stage 2 structured payload
    03_techniques.md        # Stage 3 markdown — 3-5 technique cards
    03_techniques.json      # Stage 3 structured payload
    fusion_candidate.json   # Aggregated dossier (matches
                            # fusion_candidate.schema.json). Stage 3 writes
                            # this; Stage 4 reads it.
    .cache/                 # Per-stage cached intermediate artefacts
                            # (arxiv pulls, model transcripts). 7-day TTL.
```

## Cache invalidation

Caching is per-stage and per-problem:
- Stage 1 caches each arXiv query result for 7 days, keyed on
  (problem_id, domain, query_string).
- Stage 2 caches the debate transcript for 7 days, keyed on
  (problem_id, sha256(prompt)).
- Stage 3 caches each technique-card response for 7 days, keyed on
  (problem_id, analog_id, technique_name).
- To force a re-run, delete `runs/<problem_id>/.cache/`.

## Adding a new problem

Either:
1. Call `python3 -m research_fusion.stage1_literature --problem-id <id>` —
   it will auto-generate a minimal `problem_card.json` from
   `formal-conjectures/FormalConjectures/ErdosProblems/<n>.lean` for Erdős
   problems; OR
2. Pre-write `runs/<id>/problem_card.json` matching
   `schemas/problem_card.schema.json` for non-Erdős problems.

Then run `mk fusion <problem_id>` to execute Stages 1-3 in sequence.

## What's NOT in this directory

- The actual fusion-lane `.txt` sketch (Stage 4, owned by I8).
- Aristotle results / `.fusion.json` companions (Stage 5, owned by I8).
- Submission metadata in tracking.db (owned by safe_aristotle_submit.py).

This directory is a pure research dossier. Submission lives elsewhere.
