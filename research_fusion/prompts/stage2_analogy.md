# Stage 2 — Analogy Mining Prompt (shared across Grok/Gemini/Codex)

You are consulting on an open mathematics problem. You are NOT asked to prove
it. You are asked for structural analogies in OTHER math areas.

PROBLEM (bare statement, do not propose to modify it)
```lean
{bare_statement}
```

ENGLISH GLOSS
{english_abstract}

HOME DOMAIN
{home_domain} (forbidden — your analogs must be from OTHER domains)

RECENT LITERATURE IN ADJACENT DOMAINS (pre-curated, NOT exhaustive)
{literature_block}

YOUR TASK
Identify 5-10 STRUCTURALLY SIMILAR problems in OTHER math areas. For each, give:

1. `analog_problem` — short name, e.g. "Erdős-Ko-Rado theorem".
2. `analog_domain` — the home of the analog (must NOT be {home_domain}).
3. `named_technique` — the technique that closed it OR made the strongest
   partial progress. Must be a named, citable technique
   (Frey curve, polynomial method, Bilu-Tichy, multidim sieve, slice rank,
   semidefinite programming, entropy compression, etc.).
4. `structural_map` — ONE sentence: what structural feature in our problem
   corresponds to what structural feature in the analog.
5. `obstruction` — ONE sentence: what would block the transfer to our problem.
   "None obvious" is acceptable but rare.
6. `confidence` — integer 1-5, how strong is the structural analogy?
   - 5 = direct same-shape correspondence (e.g. parity problems mapping to
        parity problems)
   - 1 = vague metaphorical resemblance

OUTPUT FORMAT — return a JSON array of objects with EXACTLY these keys, then a
short prose section explaining your top pick. Use a code fence so the orchestrator
can parse the JSON:

```json
[
  {
    "analog_id": "A1",
    "analog_problem": "...",
    "analog_domain": "...",
    "named_technique": "...",
    "structural_map": "...",
    "obstruction": "...",
    "confidence": 4
  }
]
```

After the JSON, write a single paragraph (<= 8 sentences) titled
`## Top pick rationale` justifying the highest-confidence analog you returned.

CRITICAL HONESTY GUARDRAILS
- We are NOT asking you to write a proof.
- If no honest cross-domain analogy exists, return `[]` and say so in the
  rationale paragraph. An empty list is a valid answer.
- Do NOT name techniques you cannot cite to a specific seminal paper.
- The home domain `{home_domain}` is forbidden for the `analog_domain` field.
