#!/usr/bin/env python3
"""
EXP3: Cross-Domain Analog Mining Experiment

Runs the same cross-domain analog prompt across 3 models (Grok-4, Gemini-2.5-Pro,
Codex/GPT-5.x) over 4 domains (physics, CS, biology, economics) for 2 target
problems (E938, E373). Total: 24 LLM calls.

The prompt forces the LLM out of its mathematical-analog comfort zone into
specifically NON-MATHEMATICAL domains where structural analogies might exist.

Hypothesis (A2 prediction): "LLMs retrieve and recombine, they do not invent."
If A2 is correct, cross-domain analogs should reduce to surface-level keyword
matches with no genuinely new attack vectors.
"""

import json
import os
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

# Grok rate-limit lock — serialize Grok calls
_GROK_LOCK = threading.Lock()

ROOT = Path("/Users/patrickkavanagh/math")
SCRIPTS = ROOT / "scripts"
RAW_DIR = ROOT / "analysis" / "exp3_raw"
RAW_DIR.mkdir(parents=True, exist_ok=True)

# -- Problem definitions ---------------------------------------------------

E938_STATEMENT = (
    "Let A = {n_1 < n_2 < ...} be the sequence of powerful numbers "
    "(integers n such that if a prime p divides n, then p^2 divides n). "
    "Erdős conjectured (Problem 938) that there are only finitely many "
    "three-term arithmetic progressions of CONSECUTIVE terms n_k, n_{k+1}, n_{k+2}. "
    "Powerful numbers have density 0; classical Roth-type density results do "
    "not apply. The gap sequence (n_{k+1} - n_k) is irregular. Known: "
    "Habsieger 2019 verified no solutions exist for small ranges; van Doorn 2026 "
    "found very-large non-consecutive AP triples among powerful numbers."
)

E938_STRUCTURE = (
    "STRUCTURE: A combinatorial problem about a deterministic zero-density "
    "sequence defined by a MULTIPLICATIVE predicate (prime-squarefull). The "
    "target is a SECOND-ORDER pattern (consecutiveness of an AP) — distinct "
    "from finding any AP. The gap function is shaped by additive interactions "
    "between multiplicative shells (kernel/squarepart factorization). Known "
    "tools (Roth, Szemerédi, cap-set slice-rank) all require positive density "
    "or finite-field structure. Local-global obstructions (mod 72) do not "
    "close because admissible AP triples mod-N GROWS with N."
)

E373_STATEMENT = (
    "Erdős/Surányi conjectured (Problem 373) that the only solution in "
    "integers ≥ 2 to the equation n! = a! · b! (with n > a ≥ b ≥ 2) is "
    "(n,a,b) = (10,7,6) — i.e., 10! = 7! · 6!. The conjecture predicts "
    "finiteness; only one solution is known. Habsieger 2019 verified up to "
    "C ≤ 10^3000. Luca 2007 gives conditional finiteness on ABC. The "
    "Stirling–Bernoulli expansion of log Γ provides a high-order analytic "
    "constraint, but turning it into a finite check requires bounding (n - a) "
    "uniformly (Erdős 1993 gives a_1 ≥ n - 5 log log n)."
)

E373_STRUCTURE = (
    "STRUCTURE: A Diophantine equation in 3 variables (n, a, b) where both "
    "sides are EXPONENTIALLY-GROWING multiplicative objects (factorials). "
    "The equation forces a near-cancellation between log Γ(n+1) and "
    "log Γ(a+1) + log Γ(b+1). Asymptotic expansion produces a finite-dim "
    "constraint, but it lives in real coordinates while solutions live in "
    "integers. The TENSION is: continuous near-cancellation must support "
    "an integer-valued exact identity at exactly one (n,a,b). The known "
    "solution (10,7,6) is a tiny isolated exceptional case."
)

DOMAINS = [
    ("physics", "physics (statistical mechanics, gauge theory, condensed matter, phase transitions, renormalization group)"),
    ("cs", "computer science (complexity theory, algorithms, distributed systems, formal languages, automata)"),
    ("biology", "biology (evolutionary dynamics, network theory, ecology, population genetics, protein folding)"),
    ("economics", "economics (auction theory, equilibrium, mechanism design, game theory, financial markets)")
]

# -- Prompt construction ---------------------------------------------------

PROMPT_TEMPLATE = """You are a cross-domain mathematician searching for DEEP STRUCTURAL ANALOGS — not surface keyword matches.

PROBLEM:
{problem_statement}

{structure}

TASK: Find the deepest structural analog to this problem in {domain_description}.

CRITICAL: Do NOT propose mathematical analogs (no Roth, no cap-set, no Szemerédi, no removal lemmas, no slice-rank, no Bombieri-Lang, no ABC, no L-functions, no sieve methods, no Mordell-Weil). These have already been mined. Your job is to find the OFF-DOMAIN analog.

For your chosen analog, give:

(i) THE ANALOG PROBLEM: Name and one-sentence statement of the problem in the target domain that has the SAME structural shape (sparse deterministic set + second-order pattern, or near-cancellation of multiplicative quantities). Be specific — name researchers, papers, equations.

(ii) THE TECHNIQUE THAT SOLVED IT THERE: The named method/argument (e.g., "renormalization group flow with relevant operator analysis at the Wilson-Fisher fixed point"). If unsolved in the target domain, name the most successful partial result.

(iii) THE OBSTRUCTION TO DIRECT TRANSPLANT: What property of the original problem fails the precondition of the technique? Be precise about the failure mode.

(iv) THE BRIDGE: A SPECIFIC modification of either the technique or the problem reformulation that bridges the obstruction. This must be CONCRETE — a defined object, a measurable parameter, a function to compute. Not "consider an analogous structure" — produce a named construction with explicit ingredients.

FORMAT: 4 numbered paragraphs (i)-(iv), 100-200 words each. Be terse and technical. If no genuine analog exists in this domain, say so directly with one sentence of explanation — do NOT fabricate.

REMEMBER: The user knows the standard mathematical analogs. We are searching for a NON-OBVIOUS bridge. Surprise us, or admit there is no bridge here.
"""


def build_prompt(problem_key: str, domain_key: str) -> str:
    if problem_key == "E938":
        stmt, struct = E938_STATEMENT, E938_STRUCTURE
    elif problem_key == "E373":
        stmt, struct = E373_STATEMENT, E373_STRUCTURE
    else:
        raise ValueError(problem_key)
    domain_desc = next(d for k, d in DOMAINS if k == domain_key)
    return PROMPT_TEMPLATE.format(
        problem_statement=stmt, structure=struct, domain_description=domain_desc
    )


# -- Model runners ---------------------------------------------------------

def run_grok(prompt: str, timeout: int = 600) -> str:
    """Run Grok-4 via the project's grok_query.py with retry on transient errors.

    SERIALIZED via a global lock to avoid the xAI throttle that surfaces as
    "model grok-4 does not exist" responses under concurrent load.
    """
    last_err = ""
    with _GROK_LOCK:
        for attempt in range(4):
            result = subprocess.run(
                ["python3", str(SCRIPTS / "grok_query.py"), prompt, str(timeout)],
                capture_output=True, text=True, timeout=timeout + 60
            )
            if result.returncode != 0:
                last_err = f"GROK ERROR (rc={result.returncode}): {result.stderr[:500]}"
                time.sleep(15 * (attempt + 1))
                continue
            body = result.stdout.strip()
            is_error = (
                body.startswith("API ERROR")
                or body.startswith("ERROR")
                or "does not exist or your team" in body
            )
            if is_error:
                last_err = body[:500]
                time.sleep(15 * (attempt + 1))
                continue
            return result.stdout
        return f"GROK FAILED 4 attempts. Last error: {last_err}"


def run_gemini(prompt: str, timeout: int = 600) -> str:
    """Run Gemini-2.5-Pro via gemini CLI in non-interactive mode."""
    result = subprocess.run(
        ["gemini", "-m", "gemini-2.5-pro", "-p", prompt],
        capture_output=True, text=True, timeout=timeout
    )
    if result.returncode != 0:
        return f"GEMINI ERROR (rc={result.returncode}): {result.stderr[:500]}\nSTDOUT: {result.stdout[:500]}"
    return result.stdout


def run_codex(prompt: str, timeout: int = 600) -> str:
    """Run Codex non-interactively."""
    result = subprocess.run(
        ["codex", "exec", prompt],
        capture_output=True, text=True, timeout=timeout
    )
    if result.returncode != 0:
        return f"CODEX ERROR (rc={result.returncode}): {result.stderr[:500]}\nSTDOUT: {result.stdout[:500]}"
    return result.stdout


MODELS = {
    "grok": run_grok,
    "gemini": run_gemini,
    "codex": run_codex,
}


# -- Driver ---------------------------------------------------------------

def run_one(problem_key: str, domain_key: str, model_key: str) -> dict:
    out_path = RAW_DIR / f"{problem_key}_{domain_key}_{model_key}.md"
    if out_path.exists() and out_path.stat().st_size > 200:
        print(f"  SKIP {out_path.name} (already exists)", flush=True)
        return {"problem": problem_key, "domain": domain_key, "model": model_key,
                "status": "cached", "path": str(out_path), "size": out_path.stat().st_size}
    prompt = build_prompt(problem_key, domain_key)
    t0 = time.time()
    try:
        body = MODELS[model_key](prompt)
    except subprocess.TimeoutExpired:
        body = f"TIMEOUT after {time.time()-t0:.1f}s"
    except Exception as e:
        body = f"EXCEPTION: {e}"
    elapsed = time.time() - t0
    header = f"# EXP3 — {problem_key} × {domain_key} × {model_key}\n"
    header += f"Prompt date: 2026-05-31  Elapsed: {elapsed:.1f}s  Bytes: {len(body)}\n\n"
    header += "## Prompt\n\n```\n" + prompt + "\n```\n\n## Response\n\n"
    out_path.write_text(header + body)
    print(f"  DONE {out_path.name}  ({elapsed:.1f}s, {len(body)}B)", flush=True)
    return {"problem": problem_key, "domain": domain_key, "model": model_key,
            "status": "ok" if "ERROR" not in body[:200] and "TIMEOUT" not in body[:50] else "err",
            "elapsed_s": elapsed, "bytes": len(body), "path": str(out_path)}


def main():
    problems = ["E938", "E373"]
    domain_keys = [k for k, _ in DOMAINS]
    model_keys = list(MODELS.keys())

    jobs = []
    for p in problems:
        for d in domain_keys:
            for m in model_keys:
                jobs.append((p, d, m))

    print(f"Running {len(jobs)} jobs (2 problems × 4 domains × 3 models)...", flush=True)
    results = []
    # Parallel but constrained: 3 at a time (one of each model) to avoid rate limits.
    with ThreadPoolExecutor(max_workers=3) as ex:
        futs = {ex.submit(run_one, p, d, m): (p, d, m) for (p, d, m) in jobs}
        for fut in as_completed(futs):
            try:
                results.append(fut.result())
            except Exception as e:
                p, d, m = futs[fut]
                print(f"  FAIL {p}/{d}/{m}: {e}", flush=True)
                results.append({"problem": p, "domain": d, "model": m,
                                "status": "exception", "error": str(e)})

    manifest = RAW_DIR / "manifest.json"
    manifest.write_text(json.dumps(results, indent=2))
    print(f"\nManifest: {manifest}")
    ok = sum(1 for r in results if r.get("status") in ("ok", "cached"))
    print(f"OK: {ok}/{len(results)}")


if __name__ == "__main__":
    main()
