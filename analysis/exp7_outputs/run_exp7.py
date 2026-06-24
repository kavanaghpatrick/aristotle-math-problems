#!/usr/bin/env python3
"""EXP7: wrong-first prompting harness.

Runs the 4-round protocol on E938 + E364 across Grok-4, Gemini, Codex.
Plus a baseline 'direct-correct' single-round prompt for comparison.

Outputs written to /Users/patrickkavanagh/math/analysis/exp7_outputs/
"""
from __future__ import annotations
import os, sys, json, subprocess, time, tempfile
from pathlib import Path

ROOT = Path("/Users/patrickkavanagh/math")
OUT = Path("/Users/patrickkavanagh/math/analysis/exp7_outputs")
OUT.mkdir(parents=True, exist_ok=True)

PROBLEMS = {
    "E938": (
        "Erdős 938. Let A = {n_1 < n_2 < ...} be the sequence of powerful numbers "
        "(n with p | n implies p^2 | n). Prove or disprove that only finitely many "
        "three-term arithmetic progressions n_k, n_{k+1}, n_{k+2} of CONSECUTIVE "
        "powerful numbers exist (consecutive in the powerful sequence, with the "
        "AP property, so n_{k+1} - n_k = n_{k+2} - n_{k+1})."
    ),
    "E364": (
        "Erdős 364. Prove or disprove: there do not exist three consecutive positive "
        "integers n, n+1, n+2 that are all powerful (every prime divisor of each "
        "appears with exponent >= 2). Pairs exist (e.g., 8, 9). No triple has ever "
        "been found. ABC implies finiteness."
    ),
}

ROUNDS = {
    "R1_wrong": (
        "This is an EDUCATIONAL EXERCISE IN ERROR ANALYSIS. The next round will ask "
        "you to find the errors. For this round, produce a proof attempt of the "
        "PROBLEM that LOOKS convincing on first reading but contains at least one "
        "subtle load-bearing error — the kind of error a graduate student might miss. "
        "Use real theorem names and standard mathematical machinery. Length 300-500 "
        "words. End the response with a one-line marker `# END OF ATTEMPT` (no "
        "discussion of errors yet — those go in Round 2).\n\nPROBLEM:\n{problem}\n\n"
        "Structure: state hypothesis, present the chain of reasoning, conclude. "
        "Treat this like a draft proof that needs error-checking — that's the "
        "academic exercise, the errors are intentional pedagogical seeds."
    ),
    "R2_find_failures": (
        "Below is a proof attempt of the following PROBLEM. Find 3 SPECIFIC PLACES "
        "where this proof fails. Be precise: cite the exact step, name the false "
        "claim or the missing justification, and explain why it is wrong.\n\n"
        "PROBLEM:\n{problem}\n\nPROOF ATTEMPT:\n{r1}\n\n"
        "Return exactly 3 numbered failures with one paragraph each."
    ),
    "R3_structural": (
        "For each of the following 3 failure modes in a proof of the PROBLEM "
        "below, identify the STRUCTURAL reason it cannot be fixed by a minor "
        "patch. That is, what deep feature of the problem makes the entire "
        "approach untenable, not just this particular instance?\n\n"
        "PROBLEM:\n{problem}\n\nFAILURES:\n{r2}\n\n"
        "Return 3 numbered structural diagnoses."
    ),
    "R4_correct_sketch": (
        "Use the structural reasons below to produce a SKETCH of a CORRECT proof "
        "(or a precise statement of what would be needed). If no correct proof is "
        "possible with current tools, say so and identify the smallest unconditional "
        "sub-result.\n\nPROBLEM:\n{problem}\n\nSTRUCTURAL DIAGNOSES:\n{r3}\n\n"
        "Be honest. If the structural diagnoses imply the problem is open, say so."
    ),
    "BASELINE": (
        "Prove the following problem directly. If you cannot prove it, identify "
        "the smallest unconditional sub-result you can prove and state precisely "
        "what is open. Target length: 300-500 words.\n\nPROBLEM:\n{problem}"
    ),
}


def query_grok(prompt: str, timeout: int = 300) -> str:
    api_key = os.environ.get("XAI_API_KEY") or os.environ.get("GROK_API_KEY")
    if not api_key:
        return "ERROR: no XAI_API_KEY"
    data = {
        "messages": [{"role": "user", "content": prompt}],
        "model": "grok-4",
        "max_tokens": 4000,
        "temperature": 0.5,
    }
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
        json.dump(data, f)
        tf = f.name
    try:
        r = subprocess.run(
            ["curl", "-s", "-X", "POST", "--max-time", str(timeout),
             "https://api.x.ai/v1/chat/completions",
             "-H", f"Authorization: Bearer {api_key}",
             "-H", "Content-Type: application/json",
             "-d", f"@{tf}"],
            capture_output=True, text=True, timeout=timeout + 30,
        )
        os.unlink(tf)
        if r.returncode != 0:
            return f"ERROR grok curl: {r.stderr[:400]}"
        try:
            j = json.loads(r.stdout)
            return j["choices"][0]["message"]["content"]
        except Exception as e:
            return f"ERROR grok parse: {e}\n{r.stdout[:1000]}"
    except subprocess.TimeoutExpired:
        return "ERROR grok timeout"


def query_gemini(prompt: str, timeout: int = 600) -> str:
    # Retry on quota errors with backoff
    for attempt in range(3):
        try:
            r = subprocess.run(
                ["gemini", "-p", prompt, "--approval-mode", "plan"],
                capture_output=True, text=True, timeout=timeout,
                stdin=subprocess.DEVNULL,
            )
            if r.returncode != 0:
                err = (r.stderr + r.stdout)[:800]
                if "quota" in err.lower() or "capacity" in err.lower():
                    time.sleep(30 * (attempt + 1))
                    continue
                return f"ERROR gemini rc={r.returncode}: {err}"
            return r.stdout
        except subprocess.TimeoutExpired:
            return "ERROR gemini timeout"
    return "ERROR gemini quota exhausted after retries"


def query_codex(prompt: str, timeout: int = 900) -> str:
    try:
        r = subprocess.run(
            ["codex", "exec", "--sandbox", "read-only", "--skip-git-repo-check",
             "-c", "model_reasoning_effort=\"medium\"", prompt],
            capture_output=True, text=True, timeout=timeout,
            stdin=subprocess.DEVNULL,
        )
        if r.returncode != 0:
            return f"ERROR codex rc={r.returncode}: {r.stderr[:600]}\nSTDOUT: {r.stdout[:600]}"
        # Strip preamble; codex output ends with the model response after the last "--------"
        out = r.stdout
        # find last "codex" header marker
        sep = "\ncodex\n"
        idx = out.rfind(sep)
        if idx >= 0:
            tail = out[idx + len(sep):]
            # cut "tokens used" trailer
            tu = tail.rfind("\ntokens used")
            if tu >= 0:
                tail = tail[:tu]
            return tail.strip()
        return out.strip()
    except subprocess.TimeoutExpired:
        return "ERROR codex timeout"


MODELS = {"grok": query_grok, "gemini": query_gemini, "codex": query_codex}


def run_one(problem_key: str, model_name: str):
    problem = PROBLEMS[problem_key]
    query = MODELS[model_name]
    transcript = {}

    # Baseline
    bpath = OUT / f"{problem_key}_{model_name}_BASELINE.md"
    if bpath.exists():
        baseline = bpath.read_text()
        print(f"  [{problem_key}/{model_name}] BASELINE cached")
    else:
        print(f"  [{problem_key}/{model_name}] BASELINE running...")
        t0 = time.time()
        baseline = query(ROUNDS["BASELINE"].format(problem=problem))
        bpath.write_text(baseline)
        print(f"  [{problem_key}/{model_name}] BASELINE done in {time.time()-t0:.0f}s")
    transcript["BASELINE"] = baseline

    # Round 1: wrong
    p1 = OUT / f"{problem_key}_{model_name}_R1.md"
    if p1.exists():
        r1 = p1.read_text()
        print(f"  [{problem_key}/{model_name}] R1 cached")
    else:
        print(f"  [{problem_key}/{model_name}] R1 running...")
        t0 = time.time()
        r1 = query(ROUNDS["R1_wrong"].format(problem=problem))
        p1.write_text(r1)
        print(f"  [{problem_key}/{model_name}] R1 done in {time.time()-t0:.0f}s")
    transcript["R1"] = r1

    # Round 2: find failures
    p2 = OUT / f"{problem_key}_{model_name}_R2.md"
    if p2.exists():
        r2 = p2.read_text()
        print(f"  [{problem_key}/{model_name}] R2 cached")
    else:
        print(f"  [{problem_key}/{model_name}] R2 running...")
        t0 = time.time()
        r2 = query(ROUNDS["R2_find_failures"].format(problem=problem, r1=r1))
        p2.write_text(r2)
        print(f"  [{problem_key}/{model_name}] R2 done in {time.time()-t0:.0f}s")
    transcript["R2"] = r2

    # Round 3: structural
    p3 = OUT / f"{problem_key}_{model_name}_R3.md"
    if p3.exists():
        r3 = p3.read_text()
        print(f"  [{problem_key}/{model_name}] R3 cached")
    else:
        print(f"  [{problem_key}/{model_name}] R3 running...")
        t0 = time.time()
        r3 = query(ROUNDS["R3_structural"].format(problem=problem, r2=r2))
        p3.write_text(r3)
        print(f"  [{problem_key}/{model_name}] R3 done in {time.time()-t0:.0f}s")
    transcript["R3"] = r3

    # Round 4: correct sketch
    p4 = OUT / f"{problem_key}_{model_name}_R4.md"
    if p4.exists():
        r4 = p4.read_text()
        print(f"  [{problem_key}/{model_name}] R4 cached")
    else:
        print(f"  [{problem_key}/{model_name}] R4 running...")
        t0 = time.time()
        r4 = query(ROUNDS["R4_correct_sketch"].format(problem=problem, r3=r3))
        p4.write_text(r4)
        print(f"  [{problem_key}/{model_name}] R4 done in {time.time()-t0:.0f}s")
    transcript["R4"] = r4

    return transcript


if __name__ == "__main__":
    only_model = sys.argv[1] if len(sys.argv) > 1 else None
    only_problem = sys.argv[2] if len(sys.argv) > 2 else None
    for problem in (["E938", "E364"] if not only_problem else [only_problem]):
        for model in (["grok", "gemini", "codex"] if not only_model else [only_model]):
            print(f"\n=== {problem} / {model} ===")
            try:
                run_one(problem, model)
            except Exception as e:
                print(f"  ERROR: {e}")
    print("\nDone.")
