#!/usr/bin/env python3
"""EXP2 driver for Grok-4: three rounds of adversarial counter-conjecture prompting on E938."""
import json
import os
import sys
import time
from pathlib import Path
import urllib.request
import urllib.error

API_KEY = os.environ.get("XAI_API_KEY") or os.environ.get("GROK_API_KEY")
if not API_KEY:
    sys.exit("XAI_API_KEY / GROK_API_KEY not set")

ENDPOINT = "https://api.x.ai/v1/chat/completions"
MODEL = "grok-4-0709"

OUTDIR = Path("/Users/patrickkavanagh/math/analysis/exp2_runs")
OUTDIR.mkdir(parents=True, exist_ok=True)

PROBLEM_BLOCK = """\
TARGET PROBLEM: Erdős 938 — Powerful-number consecutive 3-AP conjecture.

Formal statement: Let A = {n_1 < n_2 < ...} be the strictly increasing sequence of
"powerful numbers" (n such that every prime p | n satisfies p^2 | n). The conjecture
is that the set of indices k for which (n_k, n_{k+1}, n_{k+2}) is a 3-term
arithmetic progression is FINITE.

Equivalently: are there only finitely many k with 2 n_{k+1} = n_k + n_{k+2}?

Known data:
- Exactly 6 such triples below 10^10, falling into two scaling families:
  F1: (48,49,50) * k^2 for k ∈ {6, 12}  → (1728,1764,1800), (6912,7056,7200)
  F2: (729000,729316,729632) * m for m ∈ {1, 2, 4, 16}
- van Doorn 2026 (arXiv:2605.06697) Conj 5 asserts the conjecture is FALSE via the
  Pell family x^2 - 7^3 y^2 = 2, generating triples ((x-2)^2, (x-1)^2, 7^3 y^2).
  First solution (11427, 617): triple (130530625, 130553476, 130576327) — REAL AP
  of powerfuls but has 5 intermediate powerful integers, so NOT consecutive.
- Chan 2022 (arXiv:2210.00281): under abc, common difference d ≫_ε N^{1/2-ε}.

OPEN: is the conjecture TRUE (finitely many) or FALSE (infinitely many)?
"""

ROUND_A = """\
ROUND A — FALSIFY.

The conjecture is FALSE. Construct an explicit counterexample family for Erdős 938.

Constraints:
1. Defend a specific construction that, if it works, exhibits INFINITELY MANY
   consecutive powerful 3-APs.
2. Find the WEAKEST structural point in the conjecture — the place where it is
   most vulnerable to disproof. Name the invariant that you expect to violate.
3. Argue (1000 words) for the most plausible falsification path. Use Pell-family
   constructions, Frey-curve obstructions reversed, or any genuine algebraic
   structure — but commit to ONE explicit construction and defend it.

Be specific. Give parameters. Give the first 2-3 predicted triples. Argue why
intermediate-powerful-density does NOT obstruct your family.
"""

ROUND_B = """\
ROUND B — REFUTE YOUR OWN FALSIFICATION.

Now switch sides. The construction you defended in Round A is wrong. Find the
structural reason your counterexample family does NOT actually disprove Erdős 938.

Constraints:
1. Identify the specific invariant of your Pell/algebraic family that PREVENTS
   it from producing infinitely many consecutive triples. (e.g., does the density
   of intermediate powerfuls grow faster than your family separation? Is there
   an algebraic obstruction in the intervening interval?)
2. Be quantitative. Give a heuristic or actual count.
3. ~800 words.

Do not retreat to "abc implies finiteness". Find the structural defect in YOUR
family.
"""

ROUND_C = """\
ROUND C — SYNTHESIZE.

What did the failed counterexample reveal about the STRUCTURE of the conjecture?

Constraints:
1. Name ONE load-bearing invariant that the conjecture implicitly asserts —
   something neither Chan, Mollin-Walsh, van Doorn, Heath-Brown, nor existing
   abc-conditional proofs make explicit.
2. State that invariant as a candidate LEMMA that, if proved unconditionally,
   would either resolve E938 or sharply reduce it to a tractable Diophantine
   problem.
3. Distinguish your invariant from the standard four (square-gap bound,
   Pell-family count, level-of-distribution, ternary Mordell-Siegel). If you
   can't, say so honestly.
4. ~600 words.

The point is to produce something the direct-prove literature has missed.
"""

def call_grok(messages, retry=3):
    payload = {
        "model": MODEL,
        "messages": messages,
        "temperature": 0.5,
        "max_tokens": 8000,
    }
    body = json.dumps(payload).encode()
    req = urllib.request.Request(
        ENDPOINT,
        data=body,
        headers={
            "Authorization": f"Bearer {API_KEY}",
            "Content-Type": "application/json",
        },
    )
    last_err = None
    for attempt in range(retry):
        try:
            with urllib.request.urlopen(req, timeout=300) as resp:
                data = json.loads(resp.read().decode())
                return data["choices"][0]["message"]["content"]
        except urllib.error.HTTPError as e:
            last_err = f"HTTP {e.code}: {e.read().decode()[:500]}"
            print(f"  attempt {attempt+1} failed: {last_err}", file=sys.stderr)
            time.sleep(5 * (attempt + 1))
        except Exception as e:
            last_err = str(e)
            print(f"  attempt {attempt+1} failed: {last_err}", file=sys.stderr)
            time.sleep(5 * (attempt + 1))
    raise RuntimeError(f"Grok failed after {retry} attempts: {last_err}")


def main():
    transcript = []
    # Seed
    transcript.append({"role": "user", "content": PROBLEM_BLOCK + "\n\n" + ROUND_A})
    print("Round A: falsify ...", file=sys.stderr)
    a = call_grok(transcript)
    transcript.append({"role": "assistant", "content": a})
    (OUTDIR / "grok_round_A.md").write_text(
        f"# Grok-4 Round A — Falsify\n\n**Model:** {MODEL}\n\n**Prompt:**\n\n{PROBLEM_BLOCK}\n\n{ROUND_A}\n\n---\n\n# Response\n\n{a}\n"
    )
    print(f"Round A: {len(a)} chars", file=sys.stderr)

    transcript.append({"role": "user", "content": ROUND_B})
    print("Round B: refute ...", file=sys.stderr)
    b = call_grok(transcript)
    transcript.append({"role": "assistant", "content": b})
    (OUTDIR / "grok_round_B.md").write_text(
        f"# Grok-4 Round B — Refute self\n\n**Model:** {MODEL}\n\n**Prompt:**\n\n{ROUND_B}\n\n---\n\n# Response\n\n{b}\n"
    )
    print(f"Round B: {len(b)} chars", file=sys.stderr)

    transcript.append({"role": "user", "content": ROUND_C})
    print("Round C: synthesize ...", file=sys.stderr)
    c = call_grok(transcript)
    transcript.append({"role": "assistant", "content": c})
    (OUTDIR / "grok_round_C.md").write_text(
        f"# Grok-4 Round C — Synthesize\n\n**Model:** {MODEL}\n\n**Prompt:**\n\n{ROUND_C}\n\n---\n\n# Response\n\n{c}\n"
    )
    print(f"Round C: {len(c)} chars", file=sys.stderr)

    # Full transcript
    with open(OUTDIR / "grok_full_transcript.json", "w") as f:
        json.dump(transcript, f, indent=2)
    print("DONE: Grok 3-round transcript saved.", file=sys.stderr)


if __name__ == "__main__":
    main()
