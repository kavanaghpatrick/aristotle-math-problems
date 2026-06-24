#!/usr/bin/env python3
"""Build a critique prompt for one persona, then call Grok and write output."""
import os, sys, json, subprocess, tempfile

PERSONAS = {
    1: ("ADDITIVE COMBINATORIALIST",
        "additive combinatorialist (Tao/Green/Bloom paradigm: Fourier on Z/NZ, density increments, Croot-Lev-Pach polynomial method, Bohr sets, Plunnecke-Ruzsa)"),
    2: ("MULTIPLICATIVE NUMBER THEORIST",
        "multiplicative number theorist (Erdos/Heath-Brown paradigm: rad(n), large sieve, Heath-Brown identity, Bombieri-Vinogradov, hybrid sieves)"),
    3: ("ANALYTIC NUMBER THEORIST",
        "analytic number theorist (Bombieri/Iwaniec/Vinogradov paradigm: L-functions, contour integration, circle method, Burgess, exponential sums, Vinogradov mean value)"),
    4: ("COMPUTATIONAL / ALGORITHMIC",
        "computational/algorithmic mathematician (Knuth/Bernstein paradigm: LLL, smooth numbers, ECM, lattice reduction, Coppersmith, Dickman rho, sorted enumeration)"),
    5: ("ALGEBRAIC GEOMETER",
        "algebraic geometer (Faltings/Vojta paradigm: integral points, Vojta conjecture, heights, Chabauty-Coleman, moduli of elliptic curves)"),
}

def load(p):
    with open(f"/Users/patrickkavanagh/math/analysis/exp5_artifacts/p{p}_{'additive' if p==1 else 'multiplicative' if p==2 else 'analytic' if p==3 else 'computational' if p==4 else 'alggeom'}_attack.md") as f:
        return f.read()

def build_prompt(persona_id):
    label, desc = PERSONAS[persona_id]
    attacks = {pid: load(pid) for pid in PERSONAS}
    bodies = []
    letters = "ABCDE"
    pids = [1,2,3,4,5]
    for letter, pid in zip(letters, pids):
        if pid == persona_id:
            bodies.append(f"=== ATTACK {letter}: {PERSONAS[pid][0]} (YOUR OWN — SKIP) ===\n[do not critique]")
        else:
            bodies.append(f"=== ATTACK {letter}: {PERSONAS[pid][0]} ===\n{attacks[pid]}")
    body = "\n\n".join(bodies)
    prompt = f"""You are PERSONA: {label} — a {desc}.

Below are 5 attacks on Erdős Problem #364 (no n with n, n+1, n+2 all powerful) by 5 different specialists. CRITIQUE the 4 attacks that are NOT your own. For each, give:

1. **One specific weakness** (≤3 sentences, sharp).
2. **One specific suggestion** from YOUR paradigm to plug a hole.
3. **Confidence** (HIGH/MED/LOW) it would advance E364 if completed.

Then one sentence on which OTHER attack you found strongest. Be aggressive, NOT balanced. Cut from YOUR paradigm.

{body}
"""
    return prompt

def query_grok(prompt, max_tokens=4000, temperature=0.5):
    api_key = os.environ["XAI_API_KEY"]
    data = {"messages":[{"role":"user","content":prompt}], "model":"grok-4", "max_tokens":max_tokens, "temperature":temperature}
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        json.dump(data, f); tmp=f.name
    r = subprocess.run(['curl','-s','-X','POST','--max-time','480',
                        'https://api.x.ai/v1/chat/completions',
                        '-H', f'Authorization: Bearer {api_key}',
                        '-H','Content-Type: application/json',
                        '-d', f'@{tmp}'],
                       capture_output=True, text=True, timeout=510)
    os.unlink(tmp)
    resp = json.loads(r.stdout)
    if 'choices' not in resp:
        return f"NO CHOICES: {r.stdout[:1000]}"
    return resp['choices'][0]['message']['content']

if __name__ == "__main__":
    pid = int(sys.argv[1])
    prompt = build_prompt(pid)
    out = query_grok(prompt)
    name = PERSONAS[pid][0].lower().replace(' / ', '_').replace(' ', '_')
    path = f"/Users/patrickkavanagh/math/analysis/exp5_artifacts/critique_p{pid}.md"
    with open(path, "w") as f:
        f.write(out)
    print(f"WROTE {path} ({len(out)} chars)")
