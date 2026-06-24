#!/usr/bin/env python3
"""Assemble the synthesis prompt and call Grok."""
import os, json, subprocess, tempfile

BASE = "/Users/patrickkavanagh/math/analysis/exp5_artifacts"

def load(name):
    with open(f"{BASE}/{name}") as f:
        return f.read()

template = load("synthesis_prompt.txt")
replacements = {
    "ATTACK_A_BODY": load("p1_additive_attack.md"),
    "ATTACK_B_BODY": load("p2_multiplicative_attack.md"),
    "ATTACK_C_BODY": load("p3_analytic_attack.md"),
    "ATTACK_D_BODY": load("p4_computational_attack.md"),
    "ATTACK_E_BODY": load("p5_alggeom_attack.md"),
    "CRIT_1_BODY": load("critique_p1.md"),
    "CRIT_2_BODY": load("critique_p2.md"),
    "CRIT_3_BODY": load("critique_p3.md"),
    "CRIT_4_BODY": load("critique_p4.md"),
    "CRIT_5_BODY": load("critique_p5.md"),
}
prompt = template
for k, v in replacements.items():
    prompt = prompt.replace(k, v)

# Save it for review
with open(f"{BASE}/synthesis_prompt_built.txt", "w") as f:
    f.write(prompt)

api_key = os.environ["XAI_API_KEY"]
data = {"messages":[{"role":"user","content":prompt}], "model":"grok-4", "max_tokens":4000, "temperature":0.45}
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
    print(f"NO CHOICES: {r.stdout[:1000]}"); raise SystemExit(1)
out = resp['choices'][0]['message']['content']
with open(f"{BASE}/synthesis_attack.md", "w") as f:
    f.write(out)
print(f"WROTE synthesis_attack.md ({len(out)} chars)")
