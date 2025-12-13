#!/usr/bin/env python3
"""
Comprehensive Problem Verification and Refinement Framework
Uses Grok, Gemini, and Codex to verify each problem is truly unsolved
and refine the approach for maximum success probability.
"""

import json
import subprocess
import os
from typing import List, Dict

# Load all GitHub issues
def load_github_issues() -> List[Dict]:
    """Fetch all issues from GitHub"""
    result = subprocess.run(
        ["gh", "issue", "list", "--repo", "kavanaghpatrick/aristotle-math-problems",
         "--limit", "100", "--json", "number,title,labels,body", "--state", "open"],
        capture_output=True,
        text=True,
        check=True
    )
    return json.loads(result.stdout)

# Extract problem details
def extract_problem_info(issue: Dict) -> Dict:
    """Extract key information from issue"""
    body = issue['body']

    # Parse problem statement
    problem_start = body.find("## Problem Statement") + len("## Problem Statement")
    problem_end = body.find("## Why Tractable")
    problem_statement = body[problem_start:problem_end].strip()

    # Parse metadata
    metadata = {}
    for line in body.split('\n'):
        if '**Success Probability**:' in line:
            metadata['success_rate'] = line.split(':')[1].strip()
        elif '**Difficulty**:' in line:
            metadata['difficulty'] = line.split(':')[1].strip()
        elif '**Impact**:' in line:
            metadata['impact'] = line.split(':')[1].strip()

    return {
        'number': issue['number'],
        'title': issue['title'],
        'statement': problem_statement,
        'metadata': metadata,
        'tier': [l['name'] for l in issue['labels'] if 'tier-' in l['name']][0],
        'category': [l['name'] for l in issue['labels'] if l['name'] in ['number-theory', 'algebra', 'combinatorics', 'analysis']][0]
    }

# Create verification prompts for each AI
VERIFICATION_TEMPLATE = """CRITICAL VERIFICATION TASK - Issue #{number}: {title}

PROBLEM STATEMENT:
{statement}

YOUR TASK (ULTRA-THOROUGH):

1. **VERIFY IF TRULY UNSOLVED**:
   - Search arXiv, MathOverflow, recent papers (2023-2025)
   - Check if this has been solved recently
   - Verify the problem statement is accurate
   - Check for subtleties (e.g., is "bounded case" actually interesting?)
   - Look for "almost solved" cases or trivial variants

2. **ASSESS FORMALIZABILITY**:
   - Can this be precisely stated in Lean 4?
   - Are all necessary definitions in Mathlib?
   - What's missing from Mathlib that would be needed?
   - Rate formalizability: EASY / MEDIUM / HARD / VERY HARD

3. **IDENTIFY PROOF STRATEGIES**:
   - What are ALL known approaches to this problem?
   - Which approaches are most suitable for automated proving?
   - What are the key lemmas/techniques required?
   - Are there simpler special cases to try first?

4. **DETECT RED FLAGS**:
   - Is this actually trivial? (e.g., "prove n+0=n")
   - Is it a renamed/disguised version of a solved problem?
   - Are the bounds too weak to be interesting?
   - Would solving this bounded case tell us anything new?

5. **ESTIMATE TRUE SUCCESS PROBABILITY**:
   Current estimate: {success_rate}
   - Is this realistic?
   - What would increase/decrease the probability?
   - What are the main obstacles?

6. **RECOMMEND REFINEMENTS**:
   - How should we reformulate the problem?
   - What's the optimal scope (broader/narrower)?
   - What preparatory work is needed?
   - What's the best attack strategy for Aristotle?

OUTPUT FORMAT:
```json
{{
  "issue_number": {number},
  "verdict": "KEEP | REFORMULATE | REJECT",
  "still_unsolved": true/false,
  "confidence": "HIGH | MEDIUM | LOW",
  "formalizability": "EASY | MEDIUM | HARD | VERY HARD",
  "true_success_probability": "X%",
  "red_flags": ["list", "of", "concerns"],
  "recommended_refinements": ["specific", "improvements"],
  "proof_strategies": ["strategy1", "strategy2"],
  "key_obstacles": ["obstacle1", "obstacle2"],
  "preparatory_steps": ["step1", "step2"],
  "reasoning": "detailed explanation of your assessment"
}}
```

BE BRUTALLY HONEST. We want to MAXIMIZE actual success, not preserve our existing list.
"""

def create_verification_requests(problems: List[Dict]) -> None:
    """Create verification requests for all AI systems"""

    os.makedirs("verification-results", exist_ok=True)

    # Create Grok verification requests
    grok_requests = []
    for prob in problems:
        prompt = VERIFICATION_TEMPLATE.format(
            number=prob['number'],
            title=prob['title'],
            statement=prob['statement'],
            success_rate=prob['metadata'].get('success_rate', 'Unknown')
        )

        grok_req = {
            "messages": [{"role": "user", "content": prompt}],
            "model": "grok-2-1212",
            "temperature": 0.2,
            "max_tokens": 4000
        }
        grok_requests.append((prob['number'], grok_req))

    # Save Grok requests
    for num, req in grok_requests:
        with open(f"verification-results/grok_request_{num}.json", 'w') as f:
            json.dump(req, f, indent=2)

    # Create Gemini prompts
    for prob in problems:
        prompt = VERIFICATION_TEMPLATE.format(
            number=prob['number'],
            title=prob['title'],
            statement=prob['statement'],
            success_rate=prob['metadata'].get('success_rate', 'Unknown')
        )
        with open(f"verification-results/gemini_prompt_{prob['number']}.txt", 'w') as f:
            f.write(prompt)

    # Create Codex commands
    codex_script = "#!/bin/bash\n\n"
    for prob in problems:
        prompt = VERIFICATION_TEMPLATE.format(
            number=prob['number'],
            title=prob['title'],
            statement=prob['statement'],
            success_rate=prob['metadata'].get('success_rate', 'Unknown')
        )

        # Escape for bash
        prompt_escaped = prompt.replace('"', '\\"').replace('$', '\\$').replace('`', '\\`')

        codex_script += f"""
echo "Verifying Issue #{prob['number']}..."
cd /Users/patrickkavanagh/math
codex exec --skip-git-repo-check "VERIFICATION TASK: {prompt_escaped}

Output findings to verification-results/codex_result_{prob['number']}.md" &

"""

    with open("verification-results/run_codex_verification.sh", 'w') as f:
        f.write(codex_script)

    os.chmod("verification-results/run_codex_verification.sh", 0o755)

    print(f"✅ Created verification requests for {len(problems)} problems")
    print(f"   - Grok: {len(grok_requests)} JSON files")
    print(f"   - Gemini: {len(problems)} prompt files")
    print(f"   - Codex: 1 batch script")

def main():
    print("="*80)
    print("PROBLEM VERIFICATION AND REFINEMENT FRAMEWORK")
    print("="*80)
    print()

    # Load issues
    print("[1/4] Loading GitHub issues...")
    issues = load_github_issues()
    print(f"   Found {len(issues)} open issues")

    # Extract problem info
    print("[2/4] Extracting problem details...")
    problems = [extract_problem_info(issue) for issue in issues]

    # Group by tier
    tier1 = [p for p in problems if 'tier-1' in p['tier']]
    tier2 = [p for p in problems if 'tier-2' in p['tier']]
    tier3 = [p for p in problems if 'tier-3' in p['tier']]

    print(f"   Tier 1: {len(tier1)} problems")
    print(f"   Tier 2: {len(tier2)} problems")
    print(f"   Tier 3: {len(tier3)} problems")

    # Create verification requests
    print("[3/4] Creating verification requests...")
    create_verification_requests(problems)

    print()
    print("="*80)
    print("VERIFICATION REQUESTS CREATED")
    print("="*80)
    print()
    print("Next steps:")
    print()
    print("1. GROK VERIFICATION:")
    print("   for i in verification-results/grok_request_*.json; do")
    print("     curl -X POST https://api.x.ai/v1/chat/completions \\")
    print("       -H \"Authorization: Bearer $GROK_API_KEY\" \\")
    print("       -H \"Content-Type: application/json\" \\")
    print("       -d @$i > ${i/request/response}")
    print("     sleep 2")
    print("   done")
    print()
    print("2. GEMINI VERIFICATION:")
    print("   for prompt in verification-results/gemini_prompt_*.txt; do")
    print("     gemini -p \"$(cat $prompt)\" > ${prompt/prompt/response}.txt")
    print("     sleep 2")
    print("   done")
    print()
    print("3. CODEX VERIFICATION:")
    print("   ./verification-results/run_codex_verification.sh")
    print()

if __name__ == "__main__":
    main()
