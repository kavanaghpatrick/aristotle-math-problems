#!/usr/bin/env python3
"""
Analyze Verification Results from Grok, Gemini, and Codex
Cross-validates findings and generates refined problem list
"""

import json
import os
import re
from pathlib import Path
from collections import defaultdict

RESULTS_DIR = Path("verification-results")

def parse_grok_response(file_path):
    """Parse Grok JSON response"""
    try:
        with open(file_path) as f:
            data = json.load(f)
            if 'choices' in data and len(data['choices']) > 0:
                content = data['choices'][0]['message']['content']
                # Try to extract JSON from content
                json_match = re.search(r'```json\s*(\{.*?\})\s*```', content, re.DOTALL)
                if json_match:
                    return json.loads(json_match.group(1))
                return {"raw_content": content}
    except Exception as e:
        return {"error": str(e)}
    return None

def parse_gemini_response(file_path):
    """Parse Gemini text response"""
    try:
        with open(file_path) as f:
            content = f.read()
            # Try to extract JSON
            json_match = re.search(r'```json\s*(\{.*?\})\s*```', content, re.DOTALL)
            if json_match:
                return json.loads(json_match.group(1))
            return {"raw_content": content}
    except Exception as e:
        return {"error": str(e)}
    return None

def parse_codex_response(file_path):
    """Parse Codex markdown response"""
    try:
        with open(file_path) as f:
            content = f.read()
            # Extract key information
            return {"raw_content": content}
    except Exception as e:
        return {"error": str(e)}
    return None

def cross_validate(grok_result, gemini_result, codex_result):
    """Cross-validate results from 3 AI systems"""

    verdicts = []
    confidence_scores = []
    unsolved_checks = []

    # Grok analysis
    if grok_result and 'verdict' in grok_result:
        verdicts.append(grok_result['verdict'])
        if 'still_unsolved' in grok_result:
            unsolved_checks.append(grok_result['still_unsolved'])
        if 'confidence' in grok_result:
            conf_map = {'HIGH': 3, 'MEDIUM': 2, 'LOW': 1}
            confidence_scores.append(conf_map.get(grok_result['confidence'], 2))

    # Gemini analysis
    if gemini_result and 'verdict' in gemini_result:
        verdicts.append(gemini_result['verdict'])
        if 'still_unsolved' in gemini_result:
            unsolved_checks.append(gemini_result['still_unsolved'])
        if 'confidence' in gemini_result:
            conf_map = {'HIGH': 3, 'MEDIUM': 2, 'LOW': 1}
            confidence_scores.append(conf_map.get(gemini_result['confidence'], 2))

    # Codex analysis
    if codex_result and 'verdict' in codex_result:
        verdicts.append(codex_result['verdict'])

    # Consensus verdict
    if verdicts:
        from collections import Counter
        verdict_counts = Counter(verdicts)
        consensus_verdict = verdict_counts.most_common(1)[0][0]
        agreement = verdict_counts[consensus_verdict] / len(verdicts)
    else:
        consensus_verdict = "UNKNOWN"
        agreement = 0.0

    # Unsolved consensus
    unsolved_consensus = all(unsolved_checks) if unsolved_checks else None

    # Average confidence
    avg_confidence = sum(confidence_scores) / len(confidence_scores) if confidence_scores else 0

    return {
        "consensus_verdict": consensus_verdict,
        "agreement_rate": agreement,
        "still_unsolved": unsolved_consensus,
        "avg_confidence": avg_confidence,
        "ai_verdicts": verdicts
    }

def generate_report():
    """Generate comprehensive verification report"""

    print("="*80)
    print("VERIFICATION RESULTS ANALYSIS")
    print("="*80)
    print()

    results_by_issue = {}

    # Collect all results
    for i in range(1, 21):
        issue_num = i
        results = {}

        # Grok
        grok_file = RESULTS_DIR / f"grok_response_{i}.json"
        if grok_file.exists():
            results['grok'] = parse_grok_response(grok_file)

        # Gemini
        gemini_file = RESULTS_DIR / f"gemini_response_{i}.txt"
        if gemini_file.exists():
            results['gemini'] = parse_gemini_response(gemini_file)

        # Codex
        codex_file = RESULTS_DIR / f"codex_result_{i}.md"
        if codex_file.exists():
            results['codex'] = parse_codex_response(codex_file)

        if results:
            results_by_issue[issue_num] = results

    print(f"Found results for {len(results_by_issue)} issues\n")

    # Analyze each issue
    keep_list = []
    reformulate_list = []
    reject_list = []
    unknown_list = []

    for issue_num in sorted(results_by_issue.keys()):
        results = results_by_issue[issue_num]

        print(f"Issue #{issue_num}")
        print("-" * 40)

        grok = results.get('grok', {})
        gemini = results.get('gemini', {})
        codex = results.get('codex', {})

        # Cross-validate
        validation = cross_validate(grok, gemini, codex)

        print(f"  Consensus: {validation['consensus_verdict']}")
        print(f"  Agreement: {validation['agreement_rate']*100:.0f}%")
        print(f"  Still Unsolved: {validation['still_unsolved']}")
        print(f"  Confidence: {validation['avg_confidence']:.1f}/3")

        # Show individual verdicts
        if grok and 'verdict' in grok:
            print(f"  • Grok: {grok['verdict']}")
        if gemini and 'verdict' in gemini:
            print(f"  • Gemini: {gemini['verdict']}")
        if codex and 'verdict' in codex:
            print(f"  • Codex: {codex['verdict']}")

        print()

        # Categorize
        if validation['consensus_verdict'] == "KEEP":
            keep_list.append(issue_num)
        elif validation['consensus_verdict'] == "REFORMULATE":
            reformulate_list.append(issue_num)
        elif validation['consensus_verdict'] == "REJECT":
            reject_list.append(issue_num)
        else:
            unknown_list.append(issue_num)

    # Summary
    print("="*80)
    print("SUMMARY")
    print("="*80)
    print()
    print(f"✅ KEEP ({len(keep_list)}): {keep_list}")
    print(f"⚠️  REFORMULATE ({len(reformulate_list)}): {reformulate_list}")
    print(f"❌ REJECT ({len(reject_list)}): {reject_list}")
    print(f"❓ UNKNOWN ({len(unknown_list)}): {unknown_list}")
    print()

    # Save summary
    with open("VERIFICATION_RESULTS.md", "w") as f:
        f.write("# Verification Results Summary\n\n")
        f.write(f"**Date**: {Path().cwd()}\n\n")
        f.write(f"## Overview\n\n")
        f.write(f"- **KEEP**: {len(keep_list)} problems\n")
        f.write(f"- **REFORMULATE**: {len(reformulate_list)} problems\n")
        f.write(f"- **REJECT**: {len(reject_list)} problems\n")
        f.write(f"- **UNKNOWN**: {len(unknown_list)} problems\n\n")

        f.write(f"## Detailed Results\n\n")
        for issue_num in sorted(results_by_issue.keys()):
            results = results_by_issue[issue_num]
            validation = cross_validate(
                results.get('grok', {}),
                results.get('gemini', {}),
                results.get('codex', {})
            )

            f.write(f"### Issue #{issue_num}\n\n")
            f.write(f"- **Verdict**: {validation['consensus_verdict']}\n")
            f.write(f"- **Agreement**: {validation['agreement_rate']*100:.0f}%\n")
            f.write(f"- **Still Unsolved**: {validation['still_unsolved']}\n")
            f.write(f"- **Confidence**: {validation['avg_confidence']:.1f}/3\n\n")

    print("✅ Results saved to VERIFICATION_RESULTS.md")

if __name__ == "__main__":
    generate_report()
