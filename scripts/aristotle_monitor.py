#!/usr/bin/env python3
"""
Aristotle Monitor v1 - Monitors, downloads, analyzes Aristotle outputs
"""

import json
import asyncio
import argparse
import re
from pathlib import Path
from datetime import datetime
from typing import Optional

SUBMISSIONS_LOG = "submissions/submitted_projects.json"
RESULTS_DIR = "submissions/results"
ANALYSIS_LOG = "submissions/analysis_log.json"

def log(msg: str):
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)

def load_json(path: str) -> dict:
    try:
        with open(path, 'r') as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}

def save_json(path: str, data: dict):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w') as f:
        json.dump(data, f, indent=2, default=str)

async def get_all_projects() -> list:
    try:
        from aristotlelib import Project
        projects = await Project.list_projects()
        all_projects = []
        for item in projects:
            if isinstance(item, list):
                all_projects.extend(item)
        return all_projects
    except Exception as e:
        log(f"Error fetching projects: {e}")
        return []

async def download_output(project_id: str, output_dir: str = RESULTS_DIR) -> Optional[str]:
    try:
        from aristotlelib import Project
        project = await Project.from_id(project_id)
        Path(output_dir).mkdir(parents=True, exist_ok=True)
        output_path = f"{output_dir}/{project_id}-output.lean"

        if hasattr(project, 'output') and project.output:
            with open(output_path, 'w') as f:
                f.write(project.output)
            return output_path
        elif hasattr(project, 'download_output'):
            await project.download_output(output_path)
            if Path(output_path).exists():
                return output_path
        return None
    except Exception as e:
        log(f"Error downloading {project_id}: {e}")
        return None

def analyze_output(filepath: str) -> dict:
    try:
        with open(filepath, 'r') as f:
            content = f.read()
    except FileNotFoundError:
        return {'status': 'error', 'message': 'File not found'}

    analysis = {
        'filepath': filepath,
        'status': 'unknown',
        'sorries': 0,
        'proven_lemmas': [],
        'failed_lemmas': [],
        'negated_theorems': [],
        'syntax_errors': [],
        'suggestions': []
    }

    # Count real sorries (not in comments)
    # Simple: count "sorry" not preceded by /- or --
    analysis['sorries'] = len(re.findall(r'(?<![-/])\bsorry\b', content))

    # Check for negations
    if 'The following was negated by Aristotle:' in content:
        negation_match = re.search(r'The following was negated by Aristotle:\s*\n(.*?)(?=Here is the code|$)',
                                    content, re.DOTALL)
        if negation_match:
            negated = negation_match.group(1).strip()
            analysis['negated_theorems'] = [line.strip() for line in negated.split('\n')
                                            if line.strip().startswith('-')]
        analysis['status'] = 'negated'
        analysis['suggestions'].append('Check formalization matches original problem')
        analysis['suggestions'].append('Look for floor/ceil, quantifier issues')

    # Check for syntax errors
    if 'Aristotle failed to load this code' in content:
        analysis['syntax_errors'].append('Load error detected')
        analysis['status'] = 'syntax_error'
        analysis['suggestions'].append('Fix syntax errors before resubmitting')

    # Find all lemma/theorem names
    lemma_names = re.findall(r'(?:lemma|theorem)\s+(\w+)', content)
    
    # For each lemma, check if it has sorry in its body
    for name in lemma_names:
        # Find the lemma definition and its body
        pattern = rf'(?:lemma|theorem)\s+{re.escape(name)}.*?:=\s*by(.*?)(?=\n(?:lemma|theorem|def |end\b|/-)|$)'
        match = re.search(pattern, content, re.DOTALL)
        if match:
            body = match.group(1)
            if 'sorry' in body or 'negate_state' in body:
                analysis['failed_lemmas'].append(name)
            else:
                analysis['proven_lemmas'].append(name)
        else:
            # Might be a declaration with sorry at top level
            simple_pattern = rf'(?:lemma|theorem)\s+{re.escape(name)}[^:]*:.*?:=.*?sorry'
            if re.search(simple_pattern, content, re.DOTALL):
                analysis['failed_lemmas'].append(name)

    # Determine overall status
    if analysis['status'] == 'unknown':
        if analysis['sorries'] == 0 and analysis['proven_lemmas']:
            analysis['status'] = 'success'
            analysis['suggestions'].append('🎉 Complete proof! Verify against original problem.')
        elif analysis['proven_lemmas'] and analysis['failed_lemmas']:
            analysis['status'] = 'partial'
            analysis['suggestions'].append(f'Partial: {len(analysis["proven_lemmas"])} proven, {len(analysis["failed_lemmas"])} need work')
        elif analysis['sorries'] > 0:
            analysis['status'] = 'incomplete'

    # Special pattern checks
    if 'C5' in content or 'cycleGraph 5' in content:
        analysis['suggestions'].append('Contains C5 cycle - verify counterexample')
    if 'negate_state' in content and analysis['status'] != 'negated':
        analysis['suggestions'].append('Uses negate_state - check validity')

    return analysis

def print_analysis(analysis: dict):
    status_emoji = {
        'success': '✅', 'partial': '🔶', 'negated': '⚠️',
        'syntax_error': '❌', 'incomplete': '📝', 'unknown': '❓', 'error': '💥'
    }
    emoji = status_emoji.get(analysis['status'], '❓')
    
    print(f"\n{'='*60}")
    print(f"{emoji} STATUS: {analysis['status'].upper()}")
    print(f"   File: {Path(analysis.get('filepath', 'N/A')).name}")
    print(f"{'='*60}")

    if analysis['proven_lemmas']:
        print(f"\n✅ PROVEN ({len(analysis['proven_lemmas'])}):")
        for name in analysis['proven_lemmas']:
            print(f"   • {name}")

    if analysis['failed_lemmas']:
        print(f"\n❌ FAILED/SORRY ({len(analysis['failed_lemmas'])}):")
        for name in analysis['failed_lemmas']:
            print(f"   • {name}")

    if analysis['negated_theorems']:
        print(f"\n⚠️  NEGATED ({len(analysis['negated_theorems'])}):")
        for neg in analysis['negated_theorems'][:5]:
            print(f"   {neg[:70]}...")

    if analysis['syntax_errors']:
        print(f"\n💥 SYNTAX ERRORS: {len(analysis['syntax_errors'])}")

    if analysis['sorries']:
        print(f"\n📝 Remaining sorries: {analysis['sorries']}")

    if analysis['suggestions']:
        print(f"\n💡 SUGGESTIONS:")
        for sug in analysis['suggestions']:
            print(f"   → {sug}")
    print()

async def check_completions() -> list:
    submissions = load_json(SUBMISSIONS_LOG)
    analysis_log = load_json(ANALYSIS_LOG)
    projects = await get_all_projects()
    completed = []

    for project in projects:
        status = str(project.status).split('.')[-1]
        pid = project.project_id

        our_submission = None
        for filepath, info in submissions.items():
            if info.get('project_id') == pid:
                our_submission = filepath
                break
        if not our_submission:
            continue

        if pid in analysis_log:
            continue

        if status in ['COMPLETE', 'FAILED', 'ERROR']:
            log(f"Completed: {pid[:8]}... ({status}) - {Path(our_submission).name}")
            output_path = await download_output(pid)

            if output_path and Path(output_path).exists():
                analysis = analyze_output(output_path)
                analysis['project_id'] = pid
                analysis['original_file'] = our_submission
                analysis['completion_status'] = status

                analysis_log[pid] = analysis
                save_json(ANALYSIS_LOG, analysis_log)

                submissions[our_submission]['status'] = status.lower()
                submissions[our_submission]['analyzed'] = True
                submissions[our_submission]['analysis_status'] = analysis['status']
                save_json(SUBMISSIONS_LOG, submissions)

                completed.append(analysis)
                print_analysis(analysis)

    return completed

async def watch_loop(interval: int = 120):
    log("🔍 Starting Aristotle Monitor...")
    log(f"   Check interval: {interval}s")
    log(f"   Results dir: {RESULTS_DIR}")

    while True:
        try:
            completed = await check_completions()
            if completed:
                successes = [c for c in completed if c['status'] == 'success']
                negated = [c for c in completed if c['status'] == 'negated']
                
                if successes:
                    log(f"🎉 {len(successes)} SUCCESS(ES)!")
                if negated:
                    log(f"⚠️  {len(negated)} NEGATED - check formalization!")
            else:
                log("No new completions")
        except Exception as e:
            log(f"Error: {e}")

        log(f"Next check in {interval}s...")
        await asyncio.sleep(interval)

def main():
    parser = argparse.ArgumentParser(description="Aristotle Monitor")
    parser.add_argument("--watch", action="store_true", help="Continuous monitoring")
    parser.add_argument("--check-once", action="store_true", help="Single check")
    parser.add_argument("--analyze", type=str, help="Analyze specific file")
    parser.add_argument("--interval", type=int, default=120, help="Check interval (s)")
    args = parser.parse_args()

    if args.analyze:
        analysis = analyze_output(args.analyze)
        print_analysis(analysis)
        return
    if args.check_once:
        asyncio.run(check_completions())
        return
    if args.watch:
        asyncio.run(watch_loop(args.interval))
        return
    parser.print_help()

if __name__ == "__main__":
    main()
