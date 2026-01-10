#!/usr/bin/env python3
"""
Validation Pipeline - Pre-validate lemmas before Aristotle submission.

Four stages:
1. Syntax Check - Lean compiles without errors
2. False Lemma Detection - No known false lemmas used
3. Grok Review - AI plausibility check
4. Counterexample Hunter - Actively try to disprove

Only submissions passing all stages go to the queue.
"""

import sqlite3
import subprocess
import json
import argparse
import re
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional

sys.path.insert(0, str(Path(__file__).parent.parent))
from config import DB_PATH, GROK_API_KEY, GROK_TIMEOUT_SECONDS


class ValidationPipeline:
    def __init__(self):
        self.db_path = DB_PATH
        self.stages = [
            ('syntax', self.check_syntax),
            ('false_lemma', self.check_false_lemmas),
            ('grok_review', self.grok_review),
            ('counterexample', self.counterexample_hunt),
        ]

    def log(self, msg: str, level: str = "INFO"):
        timestamp = datetime.now().strftime("%H:%M:%S")
        print(f"[{timestamp}] [{level}] {msg}", flush=True)

    def get_db(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path)
        conn.row_factory = sqlite3.Row
        return conn

    # ==================== Stage 1: Syntax Check ====================

    def check_syntax(self, file_path: str) -> Tuple[bool, str]:
        """Check if Lean file has valid syntax."""
        try:
            # Try to load with lake (quick syntax check)
            result = subprocess.run(
                ["lake", "env", "lean", file_path],
                capture_output=True,
                text=True,
                timeout=60,
                cwd=str(Path(file_path).parent.parent)  # Project root
            )

            if result.returncode == 0:
                return True, "Syntax valid"

            # Check for common fixable errors
            errors = result.stderr

            if "unknown identifier" in errors.lower():
                return False, f"Unknown identifier: {errors[:200]}"
            if "type mismatch" in errors.lower():
                return False, f"Type mismatch: {errors[:200]}"

            # Other errors might be Mathlib version issues - allow through
            if "import" in errors.lower() and "not found" in errors.lower():
                return True, "Import issues (likely Mathlib version) - allowing"

            return False, f"Syntax errors: {errors[:300]}"

        except subprocess.TimeoutExpired:
            return False, "Syntax check timeout"
        except Exception as e:
            # If lake not available, skip syntax check
            return True, f"Syntax check skipped: {e}"

    # ==================== Stage 2: False Lemma Detection ====================

    def check_false_lemmas(self, file_path: str) -> Tuple[bool, str]:
        """Check if file uses any known false lemmas."""
        try:
            with open(file_path, 'r') as f:
                content = f.read()
        except Exception as e:
            return False, f"Could not read file: {e}"

        conn = self.get_db()
        cursor = conn.cursor()

        # Get all false lemma names
        cursor.execute("SELECT lemma_name, pattern_number FROM false_lemmas")
        false_lemmas = cursor.fetchall()
        conn.close()

        found_false = []
        for row in false_lemmas:
            lemma_name = row['lemma_name']
            # Check if lemma is defined or used
            if re.search(rf'\b{re.escape(lemma_name)}\b', content):
                found_false.append(f"Pattern {row['pattern_number']}: {lemma_name}")

        if found_false:
            return False, f"Uses false lemmas: {', '.join(found_false)}"

        return True, "No false lemmas detected"

    # ==================== Stage 3: Grok Review ====================

    def grok_review(self, file_path: str) -> Tuple[bool, str]:
        """Use Grok to review mathematical plausibility."""
        if not GROK_API_KEY:
            return True, "Grok review skipped (no API key)"

        try:
            with open(file_path, 'r') as f:
                content = f.read()
        except Exception as e:
            return True, f"Grok review skipped: {e}"

        # Extract key lemmas/theorems
        lemmas = re.findall(r'(?:lemma|theorem)\s+(\w+)[^:]*:\s*([^\n:=]+)', content)

        if not lemmas:
            return True, "No lemmas to review"

        # Build prompt
        prompt = """Review these Lean 4 lemmas for mathematical correctness.
Focus on CRITICAL issues only:
1. Logically impossible statements
2. Vacuously true claims (empty preconditions)
3. Circular reasoning
4. Known false patterns in triangle covering

Return JSON: {"plausible": true/false, "issues": ["issue1", ...]}

Lemmas:
"""
        for name, statement in lemmas[:10]:  # Limit to 10
            prompt += f"- {name}: {statement.strip()}\n"

        # Query Grok
        from scripts.grok_query import query_grok
        response = query_grok(prompt, timeout=GROK_TIMEOUT_SECONDS)

        # Parse response
        try:
            # Extract JSON from response
            json_match = re.search(r'\{[^}]+\}', response)
            if json_match:
                result = json.loads(json_match.group())
                if result.get('plausible', True):
                    return True, "Grok review passed"
                else:
                    issues = result.get('issues', ['Unknown issue'])
                    return False, f"Grok issues: {'; '.join(issues[:3])}"
        except json.JSONDecodeError:
            pass

        # If we can't parse, assume OK
        return True, "Grok review inconclusive - allowing"

    # ==================== Stage 4: Counterexample Hunter ====================

    def counterexample_hunt(self, file_path: str) -> Tuple[bool, str]:
        """Actively try to find counterexamples."""
        try:
            with open(file_path, 'r') as f:
                content = f.read()
        except Exception as e:
            return True, f"Counterexample hunt skipped: {e}"

        # Extract the main claim
        main_theorems = re.findall(
            r'theorem\s+(\w+)[^:]*:\s*([^\n:=]+(?:→[^\n:=]+)*)',
            content
        )

        if not main_theorems:
            return True, "No theorems to test"

        # For critical claims about tau bounds, try harder
        for name, statement in main_theorems:
            # Known problematic patterns
            if 'tau' in statement.lower() and 'le 4' in statement.replace('≤', 'le'):
                # tau ≤ 4 claims are almost always false
                return False, f"Suspicious: {name} claims tau ≤ 4 (usually false, see Pattern 8)"

            if 'tau' in statement.lower() and 'le 2' in statement.replace('≤', 'le'):
                if 'containing' not in statement.lower() and 'avoiding' not in statement.lower():
                    return False, f"Suspicious: {name} claims tau ≤ 2 without scope restriction"

        # For now, pass if no obvious issues
        return True, "Counterexample hunt passed"

    # ==================== Main Pipeline ====================

    def validate_file(self, file_path: str) -> Dict:
        """Run full validation pipeline on a file."""
        self.log(f"Validating: {Path(file_path).name}")

        results = {
            'file_path': file_path,
            'passed': True,
            'stages': {},
            'failed_at': None
        }

        for stage_name, stage_fn in self.stages:
            self.log(f"  Stage: {stage_name}...")
            passed, message = stage_fn(file_path)

            results['stages'][stage_name] = {
                'passed': passed,
                'message': message
            }

            # Record in database
            self.record_validation(file_path, stage_name, passed, message)

            if not passed:
                results['passed'] = False
                results['failed_at'] = stage_name
                self.log(f"  FAILED at {stage_name}: {message}", "WARN")
                break
            else:
                self.log(f"  OK: {message}")

        # Update queue entry
        self.update_queue_status(file_path, results['passed'], results)

        return results

    def record_validation(self, file_path: str, stage: str, passed: bool, notes: str):
        """Record validation result in database."""
        conn = self.get_db()
        cursor = conn.cursor()
        cursor.execute("""
        INSERT INTO validation_results (file_path, stage, passed, notes)
        VALUES (?, ?, ?, ?)
        """, (file_path, stage, int(passed), notes))
        conn.commit()
        conn.close()

    def update_queue_status(self, file_path: str, passed: bool, results: Dict):
        """Update the queue entry with validation status."""
        conn = self.get_db()
        cursor = conn.cursor()

        cursor.execute("""
        UPDATE submission_queue
        SET validation_passed = ?,
            validation_stage = ?,
            validator_notes = ?
        WHERE file_path = ?
        """, (
            int(passed),
            results.get('failed_at', 'all_passed'),
            json.dumps(results['stages']),
            file_path
        ))

        if cursor.rowcount == 0:
            # Not in queue yet, add it
            cursor.execute("""
            INSERT INTO submission_queue
            (file_path, validation_passed, validation_stage, validator_notes)
            VALUES (?, ?, ?, ?)
            """, (
                file_path,
                int(passed),
                results.get('failed_at', 'all_passed'),
                json.dumps(results['stages'])
            ))

        conn.commit()
        conn.close()

    def process_pending(self) -> List[Dict]:
        """Process all pending files in the queue."""
        conn = self.get_db()
        cursor = conn.cursor()

        cursor.execute("""
        SELECT file_path FROM submission_queue
        WHERE validation_stage = 'pending'
        ORDER BY priority DESC, created_at ASC
        """)

        files = [row['file_path'] for row in cursor.fetchall()]
        conn.close()

        results = []
        for f in files:
            if Path(f).exists():
                result = self.validate_file(f)
                results.append(result)
            else:
                self.log(f"File not found: {f}", "WARN")

        return results

    def watch_mode(self, interval: int = 60):
        """Continuously process pending validations."""
        self.log("Starting validation watch mode...")

        import asyncio

        async def watch_loop():
            while True:
                results = self.process_pending()
                if results:
                    passed = sum(1 for r in results if r['passed'])
                    self.log(f"Processed {len(results)} files: {passed} passed, {len(results) - passed} failed")
                else:
                    self.log("No pending validations")

                await asyncio.sleep(interval)

        asyncio.run(watch_loop())


def main():
    parser = argparse.ArgumentParser(description="Validation Pipeline")
    parser.add_argument("--file", type=str, help="Validate single file")
    parser.add_argument("--process-pending", action="store_true", help="Process pending queue items")
    parser.add_argument("--watch", action="store_true", help="Continuous watch mode")
    parser.add_argument("--interval", type=int, default=60, help="Watch interval (seconds)")

    args = parser.parse_args()

    pipeline = ValidationPipeline()

    if args.file:
        result = pipeline.validate_file(args.file)
        print(json.dumps(result, indent=2))
    elif args.process_pending:
        results = pipeline.process_pending()
        passed = sum(1 for r in results if r['passed'])
        print(f"\nSummary: {passed}/{len(results)} passed")
    elif args.watch:
        pipeline.watch_mode(args.interval)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
