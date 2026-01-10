#!/usr/bin/env python3
"""
Learning Extractor - Extract knowledge from Aristotle outputs.

Responsibilities:
1. Parse proven/sorry/negated lemmas from outputs
2. Add proven theorems to scaffolding table
3. Record counterexamples in false_lemmas table
4. Update nu4_cases with new insights
5. Trigger follow-up proof generation for near-misses
"""

import sqlite3
import json
import re
import argparse
import asyncio
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass

sys.path.insert(0, str(Path(__file__).parent.parent))
from config import DB_PATH, RESULTS_DIR


@dataclass
class ExtractedLemma:
    name: str
    type: str  # lemma, theorem, def
    statement: str
    proof_complete: bool
    proof_code: Optional[str]


@dataclass
class ExtractedCounterexample:
    theorem_name: str
    negated_statement: str
    counterexample_description: str


class LearningExtractor:
    """Extract knowledge from Aristotle outputs."""

    def __init__(self):
        self.db_path = DB_PATH
        self.results_dir = RESULTS_DIR

    def log(self, msg: str, level: str = "INFO"):
        timestamp = datetime.now().strftime("%H:%M:%S")
        print(f"[{timestamp}] [Extractor] [{level}] {msg}", flush=True)

    def get_db(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path)
        conn.row_factory = sqlite3.Row
        return conn

    async def download_output(self, project_id: str) -> Optional[str]:
        """Download Aristotle output for a project."""
        try:
            from aristotlelib import Project
            project = await Project.from_id(project_id)

            Path(self.results_dir).mkdir(parents=True, exist_ok=True)
            output_path = f"{self.results_dir}/{project_id}-output.lean"

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
            self.log(f"Download failed: {e}", "ERROR")
            return None

    def parse_output(self, content: str) -> Dict:
        """Parse Aristotle output into structured data."""
        result = {
            'lemmas': [],
            'counterexamples': [],
            'sorry_count': 0,
            'proven_count': 0,
            'negated': False,
            'syntax_error': False
        }

        # Check for negation
        if 'The following was negated by Aristotle:' in content:
            result['negated'] = True

            # Extract negated theorem
            negation_match = re.search(
                r'The following was negated by Aristotle:\s*\n(.*?)(?=Here is the code|$)',
                content, re.DOTALL
            )
            if negation_match:
                negated_text = negation_match.group(1).strip()
                # Parse the negated statements
                for line in negated_text.split('\n'):
                    line = line.strip()
                    if line.startswith('-'):
                        result['counterexamples'].append({
                            'statement': line[1:].strip(),
                            'type': 'negated'
                        })

        # Check for syntax errors
        if 'Aristotle failed to load this code' in content:
            result['syntax_error'] = True
            return result

        # Extract lemmas/theorems
        # Pattern: lemma/theorem name [...] : statement := by proof
        decl_pattern = r'(lemma|theorem|def)\s+(\w+)([^:]*):([^:=]+):=\s*by(.*?)(?=\n(?:lemma|theorem|def |end\b|/-)|$)'

        for match in re.finditer(decl_pattern, content, re.DOTALL):
            decl_type = match.group(1)
            name = match.group(2)
            params = match.group(3).strip()
            statement = match.group(4).strip()
            proof = match.group(5).strip()

            has_sorry = 'sorry' in proof or 'negate_state' in proof
            proof_complete = not has_sorry

            lemma = ExtractedLemma(
                name=name,
                type=decl_type,
                statement=statement,
                proof_complete=proof_complete,
                proof_code=proof if proof_complete else None
            )

            result['lemmas'].append(lemma)

            if proof_complete:
                result['proven_count'] += 1
            else:
                result['sorry_count'] += 1

        return result

    def extract_counterexample_details(self, content: str) -> List[ExtractedCounterexample]:
        """Extract detailed counterexample information."""
        counterexamples = []

        # Look for counterexample graphs
        ce_pattern = r'CounterexampleGraph:?\s*(?:=\s*)?\{([^}]+)\}'
        for match in re.finditer(ce_pattern, content):
            graph_desc = match.group(1)
            counterexamples.append(ExtractedCounterexample(
                theorem_name='unknown',
                negated_statement='',
                counterexample_description=f"Graph: {graph_desc}"
            ))

        # Look for specific vertex/edge descriptions
        vertex_pattern = r'vertices?:\s*\{([^}]+)\}|V\s*=\s*\{([^}]+)\}'
        edge_pattern = r'edges?:\s*\{([^}]+)\}|E\s*=\s*\{([^}]+)\}'

        for vp in re.finditer(vertex_pattern, content, re.IGNORECASE):
            vertices = vp.group(1) or vp.group(2)
            for ep in re.finditer(edge_pattern, content, re.IGNORECASE):
                edges = ep.group(1) or ep.group(2)
                counterexamples.append(ExtractedCounterexample(
                    theorem_name='unknown',
                    negated_statement='',
                    counterexample_description=f"V={vertices}, E={edges}"
                ))
                break

        return counterexamples

    def save_proven_lemmas(self, lemmas: List[ExtractedLemma], submission_id: int):
        """Save proven lemmas to scaffolding."""
        conn = self.get_db()
        cursor = conn.cursor()

        for lemma in lemmas:
            if lemma.proof_complete:
                cursor.execute("""
                INSERT OR REPLACE INTO proven_theorems
                (submission_id, theorem_name, theorem_type, statement, proof_complete)
                VALUES (?, ?, ?, ?, 1)
                """, (submission_id, lemma.name, lemma.type, lemma.statement))

                # Also update literature_lemmas if it's a known lemma
                cursor.execute("""
                UPDATE literature_lemmas
                SET validated_true = 1, proof_code = ?
                WHERE name = ? AND validated_true IS NULL
                """, (lemma.proof_code, lemma.name))

                self.log(f"Saved proven lemma: {lemma.name}")

        conn.commit()
        conn.close()

    def save_counterexample(self, ce: ExtractedCounterexample, project_id: str):
        """Save counterexample to false_lemmas table."""
        conn = self.get_db()
        cursor = conn.cursor()

        # Get next pattern number
        cursor.execute("SELECT MAX(pattern_number) FROM false_lemmas")
        max_pattern = cursor.fetchone()[0] or 0
        new_pattern = max_pattern + 1

        cursor.execute("""
        INSERT INTO false_lemmas
        (pattern_number, lemma_name, false_statement, false_statement_english,
         counterexample, why_false, evidence_level, discovered_by,
         discovered_date, aristotle_uuid)
        VALUES (?, ?, ?, ?, ?, ?, 'aristotle_verified', 'Aristotle', date('now'), ?)
        """, (
            new_pattern,
            ce.theorem_name,
            ce.negated_statement,
            ce.negated_statement,
            ce.counterexample_description,
            f"Negated by Aristotle with counterexample: {ce.counterexample_description}",
            project_id
        ))

        conn.commit()
        conn.close()

        self.log(f"Recorded counterexample for: {ce.theorem_name}")

    def update_case_knowledge(self, case_name: str, parsed: Dict):
        """Update nu4_cases with new knowledge."""
        if not case_name or case_name == 'unknown':
            return

        conn = self.get_db()
        cursor = conn.cursor()

        # Update proven_lemmas list
        if parsed['proven_count'] > 0:
            proven_names = [l.name for l in parsed['lemmas'] if l.proof_complete]
            cursor.execute("""
            UPDATE nu4_cases
            SET proven_lemmas = COALESCE(proven_lemmas, '') || ', ' || ?
            WHERE case_name = ?
            """, (', '.join(proven_names), case_name))

        # Update status based on results
        if parsed['sorry_count'] == 0 and parsed['proven_count'] > 0:
            cursor.execute("""
            UPDATE nu4_cases
            SET status = 'proven', notes = 'Proven via Aristotle on ' || date('now')
            WHERE case_name = ? AND status != 'proven'
            """, (case_name,))
            self.log(f"Case {case_name} marked as PROVEN!")

        elif parsed['negated']:
            cursor.execute("""
            UPDATE nu4_cases
            SET notes = COALESCE(notes, '') || ' | Counterexample found on ' || date('now')
            WHERE case_name = ?
            """, (case_name,))

        conn.commit()
        conn.close()

    def trigger_followup(self, parsed: Dict, case_name: str, file_path: str):
        """Trigger follow-up generation for near-misses."""
        if 0 < parsed['sorry_count'] <= 2 and parsed['proven_count'] > 0:
            self.log(f"Near-miss detected: {parsed['sorry_count']} sorry, {parsed['proven_count']} proven")

            # Add to generator tasks
            conn = self.get_db()
            cursor = conn.cursor()

            cursor.execute("""
            INSERT INTO generator_tasks
            (generator_type, target_case, base_file, status)
            VALUES ('gap_filler', ?, ?, 'pending')
            """, (case_name, file_path))

            conn.commit()
            conn.close()

            self.log(f"Queued gap-fill task for {Path(file_path).name}")

    async def process_project(self, project_id: str, file_path: str, case_name: str):
        """Process a completed Aristotle project."""
        self.log(f"Processing: {project_id[:8]}... ({case_name})")

        # Download output
        output_path = await self.download_output(project_id)
        if not output_path:
            self.log("No output available", "WARN")
            return

        # Read and parse
        try:
            with open(output_path, 'r') as f:
                content = f.read()
        except Exception as e:
            self.log(f"Could not read output: {e}", "ERROR")
            return

        parsed = self.parse_output(content)

        self.log(f"Parsed: {parsed['proven_count']} proven, {parsed['sorry_count']} sorry, "
                 f"negated={parsed['negated']}, syntax_error={parsed['syntax_error']}")

        # Update submissions table
        conn = self.get_db()
        cursor = conn.cursor()

        cursor.execute("""
        UPDATE submissions
        SET sorry_count = ?, proven_count = ?, output_file = ?, status = 'completed'
        WHERE uuid = ?
        """, (parsed['sorry_count'], parsed['proven_count'], output_path, project_id))

        # Get submission_id
        cursor.execute("SELECT id FROM submissions WHERE uuid = ?", (project_id,))
        row = cursor.fetchone()
        submission_id = row['id'] if row else None

        conn.commit()
        conn.close()

        # Save proven lemmas
        if submission_id and parsed['lemmas']:
            self.save_proven_lemmas(parsed['lemmas'], submission_id)

        # Save counterexamples
        if parsed['negated']:
            for ce_data in parsed['counterexamples']:
                ce = ExtractedCounterexample(
                    theorem_name=ce_data.get('statement', 'unknown')[:50],
                    negated_statement=ce_data.get('statement', ''),
                    counterexample_description=str(ce_data)
                )
                self.save_counterexample(ce, project_id)

        # Update case knowledge
        self.update_case_knowledge(case_name, parsed)

        # Trigger follow-up
        self.trigger_followup(parsed, case_name, file_path)

        # Record metric
        conn = self.get_db()
        cursor = conn.cursor()
        cursor.execute("""
        INSERT INTO agentic_metrics (metric_name, metric_value, tags)
        VALUES ('proven_lemmas', ?, ?)
        """, (parsed['proven_count'], case_name))
        conn.commit()
        conn.close()

        self.log(f"Processing complete for {project_id[:8]}")


def main():
    parser = argparse.ArgumentParser(description="Learning Extractor")
    parser.add_argument("--project-id", required=True, help="Aristotle project ID")
    parser.add_argument("--file-path", required=True, help="Original file path")
    parser.add_argument("--case-name", default="unknown", help="Nu4 case name")

    args = parser.parse_args()

    extractor = LearningExtractor()
    asyncio.run(extractor.process_project(
        args.project_id,
        args.file_path,
        args.case_name
    ))


if __name__ == "__main__":
    main()
