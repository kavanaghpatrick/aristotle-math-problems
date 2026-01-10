#!/usr/bin/env python3
"""
Generator Pool - Spawns and manages proof generation agents.

Generators:
1. Proof Generator - Creates new proof attempts using scaffolding
2. Gap Filler - Completes near-miss proofs (1-2 sorry)
3. Variant Explorer - Mutates successful approaches
"""

import sqlite3
import subprocess
import json
import argparse
import asyncio
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional
from concurrent.futures import ProcessPoolExecutor, as_completed

sys.path.insert(0, str(Path(__file__).parent.parent))
from config import (
    DB_PATH, CODEX_WORKTREES, NU4_CASES, PROOF_STRATEGIES,
    SUBMISSIONS_DIR, WORKTREES_DIR
)


class GeneratorPool:
    """Manages a pool of proof generators."""

    def __init__(self, max_workers: int = 5):
        self.db_path = DB_PATH
        self.max_workers = max_workers
        self.active_generators: Dict[int, subprocess.Popen] = {}

    def log(self, msg: str, level: str = "INFO"):
        timestamp = datetime.now().strftime("%H:%M:%S")
        print(f"[{timestamp}] [Generator] [{level}] {msg}", flush=True)

    def get_db(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path)
        conn.row_factory = sqlite3.Row
        return conn

    def get_pending_tasks(self, limit: int = 10) -> List[Dict]:
        """Get pending generator tasks."""
        conn = self.get_db()
        cursor = conn.cursor()

        cursor.execute("""
        SELECT id, generator_type, target_case, strategy, base_file
        FROM generator_tasks
        WHERE status = 'pending'
        ORDER BY
            CASE target_case
                WHEN 'cycle_4' THEN 1
                WHEN 'path_4' THEN 2
                ELSE 3
            END,
            created_at ASC
        LIMIT ?
        """, (limit,))

        tasks = [dict(row) for row in cursor.fetchall()]
        conn.close()
        return tasks

    def get_near_misses(self) -> List[Dict]:
        """Get near-miss proofs for gap filling."""
        conn = self.get_db()
        cursor = conn.cursor()

        cursor.execute("""
        SELECT s.uuid, s.filename, s.sorry_count, s.proven_count, s.output_file
        FROM submissions s
        WHERE s.status = 'completed'
          AND s.sorry_count BETWEEN 1 AND 2
          AND s.proven_count > 0
        ORDER BY s.sorry_count ASC, s.proven_count DESC
        LIMIT 10
        """)

        near_misses = [dict(row) for row in cursor.fetchall()]
        conn.close()
        return near_misses

    def get_scaffolding(self, case_name: str) -> str:
        """Get proven scaffolding for a case."""
        conn = self.get_db()
        cursor = conn.cursor()

        # Get proven lemmas for this case
        cursor.execute("""
        SELECT name, statement, proof_code
        FROM literature_lemmas
        WHERE validated_true = 1
        ORDER BY name
        """)

        scaffolding = []
        for row in cursor.fetchall():
            scaffolding.append(f"-- {row['name']}: {row['statement']}")
            if row['proof_code']:
                scaffolding.append(row['proof_code'])
            scaffolding.append("")

        conn.close()
        return "\n".join(scaffolding)

    def update_task_status(self, task_id: int, status: str, output_file: str = None, error: str = None):
        """Update task status in database."""
        conn = self.get_db()
        cursor = conn.cursor()

        if status == 'running':
            cursor.execute("""
            UPDATE generator_tasks
            SET status = 'running', started_at = datetime('now')
            WHERE id = ?
            """, (task_id,))
        elif status == 'completed':
            cursor.execute("""
            UPDATE generator_tasks
            SET status = 'completed', completed_at = datetime('now'), output_file = ?
            WHERE id = ?
            """, (output_file, task_id))
        elif status == 'failed':
            cursor.execute("""
            UPDATE generator_tasks
            SET status = 'failed', completed_at = datetime('now'), error_message = ?
            WHERE id = ?
            """, (error, task_id))

        conn.commit()
        conn.close()

    def generate_proof_template(self, case_name: str, strategy: str) -> str:
        """Generate a proof template for a case and strategy."""
        # Get case-specific info
        conn = self.get_db()
        cursor = conn.cursor()

        cursor.execute("""
        SELECT correct_approach, proven_lemmas, key_insight
        FROM nu4_cases
        WHERE case_name = ?
        """, (case_name,))

        case_info = cursor.fetchone()
        conn.close()

        template = f"""/-
  Tuza's Conjecture: ν=4 Case - {case_name}
  Strategy: {strategy}
  Generated: {datetime.now().isoformat()}

  Goal: Prove τ(G) ≤ 8 for graphs with ν(G) = 4
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {{V : Type*}} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- Basic definitions
def Triangle (G : SimpleGraph V) : Type := {{ t : Finset V // t.card = 3 ∧ G.IsClique t }}

def trianglePacking (G : SimpleGraph V) (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, ∃ ht : t.card = 3, G.IsClique t) ∧
  (∀ t₁ t₂ : Finset V, t₁ ∈ M → t₂ ∈ M → t₁ ≠ t₂ → (t₁.sym2 ∩ t₂.sym2 : Finset _) = ∅)

def triangleCover (G : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  ∀ t : Finset V, (∃ ht : t.card = 3, G.IsClique t) → ∃ e ∈ C, e ∈ t.sym2

def tau (G : SimpleGraph V) : ℕ :=
  sInf {{ C.card | C : Finset (Sym2 V) // C ⊆ G.edgeFinset ∧ triangleCover G C }}

def nu (G : SimpleGraph V) : ℕ :=
  sSup {{ M.card | M : Finset (Finset V) // trianglePacking G M }}

"""

        if case_info:
            template += f"""
-- Case-specific information:
-- Approach: {case_info['correct_approach'] or 'TBD'}
-- Proven lemmas: {case_info['proven_lemmas'] or 'None'}
-- Key insight: {case_info['key_insight'] or 'None'}
"""

        # Add strategy-specific structure
        if strategy == 'direct_decomposition':
            template += """
-- Direct decomposition: Break into T_pair components
-- T_pair(A,B) = triangles sharing edge with A or B

def T_pair (M : Finset (Finset V)) (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) : Finset (Finset V) :=
  M.filter (fun t => (t.sym2 ∩ A.sym2).Nonempty ∨ (t.sym2 ∩ B.sym2).Nonempty)

theorem tau_le_8_decomposition
    (hM : trianglePacking G M) (hcard : M.card = 4) (hmax : ∀ t, (∃ ht : t.card = 3, G.IsClique t) → (t.sym2 ∩ ⋃₀ (M.image (·.sym2))).Nonempty) :
    tau G ≤ 8 := by
  sorry
"""
        elif strategy == 'LP_dual_certificate':
            template += """
-- LP Dual Certificate approach
-- Construct a covering selection S ⊆ M-edges with |S| = |M|

def CoveringSelection (M : Finset (Finset V)) (S : Finset (Sym2 V)) : Prop :=
  S.card = M.card ∧
  S ⊆ ⋃ t ∈ M, t.sym2 ∧
  ∀ t : Finset V, (∃ ht : t.card = 3, G.IsClique t) → ∃ e ∈ S, e ∈ t.sym2

theorem covering_selection_exists
    (hM : trianglePacking G M) (hcard : M.card = 4) (hmax : ∀ t, (∃ ht : t.card = 3, G.IsClique t) → (t.sym2 ∩ ⋃₀ (M.image (·.sym2))).Nonempty) :
    ∃ S : Finset (Sym2 V), CoveringSelection M S := by
  sorry

theorem tau_le_8_via_LP
    (hM : trianglePacking G M) (hcard : M.card = 4) (hmax : ∀ t, (∃ ht : t.card = 3, G.IsClique t) → (t.sym2 ∩ ⋃₀ (M.image (·.sym2))).Nonempty) :
    tau G ≤ 8 := by
  obtain ⟨S, hS⟩ := covering_selection_exists G hM hcard hmax
  sorry
"""
        elif strategy == 'sunflower_vertex_cover':
            template += """
-- Sunflower approach: Cover by shared vertices
-- Warning: Known false patterns - external triangles DON'T share common vertex

def sharedVertices (M : Finset (Finset V)) : Finset V :=
  (M.powerset.filter (fun S => S.card ≥ 2)).biUnion (fun S =>
    S.toList.foldl (· ∩ ·) (S.toList.head!))

-- τ ≤ 12 is provable (3 edges per shared vertex × 4 vertices)
-- τ ≤ 8 requires non-vertex-centric approach

theorem tau_le_12_sunflower
    (hM : trianglePacking G M) (hcard : M.card = 4) :
    tau G ≤ 12 := by
  sorry
"""

        template += """
-- Main theorem placeholder
theorem tuza_nu_4_{case_name} (hnu : nu G = 4) : tau G ≤ 8 := by
  sorry
""".replace("{case_name}", case_name)

        return template

    def run_proof_generator(self, task: Dict) -> Optional[str]:
        """Run a single proof generation task."""
        case_name = task['target_case']
        strategy = task['strategy']

        self.log(f"Generating proof: {case_name} / {strategy}")
        self.update_task_status(task['id'], 'running')

        try:
            # Generate template
            template = self.generate_proof_template(case_name, strategy)

            # Create output file
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            slot_num = 200 + task['id']  # Start at slot 200 for generated
            output_file = SUBMISSIONS_DIR / "generated" / f"slot{slot_num}_{case_name}_{strategy[:10]}.lean"
            output_file.parent.mkdir(parents=True, exist_ok=True)

            with open(output_file, 'w') as f:
                f.write(template)

            self.update_task_status(task['id'], 'completed', str(output_file))

            # Add to submission queue
            conn = self.get_db()
            cursor = conn.cursor()
            cursor.execute("""
            INSERT OR IGNORE INTO submission_queue
            (file_path, case_name, approach, priority, validation_stage)
            VALUES (?, ?, ?, 50, 'pending')
            """, (str(output_file), case_name, strategy))
            conn.commit()
            conn.close()

            self.log(f"Generated: {output_file.name}")
            return str(output_file)

        except Exception as e:
            self.update_task_status(task['id'], 'failed', error=str(e))
            self.log(f"Generation failed: {e}", "ERROR")
            return None

    def run_gap_filler(self, near_miss: Dict) -> Optional[str]:
        """Try to fill gaps in a near-miss proof."""
        self.log(f"Gap filling: {near_miss['filename']} ({near_miss['sorry_count']} sorry)")

        if not near_miss.get('output_file') or not Path(near_miss['output_file']).exists():
            self.log("No output file available", "WARN")
            return None

        # Read the output
        try:
            with open(near_miss['output_file'], 'r') as f:
                content = f.read()
        except Exception as e:
            self.log(f"Could not read output: {e}", "ERROR")
            return None

        # Find sorry locations
        import re
        sorry_matches = list(re.finditer(r'sorry', content))

        if not sorry_matches:
            self.log("No sorries found", "WARN")
            return None

        # Use Grok to suggest gap fills
        try:
            sys.path.insert(0, str(Path(__file__).parent.parent.parent / "scripts"))
            from grok_query import query_grok

            # Extract context around first sorry
            sorry_pos = sorry_matches[0].start()
            context_start = max(0, sorry_pos - 500)
            context_end = min(len(content), sorry_pos + 500)
            context = content[context_start:context_end]

            prompt = f"""Complete this Lean 4 proof. Replace the sorry with actual proof code.

Context (around the sorry):
```lean
{context}
```

Focus on:
1. The goal state at that point
2. Available hypotheses
3. Appropriate tactics

Return ONLY the replacement for 'sorry' (the proof tactic sequence).
"""

            response = query_grok(prompt, timeout=300)

            # Create a new version with the suggested fix
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            new_file = SUBMISSIONS_DIR / "gap_filled" / f"{Path(near_miss['filename']).stem}_filled_{timestamp}.lean"
            new_file.parent.mkdir(parents=True, exist_ok=True)

            # Replace first sorry with suggestion (crude, but a start)
            if response and 'sorry' not in response.lower():
                new_content = content[:sorry_matches[0].start()] + response.strip() + content[sorry_matches[0].end():]
            else:
                new_content = content  # Keep original

            with open(new_file, 'w') as f:
                f.write(new_content)

            self.log(f"Gap-filled version: {new_file.name}")

            # Add to queue
            conn = self.get_db()
            cursor = conn.cursor()
            cursor.execute("""
            INSERT OR IGNORE INTO submission_queue
            (file_path, priority, validation_stage)
            VALUES (?, 90, 'pending')
            """, (str(new_file),))
            conn.commit()
            conn.close()

            return str(new_file)

        except Exception as e:
            self.log(f"Gap filling failed: {e}", "ERROR")
            return None

    def run_batch(self, count: int = 10):
        """Run a batch of generator tasks."""
        self.log(f"Starting batch generation (target: {count} files)")

        generated = 0

        # First, handle near-misses (highest priority)
        near_misses = self.get_near_misses()
        for nm in near_misses[:3]:  # Max 3 gap fills per batch
            if self.run_gap_filler(nm):
                generated += 1
            if generated >= count:
                break

        # Then, run proof generators
        if generated < count:
            tasks = self.get_pending_tasks(count - generated)
            for task in tasks:
                if self.run_proof_generator(task):
                    generated += 1

        self.log(f"Batch complete: {generated} files generated")
        return generated


def main():
    parser = argparse.ArgumentParser(description="Generator Pool")
    parser.add_argument("--count", type=int, default=10, help="Number of files to generate")
    parser.add_argument("--gap-fill-only", action="store_true", help="Only run gap filler")
    parser.add_argument("--proof-only", action="store_true", help="Only run proof generator")

    args = parser.parse_args()

    pool = GeneratorPool()

    if args.gap_fill_only:
        near_misses = pool.get_near_misses()
        for nm in near_misses[:args.count]:
            pool.run_gap_filler(nm)
    elif args.proof_only:
        tasks = pool.get_pending_tasks(args.count)
        for task in tasks:
            pool.run_proof_generator(task)
    else:
        pool.run_batch(args.count)


if __name__ == "__main__":
    main()
