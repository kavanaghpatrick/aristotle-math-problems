#!/usr/bin/env python3
"""
Codex Proof Loop — Iterate Codex against lake build to produce verified Lean 4 proofs.

Flow: Codex writes Lean code -> lake build checks it -> errors feed back -> repeat.
Results saved to codex_proofs/<problem_id>/ and tracked in submissions/tracking.db.
"""

import argparse
import json
import os
import re
import shutil
import signal
import sqlite3
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Optional

# ── Configuration ──────────────────────────────────────────────────────────
MATH_DIR = Path(__file__).resolve().parent.parent
TRACKING_DB = MATH_DIR / "submissions" / "tracking.db"
PROOFS_DIR = MATH_DIR / "codex_proofs"
LAKE_PACKAGES = MATH_DIR / ".lake" / "packages"
MATHLIB_REV = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
FORMAL_CONJECTURES = MATH_DIR / "formal-conjectures" / "FormalConjectures"

# ── Dataclasses ────────────────────────────────────────────────────────────

@dataclass
class LoopConfig:
    problem: str
    context_files: list = field(default_factory=list)
    max_iterations: int = 5
    build_timeout: int = 300
    reasoning_effort: str = "high"
    keep_temp: bool = False
    problem_id: Optional[str] = None


@dataclass
class IterationResult:
    iteration: int
    lean_code: str
    build_success: bool
    build_errors: str
    sorry_count: int
    wall_time: float


@dataclass
class LoopResult:
    problem_id: str
    iterations: list
    best: Optional[IterationResult]
    compiled: bool
    total_wall_time: float
    lean_file: Optional[Path] = None
    build_log: Optional[Path] = None
    sorry_targets: list = field(default_factory=list)


# ── Pure Functions ─────────────────────────────────────────────────────────

def count_sorries(lean_code: str) -> int:
    """Count non-comment sorry occurrences in Lean code."""
    count = 0
    in_block_comment = False
    for line in lean_code.splitlines():
        stripped = line.strip()
        # Track block comments
        if "/-" in stripped and "-/" not in stripped:
            in_block_comment = True
            continue
        if "-/" in stripped:
            in_block_comment = False
            continue
        if in_block_comment:
            continue
        # Skip line comments
        code_part = stripped.split("--")[0]
        count += len(re.findall(r'\bsorry\b', code_part))
    return count


def extract_theorem_statement(lean_code: str) -> Optional[str]:
    """Extract the first theorem/lemma declaration up to := or where."""
    lines = lean_code.splitlines()
    collecting = False
    stmt_lines = []
    for line in lines:
        stripped = line.strip()
        if not collecting:
            if re.match(r'^(theorem|lemma)\s+', stripped):
                collecting = True
                stmt_lines = [stripped]
                if ":=" in stripped or "where" in stripped:
                    # Single-line declaration
                    return re.split(r':=|where', stripped)[0].strip()
        else:
            stmt_lines.append(stripped)
            if ":=" in stripped or "where" in stripped:
                full = " ".join(stmt_lines)
                return re.split(r':=|where', full)[0].strip()
    if stmt_lines:
        return " ".join(stmt_lines)
    return None


def check_statement_locked(original: str, revised: str) -> bool:
    """Check that the theorem statement hasn't been changed (normalize whitespace)."""
    def normalize(s):
        return " ".join(s.split())
    return normalize(original) == normalize(revised)


def select_best(iterations: list) -> Optional[IterationResult]:
    """Pick best iteration: prefer compiled + fewer sorries, break ties by later iteration."""
    if not iterations:
        return None
    compiled = [it for it in iterations if it.build_success]
    if compiled:
        return min(compiled, key=lambda it: (it.sorry_count, -it.iteration))
    # None compiled — pick fewest sorries
    return min(iterations, key=lambda it: (it.sorry_count, -it.iteration))


def extract_lean_from_output(raw: str) -> str:
    """Extract Lean code from Codex output, stripping markdown fences if present."""
    # Try to find ```lean ... ``` block
    match = re.search(r'```lean\s*\n(.*?)```', raw, re.DOTALL)
    if match:
        return match.group(1).strip()
    # Try generic code fence
    match = re.search(r'```\s*\n(.*?)```', raw, re.DOTALL)
    if match:
        return match.group(1).strip()
    # If it starts with import, assume it's raw Lean
    if raw.strip().startswith("import"):
        return raw.strip()
    # Last resort: return as-is
    return raw.strip()


def derive_problem_id(problem: str) -> str:
    """Derive a problem ID from the problem description."""
    # If it's a file path, use the filename
    if os.path.isfile(problem):
        return Path(problem).stem
    # Otherwise, slugify the first few words
    words = re.sub(r'[^a-zA-Z0-9\s]', '', problem).split()[:4]
    return "_".join(w.lower() for w in words) or "unnamed"


# ── Temp Lean Project ──────────────────────────────────────────────────────

LAKEFILE_TEMPLATE = f"""name = "codex-proof"
version = "0.1.0"
defaultTargets = ["CodexProof"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "{MATHLIB_REV}"

[[lean_lib]]
name = "CodexProof"
"""


def create_temp_project() -> Path:
    """Create an isolated Lean project with symlinked Mathlib cache."""
    if not LAKE_PACKAGES.exists():
        print("ERROR: .lake/packages/ not found. Run `lake build` in main project first.")
        sys.exit(1)

    tmp = Path(tempfile.mkdtemp(prefix="codex_proof_"))

    # lakefile.toml
    (tmp / "lakefile.toml").write_text(LAKEFILE_TEMPLATE)

    # lean-toolchain (symlink)
    os.symlink(MATH_DIR / "lean-toolchain", tmp / "lean-toolchain")

    # lake-manifest.json (copy — lake writes to it)
    manifest = MATH_DIR / "lake-manifest.json"
    if manifest.exists():
        shutil.copy2(manifest, tmp / "lake-manifest.json")

    # .lake/packages/ (symlink)
    lake_dir = tmp / ".lake"
    lake_dir.mkdir()
    os.symlink(LAKE_PACKAGES, lake_dir / "packages")

    # Source file will be written as CodexProof.lean at root
    # (lake expects CodexProof.lean for lean_lib named "CodexProof")

    return tmp


def cleanup_temp(temp_dir: Path, keep: bool):
    """Remove temp directory unless keep=True."""
    if keep:
        print(f"  Temp dir kept: {temp_dir}")
    else:
        shutil.rmtree(temp_dir, ignore_errors=True)


# ── Knowledge Enrichment ──────────────────────────────────────────────────

def resolve_formal_statement(problem_id: str) -> Optional[str]:
    """Look up the formal theorem statement from formal-conjectures repo."""
    if not FORMAL_CONJECTURES.exists():
        return None

    # Try common patterns: ErdosProblems/NNN.lean, Arxiv/*/Name.lean
    pid = problem_id.lower().replace('_', '')

    # Extract number from erdosNNN patterns
    import re
    m = re.match(r'erdos(\d+)', pid)
    if m:
        num = m.group(1)
        candidate = FORMAL_CONJECTURES / "ErdosProblems" / f"{num}.lean"
        if candidate.exists():
            content = candidate.read_text()
            # Extract the open theorem(s)
            theorems = []
            for line in content.splitlines():
                if '@[category research open' in line:
                    theorems.append(line)
                elif theorems and ('theorem ' in line or 'sorry' in line or ':=' in line):
                    theorems.append(line)
                elif theorems and line.strip() == '':
                    break
            if theorems:
                return '\n'.join(theorems)
            # Fallback: return first theorem with sorry
            lines = content.splitlines()
            for i, line in enumerate(lines):
                if 'theorem ' in line and 'sorry' in content[content.index(line):]:
                    return '\n'.join(lines[max(0,i-2):min(len(lines),i+8)])
            return None

    # Try glob for other patterns
    for candidate in FORMAL_CONJECTURES.rglob("*.lean"):
        if problem_id.lower().replace('_', '') in candidate.stem.lower().replace('_', ''):
            content = candidate.read_text()
            lines = content.splitlines()
            for i, line in enumerate(lines):
                if '@[category research open' in line:
                    return '\n'.join(lines[i:min(len(lines),i+6)])
            break

    return None


def get_failed_approaches(problem_id: str) -> list:
    """Check failed_approaches and false_lemmas tables for this problem."""
    results = []
    try:
        conn = sqlite3.connect(str(TRACKING_DB))
        # Failed approaches
        rows = conn.execute(
            "SELECT approach, reason FROM failed_approaches WHERE problem_id LIKE ? LIMIT 5",
            (f'%{problem_id}%',)
        ).fetchall()
        for r in rows:
            results.append(f"FAILED: {r[0]} — {r[1]}")

        # False lemmas
        rows = conn.execute(
            "SELECT lemma_name, reason FROM false_lemmas WHERE lemma_name LIKE ? LIMIT 5",
            (f'%{problem_id}%',)
        ).fetchall()
        for r in rows:
            results.append(f"FALSE LEMMA: {r[0]} — {r[1]}")

        conn.close()
    except Exception:
        pass
    return results


# ── Codex Invocation ───────────────────────────────────────────────────────

def _summarize_lean_context(lean_code: str, max_lines: int = 200) -> str:
    """Extract a useful summary from a large Lean context file.

    Keeps: theorem/lemma/def signatures, sorry locations, key structure.
    Drops: long proof bodies, repetitive tactic blocks.
    """
    lines = lean_code.splitlines()
    if len(lines) <= max_lines:
        return lean_code

    summary_lines = []
    in_proof_body = False
    proof_depth = 0

    for i, line in enumerate(lines):
        stripped = line.strip()

        # Always keep: imports, theorem/lemma/def signatures, sorry lines, section markers
        if any(stripped.startswith(kw) for kw in
               ['import ', 'open ', 'namespace ', 'end ', 'section ',
                'theorem ', 'lemma ', 'def ', 'instance ', 'class ',
                'structure ', '#check ', '#eval ', '@[', '/-', '-/']):
            summary_lines.append(line)
            in_proof_body = False
            continue

        if 'sorry' in stripped:
            summary_lines.append(line)
            continue

        if ':= by' in stripped or ':= by' in (lines[i-1] if i > 0 else ''):
            summary_lines.append(line)
            in_proof_body = True
            proof_depth = 0
            continue

        # In proof bodies, keep first 3 lines then skip
        if in_proof_body:
            proof_depth += 1
            if proof_depth <= 3:
                summary_lines.append(line)
            elif proof_depth == 4:
                summary_lines.append("    -- [proof body truncated]")
            continue

        # Keep other structural lines
        if stripped and not stripped.startswith('--'):
            summary_lines.append(line)

    result = '\n'.join(summary_lines[:max_lines])
    if len(summary_lines) > max_lines:
        result += f"\n-- [truncated, {len(lines)} total lines in original]"
    return result


def build_initial_prompt(problem: str, context_files: list,
                         problem_id: Optional[str] = None) -> str:
    """Build the first-iteration prompt for Codex.

    Auto-enriches with:
    - Formal theorem statement from formal-conjectures (if available)
    - Failed approaches / false lemmas from DB (to avoid dead ends)
    - Summarized context from prior attempts
    """
    # If problem is a file path, read it
    problem_text = problem
    if os.path.isfile(problem):
        problem_text = Path(problem).read_text()

    # Auto-resolve formal theorem statement
    formal_section = ""
    if problem_id:
        formal = resolve_formal_statement(problem_id)
        if formal:
            formal_section = f"\nFORMAL THEOREM (from formal-conjectures, this is the exact target):\n```lean\n{formal}\n```\n"

    # Check for dead ends
    dead_ends_section = ""
    if problem_id:
        dead_ends = get_failed_approaches(problem_id)
        if dead_ends:
            dead_ends_section = "\nKNOWN DEAD ENDS (do NOT try these approaches):\n"
            for de in dead_ends:
                dead_ends_section += f"- {de}\n"

    # Build context from prior work
    context_section = ""
    for cf in context_files:
        p = Path(cf)
        if p.exists():
            raw = p.read_text()
            # Summarize large context files
            if len(raw.splitlines()) > 200:
                summarized = _summarize_lean_context(raw)
                sorry_count = count_sorries(raw)
                context_section += (
                    f"\nPRIOR WORK ({p.name}, {len(raw.splitlines())} lines, {sorry_count} sorry remaining):\n"
                    f"The following Lean 4 code was produced by a prior attempt. "
                    f"It contains proven lemmas you can REUSE and sorry gaps you should try to CLOSE.\n"
                    f"```lean\n{summarized}\n```\n"
                )
            else:
                sorry_count = count_sorries(raw)
                label = f"PRIOR WORK ({p.name}, {sorry_count} sorry)" if sorry_count else f"PROVEN CONTEXT ({p.name})"
                context_section += f"\n{label}:\n```lean\n{raw}\n```\n"

    return f"""Write a Lean 4 proof for the following problem. Output ONLY valid Lean 4 code.

PROBLEM:
{problem_text}
{formal_section}{dead_ends_section}
YOUR TASK:
1. If prior work is provided below, BUILD ON IT — reuse proven lemmas, close remaining sorry gaps.
2. If no prior work exists, write a proof from scratch.
3. Focus on CLOSING sorry gaps. Each sorry you eliminate is progress.
{context_section}
RULES:
- Start with `import Mathlib`
- Use `sorry` for sub-goals you cannot prove, but minimize sorry count
- Do NOT change the theorem statement if one is provided
- Target Lean 4 v4.24.0 with current Mathlib
- Output a single complete .lean file, nothing else
- Prefer `omega`, `simp`, `norm_num`, `decide`, `ring`, `linarith` tactics
- Keep the file under 500 lines
"""


def build_revision_prompt(problem: str, prior_code: str, errors: str,
                          locked_statement: Optional[str], sorry_count: int,
                          iteration: int) -> str:
    """Build the error-feedback prompt for subsequent iterations."""
    problem_text = problem
    if os.path.isfile(problem):
        problem_text = Path(problem).read_text()

    lock_line = ""
    if locked_statement:
        lock_line = f"- Do NOT change the theorem statement: `{locked_statement}`"

    return f"""Your Lean 4 proof failed to compile. Fix the errors below.

ORIGINAL PROBLEM:
{problem_text}

YOUR PREVIOUS CODE (iteration {iteration}):
```lean
{prior_code}
```

COMPILER ERRORS:
{errors}

RULES:
- Fix the compilation errors
{lock_line}
- Do NOT add new `sorry` unless absolutely necessary (current sorry count: {sorry_count})
- Minimize total sorry count
- Output the complete corrected .lean file, nothing else
- Start with `import Mathlib`
"""


def invoke_codex(prompt: str, reasoning_effort: str = "high") -> str:
    """Run codex exec and return the output."""
    # Write prompt to temp file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
        f.write(prompt)
        prompt_file = f.name

    try:
        # Read prompt text to pass directly
        prompt_text = Path(prompt_file).read_text()

        cmd = ["codex", "exec", "--full-auto"]
        if reasoning_effort != "medium":
            cmd.extend(["-c", f"model_reasoning_effort={reasoning_effort}"])
        cmd.append(prompt_text)

        result = subprocess.run(
            cmd,
            capture_output=True, text=True, timeout=3600,
            cwd=str(MATH_DIR)
        )
        output = result.stdout.strip()
        if not output and result.stderr:
            # Show last 200 chars of stderr for debugging
            print(f"  Codex stderr: {result.stderr[-200:]}")
        return output
    except subprocess.TimeoutExpired:
        print("  Codex timed out (3600s)")
        return ""
    except FileNotFoundError:
        print("  ERROR: `codex` CLI not found. Install: npm install -g @anthropic-ai/codex")
        return ""
    finally:
        os.unlink(prompt_file)


# ── Lake Build ─────────────────────────────────────────────────────────────

def run_lake_build(project_dir: Path, timeout: int = 300) -> tuple:
    """Run lake build in the temp project. Returns (success, stderr)."""
    try:
        result = subprocess.run(
            ["lake", "build"],
            cwd=str(project_dir),
            capture_output=True, text=True,
            timeout=timeout
        )
        return (result.returncode == 0, result.stderr)
    except subprocess.TimeoutExpired:
        return (False, f"Build timed out after {timeout}s")
    except FileNotFoundError:
        return (False, "lake not found in PATH")


# ── Sorry Extraction ───────────────────────────────────────────────────────

def extract_sorry_targets(lean_code: str, problem_id: str, output_dir: Path) -> list:
    """Extract each sorry into a standalone sub-problem file."""
    targets = []
    lines = lean_code.splitlines()
    current_decl = None
    current_decl_start = -1
    decl_lines = []

    for i, line in enumerate(lines):
        stripped = line.strip()
        # Track theorem/lemma declarations
        if re.match(r'^(theorem|lemma)\s+', stripped):
            current_decl = stripped
            current_decl_start = i
            decl_lines = [line]
        elif current_decl is not None:
            decl_lines.append(line)

        # Check for sorry (not in comment)
        code_part = stripped.split("--")[0]
        if re.search(r'\bsorry\b', code_part) and current_decl:
            n = len(targets) + 1
            # Build standalone lean file
            stmt = "\n".join(decl_lines[:10])  # First 10 lines of declaration
            lean_content = f"import Mathlib\n\n-- Extracted sorry target from {problem_id}\n{stmt}\n  sorry\n"

            # Build informal sketch
            decl_name = re.search(r'(theorem|lemma)\s+(\S+)', current_decl)
            name = decl_name.group(2) if decl_name else f"sorry_{n}"
            txt_content = f"""OPEN GAP: Sub-goal from {problem_id} — {name}
Source: Codex proof loop extraction
Domain: nt

Extracted sorry target: {name}
From parent proof of {problem_id}.

{stmt}
  sorry

Status: OPEN. Extracted from partial Codex proof.
"""
            sorry_dir = output_dir / "sorry_targets"
            sorry_dir.mkdir(exist_ok=True)

            lean_path = sorry_dir / f"sorry_{n}.lean"
            lean_path.write_text(lean_content)

            txt_path = sorry_dir / f"sorry_{n}.txt"
            txt_path.write_text(txt_content)

            targets.append(lean_path)
            # Reset to avoid duplicating the same sorry scope
            current_decl = None
            decl_lines = []

    return targets


# ── Result Storage ─────────────────────────────────────────────────────────

def save_result(result: LoopResult, config: LoopConfig) -> Path:
    """Save proof result to codex_proofs/ and DB."""
    prob_dir = PROOFS_DIR / result.problem_id
    prob_dir.mkdir(parents=True, exist_ok=True)

    # Find next attempt number
    existing = sorted(prob_dir.glob("attempt_*"))
    next_num = len(existing) + 1
    attempt_dir = prob_dir / f"attempt_{next_num:03d}"
    attempt_dir.mkdir()

    # Save best .lean
    if result.best and result.best.lean_code:
        lean_path = attempt_dir / "proof.lean"
        lean_path.write_text(result.best.lean_code)
        result.lean_file = lean_path

        # Update best.lean symlink
        best_link = prob_dir / "best.lean"
        if best_link.is_symlink() or best_link.exists():
            best_link.unlink()
        best_link.symlink_to(lean_path)

    # Save build log
    if result.best:
        log_path = attempt_dir / "build.log"
        log_path.write_text(result.best.build_errors or "(no errors)")
        result.build_log = log_path

    # Save metadata
    meta = {
        "problem_id": result.problem_id,
        "attempt": next_num,
        "timestamp": datetime.now().isoformat(),
        "iterations": len(result.iterations),
        "sorry_count": result.best.sorry_count if result.best else -1,
        "compiled": result.compiled,
        "model": "gpt-5.3-codex",
        "reasoning_effort": config.reasoning_effort,
        "wall_time_seconds": round(result.total_wall_time, 1),
        "theorem_statement": extract_theorem_statement(result.best.lean_code) if result.best else None,
        "context_files": [str(f) for f in config.context_files],
    }
    (attempt_dir / "metadata.json").write_text(json.dumps(meta, indent=2))

    # Extract sorry targets if any
    if result.best and result.best.sorry_count > 0:
        result.sorry_targets = extract_sorry_targets(
            result.best.lean_code, result.problem_id, prob_dir
        )

    # Record to DB
    record_to_db(result, config)

    return attempt_dir


# ── Database ───────────────────────────────────────────────────────────────

def ensure_db_table():
    """Create codex_proofs table if it doesn't exist."""
    try:
        conn = sqlite3.connect(str(TRACKING_DB))
        conn.executescript("""
            CREATE TABLE IF NOT EXISTS codex_proofs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                problem_id TEXT NOT NULL,
                created_at TEXT DEFAULT CURRENT_TIMESTAMP,
                iterations INTEGER NOT NULL,
                sorry_count INTEGER,
                compiled INTEGER NOT NULL DEFAULT 0,
                model TEXT DEFAULT 'gpt-5.3-codex',
                reasoning_effort TEXT DEFAULT 'high',
                wall_time_seconds REAL,
                lean_file TEXT,
                build_log TEXT,
                promoted_to_aristotle TEXT,
                parent_proof_id INTEGER,
                theorem_statement TEXT,
                context_files TEXT,
                FOREIGN KEY (parent_proof_id) REFERENCES codex_proofs(id)
            );
            CREATE INDEX IF NOT EXISTS idx_codex_proofs_problem ON codex_proofs(problem_id);
            CREATE INDEX IF NOT EXISTS idx_codex_proofs_compiled ON codex_proofs(compiled);
            CREATE INDEX IF NOT EXISTS idx_codex_proofs_parent ON codex_proofs(parent_proof_id);
        """)
        conn.close()
    except Exception as e:
        print(f"  WARNING: DB table creation failed: {e}")


def record_to_db(result: LoopResult, config: LoopConfig):
    """Insert a row into codex_proofs."""
    try:
        conn = sqlite3.connect(str(TRACKING_DB))
        conn.execute(
            """INSERT INTO codex_proofs
               (problem_id, iterations, sorry_count, compiled,
                model, reasoning_effort, wall_time_seconds,
                lean_file, build_log, theorem_statement, context_files)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (
                result.problem_id,
                len(result.iterations),
                result.best.sorry_count if result.best else -1,
                1 if result.compiled else 0,
                "gpt-5.3-codex",
                config.reasoning_effort,
                round(result.total_wall_time, 1),
                str(result.lean_file) if result.lean_file else None,
                str(result.build_log) if result.build_log else None,
                extract_theorem_statement(result.best.lean_code) if result.best else None,
                json.dumps([str(f) for f in config.context_files]),
            )
        )
        conn.commit()
        conn.close()
    except Exception as e:
        print(f"  WARNING: DB recording failed: {e}")


# ── Main Loop ──────────────────────────────────────────────────────────────

def run_loop(config: LoopConfig) -> LoopResult:
    """Run the Codex proof loop."""
    problem_id = config.problem_id or derive_problem_id(config.problem)
    iterations = []
    locked_statement = None
    best_sorry_count = float('inf')
    start_time = time.time()

    print(f"\n{'='*60}")
    print(f"  CODEX PROOF LOOP: {problem_id}")
    print(f"  Max iterations: {config.max_iterations}")
    print(f"  Reasoning effort: {config.reasoning_effort}")
    print(f"{'='*60}\n")

    temp_dir = create_temp_project()
    print(f"  Temp project: {temp_dir}")

    try:
        for i in range(1, config.max_iterations + 1):
            iter_start = time.time()
            print(f"\n--- Iteration {i}/{config.max_iterations} ---")

            # Build prompt
            if i == 1:
                prompt = build_initial_prompt(config.problem, config.context_files, config.problem_id)
            elif iterations:
                prev = iterations[-1]
                prompt = build_revision_prompt(
                    config.problem, prev.lean_code, prev.build_errors,
                    locked_statement, prev.sorry_count, i
                )
            else:
                # No prior iteration succeeded — retry with initial prompt
                prompt = build_initial_prompt(config.problem, config.context_files, config.problem_id)

            # Invoke Codex
            print("  Calling Codex...", end=" ", flush=True)
            raw_output = invoke_codex(prompt, config.reasoning_effort)
            if not raw_output:
                print("empty output, skipping")
                continue

            lean_code = extract_lean_from_output(raw_output)
            if not lean_code or len(lean_code) < 20:
                print("garbage output, skipping")
                continue
            print(f"got {len(lean_code)} chars")

            # Lock theorem statement after first valid output
            stmt = extract_theorem_statement(lean_code)
            if i == 1 and stmt:
                locked_statement = stmt
                print(f"  Locked statement: {stmt[:80]}...")
            elif locked_statement and stmt and not check_statement_locked(locked_statement, stmt):
                print("  REJECTED: theorem statement changed, using prior code")
                continue

            # Count sorries
            sorry_count = count_sorries(lean_code)

            # Reject sorry inflation
            if sorry_count > best_sorry_count and iterations:
                print(f"  REJECTED: sorry count increased ({sorry_count} > {best_sorry_count})")
                # Still use this iteration for error feedback but don't count it as best
                # Write the prior best code instead
                lean_code = select_best(iterations).lean_code
                sorry_count = count_sorries(lean_code)

            if sorry_count < best_sorry_count:
                best_sorry_count = sorry_count

            print(f"  Sorry count: {sorry_count}")

            # Write to temp project and build
            attempt_file = temp_dir / "CodexProof.lean"
            attempt_file.write_text(lean_code)

            print("  Building...", end=" ", flush=True)
            build_ok, build_errors = run_lake_build(temp_dir, config.build_timeout)
            iter_time = time.time() - iter_start

            if build_ok:
                print(f"COMPILED ({iter_time:.1f}s)")
            else:
                # Truncate long error output for display
                err_preview = build_errors[:300].replace('\n', ' | ')
                print(f"FAILED ({iter_time:.1f}s)")
                print(f"  Errors: {err_preview}")

            it_result = IterationResult(
                iteration=i,
                lean_code=lean_code,
                build_success=build_ok,
                build_errors=build_errors,
                sorry_count=sorry_count,
                wall_time=iter_time
            )
            iterations.append(it_result)

            # Short-circuit on perfect result
            if build_ok and sorry_count == 0:
                print("\n  *** PERFECT: Compiled with 0 sorries! ***")
                break

    finally:
        cleanup_temp(temp_dir, config.keep_temp)

    total_time = time.time() - start_time
    best = select_best(iterations)

    result = LoopResult(
        problem_id=problem_id,
        iterations=iterations,
        best=best,
        compiled=best.build_success if best else False,
        total_wall_time=total_time,
    )

    # Print summary
    print(f"\n{'='*60}")
    print(f"  RESULT: {problem_id}")
    if best:
        status = "COMPILED" if best.build_success else "PARTIAL"
        print(f"  Status: {status}")
        print(f"  Sorry count: {best.sorry_count}")
        print(f"  Best iteration: {best.iteration}/{len(iterations)}")
    else:
        print("  Status: FAILED (no valid output)")
    print(f"  Total time: {total_time:.1f}s")
    print(f"{'='*60}\n")

    return result


# ── CLI ────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Codex Proof Loop — iterate Codex against lake build",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s "Prove 1+1=2 in Lean 4"
  %(prog)s submissions/sketches/erdos850.txt --context results_v07/slot700_result.lean
  %(prog)s "theorem foo : P := by sorry" --max-iterations 8 --reasoning-effort xhigh
  %(prog)s --problem-id agoh_giuga_m9 codex_results/v3/agoh_giuga_ge6_factors.lean
        """
    )
    parser.add_argument("problem", help="Problem description, theorem statement, or .txt/.lean file path")
    parser.add_argument("--context", action="append", default=[], help="Context .lean file (repeatable)")
    parser.add_argument("--max-iterations", type=int, default=5, help="Max compile-fix iterations (default: 5)")
    parser.add_argument("--build-timeout", type=int, default=300, help="Lake build timeout in seconds (default: 300)")
    parser.add_argument("--reasoning-effort", choices=["low", "medium", "high", "xhigh"], default="high",
                        help="Codex reasoning effort (default: high)")
    parser.add_argument("--keep-temp", action="store_true", help="Keep temp Lean project for debugging")
    parser.add_argument("--problem-id", help="Explicit problem ID (default: derived from problem text)")

    args = parser.parse_args()

    # Ensure DB table exists
    ensure_db_table()

    config = LoopConfig(
        problem=args.problem,
        context_files=[Path(f) for f in args.context],
        max_iterations=args.max_iterations,
        build_timeout=args.build_timeout,
        reasoning_effort=args.reasoning_effort,
        keep_temp=args.keep_temp,
        problem_id=args.problem_id,
    )

    # Handle SIGINT gracefully
    def sigint_handler(sig, frame):
        print("\n\n  Interrupted! Saving current best...")
        sys.exit(1)
    signal.signal(signal.SIGINT, sigint_handler)

    result = run_loop(config)

    if result.best:
        attempt_dir = save_result(result, config)
        print(f"  Saved to: {attempt_dir}")
        if result.compiled:
            print(f"  Best proof: {result.lean_file}")
        if result.sorry_targets:
            print(f"  Sorry targets: {len(result.sorry_targets)} extracted")
            for t in result.sorry_targets:
                print(f"    - {t}")
    else:
        print("  No valid output produced.")
        sys.exit(1)


if __name__ == "__main__":
    main()
