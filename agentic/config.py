"""
Agentic Theorem Proving System - Configuration
"""

import os
from pathlib import Path

# Paths
PROJECT_ROOT = Path(__file__).parent.parent
DB_PATH = PROJECT_ROOT / "submissions" / "tracking.db"
SUBMISSIONS_DIR = PROJECT_ROOT / "submissions"
AGENTIC_DIR = PROJECT_ROOT / "agentic"
RESULTS_DIR = SUBMISSIONS_DIR / "results"
WORKTREES_DIR = PROJECT_ROOT.parent / "math-worktrees"

# Aristotle settings
MAX_PARALLEL_SLOTS = 15
POLL_INTERVAL_SECONDS = 30
RESULT_CHECK_INTERVAL = 120
MAX_WAIT_FOR_SLOT = 3600  # 1 hour

# Queue management
MIN_QUEUE_DEPTH = 30  # Spawn generators when below this
MAX_QUEUE_DEPTH = 100  # Stop generating when above this
MAX_RETRIES_PER_APPROACH = 3

# Priority settings
PRIORITY_NEAR_MISS = 90      # 1-2 sorry
PRIORITY_BLOCKED_CASE = 80   # cycle_4
PRIORITY_NEW_APPROACH = 70   # Untried strategies
PRIORITY_STANDARD = 50       # Normal submissions
PRIORITY_EXPLORATORY = 30    # Low probability attempts

# Validation settings
GROK_PLAUSIBILITY_THRESHOLD = 0.7
COUNTEREXAMPLE_TIMEOUT_SECONDS = 120
GROK_TIMEOUT_SECONDS = 300

# Generator settings
CODEX_WORKTREES = 5
VARIANT_MUTATIONS_PER_PROOF = 3
GAP_FILL_MAX_ATTEMPTS = 5

# Slot allocation
SLOT_ALLOCATION = {
    'cycle_4': range(1, 6),      # Slots 1-5: hardest case
    'near_miss': range(6, 9),    # Slots 6-8: high success probability
    'general': range(9, 13),     # Slots 9-12: standard queue
    'exploratory': range(13, 16) # Slots 13-15: experimental
}

# Nu4 cases with priority order
NU4_CASES = [
    'cycle_4',       # Hardest, needs most attention
    'path_4',        # Partial progress
    'two_two_vw',    # Partial progress
    'matching_2',    # Converts to two_two_vw
    'scattered',     # Proven but needs tau<=8
    'three_share_v', # Trivially proven
    'star_all_4',    # Trivially proven
]

# Known proof strategies
PROOF_STRATEGIES = [
    'direct_decomposition',      # Break into T_pair components
    'LP_dual_certificate',       # Construct fractional dual
    'covering_selection',        # Choose |M| edges covering all
    'sunflower_vertex_cover',    # Cover by shared vertices
    'greedy_edge_selection',     # Greedy algorithm proof
    'case_analysis',             # Exhaustive case split
    'induction_on_triangles',    # Induction on triangle count
    'contrapositive',            # Assume tau > 8, derive contradiction
]

# API Keys (from environment)
GROK_API_KEY = os.environ.get("GROK_API_KEY") or os.environ.get("XAI_API_KEY")

# Logging
LOG_LEVEL = os.environ.get("AGENTIC_LOG_LEVEL", "INFO")
LOG_FILE = AGENTIC_DIR / "logs" / "agentic.log"
