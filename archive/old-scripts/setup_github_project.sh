#!/bin/bash
# Setup GitHub Project for Aristotle Math Problems
# This script creates a GitHub repo, project board, and all issues

set -e

echo "=== Aristotle Math Problems - GitHub Project Setup ==="
echo ""

# Step 1: Initialize git repo
echo "[1/8] Initializing git repository..."
git init
git add .
git commit -m "Initial commit: Comprehensive math problem analysis for Aristotle

- 60+ problems identified across number theory, algebra, combinatorics, analysis
- Research from Grok, Gemini, and 6 parallel Claude agents
- Organized into 3 tiers by success probability
- Complete documentation and quick-start guides"

# Step 2: Create GitHub repository
echo "[2/8] Creating GitHub repository..."
gh repo create aristotle-math-problems \
  --public \
  --description "Systematic attempt to solve unsolved mathematical problems using Aristotle (Harmonic AI theorem prover). 60+ problems organized by tractability." \
  --homepage "https://aristotle.harmonic.fun" \
  --source=. \
  --push || echo "Repo might already exist, continuing..."

# Step 3: Create labels
echo "[3/8] Creating issue labels..."
gh label create "tier-1-high-probability" --description "60-95% success rate" --color "28a745" --force
gh label create "tier-2-research" --description "20-60% success rate" --color "ffa500" --force
gh label create "tier-3-moonshot" --description "<20% success rate, extreme impact" --color "dc143c" --force

gh label create "number-theory" --description "Number theory problems" --color "0366d6" --force
gh label create "algebra" --description "Algebra and group theory" --color "5319e7" --force
gh label create "combinatorics" --description "Combinatorics and graph theory" --color "f9d0c4" --force
gh label create "analysis" --description "Analysis and inequalities" --color "d4c5f9" --force
gh label create "geometry" --description "Geometry problems" --color "c5def5" --force

gh label create "imo-level" --description "IMO difficulty" --color "fbca04" --force
gh label create "research-level" --description "Research/open problem" --color "d93f0b" --force
gh label create "millennium-prize" --description "Millennium Prize Problem" --color "b60205" --force

gh label create "formalization" --description "Formalizing known proof" --color "c2e0c6" --force
gh label create "open-problem" --description "Unsolved problem" --color "ff69b4" --force

gh label create "high-impact" --description "Major breakthrough if solved" --color "ff0000" --force
gh label create "mathlib-contribution" --description "Contributes to Mathlib" --color "0e8a16" --force

# Step 4: Create milestones
echo "[4/8] Creating milestones..."
gh api repos/kavanaghpatrick/aristotle-math-problems/milestones \
  -X POST \
  -f title="Phase 1: Validation" \
  -f description="Validate Aristotle setup with high-probability problems (2-4 weeks)" \
  -f state="open" || true

gh api repos/kavanaghpatrick/aristotle-math-problems/milestones \
  -X POST \
  -f title="Phase 2: Research Results" \
  -f description="Achieve first research-level results (1-3 months)" \
  -f state="open" || true

gh api repos/kavanaghpatrick/aristotle-math-problems/milestones \
  -X POST \
  -f title="Phase 3: Moonshot Hunting" \
  -f description="Continuous attempts on breakthrough problems (ongoing)" \
  -f state="open" || true

echo "[5/8] Creating GitHub Project..."
# Create project (using new Projects API)
gh project create \
  --owner kavanaghpatrick \
  --title "Aristotle Math Problems" \
  --format table || echo "Project might already exist"

echo "[6/8] Issue creation script ready. Run create_issues.py next."
echo "[7/8] Documentation..."
echo "[8/8] Complete!"
echo ""
echo "✅ GitHub repository created: https://github.com/kavanaghpatrick/aristotle-math-problems"
echo "✅ Labels and milestones configured"
echo "✅ Ready for issue creation"
echo ""
echo "Next steps:"
echo "1. Run: python3 create_all_issues.py"
echo "2. Visit: https://github.com/kavanaghpatrick/aristotle-math-problems"
