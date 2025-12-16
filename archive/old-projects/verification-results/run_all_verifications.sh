#!/bin/bash
# ULTRA-AGGRESSIVE PARALLEL VERIFICATION LAUNCHER
# Runs Grok, Gemini, and Codex verifications for all 20 problems

set -e

cd /Users/patrickkavanagh/math/verification-results

echo "================================================================================"
echo "🔥 ULTRA-AGGRESSIVE VERIFICATION CAMPAIGN - ALL 3 AI SYSTEMS"
echo "================================================================================"
echo ""
echo "Target: 20 problems × 3 AI systems = 60 total verifications"
echo "Strategy: Maximum parallelization for speed"
echo ""

# Track start time
START_TIME=$(date +%s)

# PHASE 1: GROK VERIFICATION (API-based, fast)
echo "[1/3] 🚀 LAUNCHING GROK VERIFICATIONS..."
echo "----------------------------------------"
GROK_COUNT=0
for i in grok_request_{1..20}.json; do
  if [ -f "$i" ]; then
    num=$(echo $i | grep -o '[0-9]*')
    echo "  → Grok #$num: Queued"
    curl -s -X POST https://api.x.ai/v1/chat/completions \
      -H "Authorization: Bearer $GROK_API_KEY" \
      -H "Content-Type: application/json" \
      -d @$i > grok_response_${num}.json 2>&1 &
    ((GROK_COUNT++))
    sleep 0.3  # Prevent rate limiting
  fi
done
echo "  ✅ Launched $GROK_COUNT Grok verifications"
echo ""

# PHASE 2: GEMINI VERIFICATION (CLI-based, thorough)
echo "[2/3] 🧠 LAUNCHING GEMINI VERIFICATIONS..."
echo "----------------------------------------"
GEMINI_COUNT=0
for i in {1..20}; do
  if [ -f "gemini_prompt_${i}.txt" ]; then
    echo "  → Gemini #$i: Queued"
    (gemini -p "$(cat gemini_prompt_${i}.txt)" > gemini_response_${i}.txt 2>&1) &
    ((GEMINI_COUNT++))
    sleep 0.3  # Stagger launches
  fi
done
echo "  ✅ Launched $GEMINI_COUNT Gemini verifications"
echo ""

# PHASE 3: CODEX VERIFICATION (Autonomous agents)
echo "[3/3] 🤖 LAUNCHING CODEX AUTONOMOUS AGENTS..."
echo "----------------------------------------"
echo "  → Codex: Launching autonomous verification agents"
echo "  → NOTE: Codex agents run autonomously and may take hours"
echo ""

# Launch top 5 critical problems via Codex
CODEX_PROBLEMS=(1 3 9 15 16)  # Goldbach, McKay, Anderson-Badawi, R(5,5), ζ(5)
CODEX_COUNT=0

for prob_num in "${CODEX_PROBLEMS[@]}"; do
  if [ -f "gemini_prompt_${prob_num}.txt" ]; then
    echo "  → Codex #$prob_num: Launching autonomous agent"
    prompt=$(cat "gemini_prompt_${prob_num}.txt")

    # Launch Codex in background
    (cd /Users/patrickkavanagh/math && \
     codex exec --skip-git-repo-check "CRITICAL VERIFICATION: $prompt. Output to verification-results/codex_result_${prob_num}.md" > "verification-results/codex_log_${prob_num}.txt" 2>&1) &

    ((CODEX_COUNT++))
    sleep 1
  fi
done
echo "  ✅ Launched $CODEX_COUNT Codex autonomous agents"
echo ""

# Wait for Grok and Gemini (Codex runs in background)
echo "⏳ WAITING FOR GROK & GEMINI TO COMPLETE..."
echo "(Codex agents running autonomously in background)"
echo ""
wait

# Calculate elapsed time
END_TIME=$(date +%s)
ELAPSED=$((END_TIME - START_TIME))

echo ""
echo "================================================================================"
echo "✅ VERIFICATION CAMPAIGN COMPLETE!"
echo "================================================================================"
echo ""
echo "Summary:"
echo "  • Grok verifications: $GROK_COUNT launched"
echo "  • Gemini verifications: $GEMINI_COUNT launched"
echo "  • Codex agents: $CODEX_COUNT running autonomously"
echo "  • Total verifications: $((GROK_COUNT + GEMINI_COUNT + CODEX_COUNT))"
echo "  • Elapsed time: ${ELAPSED}s"
echo ""
echo "Next steps:"
echo "  1. Check grok_response_*.json for Grok results"
echo "  2. Check gemini_response_*.txt for Gemini results"
echo "  3. Check codex_result_*.md for Codex results (may take hours)"
echo "  4. Run: python3 ../analyze_verification_results.py"
echo ""
echo "Results directory: $(pwd)"
echo ""
