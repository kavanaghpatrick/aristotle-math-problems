# Grok Temperature Experiment v2: Finding Optimal Setting

## Experiment Design

### Hypothesis
Different temperatures serve different purposes:
- Low (0-0.3): Reliable, structured, directly usable
- Medium (0.5): Balance of creativity and coherence
- High (0.7-1.0): Maximum creativity, may find non-obvious gaps

### Variables
- **Independent**: Temperature (0, 0.3, 0.5, 0.7, 1.0)
- **Dependent**: Response quality metrics (see below)
- **Control**: Same prompt, same model (grok-4), same max_tokens

### Metrics (1-5 scale)
1. **Actionability**: Can this directly inform a Lean proof? (1=vague, 5=copy-paste ready)
2. **Novelty**: Does it suggest approaches not in our existing work? (1=rehash, 5=completely new)
3. **Correctness**: Is the mathematical reasoning sound? (1=errors, 5=rigorous)
4. **Gap Detection**: Does it identify potential issues in our approach? (1=none, 5=critical find)
5. **Coherence**: Is the response well-organized and complete? (1=rambling, 5=structured)

### Test Prompt
Use a DIFFERENT blocker to avoid any caching/memorization:
- Blocker 1: tau_union_le_4 (already tested)
- **NEW**: Focus on the overlap lemma specifically

### Trials
- 2 trials per temperature = 10 total API calls
- Score each independently, average per temp

## Results

(To be filled in)
