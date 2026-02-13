# Multi-Agent Debate: Tuza ν=4 Proof Strategy
## Date: January 30, 2026

## UNANIMOUS CONSENSUS: Strategy A - K4 vs K4-free Split

### Participants
- **Grok-4** (xAI)
- **Codex** (OpenAI gpt-5.2-codex)
- **Gemini** (Google)

### The Question
What is the cleanest proof strategy for proving τ ≤ 8 when ν = 4?

### Context: K4 Counterexample Discovery
Aristotle NEGATED the lemma `not_all_three_types` with this counterexample:
- Graph has K4 on vertices {0,1,2,3} plus chain triangles {4,5,6}, {6,7,8}, {8,9,10}
- Packing M = {{0,1,2}, {4,5,6}, {6,7,8}, {8,9,10}}
- For triangle e = {0,1,2}, ALL THREE edge-types have externals sharing vertex 3

### Options Considered
- **A)** Case split: K4-containing vs K4-free graphs
- **B)** Unified approach: Single cover construction for both
- **C)** Classification: Enumerate all 4-packing configurations
- **D)** Different approach entirely

---

## Grok-4's Recommendation: Strategy A

### Key Arguments:
1. **Natural split point**: K4 counterexample shows this is where the lemma fails
2. **K4-free reuses existing work**: 5-packing argument works without shared apex
3. **K4 case is tractable**: Just 2 edges from apex cover all externals
4. **Handles general case**: Focus on graph property, not infinite enumeration

### Implementation:
```lean
theorem tuza_nu_4 (G : SimpleGraph V) (h : trianglePackingNumber G = 4) :
    triangleTransversalNumber G ≤ 8 := by
  by_cases hK4 : ∃ (s : Finset V) (hcard : s.card = 4), IsClique (G.induced_subgraph s)
  · sorry -- K4 case
  · sorry -- K4-free case
```

---

## Codex's Recommendation: Strategy A

### Key Arguments:
1. **Lowest-complexity formalization**: Split fits 2-minute/5-line rules
2. **Aristotle-friendly**: K4-free branch validates lemmas on `Fin 6-7`
3. **Avoids over-enumeration**: C is brittle, B is broken by counterexample

### Implementation Focus:
- K4 branch: 4 edges incident to one vertex (apex spokes)
- K4-free branch: Strengthen T_pair ≤ 6, enforce stricter intersection patterns

---

## Gemini's Recommendation: Strategy A ("Dense vs Sparse")

### Key Arguments:
1. **Structural hint**: K4 is exactly where sparse logic fails
2. **Perfect ratio in K4**: ν(K4)=1, τ(K4)=2
3. **Literature support**: Haxell's proof distinguishes "thick" vs "thin" structures

### Implementation:
- **Dense (K4)**: Cover K4 with 2 edges, reduce to ν ≤ 3
- **Sparse (K4-free)**: `not_all_three_types` should hold

---

## Why Other Strategies Were Rejected

| Strategy | Reason |
|----------|--------|
| **B (Unified)** | K4 counterexample shows unified "type" argument is brittle |
| **C (Classification)** | Combinatorial explosion; not clean for general `SimpleGraph V` |
| **D (Other)** | No concrete alternative that beats A |

---

## Immediate Next Steps (All Agree)

1. **Submit K4-free `not_all_three_types` to Aristotle** ✅ DONE
   - Aristotle UUID: `bb7c957f-9534-4002-a9a4-c5ff4e7aba9e`
   - Prediction: No counterexample (lemma should hold when K4-free)

2. **If K4-free version holds**: Formalize the split theorem
   - Create top lemma with `by_cases` on K4 existence
   - K4 branch: explicit 2-edge cover construction
   - K4-free branch: 5-packing contradiction

3. **If K4-free version fails**: Analyze counterexample for next refinement

---

## Token Usage
- Grok-4: 10,228 tokens (7,334 reasoning)
- Codex: 8,854 tokens
- Gemini: ~5,000 tokens (estimated)
