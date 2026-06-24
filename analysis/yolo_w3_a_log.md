# YOLO-W3-A Log (angle D: Bombieri-Lang + Faltings-Vojta)

## Mission
Wave 3, angle D for σ₀ multiperfect family {11,13,17,19}.
Distinct from W1 Mihăilescu (slot 1293), W2 Chabauty NEGATIVE (slot 1297), W2 ESS Subspace (slot 1299).

## Paths
- Sketch: `submissions/sketches/yolo_w3_sigma0_bombieri_lang.txt` (22 lines)
- Fusion: `submissions/sketches/yolo_w3_sigma0_bombieri_lang.fusion.json` (27 lines, 10 candidate_lemmas, fit_score=0.42)
- LLM transcripts: `/tmp/yolo_w3_a/codex_result.md`, `/tmp/yolo_w3_a/grok_result.md`, `/tmp/yolo_w3_a/gemini_result.md` (quota exhausted)
- Retry loop: `/tmp/yolo_w3_a/retry.log` running with hash c75e288880fd9865

## Analog Paragraph
Where Faltings 1991 (Annals 133) used height inequalities on abelian varieties to prove Mordell (genus ≥ 2 curves have finitely many rational points) and Vojta 1987 (Lecture Notes 1239) generalized this to higher-dimensional subvarieties of general type via h(P) ≪ ε·deg(P) + C(V,ε), we transplant the abelian-variety / general-type framing to the cyclotomic Jacobian J(C_q) of the superelliptic curve C_q : y^(q-1) = Φ_q(x), of genus g(C_q) = (q-3)(q-4)/2 (i.e. 28, 45, 91, 120 for q ∈ {11,13,17,19}). Bombieri-Lang gives finiteness of integral (p,k) per q, but the height bound H_q is NON-UNIFORM in q (grows with canonical class K_{C_q}). The load-bearing closure is the elementary residue σ(p^(q-1))/p^(q-1) = (p^q - 1)/((p-1)p^(q-1)) < p/(p-1) ≤ 3/2 < 2, forcing integer k = 1 against k ≥ 2.

## Honest Findings (Codex correction)
Codex (gpt-5.5 xhigh) flagged that the affine graph y = Φ_q(x) is genus 0 (rational, since the ring Q[x,y]/(y - Φ_q(x)) ≅ Q[x]). The positive-genus model is the superelliptic y^(q-1) = Φ_q(x) (same as W2 Chabauty). The bridge_lemma in the fusion JSON references the genus values from the W2 superelliptic model; this is captured in the fit_score=0.42 and honest_disclaimer. Codex also corrected the arXiv citation: Stoll 'Chabauty without Mordell-Weil' is arXiv:1506.04286 (W2 mistakenly cited 1506.06463 which is Chen on Anderson-Thakur).

## LLM Consensus
1. **Grok (web+x search)**: No effective Bombieri-Lang bound in literature; the elementary k < 2 closure is load-bearing; Faltings/Vojta/Bombieri-Lang absent from Mathlib.
2. **Codex (high reasoning + Mathlib search)**: y = Φ_q(x) is genus 0, irrelevant for Bombieri-Lang; the elementary mod-p contradiction (Φ_q(p) ≡ 1 mod p but p | k·p^(q-1)) is identical to W1 Mihăilescu; closure step requires no abelian-variety machinery.
3. **Gemini**: Quota exhausted, no consultation.

## Distinction from Prior Waves
- **W1 Mihăilescu** (slot 1293): Primary-cyclotomic-unit residue Φ_q(p) ≡ 1 mod p forces p | 1 contradiction. Compiled q=11 case (slot 746/1258).
- **W2 ESS Subspace** (slot 1299): Evertse-Schlickewei-Schmidt rank-uniform Subspace Theorem framework + elementary k < 2. fit_score=0.78.
- **W2 Chabauty** (slot 1297): NEGATIVE feasibility witness — rank ≥ q-1, genus 28-120, Coleman fails. fit_score=0.18.
- **W3 Bombieri-Lang** (this): Abelian-variety / general-type framing via Faltings-Vojta. NOT uniform in q. fit_score=0.42.

## Status
Submission in-flight via /tmp/yolo_w3_a/retry_submit.sh; queue saturated on first attempt, retrying every 90s.
