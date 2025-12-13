# 🚀 HQC Formal Verification Research Roadmap
## From Trivial to Transformative

**Date:** 2025-12-11
**Goal:** Define what REAL formal verification of NIST HQC-128 would look like

---

## Current State: TRIVIAL

**What We Did:**
- ✅ Verified n=17669 is prime (arithmetic)
- ✅ Checked C(17669,66) > 2^100 (computation)
- ✅ Used `native_decide` to compute bounds

**Why It's Trivial:**
- Computable in 16 microseconds with Python
- No cryptographic insight
- Doesn't establish 128-bit security (only 2^90/2^100)
- Equivalent to running a calculator

---

## Level 1: ROUTINE → Tighten the Bounds

### Goal: Prove Actual Security Level

**Task:** Prove HQC-128 achieves 2^128 security (not just 2^100)

**What to Formalize:**
```lean
-- Current (WEAK)
theorem hqc_prange_complexity_strong_bound :
  prange_complexity n_HQC k_HQC t_HQC > 2^100

-- Target (STRONG)
theorem hqc_prange_complexity_exact :
  prange_complexity n_HQC k_HQC t_HQC > 2^128

theorem hqc_doom_complexity_exact :
  doom_complexity n_HQC k_HQC t_HQC > 2^121  -- sqrt(n) ≈ 2^7
```

**Challenges:**
- Still just computation, but at least matches security claim
- Need to prove C(17669,66)/C(3776,66) ≈ 2^147 (not just > 2^100)
- Requires better approximation techniques in Lean

**Impact:** 4/10 - More accurate, but still arithmetic

---

## Level 2: SOLID → Prove the Formula

### Goal: Formally Derive ISD Complexity

**Task:** Don't just compute - PROVE why Prange has that complexity

**What to Formalize:**
```lean
-- Define Information Set Decoding algorithm
def ISD_algorithm (H : Matrix (Fin (n-k)) (Fin n) F₂)
                   (s : Vector F₂ (n-k))
                   (t : ℕ) : Algorithm := ...

-- Prove lower bound on ANY ISD algorithm
theorem ISD_lower_bound (H : random_matrix) (t : ℕ) :
  ∀ (A : ISD_algorithm),
    expected_complexity A ≥ C(n,t) / C(n-k,t)

-- Prove Prange achieves this bound
theorem prange_optimal :
  prange_complexity = ISD_lower_bound
```

**Challenges:**
- Need to formalize algorithm execution models
- Prove expected running time (probabilistic analysis)
- Show Prange is optimal among linear-algebra ISD methods

**References:**
- Stern's paper (1988) on ISD algorithms
- Becker, Joux, May, Meurer (BJMM) improvements
- Probabilistic analysis in Lean 4

**Impact:** 6/10 - Real theorem proving, publishable at formal methods venue

---

## Level 3: SIGNIFICANT → Security Reduction

### Goal: Prove HQC Security Reduces to Hard Problem

**Task:** Formalize the security proof from HQC papers

**What to Formalize:**
```lean
-- Define Decisional QC-SDP problem
def QCSD_problem (n k t : ℕ) : DecisionalProblem :=
  { instance := (H : QC_matrix, s : syndrome),
    yes := ∃ e : weight_t_vector, H * e = s,
    no  := s is random }

-- Define IND-CPA security game for HQC
def HQC_IND_CPA_game : SecurityGame := ...

-- THE KEY THEOREM
theorem hqc_security_reduction :
  ∀ (A : adversary HQC_IND_CPA_game),
    advantage A ≤ advantage (reduction A) QCSD_problem + negl(λ)
```

**This is Game-Based Cryptography:**
1. Define sequence of games
2. Show adjacent games are indistinguishable
3. Final game is deciding QCSD
4. Therefore breaking HQC → solving QCSD

**Tools Needed:**
- Probability theory in Lean 4
- Computational indistinguishability
- Reduction framework (like EasyCrypt)

**Existing Work to Study:**
- EasyCrypt proofs for ML-KEM (Kyber)
- CertiCrypt framework in Coq
- Verypto (Isabelle/HOL) for game-based proofs

**Impact:** 8/10 - Publishable at CRYPTO/EUROCRYPT, major advance

---

## Level 4: BREAKTHROUGH → Verified Implementation

### Goal: Machine-Checked Correctness of HQC C Code

**Task:** Prove HQC implementation is correct AND secure

**What to Formalize:**
```lean
-- Reference implementation (pure functional)
def HQC_keygen_spec : KeygenSpec := ...
def HQC_encrypt_spec : EncryptSpec := ...
def HQC_decrypt_spec : DecryptSpec := ...

-- C implementation (via extraction or verification)
def HQC_keygen_impl : C_function := ...
def HQC_encrypt_impl : C_function := ...
def HQC_decrypt_impl : C_function := ...

-- Functional correctness
theorem HQC_impl_correct :
  ∀ input, HQC_keygen_impl input = HQC_keygen_spec input

-- Constant-time execution (side-channel resistance)
theorem HQC_impl_constant_time :
  ∀ input₁ input₂,
    execution_time (HQC_encrypt_impl input₁) =
    execution_time (HQC_encrypt_impl input₂)

-- Security properties
theorem HQC_impl_secure :
  ∀ (A : adversary),
    advantage A HQC_impl ≤ advantage A HQC_spec + ε
```

**Challenges:**
- Verify actual C code (not just specification)
- Model timing behavior (constant-time guarantees)
- Prove no side-channel leakage
- Memory safety

**Tools:**
- VST (Verified Software Toolchain) - Coq
- Jasmin - verified compiler for crypto
- Why3/Frama-C - C verification
- Could use Lean 4 with C extraction

**Examples:**
- Verified ML-KEM implementation in Jasmin
- Verified ChaCha20 in Frama-C
- Verified curve25519 in Coq

**Impact:** 10/10 - BREAKTHROUGH, publishable at CRYPTO + Oakland (IEEE S&P)

---

## Level 5: ULTIMATE → New Attack Analysis

### Goal: Discover and Formally Verify New Bounds

**Task:** Use ATP to discover tighter attack bounds

**Potential Discoveries:**
```lean
-- Improved DOOM attack analysis
theorem doom_attack_improved :
  doom_complexity_with_quantum n_HQC k_HQC t_HQC > 2^135
  -- Better than classical 2^140 due to quantum speedup

-- Memory-time tradeoff analysis
theorem memory_time_tradeoff :
  ∀ (M : memory_bound),
    time_complexity M ≥ f(n, k, t, M)

-- Structural attack lower bounds
theorem structural_attack_bound :
  quasi_cyclic_structure_gives_no_advantage_beyond sqrt(n)
```

**Novel Research:**
- Formally analyze quantum ISD algorithms
- Prove memory-time tradeoffs for specific attacks
- Show quasi-cyclic structure doesn't help beyond DOOM

**Impact:** 10/10 - Research breakthrough, new crypto results

---

## Comparison: What Would Be Impressive?

| Approach | Difficulty | Impact | Publishable? | Novel Crypto? |
|----------|------------|--------|--------------|---------------|
| **Current work** (arithmetic) | 1/10 | 3/10 | ❌ CRYPTO | ❌ |
| Tighter bounds (2^128) | 2/10 | 4/10 | ⚠️ Workshop | ❌ |
| Prove formula correctness | 5/10 | 6/10 | ✅ ITP/CAV | ❌ |
| Security reduction | 8/10 | 8/10 | ✅ CRYPTO | ⚠️ (if first) |
| Verified implementation | 9/10 | 10/10 | ✅ CRYPTO + S&P | ❌ |
| New attack bounds | 10/10 | 10/10 | ✅ CRYPTO (main) | ✅ |

---

## Realistic Roadmap for Aristotle

### Phase 1: Infrastructure (2-4 weeks)
1. **Formalize ISD algorithms** in Lean 4
2. **Build probability theory** for expected complexity
3. **Create reduction framework** (mini-EasyCrypt in Lean)

### Phase 2: Security Proof (1-2 months)
1. **Formalize QCSD problem**
2. **Define HQC IND-CPA game**
3. **Prove reduction theorem**
   - Game sequence: G0 → G1 → ... → QCSD
   - Show each game hop is sound
   - Aristotle could help with intermediate lemmas

### Phase 3: Implementation (2-3 months)
1. **Extract HQC reference implementation** to Lean
2. **Verify functional correctness**
3. **Prove constant-time properties**
4. **Submit to CRYPTO 2026**

---

## What Aristotle Could Realistically Do

### Good Fits for ATP:
✅ **Intermediate lemmas** in reduction proof
✅ **Combinatorial identities** in complexity analysis
✅ **Algebraic manipulations** in game transformations
✅ **Probability bound simplifications**

### Poor Fits for ATP:
❌ **High-level proof strategy** (needs human insight)
❌ **Game sequence design** (creative step)
❌ **Novel attack discovery** (requires domain expertise)

### Hybrid Approach:
1. **Human designs** reduction structure
2. **Aristotle proves** intermediate steps
3. **Human verifies** proof makes sense
4. **Iterate** until complete

---

## Comparison to Existing Crypto Verification

### ML-KEM (Kyber) - State of the Art
**What's been verified:**
- ✅ Security reduction (game-based proof in EasyCrypt)
- ✅ Implementation correctness (Jasmin verified compiler)
- ✅ Constant-time guarantees
- ✅ Side-channel resistance

**Publications:**
- "Computer-Aided Proofs for Multiparty Computation with Active Security" (CRYPTO)
- "Jasmin: High-Assurance and High-Speed Cryptography" (CCS)

### HQC - Current State
**What's been verified:**
- ✅ Arithmetic parameter checks (US, in Lean 4) ← TRIVIAL
- ❌ Security reduction - NOT DONE
- ❌ Implementation verification - NOT DONE
- ❌ Side-channel analysis - NOT DONE

**Opportunity:** HQC is less studied than Kyber → room for impact!

---

## Recommended Next Steps

### Option A: Go Deep on Security Reduction (HIGH IMPACT)
**Goal:** First formal proof of HQC IND-CPA security
**Timeline:** 2-3 months
**Publishable:** CRYPTO 2026 or EUROCRYPT 2026
**Novelty:** First game-based proof for code-based PQC in Lean 4

### Option B: Verified Implementation (VERY HIGH IMPACT)
**Goal:** Fully verified HQC implementation
**Timeline:** 3-4 months
**Publishable:** CRYPTO + Oakland (dual submission)
**Novelty:** First verified code-based PQC implementation

### Option C: Novel Attack Analysis (BREAKTHROUGH)
**Goal:** Use Aristotle to discover tighter bounds
**Timeline:** Uncertain (research)
**Publishable:** CRYPTO (main conference) if successful
**Novelty:** New crypto result

### Option D: Study Other Problems (PRAGMATIC)
**Goal:** Find problems where Aristotle shines
**Timeline:** Ongoing
**Publishable:** Depends on results
**Novelty:** Could be high if we find the right problem

---

## Concrete First Step: Security Reduction

### Minimal Viable Proof (1-2 weeks)

1. **Formalize QCSD in Lean 4**
```lean
structure QCSD_instance (n k t : ℕ) where
  H : QuasiCyclicMatrix (n-k) n
  s : Vector F₂ (n-k)

def QCSD_decision : QCSD_instance → Bool := ...
```

2. **Define IND-CPA game**
```lean
structure IND_CPA_game (KEM : KEMScheme) where
  challenger : Party
  adversary : Party

def IND_CPA_advantage (A : Adversary) : ℝ := ...
```

3. **Sketch reduction**
```lean
theorem hqc_security_sketch :
  ∃ (reduction : Adversary HQC → Adversary QCSD),
    ∀ A, advantage A ≤ advantage (reduction A) + negl(λ)
:= by sorry  -- Fill in with Aristotle's help
```

**Success Criteria:**
- Compiles in Lean 4
- Structure is sound
- Can be filled in incrementally

---

## Resources Needed

### Papers to Read:
1. HQC submission to NIST (2020) - original security proof
2. "Game-Based Cryptography" textbook
3. EasyCrypt tutorial papers
4. "High-Assurance Cryptography" (Barthe et al.)

### Tools to Learn:
1. Lean 4 probability theory
2. Mathlib tactics for real analysis
3. Game-based proof patterns

### Collaborators:
- HQC designers (Gaborit, Melchor)
- EasyCrypt community
- Lean 4 crypto developers

---

## Conclusion

**Current work:** Arithmetic verification (TRIVIAL)

**Real formal verification would require:**
1. Security reduction (game-based proof)
2. Implementation verification (C code)
3. Novel attack analysis (research)

**Most realistic next step:** Security reduction
- Clear target
- Achievable in 2-3 months
- Publishable at top venues
- Actually advances state of formal crypto

**Aristotle's role:** Prove intermediate lemmas, not design proof strategy

**Expected impact:** 8/10 if we complete security reduction properly

---

**Bottom line:** We need to move from **checking arithmetic** to **proving security properties**. That means game-based cryptography, not just binomial coefficients.
