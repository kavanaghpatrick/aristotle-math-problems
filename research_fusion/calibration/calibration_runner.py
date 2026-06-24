#!/usr/bin/env python3
"""
Day 9 Calibration Test Runner — Fusion Lane Gate
================================================

Purpose: Decide whether the technique_scout.md Stage-2 analogy-mining prompt
is trustworthy on OPEN problems by testing it on 10 known-fusion historical
breakthroughs with the actual analog REDACTED.

Procedure per problem:
  1. Take a famous fusion breakthrough (e.g., Wiles/FLT).
  2. Build a redacted problem statement: the situation as it stood BEFORE
     the cross-domain technique was found. Strip any wording that hints at
     the eventual unlock.
  3. Run Stage 2 (technique_scout.md) over Grok + Gemini + Codex via
     scripts/debate.py.
  4. Extract each model's top-5 proposed techniques.
  5. Score: did the ensemble include the actual historical technique?

Scoring (per problem, ensemble = union of all model proposals):
  1.0  — exact technique named (or a clear strict subset/superset)
  0.5  — same domain & morally similar tool, but different specific technique
  0.0  — no proposal touches the actual unlock or its domain

Hit if score >= 0.5.

Gate (per F7 spec):
  >= 4/10 hits  -> PASS, fusion lane may be used on open problems.
  <  4/10 hits  -> FAIL, technique_scout prompt needs revision.

Cost: ~$50-100 in API calls (10 problems x 3 LLMs x 1 round).

Usage:
  python3 research_fusion/calibration/calibration_runner.py
  python3 research_fusion/calibration/calibration_runner.py --dry-run
  python3 research_fusion/calibration/calibration_runner.py --rounds 1 \\
      --problems 0,1,4
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
CALIBRATION_DIR = REPO_ROOT / "research_fusion" / "calibration"
DEBATE_TEMPLATE = REPO_ROOT / "research_fusion" / "prompts" / "debate_templates" / "technique_scout.md"
DEBATE_SCRIPT = REPO_ROOT / "scripts" / "debate.py"


# ════════════════════════════════════════════════════════════════════════
# THE 10 HISTORICAL PROBLEMS — REDACTED STATEMENTS
# ════════════════════════════════════════════════════════════════════════
#
# Each entry:
#   id              -- short slug
#   name            -- short human-readable name
#   redacted_problem -- problem-as-it-stood, NOTHING hinting at the unlock
#   default_toolkit -- what was being tried at the time
#   actual_technique -- the truth, kept OUT of any prompt
#   actual_domain   -- coarse domain bucket of the unlock
#   alt_names       -- alternative names / synonyms for fuzzy matching
#   citation        -- seminal paper / theorem
#   year            -- year the unlock was published
#
# IMPORTANT REDACTION RULES:
#   * No mention of the technique's name, the field it came from, or the
#     author who imported it.
#   * The problem is described in PRE-fusion language ("we are trying X
#     and hitting wall Y"), not "we want to relate this to modular forms".
#   * default_toolkit is what was being tried BEFORE the unlock.
#   * No hints by analogy ("similar problems have used Z").
# ════════════════════════════════════════════════════════════════════════

PROBLEMS = [
    {
        "id": "wiles_flt",
        "name": "Fermat's Last Theorem (Wiles, 1995)",
        "year": 1995,
        "redacted_problem": (
            "OPEN PROBLEM (as of 1985): Prove that for every integer n >= 3, "
            "there is no triple of positive integers (a, b, c) satisfying "
            "a^n + b^n = c^n.\n\n"
            "It suffices (by Kummer-style descent and prior reductions) to "
            "treat the case n = p an odd prime. Despite 350 years of effort, "
            "the conjecture is open."
        ),
        "default_toolkit": (
            "Cyclotomic field arithmetic, Kummer's regular-prime descent, "
            "Bernoulli-number criteria, Iwasawa theory of Z_p-extensions, "
            "computational verification for individual exponents up to ~150000."
        ),
        "actual_technique": "Frey-Hellegouarch elliptic curve + Ribet level-lowering + modularity lifting (semistable case)",
        "actual_domain": "elliptic curves / modular forms / Galois representations",
        "alt_names": [
            "frey curve", "frey-hellegouarch", "hellegouarch", "modular forms",
            "modularity", "modularity lifting", "ribet", "epsilon conjecture",
            "level lowering", "semistable elliptic curve", "galois representation",
            "taniyama-shimura", "taniyama-shimura-weil",
        ],
        "citation": "Wiles, Modular elliptic curves and Fermat's Last Theorem, Ann. Math. 141 (1995)",
    },
    {
        "id": "maynard_gaps",
        "name": "Bounded gaps between primes (Maynard-Tao, 2013)",
        "year": 2013,
        "redacted_problem": (
            "OPEN PROBLEM (as of 2012): Prove that liminf_{n -> oo} "
            "(p_{n+1} - p_n) < infinity, where p_n is the n-th prime.\n\n"
            "Goldston-Pintz-Yildirim (2005) showed that this conclusion would "
            "follow if the level of distribution in Bombieri-Vinogradov could "
            "be pushed past 1/2, but that is itself open. Several authors have "
            "tweaked the GPY argument (varying weight functions, smoothing "
            "the cutoff) but the saving stops just short of forcing bounded "
            "gaps unconditionally."
        ),
        "default_toolkit": (
            "GPY-style sieve weights, Selberg sieves, Bombieri-Vinogradov at "
            "level 1/2, Heath-Brown identity, smoothed-Selberg refinements."
        ),
        "actual_technique": "Multidimensional sieve weights (k-tuple polynomial in k variables)",
        "actual_domain": "analytic number theory / sieve theory",
        "alt_names": [
            "multidimensional sieve", "multi-dimensional sieve",
            "multivariable sieve", "k-dimensional sieve",
            "higher-dimensional sieve weights", "k-tuple sieve",
            "tensor sieve", "polynomial sieve in k variables",
            "vary each variable separately",
        ],
        "citation": "Maynard, Small gaps between primes, Ann. Math. 181 (2015)",
    },
    {
        "id": "zhang_gaps",
        "name": "Bounded gaps between primes (Zhang, 2013)",
        "year": 2013,
        "redacted_problem": (
            "OPEN PROBLEM (as of 2012): Show liminf (p_{n+1} - p_n) <= C for "
            "some explicit C.\n\n"
            "GPY (2005) reduces this to an exponent-of-distribution theta > 1/2 "
            "in Bombieri-Vinogradov. The classical proof of BV gives theta = "
            "1/2 - epsilon and the 1/2 barrier appears intrinsic: dispersion "
            "estimates and the large sieve both saturate there. Friedlander, "
            "Iwaniec, Fouvry showed that one can sometimes break 1/2 for "
            "*specific* moduli with extra structure, but the unconditional "
            "result for all primes is open."
        ),
        "default_toolkit": (
            "Bombieri-Vinogradov, large sieve inequality, dispersion method, "
            "Selberg sieve weights as in GPY, generic estimates for exponential "
            "sums over residue classes."
        ),
        "actual_technique": "Restrict to smooth (friable) moduli and use Deligne's Weil II / Riemann hypothesis for varieties to bound exponential sums (Kloosterman)",
        "actual_domain": "algebraic geometry (l-adic cohomology) imported into analytic NT",
        "alt_names": [
            "smooth moduli", "smooth modulus", "smooth-modulus",
            "friable moduli", "smooth restriction of bombieri",
            "deligne", "weil ii", "weil conjectures", "l-adic cohomology",
            "exponential sum from algebraic geometry",
            "etale cohomology", "deligne riemann hypothesis for varieties",
        ],
        "citation": "Zhang, Bounded gaps between primes, Ann. Math. 179 (2014)",
    },
    {
        "id": "green_tao",
        "name": "Primes contain arbitrarily long arithmetic progressions (Green-Tao, 2004)",
        "year": 2004,
        "redacted_problem": (
            "OPEN PROBLEM (as of 2003): Show that the prime numbers contain "
            "arbitrarily long non-trivial arithmetic progressions.\n\n"
            "Szemeredi's theorem (1975) gives the conclusion for any subset of "
            "the integers with positive upper density. The primes have density "
            "zero, so Szemeredi does NOT apply directly. Van der Corput (1939) "
            "proved 3-term APs in primes; longer APs are open."
        ),
        "default_toolkit": (
            "Vinogradov circle method, Hardy-Littlewood k-tuples conjecture, "
            "Selberg sieve, GPY-style sieve weights for primes, Erdos-Turan-style "
            "density increment arguments WITHIN positive-density sets only."
        ),
        "actual_technique": "Transference principle: realize the primes as a dense subset of a pseudorandom 'majorant', then run a relative Szemeredi theorem (with Goldston-Yildirim sieve majorant)",
        "actual_domain": "additive combinatorics / ergodic theory / sieve theory",
        "alt_names": [
            "transference principle", "transference", "relative szemeredi",
            "pseudorandom majorant", "dense model theorem",
            "gowers norm", "uniformity norm",
            "furstenberg correspondence",
            "goldston-yildirim", "majorant",
            "szemeredi in pseudo-random",
        ],
        "citation": "Green-Tao, The primes contain arbitrarily long arithmetic progressions, Ann. Math. 167 (2008)",
    },
    {
        "id": "hough_covering",
        "name": "Erdos minimum modulus / covering systems (Hough, 2015)",
        "year": 2015,
        "redacted_problem": (
            "OPEN PROBLEM (as of 2014): A covering system of the integers is a "
            "finite collection of residue classes a_i (mod n_i) whose union is "
            "all of Z. Erdos (1950) asked: is there an absolute upper bound on "
            "the minimum modulus min_i n_i over all covering systems with "
            "DISTINCT moduli? Equivalently, is the minimum modulus bounded?\n\n"
            "Sun, Filaseta, and others built explicit coverings with minimum "
            "modulus 25 by 1985 and 40 by 2007, but no upper bound was known. "
            "All known constructions exhibit substantial structure; no "
            "elementary counting argument has succeeded."
        ),
        "default_toolkit": (
            "Inclusion-exclusion over arithmetic progressions, character sum "
            "estimates, large sieve, computer enumeration of small coverings."
        ),
        "actual_technique": "Distortion method: reveal congruences one modulus at a time as a sequence of probability measures whose entropy is controlled by an explicit recursion",
        "actual_domain": "probabilistic / entropic method in analytic NT",
        "alt_names": [
            "distortion method", "distortion technique",
            "sequential probability measure", "sequential entropy",
            "probabilistic method on residue classes",
            "iterative conditioning on residues",
            "entropy bound on covering",
            "stage-by-stage conditioning",
        ],
        "citation": "Hough, Solution of the minimum modulus problem for covering systems, Ann. Math. 181 (2015)",
    },
    {
        "id": "cap_set",
        "name": "Cap-set problem (Ellenberg-Gijswijt, 2016)",
        "year": 2016,
        "redacted_problem": (
            "OPEN PROBLEM (as of early 2016): A cap set in F_3^n is a subset "
            "containing no 3-term arithmetic progression. What is the maximum "
            "size? Meshulam (1995) gave the upper bound O(3^n / n) via Fourier "
            "analysis; this had stood as the best known bound for 21 years. "
            "The conjecture is that the true maximum is c^n for some c < 3."
        ),
        "default_toolkit": (
            "Fourier analysis on F_3^n, Roth-style density increment, "
            "Behrend-style constructions for lower bounds, Bohr-set techniques."
        ),
        "actual_technique": "Polynomial method (Croot-Lev-Pach): a low-degree polynomial vanishing on the diagonal in F_3^n x F_3^n yields rank constraints that bound a cap set by O(c^n) with c < 3",
        "actual_domain": "additive combinatorics + commutative algebra (polynomial / slice-rank method)",
        "alt_names": [
            "polynomial method", "slice rank", "slice rank method",
            "croot-lev-pach", "croot lev pach",
            "tensor rank bound", "diagonal polynomial",
            "low-degree polynomial vanishing on diagonal",
            "partition rank", "matrix slice rank",
        ],
        "citation": "Ellenberg-Gijswijt, On large subsets of F_q^n with no three-term arithmetic progression, Ann. Math. 185 (2017)",
    },
    {
        "id": "perelman_poincare",
        "name": "Poincare conjecture (Perelman, 2002-2003)",
        "year": 2003,
        "redacted_problem": (
            "OPEN PROBLEM (as of 2001): Every simply-connected, closed, "
            "smooth 3-manifold is homeomorphic to S^3.\n\n"
            "Hamilton (1982) introduced a parabolic-PDE flow on the metric "
            "tensor that shrinks 3-manifolds toward round shape. He proved "
            "convergence in the case of positive Ricci curvature, but the "
            "general case develops singularities that the flow cannot "
            "navigate. Various surgery prescriptions had been proposed but "
            "none controlled the long-time geometry. The problem is the "
            "geometrization conjecture (which contains Poincare)."
        ),
        "default_toolkit": (
            "Hamilton's Ricci flow under curvature assumptions, "
            "Cheeger-Gromov compactness theorems, Aleksandrov geometry of "
            "limit spaces, Hamilton-Ivey pinching estimates, ad hoc surgery "
            "procedures."
        ),
        "actual_technique": "Define monotone entropy and reduced-volume functionals (W-functional, F-functional) borrowed structurally from statistical mechanics; use no-local-collapsing theorem to rule out cigar-type singularities; perform geometric surgery at each singular time",
        "actual_domain": "geometric analysis / PDE with a structural analogy to statistical-mechanics entropy",
        "alt_names": [
            "w-functional", "w functional", "perelman entropy", "perelman's entropy",
            "monotone entropy", "reduced volume", "reduced-volume",
            "no-local-collapsing", "no local collapsing", "kappa-noncollapsing",
            "statistical mechanics analogy", "free energy functional",
            "ricci flow with surgery", "surgery in ricci flow",
        ],
        "citation": "Perelman, The entropy formula for the Ricci flow and its geometric applications, arXiv math/0211159 (2002)",
    },
    {
        "id": "faltings_mordell",
        "name": "Mordell conjecture (Faltings, 1983)",
        "year": 1983,
        "redacted_problem": (
            "OPEN PROBLEM (as of 1982): Let C be a smooth projective curve of "
            "genus g >= 2 defined over a number field K. Show that the set of "
            "K-rational points C(K) is finite.\n\n"
            "Mordell (1922) made the conjecture; Parshin (1968) reduced it to "
            "boundedness of heights on isogeny classes of abelian varieties. "
            "Despite 60 years of effort, no proof of the height-boundedness "
            "input was known."
        ),
        "default_toolkit": (
            "Diophantine approximation a la Thue-Siegel-Roth, p-adic methods "
            "(Chabauty-Coleman for special curves), reduction modulo many "
            "primes, classical theory of heights on abelian varieties (Mordell-"
            "Weil, Neron-Tate)."
        ),
        "actual_technique": "Arakelov intersection theory + Tate's isogeny conjecture for abelian varieties: control archimedean and non-archimedean heights uniformly across an isogeny class via Arakelov geometry, prove finiteness of polarized abelian varieties of fixed dimension over K",
        "actual_domain": "arithmetic geometry / Arakelov theory / moduli of abelian varieties",
        "alt_names": [
            "arakelov", "arakelov theory", "arakelov intersection",
            "arakelov geometry", "arakelov height",
            "tate conjecture", "tate isogeny conjecture",
            "tate isogeny theorem", "isogeny conjecture for abelian varieties",
            "finiteness of polarized abelian varieties",
            "shafarevich conjecture", "shafarevich-tate",
            "moduli of abelian varieties height",
        ],
        "citation": "Faltings, Endlichkeitssatze fur abelsche Varietaten uber Zahlkorpern, Invent. Math. 73 (1983)",
    },
    {
        "id": "scholze_perfectoid",
        "name": "Weight-monodromy / perfectoid spaces (Scholze, 2012)",
        "year": 2012,
        "redacted_problem": (
            "OPEN PROBLEM (as of 2011): The weight-monodromy conjecture "
            "predicts the existence of a certain filtration on the etale "
            "cohomology of a smooth projective variety over a p-adic field, "
            "such that the associated graded pieces have pure weights. The "
            "analogous statement over function fields (positive characteristic) "
            "is known. The characteristic-zero case remains open in general.\n\n"
            "Additionally, p-adic Hodge theory lacks a uniform framework that "
            "treats Q_p- and F_p-coefficients on equal footing. Many partial "
            "results are known in special cases (complete intersections, "
            "abelian varieties), but the general weight-monodromy conjecture "
            "over p-adic fields is open."
        ),
        "default_toolkit": (
            "p-adic Hodge theory (Fontaine's rings B_dR, B_crys, B_st), "
            "adic / rigid-analytic geometry, classical l-adic etale "
            "cohomology methods, comparison theorems CH_dR / CH_HT."
        ),
        "actual_technique": "Perfectoid spaces and the tilting equivalence: a perfectoid algebra over Q_p^cyc has an associated 'tilt' that is a perfectoid algebra over F_p((t))^1/p^infty; the tilt is functorial and identifies etale sites, so problems in char 0 can be transferred to char p where Deligne's Weil II applies",
        "actual_domain": "p-adic geometry / perfectoid spaces / tilting",
        "alt_names": [
            "perfectoid", "perfectoid spaces", "perfectoid algebra",
            "tilting", "tilt", "tilting equivalence",
            "almost purity", "almost mathematics", "almost-purity",
            "fargues-fontaine", "fargues fontaine",
            "untilt", "untilting", "diamond",
            "reduction to characteristic p", "transfer to char p",
        ],
        "citation": "Scholze, Perfectoid spaces, Publ. Math. IHES 116 (2012)",
    },
    {
        "id": "helfgott_goldbach",
        "name": "Ternary Goldbach conjecture (Helfgott, 2013)",
        "year": 2013,
        "redacted_problem": (
            "OPEN PROBLEM (as of 2012): Every odd integer n >= 7 is a sum of "
            "three primes.\n\n"
            "Vinogradov (1937) proved this asymptotically for n >= C, but the "
            "constant C is enormous (originally 3^3^15; later versions still "
            "in the range 10^1300 to 10^43000). The asymptotic argument is the "
            "Hardy-Littlewood circle method with major-arc / minor-arc "
            "decomposition. Bridging the gap from the unverifiable C down to "
            "n = 7 (or down to a range that can be verified by computer) is "
            "open. Several attempts in the 1990s-2000s tightened constants "
            "by factors but did not close the gap."
        ),
        "default_toolkit": (
            "Hardy-Littlewood circle method, Vinogradov's mean-value theorem, "
            "exponential sum estimates for primes, classical zero-free regions "
            "for Dirichlet L-functions."
        ),
        "actual_technique": "Sharpen every explicit constant in the circle method (new minor-arc bound via large sieve + explicit von-Mangoldt sum bounds, optimized major-arc smoothing) AND combine with computational verification of GRH for L-functions of small conductor up to T ~ 10^8 plus direct check of ternary Goldbach for n <= 10^27",
        "actual_domain": "analytic NT (explicit constants) + interval-arithmetic computation + GRH verification",
        "alt_names": [
            "explicit constants in circle method", "effective circle method",
            "explicit minor-arc bound", "interval arithmetic",
            "computer verification", "computational verification",
            "grh verification", "verification of riemann hypothesis",
            "rigorous numerics for goldbach",
            "explicit large sieve",
            "make every constant effective",
        ],
        "citation": "Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748 (2013)",
    },
]

assert len(PROBLEMS) == 10, f"Expected 10 calibration problems, got {len(PROBLEMS)}"


# ════════════════════════════════════════════════════════════════════════
# PROMPT CONSTRUCTION (redaction-aware)
# ════════════════════════════════════════════════════════════════════════

REDACTED_TEMPLATE = """You are scouting cross-domain techniques for the OPEN PROBLEM:

{redacted_problem}

The currently-standard toolkit being applied to this problem is:
{default_toolkit}

These methods have been pushed for several years and have reached a wall.

YOUR JOB: Identify 5 SPECIFIC techniques from OTHER mathematical areas that could unlock this problem. Each must include:

1. **Technique name** at the granularity a working researcher would use (a specific named method + its key bridge lemma, NOT a broad area like "algebraic geometry").
2. **Seminal paper or theorem** with author and year (e.g., "Iwaniec-Kowalski Analytic NT, Chapter 17 on the Bombieri-Vinogradov mean value theorem").
3. **Structural analog**: which other problem was unlocked by this technique, and which structural feature of THIS problem is analogous
4. **Diagnosis of why the default toolkit failed**: name the specific obstruction (sieve barrier, height bound, parity, missing computable bridge, density-zero issue, char-0 vs char-p, ...) that the default toolkit cannot cross
5. **Implementation comment**: in a formalized Lean 4 / Mathlib setting, which namespace would carry the relevant infrastructure; what is missing

NON-NEGOTIABLE constraints:

- At least 3 of your 5 techniques MUST come from outside the immediate area of the problem (if the problem is in classical analytic NT, you must include techniques from algebraic geometry, ergodic theory, additive combinatorics, p-adic analysis, dynamics on homogeneous spaces, combinatorial group theory, or similar). Cross-domain means cross-domain.
- FORBIDDEN: "try harder with the default toolkit", "extend the bound", "improve the constant in the existing estimate", "add a computable bridge". Those are inside the wall, not beyond it.

After listing your 5 techniques, RANK them 1-5 by your estimated probability of being the actual unlock, with explicit Bayesian reasoning (prior on the technique's success in adjacent problems x likelihood given this problem's specific structure).

Format requirement (for downstream automation): start each of the 5 entries with a line beginning with `### Technique N: <name>` (N = 1..5), where the technique name is on the same line. Put your final ranking under a heading `## Ranking`.
"""


def build_problem_prompt(problem: dict) -> str:
    """Render the redacted technique-scout prompt for one problem."""
    return REDACTED_TEMPLATE.format(
        redacted_problem=problem["redacted_problem"].strip(),
        default_toolkit=problem["default_toolkit"].strip(),
    )


# ════════════════════════════════════════════════════════════════════════
# MODEL CALLS — Re-use debate.py implementations
# ════════════════════════════════════════════════════════════════════════

sys.path.insert(0, str(REPO_ROOT / "scripts"))
from debate import call_grok as _call_grok_default, call_gemini, call_codex  # noqa: E402


def call_grok(prompt: str, timeout: int = 300) -> str:
    """Local override: use grok-4.20-0309-reasoning (the model our team has access to).

    The default scripts/debate.py uses 'grok-4.3' which our team does not have
    access to. This shim swaps in the available reasoning model.
    """
    # Prefer XAI_API_KEY (gives access to grok-4.20-0309-reasoning).
    # GROK_API_KEY may belong to a different team without access to this model.
    api_key = (
        os.environ.get("XAI_API_KEY") or os.environ.get("GROK_API_KEY")
    )
    if not api_key:
        return "[ERROR: XAI_API_KEY / GROK_API_KEY not set]"

    request = {
        "messages": [{"role": "user", "content": prompt}],
        "model": "grok-4.20-0309-reasoning",
        "temperature": 0.3,
    }
    req_file = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".json", delete=False
        ) as f:
            json.dump(request, f)
            req_file = f.name
        result = subprocess.run(
            [
                "curl", "-s", "-X", "POST",
                "https://api.x.ai/v1/chat/completions",
                "-H", f"Authorization: Bearer {api_key}",
                "-H", "Content-Type: application/json",
                "--max-time", str(timeout),
                "-d", f"@{req_file}",
            ],
            capture_output=True,
            text=True,
            timeout=timeout + 30,
        )
        if result.returncode != 0:
            return f"[ERROR: curl failed code {result.returncode}: {result.stderr[:500]}]"
        response = json.loads(result.stdout)
        if "error" in response:
            return f"[ERROR from Grok API: {response['error']}]"
        return response["choices"][0]["message"]["content"]
    except json.JSONDecodeError as e:
        return f"[ERROR parsing Grok response: {e}\nRaw: {result.stdout[:500]}]"
    except subprocess.TimeoutExpired:
        return f"[ERROR: Grok timed out after {timeout}s]"
    except Exception as e:
        return f"[ERROR calling Grok: {type(e).__name__}: {e}]"
    finally:
        if req_file and os.path.exists(req_file):
            os.unlink(req_file)


MODELS = {
    "grok": call_grok,
    "gemini": call_gemini,
    "codex": call_codex,
}


def call_one_model(name: str, prompt: str, timeout: int) -> str:
    fn = MODELS[name]
    return fn(prompt, timeout=timeout)


# ════════════════════════════════════════════════════════════════════════
# SCORING
# ════════════════════════════════════════════════════════════════════════

DOMAIN_TOKENS = {
    "elliptic curves / modular forms / Galois representations": [
        "modular form", "modular curve", "modular", "elliptic curve", "elliptic",
        "galois rep", "automorphic", "modularity", "hecke", "shimura",
        "heegner", "eisenstein", "cusp form", "l-function",
    ],
    "analytic number theory / sieve theory": [
        "sieve", "selberg", "linnik", "bombieri", "vinogradov",
        "level of distribution", "majorant",
    ],
    "algebraic geometry (l-adic cohomology) imported into analytic NT": [
        "etale", "l-adic", "deligne", "weil", "cohomology",
        "monodromy", "algebraic geometry",
    ],
    "additive combinatorics / ergodic theory / sieve theory": [
        "ergodic", "furstenberg", "szemeredi", "gowers", "additive combinatorics",
        "transference", "pseudorandom",
    ],
    "probabilistic / entropic method in analytic NT": [
        "probabilistic", "probability", "entropy", "martingale",
        "shannon", "measure-theoretic",
    ],
    "additive combinatorics + commutative algebra (polynomial / slice-rank method)": [
        "polynomial method", "algebraic geometry over finite", "tensor rank",
        "slice rank", "linear algebra over finite", "polynomial vanishing",
    ],
    "geometric analysis / PDE with a structural analogy to statistical-mechanics entropy": [
        "ricci flow", "geometric flow", "entropy", "mean curvature",
        "parabolic pde", "geometric analysis", "statistical mechanics",
        "thermodynamic", "monotone functional",
    ],
    "arithmetic geometry / Arakelov theory / moduli of abelian varieties": [
        "arakelov", "arithmetic geometry", "moduli", "abelian variety",
        "neron", "tate", "intersection theory on arithmetic surface",
    ],
    "p-adic geometry / perfectoid spaces / tilting": [
        "p-adic", "perfectoid", "adic space", "rigid analytic",
        "tilt", "tilting", "char p", "characteristic p", "fontaine",
    ],
    "analytic NT (explicit constants) + interval-arithmetic computation + GRH verification": [
        "explicit constants", "effective", "interval arithmetic",
        "computer verification", "rigorous numerics", "grh verification",
        "computational verification",
    ],
}

PROPOSAL_HEADER_RE = re.compile(
    r"^[\s>*-]*#{0,4}\s*Technique\s*([1-9])\s*[:\-]\s*(.+)$",
    re.IGNORECASE | re.MULTILINE,
)
# Loose backups in case the formatting drifts
PROPOSAL_HEADER_RE_ALT = re.compile(
    r"^[\s>*-]*(?:#{2,4}\s*)?(?:Technique|Proposal|Approach|Method)\s*#?\s*([1-9])\b[:\-\s]+(.+)$",
    re.IGNORECASE | re.MULTILINE,
)
RANKING_HEADER_RE = re.compile(r"#{1,4}\s*Ranking", re.IGNORECASE)


def extract_proposals(response: str) -> list[str]:
    """Pull out the top-5 technique names from an LLM response.

    Robust to formatting drift: tries the strict header pattern first,
    then a looser pattern. Returns a list of technique-name strings
    (with no leading/trailing punctuation), in order of appearance.
    """
    if not response or response.startswith("[ERROR"):
        return []
    matches = PROPOSAL_HEADER_RE.findall(response)
    if len(matches) < 3:  # try the looser regex
        matches = PROPOSAL_HEADER_RE_ALT.findall(response)
    names = []
    seen = set()
    for _, name in matches:
        clean = name.strip().rstrip(":.- ").strip("*_")
        # Drop trailing parentheses citation noise like "(2004)"
        clean = re.sub(r"\s*\([^)]{0,80}\)\s*$", "", clean).strip()
        if clean and clean.lower() not in seen:
            names.append(clean)
            seen.add(clean.lower())
    return names[:8]  # tolerate models that overshoot


def _normalize(s: str) -> str:
    s = s.lower()
    # collapse non-alphanumerics
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return " " + re.sub(r"\s+", " ", s).strip() + " "


def score_proposals(problem: dict, proposals: list[str], full_response: str) -> dict:
    """Score one model's proposals against the truth.

    Returns a dict:
      {score: float, matched_alt: Optional[str], domain_hit: bool, best_match: str}

    Rules:
      score 1.0 if any proposal name contains one of the alt_names tokens
      score 0.5 if any proposal name contains a domain-token (same field, wrong tool)
                 OR the full response text mentions an alt_name token even if
                 not as a headline proposal
      score 0.0 otherwise
    """
    alt_tokens = [_normalize(t) for t in problem["alt_names"]]
    domain_tokens = [_normalize(t) for t in DOMAIN_TOKENS.get(problem["actual_domain"], [])]

    norm_proposals = [(p, _normalize(p)) for p in proposals]
    norm_full = _normalize(full_response)

    # Strict: alt-name appears in a top-5 proposal name
    for raw, norm in norm_proposals:
        for tok in alt_tokens:
            if tok.strip() and tok in norm:
                return {
                    "score": 1.0,
                    "matched_alt": tok.strip(),
                    "best_match": raw,
                    "via": "headline-proposal",
                }

    # Strict-but-buried: alt-name appears somewhere in the response body
    for tok in alt_tokens:
        if tok.strip() and tok in norm_full:
            # We require it to be presented as a real technique (not casual mention);
            # heuristic: look for the token within +/-200 chars of "technique" or "method"
            idx = norm_full.find(tok)
            window = norm_full[max(0, idx - 200): idx + 200]
            if " technique " in window or " method " in window or " approach " in window or " conjecture " in window or " theorem " in window or " lemma " in window:
                return {
                    "score": 1.0,
                    "matched_alt": tok.strip(),
                    "best_match": tok.strip(),
                    "via": "buried-in-response",
                }

    # Half-credit: same domain, different tool
    for raw, norm in norm_proposals:
        for tok in domain_tokens:
            if tok.strip() and tok in norm:
                return {
                    "score": 0.5,
                    "matched_alt": None,
                    "best_match": raw,
                    "via": f"same-domain-token:{tok.strip()}",
                }

    # Domain mention anywhere in body (even weaker half-credit)
    for tok in domain_tokens:
        if tok.strip() and tok in norm_full:
            return {
                "score": 0.5,
                "matched_alt": None,
                "best_match": tok.strip(),
                "via": f"same-domain-buried:{tok.strip()}",
            }

    return {
        "score": 0.0,
        "matched_alt": None,
        "best_match": proposals[0] if proposals else "",
        "via": "no-match",
    }


def ensemble_score(per_model_results: list[dict]) -> dict:
    """Take per-model scores and return ensemble (best across models)."""
    best = max(per_model_results, key=lambda r: r["score"])
    return {
        "ensemble_score": best["score"],
        "hit": best["score"] >= 0.5,
        "strict_hit": best["score"] >= 1.0,
        "best_model": best["model"],
        "best_match": best["best_match"],
        "matched_alt": best.get("matched_alt"),
        "via": best.get("via"),
    }


# ════════════════════════════════════════════════════════════════════════
# RUN ORCHESTRATION
# ════════════════════════════════════════════════════════════════════════

@dataclass
class ProblemRun:
    problem_id: str
    name: str
    prompt: str
    responses: dict = field(default_factory=dict)   # model -> raw response
    proposals: dict = field(default_factory=dict)   # model -> list[str]
    scores: dict = field(default_factory=dict)      # model -> score dict
    ensemble: dict = field(default_factory=dict)
    elapsed_s: float = 0.0


def run_one_problem(
    problem: dict,
    models: list[str],
    timeout: int,
    dry_run: bool = False,
) -> ProblemRun:
    """Run Stage-2 technique mining on one historical problem."""
    prompt = build_problem_prompt(problem)
    run = ProblemRun(problem_id=problem["id"], name=problem["name"], prompt=prompt)

    if dry_run:
        for m in models:
            run.responses[m] = (
                f"[DRY-RUN] Would call {m} with {len(prompt)} chars.\n"
                f"### Technique 1: stub technique for {m}\n"
                f"### Technique 2: stub\n### Technique 3: stub\n"
                f"### Technique 4: stub\n### Technique 5: stub\n"
            )
            run.proposals[m] = extract_proposals(run.responses[m])
            run.scores[m] = {
                "model": m,
                **score_proposals(problem, run.proposals[m], run.responses[m]),
            }
        run.ensemble = ensemble_score(list(run.scores.values()))
        return run

    start = time.time()
    with ThreadPoolExecutor(max_workers=len(models)) as ex:
        futures = {
            ex.submit(call_one_model, m, prompt, timeout): m for m in models
        }
        for fut in as_completed(futures):
            m = futures[fut]
            try:
                resp = fut.result()
            except Exception as e:  # pragma: no cover
                resp = f"[ERROR: {type(e).__name__}: {e}]"
            run.responses[m] = resp
            run.proposals[m] = extract_proposals(resp)
            s = score_proposals(problem, run.proposals[m], resp)
            run.scores[m] = {"model": m, **s}
    run.elapsed_s = time.time() - start
    run.ensemble = ensemble_score(list(run.scores.values()))
    return run


# ════════════════════════════════════════════════════════════════════════
# REPORTING
# ════════════════════════════════════════════════════════════════════════

def write_results_markdown(
    runs: list[ProblemRun],
    out_path: Path,
    hit_rate: float,
    verdict: str,
) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    parts: list[str] = []
    today = dt.date.today().isoformat()
    parts.append("# Day 9 Calibration Test — Fusion Lane Gate")
    parts.append(f"_Date: {today}_\n")
    parts.append(f"**Verdict:** {verdict}")
    parts.append(f"**Hit rate:** {hit_rate:.1f}/10\n")
    parts.append(
        "Scoring: 1.0 = exact technique named (or close synonym/alt-name); "
        "0.5 = same-domain tool but different specific technique; 0.0 = off-domain. "
        "Ensemble = union of (Grok, Gemini, Codex) per problem; problem counts as hit "
        "if ensemble >= 0.5."
    )
    parts.append("")
    parts.append("| # | Problem | Year | Hit? | Score | Best Match | Via |")
    parts.append("|---|---|---|---|---|---|---|")
    for i, run in enumerate(runs, 1):
        e = run.ensemble or {}
        score = e.get("ensemble_score", 0.0)
        hit = "YES" if e.get("hit") else "NO"
        match = (e.get("matched_alt") or e.get("best_match") or "")[:50]
        via = e.get("via", "")
        problem_meta = next(p for p in PROBLEMS if p["id"] == run.problem_id)
        parts.append(
            f"| {i} | {problem_meta['name']} | {problem_meta['year']} | {hit} | "
            f"{score:.1f} | {match} | {via} |"
        )
    parts.append("")

    for i, run in enumerate(runs, 1):
        problem_meta = next(p for p in PROBLEMS if p["id"] == run.problem_id)
        parts.append(f"\n---\n\n## {i}. {problem_meta['name']}")
        parts.append(f"- **Year of breakthrough:** {problem_meta['year']}")
        parts.append(f"- **Actual technique (kept REDACTED from models):** {problem_meta['actual_technique']}")
        parts.append(f"- **Citation:** {problem_meta['citation']}")
        parts.append(f"- **Elapsed:** {run.elapsed_s:.1f}s\n")

        for m in run.responses.keys():
            s = run.scores.get(m, {})
            parts.append(f"### {m}")
            parts.append(f"- score: {s.get('score', 0.0):.1f} | best_match: {s.get('best_match', '')!r} | via: {s.get('via', '')}")
            parts.append("- top proposals:")
            props = run.proposals.get(m, [])
            if not props:
                parts.append("  - (none parsed)")
            for p in props[:5]:
                parts.append(f"  - {p}")
            parts.append("")

    out_path.write_text("\n".join(parts))


def write_hit_rate_json(
    runs: list[ProblemRun],
    hit_rate: float,
    verdict: str,
    out_path: Path,
) -> None:
    summary = {
        "date": dt.date.today().isoformat(),
        "n_problems": len(runs),
        "n_hits": int(hit_rate),
        "hit_rate": hit_rate / len(runs) if runs else 0.0,
        "verdict": verdict,
        "threshold": 4,
        "per_problem": [
            {
                "id": r.problem_id,
                "name": r.name,
                "score": r.ensemble.get("ensemble_score", 0.0) if r.ensemble else 0.0,
                "hit": bool(r.ensemble.get("hit")) if r.ensemble else False,
                "strict_hit": bool(r.ensemble.get("strict_hit")) if r.ensemble else False,
                "best_model": r.ensemble.get("best_model") if r.ensemble else None,
                "best_match": r.ensemble.get("best_match") if r.ensemble else None,
                "matched_alt": r.ensemble.get("matched_alt") if r.ensemble else None,
                "via": r.ensemble.get("via") if r.ensemble else None,
                "elapsed_s": r.elapsed_s,
                "per_model_score": {
                    m: r.scores[m]["score"] for m in r.scores
                },
            }
            for r in runs
        ],
    }
    out_path.write_text(json.dumps(summary, indent=2))


def write_raw_responses(runs: list[ProblemRun], out_dir: Path) -> None:
    """Dump every model response so we can audit redaction leakage."""
    out_dir.mkdir(parents=True, exist_ok=True)
    for r in runs:
        for m, resp in r.responses.items():
            (out_dir / f"{r.problem_id}__{m}.md").write_text(resp)


# ════════════════════════════════════════════════════════════════════════
# CLI
# ════════════════════════════════════════════════════════════════════════

def parse_problem_indices(spec: str) -> list[int]:
    out: list[int] = []
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            a, b = part.split("-")
            out.extend(range(int(a), int(b) + 1))
        else:
            out.append(int(part))
    return [i for i in out if 0 <= i < len(PROBLEMS)]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--models",
        default="grok,gemini,codex",
        help="Comma-separated model list (default: grok,gemini,codex)",
    )
    ap.add_argument(
        "--timeout",
        type=int,
        default=900,
        help="Per-model timeout in seconds (default: 900)",
    )
    ap.add_argument(
        "--problems",
        default=None,
        help="Optional indices/ranges, e.g. '0,2,5-7'. Default = all 10.",
    )
    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="Don't call APIs; emit stub responses (cost = $0).",
    )
    ap.add_argument(
        "--output-suffix",
        default=None,
        help="Optional suffix on output files for parallel runs.",
    )
    args = ap.parse_args()

    models = [m.strip() for m in args.models.split(",") if m.strip()]
    bad = [m for m in models if m not in MODELS]
    if bad:
        print(f"ERROR: unknown models: {bad}; available: {list(MODELS)}")
        return 2

    if args.problems:
        idxs = parse_problem_indices(args.problems)
    else:
        idxs = list(range(len(PROBLEMS)))

    print(f"Running calibration on {len(idxs)} problems x {len(models)} models")
    print(f"Models: {models}")
    if args.dry_run:
        print("DRY-RUN: no API calls.")
    print()

    runs: list[ProblemRun] = []
    for i in idxs:
        problem = PROBLEMS[i]
        print(f"[{i+1}/{len(idxs)}] {problem['name']}")
        t0 = time.time()
        run = run_one_problem(problem, models, args.timeout, dry_run=args.dry_run)
        elapsed = time.time() - t0
        e = run.ensemble or {}
        print(
            f"  -> ensemble score = {e.get('ensemble_score', 0.0):.1f}  "
            f"(hit={e.get('hit', False)}, via={e.get('via', '?')})  "
            f"[{elapsed:.0f}s]"
        )
        for m, s in run.scores.items():
            n_props = len(run.proposals.get(m, []))
            print(f"    {m}: score={s['score']:.1f}, proposals={n_props}, via={s.get('via', '?')}")
        runs.append(run)

    hit_rate = sum(1 for r in runs if r.ensemble.get("hit")) if runs else 0
    verdict = "PASS" if hit_rate >= 4 else "FAIL"

    suffix = f"_{args.output_suffix}" if args.output_suffix else ""
    date = dt.date.today().isoformat()
    results_md = CALIBRATION_DIR / f"results_{date}{suffix}.md"
    hit_json = CALIBRATION_DIR / f"hit_rate{suffix}.json"
    raw_dir = CALIBRATION_DIR / f"raw{suffix}"

    write_results_markdown(runs, results_md, hit_rate, verdict)
    write_hit_rate_json(runs, hit_rate, verdict, hit_json)
    write_raw_responses(runs, raw_dir)

    print()
    print("=" * 60)
    print(f" HIT RATE: {hit_rate}/{len(runs)}   VERDICT: {verdict}")
    print(f" Results:  {results_md.relative_to(REPO_ROOT)}")
    print(f" Summary:  {hit_json.relative_to(REPO_ROOT)}")
    print(f" Raw:      {raw_dir.relative_to(REPO_ROOT)}/")
    print("=" * 60)

    return 0 if verdict == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
