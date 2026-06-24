#!/usr/bin/env python3
"""
statement_diff.py — Deterministic statement-faithfulness checker (Method-1 G2-L1).

The Rivin gate: Aristotle proves ~97.6% of theorems it attempts, but only ~67%
are *semantically* the conjecture that was asked. The remaining third are
clean-compiling weaker/restricted/mis-stated variants that land silently as
"advances". This module is the deterministic, no-network, no-LLM backstop that
catches the structural subset of that failure mode at near-zero marginal cost.

Public API (integration contract — code to this exactly):

    compare_statements(proved_sig, intended_sig)
        -> {"faithful": bool, "issue": str | None,
            "severity": "none" | "minor" | "fatal"}

    extract_theorem_statement(lean_text) -> str
        (thin re-export of codex_proof_loop.extract_theorem_statement, normalized
         to always return a str — empty string when nothing is found.)

Five faithfulness violations detected (all relative: proved vs intended):
  1. hypothesis-strip   — proved drops a hypothesis the intended statement carried
                          (proving a *stronger* claim — usually a sign the proof
                          changed the theorem, fatal when it inverts the burden).
  2. quantifier-flip    — a ∀ in the intended became ∃ in the proved (or vice
                          versa), or the binder count dropped (a free variable
                          got pinned to a constant).
  3. weaker-conclusion  — the proved conclusion is a syntactic relaxation of the
                          intended one (e.g. `4 ≤ x` weakened to `1 ≤ x`, or a
                          conjunction reduced to one conjunct).
  4. bound-injection    — proved injects a numeric ceiling absent from the intended
                          statement (`n ≤ 500`, `Finset.Icc 2 500`, `q ≤ 1000`,
                          `Finset.range N`). This is the F9 family, source-relative:
                          the intended conjecture is unbounded, the proved one is a
                          finite verification. Always fatal.
  5. definition-swap    — a key symbol/operator in the intended statement is absent
                          from the proved one (the conclusion was restated against a
                          different predicate/definition). F10 family.

Design rules (per plan §7 risk #1 "err strict at G2-L1"):
  * Fail STRICT: when in doubt, mark non-faithful. A false-reject costs an advance
    (fails closed to compiled_no_advance); a false-accept lands a wrong theorem.
  * Deterministic only: pure string/regex analysis. No network, no LLM. Ambiguity
    that this layer cannot resolve is surfaced (faithful=False, severity='minor')
    so the caller can escalate to the G2-L2 cross-model adversary.
  * Reuses codex_proof_loop.extract_theorem_statement, .check_statement_locked,
    and audit_proven.detect_failure_modes / ._looks_like_em_tautology — does not
    reinvent any of them.

CLI (matches repo style: argparse + if __name__ == '__main__'):
    python3 scripts/statement_diff.py --proved-file A.lean --intended-file B.lean
    python3 scripts/statement_diff.py --proved "<sig>" --intended "<sig>"
    python3 scripts/statement_diff.py --self-test     # runs the id1254/id1255 + em real test
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Optional

# ── Reuse verified primitives (do not reinvent) ─────────────────────────────
# We import the canonical extractor + statement-lock + F-mode detectors rather
# than re-implementing them. Path insert keeps this runnable from anywhere.
_SCRIPTS_DIR = Path(__file__).resolve().parent
if str(_SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS_DIR))

from codex_proof_loop import (  # noqa: E402
    extract_theorem_statement as _cpl_extract,
    check_statement_locked,
)
from audit_proven import detect_failure_modes  # noqa: E402

# _looks_like_em_tautology lives in safe_aristotle_submit. Import defensively:
# that module is heavy and we never want statement_diff to hard-fail on its
# import (fail-closed philosophy — a missing detector must not crash the gate).
try:
    from safe_aristotle_submit import _looks_like_em_tautology  # noqa: E402
except Exception:  # pragma: no cover - defensive
    def _looks_like_em_tautology(text: str) -> bool:  # type: ignore
        """Fallback em-tautology detector if safe_aristotle_submit won't import.

        Mirrors the structural shape `(X) ∨ ¬ (X)` check. Conservative.
        """
        m = re.search(r'theorem\s+\w+[^:]*:(?P<body>.*?):=\s*by\b', text, re.DOTALL)
        if not m:
            m = re.search(r'theorem\s+\w+[^:]*:(?P<body>.*?):=\s*sorry\b', text, re.DOTALL)
        if not m:
            # Also accept a raw body (no theorem wrapper) for signature-only inputs.
            body = text
        else:
            body = m.group('body')
        body = re.sub(r'\s+', ' ', body).strip()
        parts = re.split(r'∨\s*¬', body, maxsplit=1)
        if len(parts) != 2:
            return False

        def _norm(s: str) -> str:
            return re.sub(r'[\s()]+', '', s)

        left, right = _norm(parts[0]), _norm(parts[1])
        return bool(left) and bool(right) and left == right


# ── Tokens / patterns ───────────────────────────────────────────────────────

# Numeric-ceiling shapes that, when present in the PROVED statement but absent
# from the INTENDED statement, indicate bound-injection (F9, source-relative).
# Kept deliberately broad — strict-fail philosophy.
_BOUND_INJECTION_PATTERNS = [
    re.compile(r'Finset\.Icc\s+\S+\s+\d+'),          # Finset.Icc 2 500
    re.compile(r'Finset\.range\s+\d+'),               # Finset.range 501
    re.compile(r'Finset\.Ico\s+\S+\s+\d+'),
    re.compile(r'Finset\.Ioc\s+\S+\s+\d+'),
    re.compile(r'[≤<]\s*\d{2,}'),                      # n ≤ 500 / q < 1000 (2+ digit ceiling)
    re.compile(r'\b\w+\s*≤\s*\d+\b'),                  # x ≤ 7  (any small explicit ceiling)
    re.compile(r'\bInterval\b|\binterval_cases\b'),    # interval_cases leakage into a sig
]

# A finite enumeration in the *conclusion* — `q = 71 ∨ q = 359 ∨ ...` — is the
# Feit-Thompson shape: a universally-quantified conjecture collapsed to a finite
# disjunction of constants. Treated as bound-injection (the domain was pinned to
# a finite set).
_FINITE_DISJ = re.compile(r'(?:\b\w+\s*=\s*\d+\b\s*∨\s*){2,}\b\w+\s*=\s*\d+\b')

# Quantifier tokens. We count binders, not just presence, so that pinning one of
# several universally-quantified variables to a constant (a hidden hypothesis
# strip) is caught as a binder-count drop.
_FORALL = re.compile(r'∀|\\forall\b|\bforall\b')
_EXISTS = re.compile(r'∃|\\exists\b|\bexists\b')

# Hypothesis binders in a Lean signature: `(h : P)`, `{n : ℕ}`, `[Field K]`,
# plus explicit `→`-chained antecedents. We approximate the hypothesis *set* by
# (a) the bracketed binders and (b) the arrow-separated antecedents of the body.
_BINDER = re.compile(r'[\(\{\[]\s*[^()\{\}\[\]]*?:\s*[^()\{\}\[\]]+?[\)\}\]]')

# Comparison/relation operators whose *direction or strength* matters for the
# weaker-conclusion check. Map each to a (kind, strength-rank) so a relaxation is
# detectable. Higher rank = stronger claim about the witness.
_REL_TOKENS = ['↔', '=', '≤', '<', '≥', '>', '≠', '∣', '∈', '⊆', '⊂']


# ── Helpers ──────────────────────────────────────────────────────────────────

def _normalize(s: str) -> str:
    """Whitespace-collapse a signature for comparison. Mirrors check_statement_locked's
    normalize but exposed for our own intermediate steps."""
    return " ".join((s or "").split())


def _strip_paren_noise(s: str) -> str:
    """Remove whitespace and *outer* grouping parens for content equality of operands."""
    return re.sub(r'[\s()]+', '', s or "")


def _looks_like_signature_only(text: str) -> bool:
    """True if `text` is a bare signature (`theorem foo ... : Concl`) with no
    `:=` body — i.e. already an extracted statement, not a full Lean file."""
    return ':=' not in text and ('theorem' in text or 'lemma' in text or '→' in text or '∀' in text)


def _split_hyps_and_concl(sig: str) -> tuple[list[str], str]:
    """Split a normalized signature into (hypotheses, conclusion).

    Hypotheses = bracketed binders ∪ arrow-antecedents of the colon-body.
    Conclusion = the final arrow-segment of the body (after the last top-level →).

    This is a heuristic — Lean grammar is not fully parsed — but it is robust on
    the easy-tail conjecture shapes Method-1 targets, and it fails STRICT (a
    parse ambiguity widens the hypothesis set, biasing toward 'non-faithful').
    """
    sig = _normalize(sig)

    # Bracketed binders (explicit/implicit/instance args before the `:`).
    binders = [m.group(0) for m in _BINDER.finditer(sig)]

    # Body after the first top-level `:` (the type ascription that opens the prop).
    # We split on the FIRST ' : ' that is not inside a binder. Since binders are
    # bracketed, the first colon outside any bracket starts the proposition.
    body = _colon_body(sig)

    # Arrow-antecedents: split the body on top-level → ; all but the last are hyps.
    parts = _split_top_level_arrows(body)
    if len(parts) >= 2:
        antecedents = parts[:-1]
        conclusion = parts[-1]
    else:
        antecedents = []
        conclusion = body

    hyps = [_normalize(b) for b in binders] + [_normalize(a) for a in antecedents]
    hyps = [h for h in hyps if h]
    return hyps, _normalize(conclusion)


def _colon_body(sig: str) -> str:
    """Return the proposition body: everything after the first colon that sits at
    bracket-depth 0 (i.e. the type ascription opening the statement)."""
    depth = 0
    for i, ch in enumerate(sig):
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth = max(0, depth - 1)
        elif ch == ':' and depth == 0:
            # Guard against `::` and Lean's `:=` (already stripped by extractor,
            # but be safe).
            nxt = sig[i + 1: i + 2]
            if nxt not in (':', '='):
                return sig[i + 1:].strip()
    return sig


def _split_top_level_arrows(body: str) -> list[str]:
    """Split `body` on `→` (or `->`) tokens at bracket-depth 0."""
    parts: list[str] = []
    depth = 0
    buf: list[str] = []
    i = 0
    n = len(body)
    while i < n:
        ch = body[i]
        if ch in '([{':
            depth += 1
            buf.append(ch)
            i += 1
            continue
        if ch in ')]}':
            depth = max(0, depth - 1)
            buf.append(ch)
            i += 1
            continue
        if depth == 0 and ch == '→':
            parts.append("".join(buf).strip())
            buf = []
            i += 1
            continue
        if depth == 0 and ch == '-' and body[i + 1: i + 2] == '>':
            parts.append("".join(buf).strip())
            buf = []
            i += 2
            continue
        buf.append(ch)
        i += 1
    if buf:
        parts.append("".join(buf).strip())
    return [p for p in parts if p != ""]


def _has_bound_injection(proved: str, intended: str) -> Optional[str]:
    """Detect a numeric ceiling / finite enumeration present in `proved` but not
    in `intended`. Returns a human message or None."""
    p_norm = _normalize(proved)
    i_norm = _normalize(intended)

    # Finite disjunction of constant equalities (domain pinned to a finite set).
    if _FINITE_DISJ.search(p_norm) and not _FINITE_DISJ.search(i_norm):
        m = _FINITE_DISJ.search(p_norm)
        return (f"bound-injection: proved statement pins the variable to a finite "
                f"enumeration absent from the intended conjecture "
                f"(snippet: {m.group(0)[:80]!r})")

    for pat in _BOUND_INJECTION_PATTERNS:
        p_hits = set(m.group(0) for m in pat.finditer(p_norm))
        if not p_hits:
            continue
        i_hits = set(m.group(0) for m in pat.finditer(i_norm))
        # A ceiling shape that appears in proved but is genuinely new (not also in
        # the intended statement) is an injection.
        new_hits = p_hits - i_hits
        if new_hits:
            example = sorted(new_hits)[0]
            return (f"bound-injection: proved statement carries a numeric ceiling "
                    f"absent from the intended conjecture (e.g. {example!r}); "
                    f"this is a finite verification, not the unbounded claim")
    return None


def _hypothesis_relation(proved_hyps: list[str], intended_hyps: list[str]) -> Optional[tuple[str, str]]:
    """Compare hypothesis SETS. Returns (kind, message, severity) where kind ∈
    {'hypothesis-strip', 'hypothesis-inject', 'hypothesis-rename'} or None when the
    sets match exactly.

    - hypothesis-strip:   intended has a hypothesis the proved statement dropped
                          (proved is *stronger* — usually means the theorem was
                          silently changed; fatal).
    - hypothesis-inject:  proved adds a hypothesis the intended lacked (proved is
                          *weaker* / restricted — the F9-style domain narrowing;
                          fatal). Bound-injection is the numeric subcase, handled
                          separately; this catches the non-numeric cases
                          (e.g. an extra `q ≡ 71 [MOD 72]`).
    - hypothesis-rename:  the two hypothesis sets differ ONLY by bound-variable
                          names (alpha-equivalence). Not a structural violation —
                          severity='minor' so the caller escalates to the G2-L2
                          cross-model adversary instead of hard-rejecting an honest
                          restatement.
    """
    p_set = {_strip_paren_noise(h) for h in proved_hyps}
    i_set = {_strip_paren_noise(h) for h in intended_hyps}

    # Variable-name-insensitive comparison is too lossy; we compare on
    # paren-stripped content. Identical content sets ⇒ no hypothesis change.
    only_intended = i_set - p_set
    only_proved = p_set - i_set

    if not only_intended and not only_proved:
        return None

    # Alpha-rename probe: canonicalize identifiers to positional placeholders and
    # compare the resulting binder *multisets*. If they match, the only difference
    # is naming — a faithful restatement we must not hard-reject.
    if _alpha_equiv_binders(proved_hyps, intended_hyps):
        return ("hypothesis-rename",
                "hypothesis sets differ only by bound-variable names "
                "(alpha-equivalence) — no structural change; escalate to cross-model",
                "minor")

    if only_intended and not only_proved:
        sample = sorted(only_intended, key=len)[0]
        return ("hypothesis-strip",
                f"hypothesis-strip: the proved statement dropped a hypothesis the "
                f"intended conjecture required (missing ~{sample[:60]!r}); a "
                f"stronger claim, not the asked theorem",
                "fatal")
    if only_proved and not only_intended:
        sample = sorted(only_proved, key=len)[0]
        return ("hypothesis-inject",
                f"hypothesis-injection: the proved statement adds a restricting "
                f"hypothesis absent from the intended conjecture "
                f"(extra ~{sample[:60]!r}); the domain was narrowed",
                "fatal")
    # Both differ AND not alpha-equivalent — the hypothesis block was rewritten.
    return ("hypothesis-inject",
            f"hypothesis-mismatch: proved and intended hypothesis sets differ "
            f"(proved-only ~{sorted(only_proved, key=len)[0][:40]!r}, "
            f"intended-only ~{sorted(only_intended, key=len)[0][:40]!r})",
            "fatal")


def _canonicalize_identifiers(s: str) -> str:
    """Replace every lowercase-leading identifier (bound variables, hypothesis
    names) with a positional placeholder `v`, preserving operators, numerals, and
    Capitalized/qualified names (types, defs like `Nat.Prime`). This yields an
    alpha-invariant skeleton for comparing binder shapes."""
    # Tokens: qualified/Capitalized idents (keep), lowercase idents (canonicalize).
    def repl(m: re.Match) -> str:
        tok = m.group(0)
        # Keep anything Capitalized or qualified (a type / known def).
        if tok[0].isupper() or '.' in tok:
            return tok
        return 'v'
    return re.sub(r'[A-Za-z_][A-Za-z0-9_.]*', repl, s)


def _alpha_equiv_binders(proved_hyps: list[str], intended_hyps: list[str]) -> bool:
    """True iff the two binder lists are equal as multisets after canonicalizing
    bound-variable names (alpha-equivalence)."""
    from collections import Counter
    p = Counter(_canonicalize_identifiers(_strip_paren_noise(h)) for h in proved_hyps)
    i = Counter(_canonicalize_identifiers(_strip_paren_noise(h)) for h in intended_hyps)
    return p == i


def _quantifier_relation(proved: str, intended: str) -> Optional[str]:
    """Detect ∀↔∃ flips and binder-count drops. Returns a message or None."""
    p_forall = len(_FORALL.findall(proved))
    p_exists = len(_EXISTS.findall(proved))
    i_forall = len(_FORALL.findall(intended))
    i_exists = len(_EXISTS.findall(intended))

    # Hard flip: intended was universally quantified, proved turned it existential
    # (or vice versa). E.g. "∀ n, P n" weakened to "∃ n, P n".
    if i_forall > 0 and p_forall == 0 and p_exists > 0:
        return ("quantifier-flip: intended universal (∀) became existential (∃) in "
                "the proved statement — an existence claim is not the universal one")
    if i_exists > 0 and p_exists == 0 and p_forall > 0:
        return ("quantifier-flip: intended existential (∃) became universal (∀) in "
                "the proved statement — the quantifier meaning changed")

    # Binder-count drop: the intended statement bound MORE universal variables than
    # the proved one. A dropped ∀-binder usually means a free variable was pinned
    # to a constant (a hidden specialization). Strict-fail.
    if i_forall > p_forall:
        return (f"quantifier-flip: intended statement has more universal binders "
                f"({i_forall} ∀) than the proved statement ({p_forall} ∀) — a "
                f"quantified variable was pinned/dropped")
    return None


_WEAKENING_MAP = {
    # intended_token -> set of proved_tokens that would WEAKEN the claim
    '↔': {'→', '←'},          # iff weakened to one direction
    '=': {'≤', '<', '≥', '>', '∣', '≠'},   # equality weakened to inequality/divisibility
    '⊆': {'⊂'},
}


def _conclusion_relation(proved_concl: str, intended_concl: str) -> Optional[str]:
    """Detect a weaker conclusion. Heuristic + strict.

    Triggers when:
      (a) the intended conclusion's principal relation is replaced by a strictly
          weaker one (per _WEAKENING_MAP), or
      (b) a numeric lower-bound in the intended conclusion is *reduced* in the
          proved one (e.g. `4 ≤ x` proved as `1 ≤ x`), or
      (c) the intended conclusion is a conjunction (∧) and the proved conclusion
          drops a conjunct.
    Returns a message or None.
    """
    p = _normalize(proved_concl)
    i = _normalize(intended_concl)
    if not p or not i:
        return None

    # (a) principal-relation weakening.
    for strong_tok, weak_set in _WEAKENING_MAP.items():
        if strong_tok in i and strong_tok not in p:
            for weak_tok in weak_set:
                if weak_tok in p:
                    return (f"weaker-conclusion: intended conclusion used {strong_tok!r} "
                            f"but proved conclusion uses the weaker {weak_tok!r}")

    # (b) numeric lower-bound reduction: `<k> ≤ <expr>` with the constant reduced.
    #     RHS keys are alpha-canonicalized so a bound reduction is caught even when
    #     the bound variable was renamed (`4 ≤ f n` proved as `1 ≤ f m`).
    def _lower_bounds(s: str) -> list[tuple[int, str]]:
        out = []
        for m in re.finditer(r'(\d+)\s*≤\s*([^,∧∨→]+)', s):
            rhs = _canonicalize_identifiers(_strip_paren_noise(m.group(2)))
            out.append((int(m.group(1)), rhs))
        return out

    p_lbs = _lower_bounds(p)
    i_lbs = _lower_bounds(i)
    pl = {rhs: k for k, rhs in p_lbs}
    il = {rhs: k for k, rhs in i_lbs}
    for rhs, ik in il.items():
        if rhs in pl and pl[rhs] < ik:
            return (f"weaker-conclusion: intended lower bound {ik} ≤ {rhs[:30]} was "
                    f"weakened to {pl[rhs]} ≤ {rhs[:30]} in the proved statement")
    # Positional fallback: exactly one lower-bound on each side, RHS keys did not
    # match (residual notational drift) but the proved constant is strictly smaller
    # → still a weakening. Strict-fail.
    if len(p_lbs) == 1 and len(i_lbs) == 1 and p_lbs[0][0] < i_lbs[0][0]:
        return (f"weaker-conclusion: the sole lower bound was reduced from "
                f"{i_lbs[0][0]} (intended) to {p_lbs[0][0]} (proved)")

    # (c) conjunction reduction.
    if '∧' in i and '∧' not in p:
        return ("weaker-conclusion: intended conclusion is a conjunction (∧) but the "
                "proved conclusion proves only part of it")
    return None


def _definition_swap(proved_concl: str, intended_concl: str,
                     proved_sig: str, intended_sig: str) -> Optional[str]:
    """Detect a definition/operator swap: a salient symbol carried by the intended
    conclusion is wholly absent from the proved one (the conclusion was restated
    against a different predicate). F10 family. Returns a message or None.

    Salient symbols = the relation/operator tokens and any `Foo.bar`-style
    qualified identifiers in the intended conclusion. We require that EVERY
    relation token present in the intended conclusion has a counterpart in the
    proved conclusion; a fully-missing relation operator is a swap.
    """
    p = _normalize(proved_concl)
    i = _normalize(intended_concl)
    if not p or not i:
        return None

    # If the proved and intended conclusions share NO content tokens at all, the
    # statement was wholesale replaced. (Whitespace/paren-insensitive overlap.)
    def _content_tokens(s: str) -> set[str]:
        return set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*|[↔=≤<≥>≠∣∈⊆⊂∧∨]', s))

    p_tok = _content_tokens(p)
    i_tok = _content_tokens(i)

    # Relation operators in intended must appear in proved.
    i_rels = {t for t in i_tok if t in _REL_TOKENS}
    p_rels = {t for t in p_tok if t in _REL_TOKENS}
    missing_rel = i_rels - p_rels
    # `=` ↔ `↔`/inequality is handled by weaker-conclusion; here we only flag a
    # *structural* operator (∣, ∈, ⊆) that vanished entirely.
    structural_missing = {t for t in missing_rel if t in ('∣', '∈', '⊆', '⊂')}
    if structural_missing:
        return (f"definition-swap: intended conclusion's operator(s) "
                f"{sorted(structural_missing)} are absent from the proved "
                f"conclusion — the claim was restated against a different relation")

    # Qualified identifiers (e.g. `Nat.nth`, `Nat.Prime`) present in intended but
    # absent in proved suggest the predicate was swapped. Require a NAMED ident
    # (contains a dot) to avoid flagging incidental local-variable renames.
    i_qual = {t for t in i_tok if '.' in t}
    p_qual = {t for t in p_tok if '.' in t}
    missing_qual = i_qual - p_qual
    if missing_qual and len(missing_qual) == len(i_qual) and i_qual:
        # ALL of the intended's qualified identifiers vanished — strong swap signal.
        return (f"definition-swap: every qualified identifier from the intended "
                f"conclusion {sorted(i_qual)} is absent from the proved conclusion")
    return None


# ── Public API ───────────────────────────────────────────────────────────────

def extract_theorem_statement(lean_text: str) -> str:
    """Extract the first theorem/lemma signature (up to `:=`/`where`) from Lean
    source. Thin wrapper over codex_proof_loop.extract_theorem_statement that
    normalizes the return to a `str` (empty string when nothing matched), per the
    integration contract.
    """
    if lean_text is None:
        return ""
    stripped = lean_text.strip()
    # If the caller already handed us a bare signature (single line, with a type
    # ascription `:` OR opening with theorem/lemma), return it normalized. The
    # colon/keyword requirement avoids echoing back arbitrary prose that merely
    # contains the substring "theorem".
    single_line = '\n' not in stripped
    looks_decl = bool(re.match(r'^(theorem|lemma)\b', stripped))
    has_ascription = ':' in stripped and ':=' not in stripped
    if single_line and _looks_like_signature_only(stripped) and (looks_decl or has_ascription):
        return _normalize(stripped)
    stmt = _cpl_extract(lean_text)
    return _normalize(stmt) if stmt else ""


def compare_statements(proved_sig: str, intended_sig: str) -> dict:
    """Compare a proved theorem signature against the intended conjecture.

    Args:
        proved_sig:   the signature Aristotle actually proved (a theorem/lemma
                      signature string, or full Lean text — we extract).
        intended_sig: the source conjecture signature (string or full Lean text).

    Returns (integration contract):
        {"faithful": bool, "issue": str | None,
         "severity": "none" | "minor" | "fatal"}

    Fail-STRICT semantics:
        * Any of the 5 structural violations ⇒ faithful=False, severity='fatal'.
        * An em-tautology in either statement ⇒ faithful=False, severity='fatal'
          (an LEM disjunction is never a faithful rendering of an existence /
          impossibility conjecture).
        * Inputs we cannot parse into a comparable shape ⇒ faithful=False,
          severity='minor' (escalate to G2-L2 cross-model; never auto-pass).
        * Byte-identical (whitespace-normalized) signatures ⇒ faithful=True.
    """
    # Accept either raw signatures or full Lean files.
    proved = extract_theorem_statement(proved_sig) or _normalize(proved_sig)
    intended = extract_theorem_statement(intended_sig) or _normalize(intended_sig)

    if not proved or not intended:
        return {
            "faithful": False,
            "issue": ("statement-extraction-failed: could not recover a comparable "
                      "signature from one or both inputs — escalate to cross-model check"),
            "severity": "minor",
        }

    # 0) em-tautology guard on EITHER side, BEFORE the statement-lock fast path.
    #     `(P) ∨ ¬ P` is never a faithful rendering of an existence/impossibility
    #     conjecture (PILOT_ERDOS850) — even when proved == intended, proving an
    #     LEM disjunction resolves nothing, so it must fail-closed regardless of
    #     whether the two signatures happen to be byte-identical.
    for label, sig in (("proved", proved), ("intended", intended)):
        # _looks_like_em_tautology expects a `theorem ... := by/sorry` shape; wrap
        # a bare signature so the detector's regex can bind the body.
        probe = sig if ':=' in sig else f"theorem _probe : {_colon_body(sig) or sig} := by"
        try:
            if _looks_like_em_tautology(probe):
                return {
                    "faithful": False,
                    "issue": (f"em-tautology: the {label} statement has the shape "
                              f"(X) ∨ ¬X (law of excluded middle); Aristotle discharges "
                              f"this with `exact em _` and resolves nothing"),
                    "severity": "fatal",
                }
        except Exception:
            # Detector hiccup must not crash the gate — treat as ambiguity.
            pass

    # 0b) Statement-lock fast path: identical (normalized) AND not an em-tautology
    #     ⇒ faithful. (The em guard above already rejected LEM disjunctions, so a
    #     byte-identical pair here is a genuine match.)
    if check_statement_locked(proved, intended):
        return {"faithful": True, "issue": None, "severity": "none"}

    # 0c) F-mode scan on the proved side (when it carries a tactic body). Catches
    #     iff_rfl/F9-bounded/exact?/restate-with-sorry independent of the diff.
    if ':=' in proved_sig:
        fmodes = detect_failure_modes(proved_sig)
        if fmodes:
            code, sev, msg = fmodes[0]
            return {
                "faithful": False,
                "issue": f"{code} failure-mode in proved statement: {msg}",
                "severity": "fatal",
            }

    # 1) bound-injection (F9 source-relative) — highest priority, always fatal.
    bi = _has_bound_injection(proved, intended)
    if bi:
        return {"faithful": False, "issue": bi, "severity": "fatal"}

    # Decompose both signatures into (hyps, conclusion) for the structural checks.
    p_hyps, p_concl = _split_hyps_and_concl(proved)
    i_hyps, i_concl = _split_hyps_and_concl(intended)

    # 2) quantifier-flip / binder drop.
    qf = _quantifier_relation(proved, intended)
    if qf:
        return {"faithful": False, "issue": qf, "severity": "fatal"}

    # 3) hypothesis-strip / hypothesis-injection. A pure alpha-rename returns
    #     severity='minor' — we hold it as a SOFT signal and keep checking the
    #     conclusion, because a renamed-but-otherwise-faithful statement may still
    #     have a weaker conclusion or a swapped definition (which are fatal).
    soft_issue = None
    hr = _hypothesis_relation(p_hyps, i_hyps)
    if hr:
        _kind, msg, sev = hr
        if sev == "fatal":
            return {"faithful": False, "issue": msg, "severity": "fatal"}
        soft_issue = msg  # minor — defer

    # 4) weaker-conclusion.
    wc = _conclusion_relation(p_concl, i_concl)
    if wc:
        return {"faithful": False, "issue": wc, "severity": "fatal"}

    # 5) definition-swap.
    ds = _definition_swap(p_concl, i_concl, proved, intended)
    if ds:
        return {"faithful": False, "issue": ds, "severity": "fatal"}

    # A pure alpha-rename of the hypotheses with no conclusion violation: not a
    # structural change, but we never auto-pass a non-byte-identical statement.
    if soft_issue is not None:
        return {"faithful": False, "issue": soft_issue, "severity": "minor"}

    # The signatures differ textually but none of the structural violations fired.
    # Fail-STRICT: we cannot certify faithfulness deterministically, so we flag a
    # minor issue for the cross-model adversary rather than auto-passing. (A
    # genuinely-equivalent restatement — variable renames, reordered binders — will
    # be cleared by G2-L2; we never silently promote on an unexplained diff.)
    return {
        "faithful": False,
        "issue": ("statements differ but no deterministic violation matched — "
                  "residual ambiguity, escalate to cross-model adversary (G2-L2)"),
        "severity": "minor",
    }


# ── CLI ──────────────────────────────────────────────────────────────────────

def _read(path_or_none: Optional[str]) -> Optional[str]:
    if not path_or_none:
        return None
    p = Path(path_or_none)
    if not p.is_file():
        print(f"ERROR: file not found: {path_or_none}", file=sys.stderr)
        sys.exit(2)
    return p.read_text()


def _run_self_test() -> int:
    """REAL test against the two mislabeled advances (id1254 Brocard slot722,
    id1255 Feit-Thompson slot720) + an em-tautology string. No mocks.

    Expects: both bounded extensions ⇒ faithful=False, severity='fatal'.
    """
    base = _SCRIPTS_DIR.parent
    cases = [
        {
            "name": "id1254 Brocard (slot722) — bounded n≤500",
            "proved_file": base / "submissions/nu4_final/slot722_iter2_brocard_extended_result.lean",
            "intended_file": base / "formal-conjectures/FormalConjectures/Wikipedia/BrocardConjecture.lean",
            "expect_faithful": False,
            "expect_severity": "fatal",
        },
        {
            "name": "id1255 Feit-Thompson (slot720) — 7 small primes, q≤1000",
            "proved_file": base / "submissions/nu4_final/slot720_iter2_ft_family_result.lean",
            "intended_file": base / "formal-conjectures/FormalConjectures/Wikipedia/FeitThompsonPrimeConjecture.lean",
            "expect_faithful": False,
            "expect_severity": "fatal",
        },
    ]

    all_ok = True
    print("=" * 72)
    print("statement_diff self-test — REAL artifacts (id1254, id1255) + em-tautology")
    print("=" * 72)

    for c in cases:
        pf, intf = c["proved_file"], c["intended_file"]
        if not pf.is_file() or not intf.is_file():
            print(f"  SKIP  {c['name']}: missing artifact ({pf if not pf.is_file() else intf})")
            all_ok = False
            continue
        proved_text = pf.read_text()
        intended_text = intf.read_text()
        proved_sig = extract_theorem_statement(proved_text)
        intended_sig = extract_theorem_statement(intended_text)
        res = compare_statements(proved_text, intended_text)
        ok = (res["faithful"] == c["expect_faithful"]
              and res["severity"] == c["expect_severity"])
        all_ok = all_ok and ok
        print(f"\n[{'PASS' if ok else 'FAIL'}] {c['name']}")
        print(f"    proved sig:   {proved_sig[:110]}")
        print(f"    intended sig: {intended_sig[:110]}")
        print(f"    verdict: faithful={res['faithful']} severity={res['severity']!r}")
        print(f"    issue:   {res['issue']}")
        print(f"    expected: faithful={c['expect_faithful']} severity={c['expect_severity']!r}")

    # em-tautology string case.
    em_sig = "theorem erdos850_em (P : Prop) : P ∨ ¬ P := by exact em _"
    em_res = compare_statements(em_sig, em_sig)
    em_ok = (em_res["faithful"] is False and em_res["severity"] == "fatal"
             and "em-tautology" in (em_res["issue"] or ""))
    all_ok = all_ok and em_ok
    print(f"\n[{'PASS' if em_ok else 'FAIL'}] em-tautology string `(P) ∨ ¬ P`")
    print(f"    verdict: faithful={em_res['faithful']} severity={em_res['severity']!r}")
    print(f"    issue:   {em_res['issue']}")

    # faithful-identity positive control: identical signatures must pass.
    same = "theorem t (n : ℕ) (hn : 1 ≤ n) : 4 ≤ f n := by sorry"
    same_res = compare_statements(same, same)
    same_ok = same_res["faithful"] is True and same_res["severity"] == "none"
    all_ok = all_ok and same_ok
    print(f"\n[{'PASS' if same_ok else 'FAIL'}] positive control: identical signatures")
    print(f"    verdict: faithful={same_res['faithful']} severity={same_res['severity']!r}")

    print("\n" + "=" * 72)
    print(f"SELF-TEST {'PASSED' if all_ok else 'FAILED'}")
    print("=" * 72)
    return 0 if all_ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Deterministic statement-faithfulness checker (Method-1 G2-L1).",
    )
    ap.add_argument("--proved", help="Proved theorem signature (string).")
    ap.add_argument("--intended", help="Intended conjecture signature (string).")
    ap.add_argument("--proved-file", help="Path to a .lean file Aristotle proved.")
    ap.add_argument("--intended-file", help="Path to the source-conjecture .lean file.")
    ap.add_argument("--extract", help="Path to a .lean file; print its extracted "
                                       "theorem signature and exit.")
    ap.add_argument("--self-test", action="store_true",
                    help="Run the id1254/id1255 + em-tautology real test.")
    ap.add_argument("--json", action="store_true",
                    help="Emit the verdict as a JSON object.")
    args = ap.parse_args()

    if args.self_test:
        return _run_self_test()

    if args.extract:
        text = _read(args.extract)
        print(extract_theorem_statement(text))
        return 0

    proved = args.proved if args.proved is not None else _read(args.proved_file)
    intended = args.intended if args.intended is not None else _read(args.intended_file)

    if proved is None or intended is None:
        ap.error("provide BOTH a proved statement (--proved/--proved-file) and an "
                 "intended statement (--intended/--intended-file), or use --self-test.")

    result = compare_statements(proved, intended)
    if args.json:
        print(json.dumps(result, ensure_ascii=False))
    else:
        verdict = "FAITHFUL" if result["faithful"] else "NOT FAITHFUL"
        print(f"{verdict}  (severity={result['severity']})")
        if result["issue"]:
            print(f"  issue: {result['issue']}")
    # Exit non-zero on non-faithful so callers can branch on the shell code.
    return 0 if result["faithful"] else 1


if __name__ == "__main__":
    sys.exit(main())
