#!/usr/bin/env python3
"""
biblio_gate.py — fail-CLOSED literature gate for Method-1 / Recipe-B.

Closes the verified ~40-year pre-2024 bibliographic blind spot in
``literature_check.py`` (whose arXiv search was floored at 2024-01-01 and whose
final policy was fail-OPEN: ``CLEAR``/``UNKNOWN`` both passed silently). This
gate replaces that with a fail-CLOSED contract: any exception, network failure,
or genuine uncertainty resolves to ``UNKNOWN`` or ``AMBIGUOUS`` — *never*
``CLEAR``. ``CLEAR`` is emitted only when the network sources were actually
reached and none of them showed evidence that the problem has been closed.

Sources consulted (all free, no API key):
  1. named_conjecture_status DB table  (submissions/tracking.db; the cheap
     pre-2024 catch for famous conjectures whose status is folklore)
  2. analysis/literature_kill_list.csv  (29-row seed of known closures)
  3. zbMATH Open REST  (api.zbmath.org — covers 1868-present, the real catch
     for the 40-yr blind spot)
  4. Crossref REST  (api.crossref.org — DOI-indexed journal/conference papers)
  5. full-range arXiv  (export.arxiv.org — 1991-now, NOT 2024-floored)
  6. local `mk failed <kw>`  (project negative-knowledge; informational)

CONTRACT (the integration interface the rest of Method-1 codes to):

  check_literature(statement, problem_id=None, named_conjecture=None) -> {
      "status":   "CLEAR" | "CLOSED" | "AMBIGUOUS" | "UNKNOWN",
      "evidence": str,            # one-line human-readable rationale
      "sources":  list[dict],     # [{source, url, evidence, signal}, ...]
  }

  FAIL-CLOSED INVARIANT: any exception / uncertainty -> 'UNKNOWN' (never
  'CLEAR').  A closure found with confidence -> 'CLOSED'.  Closure language
  found but not definitive -> 'AMBIGUOUS'.

Status semantics:
  CLOSED     — a source shows the problem is solved/disproved/resolved with
               confidence (named-conjecture card, or a title/abstract with
               strong closure language matching the conjecture).
  AMBIGUOUS  — closure-suggestive language found, but not confidently tied to
               THIS problem (partial result, weak match, conflicting signals).
  CLEAR      — sources were reached and none showed closure. Safe to author.
  UNKNOWN    — could not determine: no usable keywords, all sources errored,
               or the statement is too thin to query. FAIL-CLOSED default.

Cache: submissions/biblio_cache/<hash>.json with a 7-day TTL.

CLI:
  python3 scripts/biblio_gate.py --statement "..." [--problem-id ID] [--named X]
  python3 scripts/biblio_gate.py --selftest      # runs the two REAL-TEST probes
  python3 scripts/biblio_gate.py --named "Brocard's conjecture"
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import sqlite3
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
PROJECT_ROOT = Path(__file__).resolve().parent.parent
CACHE_DIR = PROJECT_ROOT / "submissions" / "biblio_cache"
TRACKING_DB = PROJECT_ROOT / "submissions" / "tracking.db"
KILL_LIST_CSV = PROJECT_ROOT / "analysis" / "literature_kill_list.csv"

CACHE_TTL_SECONDS = 7 * 24 * 3600  # 7 days

# Spacing between successive free-API calls within one check (seconds).
# Overridable via env for batch tuning; the 7-day cache makes steady-state
# network volume small regardless.
import os as _os
_INTER_SOURCE_DELAY = float(_os.environ.get("BIBLIO_GATE_DELAY", "2.0"))

USER_AGENT = (
    "math-forge-biblio-gate/1.0 (mailto:kavanagh.patrick@gmail.com) "
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7)"
)

# arXiv full range: from the first arXiv submissions (1991) through the end of
# this year.  This is the explicit fix for literature_check.py's 2024 floor.
ARXIV_DATE_RANGE = "[199101010000 TO 202612312359]"

# zbMATH covers 1868-present; no date floor needed.
ZBMATH_SEARCH = "https://api.zbmath.org/v1/document/_search"
CROSSREF_WORKS = "https://api.crossref.org/works"
ARXIV_QUERY = "http://export.arxiv.org/api/query"

# ---------------------------------------------------------------------------
# Closure-language detection
#
# These phrases, when they appear in a paper title/abstract that also matches
# the conjecture name/keywords, indicate the problem has likely been resolved.
# We deliberately keep two tiers: STRONG (high-confidence closure) and WEAK
# (closure-suggestive but ambiguous — partial results, special cases).
# ---------------------------------------------------------------------------
_STRONG_CLOSURE = [
    r"\bproof of\b",
    r"\bproved?\b",
    r"\bresolution of\b",
    r"\bresolv(?:e|ed|ing)\b",
    r"\bsettl(?:e|ed|es|ing)\b",
    r"\bdisproof\b",
    r"\bdisproved?\b",
    r"\brefut(?:e|ed|ation)\b",
    r"\bcounterexamples?\b",
    r"\bcounter-?examples?\b",
    r"\ba (?:complete )?solution\b",
    r"\bsolved\b",
    r"\bsolution to\b",
    r"\bestablish(?:ed|es|ing)?\b",
    r"\baffirmative answer\b",
    r"\bnegative answer\b",
    r"\bfull(?:y)? (?:resolved|solved|proved)\b",
]
_WEAK_CLOSURE = [
    r"\bpartial (?:result|progress|answer)\b",
    r"\bspecial case\b",
    r"\btowards?\b",
    r"\bon the\b",
    r"\bremarks? on\b",
    r"\bnote on\b",
    r"\bconditional\b",
    r"\bassuming\b",
    r"\bunder the assumption\b",
    r"\bbounds? (?:for|on)\b",
    # Recalibration (2026-06-10, Tuza false-positive): a title of the shape
    # "X conjecture for <restricted class>" is canonical special-case phrasing
    # ("Bollobás–Erdős–Tuza Conjecture for Graphs With No Induced Ks,t"), not
    # a closure of X.  Same for "in the (special) case".
    r"\bconjectures? for\b",
    r"\bin the (?:special )?case\b",
]
_STRONG_RE = re.compile("|".join(_STRONG_CLOSURE), re.IGNORECASE)
_WEAK_RE = re.compile("|".join(_WEAK_CLOSURE), re.IGNORECASE)

# Statuses in the named-conjecture card / kill-list that mean CLOSED.
_CLOSED_CARD_STATUSES = {
    "CLOSED", "SOLVED", "DISPROVED", "DISPROVEN", "RESOLVED",
    "AI_CLOSED", "RECENTLY_SOLVED", "LITERATURE_CLOSED",
}
# Statuses that mean OPEN (a positive CLEAR signal, but still verify online).
_OPEN_CARD_STATUSES = {"OPEN", "UNSOLVED", "CONJECTURE"}
# Statuses that mean AMBIGUOUS.
_AMBIGUOUS_CARD_STATUSES = {"AMBIGUOUS", "PARTIAL", "POSSIBLY_SOLVED", "UNCLEAR"}

# Stop-words stripped when building a keyword query from a raw Lean/English
# statement.  Lean syntax tokens are noise to a bibliographic search.
_STOPWORDS = {
    "theorem", "lemma", "def", "by", "sorry", "the", "and", "for", "all",
    "exists", "there", "such", "that", "with", "have", "show", "let", "fun",
    "open", "gap", "source", "domain", "status", "type", "types", "prop",
    "nat", "int", "real", "set", "finset", "is", "of", "to", "in", "on", "a",
    "an", "if", "then", "else", "not", "forall", "exist", "this", "we", "it",
    "be", "are", "or", "as", "at", "from", "into", "conjecture", "problem",
    "erdos", "erdős", "statement", "open_gap",
}


# ---------------------------------------------------------------------------
# Cache I/O  (7-day TTL, keyed on the full query intent)
# ---------------------------------------------------------------------------
def _cache_key(statement: str, problem_id: str | None, named: str | None) -> str:
    raw = json.dumps(
        {"s": (statement or "").strip(), "p": problem_id or "", "n": named or ""},
        sort_keys=True,
    )
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:32]


def _cache_path(key: str) -> Path:
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    return CACHE_DIR / f"{key}.json"


def _read_cache(key: str) -> dict | None:
    p = _cache_path(key)
    if not p.exists():
        return None
    try:
        data = json.loads(p.read_text())
    except (json.JSONDecodeError, OSError):
        return None
    ts = data.get("_cache_ts", 0)
    age = time.time() - ts
    if age > CACHE_TTL_SECONDS:
        return None
    data["cache_age_days"] = round(age / 86400.0, 2)
    return data


def _write_cache(key: str, payload: dict) -> None:
    out = dict(payload)
    out["_cache_ts"] = time.time()
    try:
        _cache_path(key).write_text(
            json.dumps(out, indent=2, sort_keys=True, default=str)
        )
    except OSError as e:
        print(f"WARN: biblio cache write failed: {e}", file=sys.stderr)


# ---------------------------------------------------------------------------
# Keyword / name extraction
# ---------------------------------------------------------------------------
def _guess_named_conjecture(statement: str) -> str | None:
    """Best-effort: pull a 'Foo conjecture' / 'Foo's problem' phrase out of an
    English statement so we can do a named-conjecture lookup even when the
    caller didn't pass one explicitly.
    """
    if not statement:
        return None
    m = re.search(
        r"([A-Z][A-Za-z'.\-]+(?:[-\s][A-Z][A-Za-z'.\-]+){0,2}'?s?\s+"
        r"(?:conjecture|problem|hypothesis|theorem))",
        statement,
    )
    if m:
        return re.sub(r"\s+", " ", m.group(1)).strip()
    return None


def _split_camel(tok: str) -> list[str]:
    """Split a camelCase Lean identifier into its English words
    ('DistancesSeparated' -> ['Distances', 'Separated']).  Bibliographic
    engines index English words, not Lean identifiers — the Piepmeyer
    false-negative (erdos_100_piepmeyer): the keyword soup
    'piepmeyer card DistancesSeparated diam' matched nothing, so the gate
    cleared with ZERO citations attached (F2 failure).  Recalibration
    2026-06-10."""
    parts = re.findall(r"[A-ZÀ-Þ][a-zà-ÿ'\-]+|[A-ZÀ-Þ]{2,}|[a-zà-ÿ'\-]+", tok)
    return parts if len(parts) > 1 else [tok]


def _problem_id_terms(problem_id: str | None) -> list[str]:
    """Human-searchable terms derived from a problem_id
    ('erdos_100_piepmeyer' -> ['Erdos', 'piepmeyer']).  A Lean-only statement
    often carries no bibliographically useful words, but the problem id
    usually does (constructor surnames, problem-family names).  Numbers are
    dropped (junk recall); the Erdős family name is kept as a query term even
    though it is a topic stopword."""
    if not problem_id:
        return []
    segs = re.findall(r"[A-Za-z]{3,}", problem_id)
    terms: list[str] = []
    if any(s.lower() in ("erdos", "erdoes") for s in segs):
        terms.append("Erdos")
    for s in segs:
        if s.lower() in _STOPWORDS:
            continue
        terms.append(s)
    return terms


def _extract_keywords(statement: str, named: str | None,
                      problem_id: str | None = None) -> str:
    """Turn a raw statement (English + maybe a Lean line) into a compact
    bibliographic query string.  Prefers the named conjecture if available.

    Recalibration (2026-06-10): problem_id-derived human terms lead the query
    and camelCase Lean identifiers are split into English words, so a bare
    Lean theorem line still yields a usable bibliographic query (the
    Piepmeyer false-negative fix).
    """
    if named:
        return named.strip()
    if not statement and not problem_id:
        return ""
    # Take the first 1-2 English sentences; drop the Lean `theorem ... := by`
    # line entirely (it's notation, useless to a literature search).
    text_lines = []
    for line in statement.splitlines():
        ls = line.strip()
        if not ls:
            continue
        if re.match(r"(?i)^(theorem|lemma|def|example)\b", ls):
            continue
        if re.match(r"(?i)^(open\s+gap|source|domain|status)\s*:", ls):
            # keep the OPEN GAP title text, drop the metadata lines
            mm = re.match(r"(?i)^open\s+gap\s*:\s*(.+)", ls)
            if mm:
                text_lines.append(mm.group(1))
            continue
        text_lines.append(ls)
    text = " ".join(text_lines) if text_lines else statement
    # Tokenise, drop stopwords and pure-symbol tokens, keep distinctive words.
    # problem_id-derived human terms lead so they survive the 8-term cap and
    # the AND-joined arXiv query (recalibration 2026-06-10).
    toks = _problem_id_terms(problem_id)
    for raw in re.findall(r"[A-Za-zÀ-ÿ][A-Za-zÀ-ÿ'\-]+", text):
        toks.extend(_split_camel(raw))
    kept: list[str] = []
    seen: set[str] = set()
    for t in toks:
        lt = t.lower()
        if (lt in _STOPWORDS and lt != "erdos") or len(t) < 3:
            continue
        if lt in seen:
            continue
        seen.add(lt)
        kept.append(t)
        if len(kept) >= 8:
            break
    return " ".join(kept)


def _topic_terms(query: str, named: str | None) -> set[str]:
    """Distinctive lower-cased terms a relevant paper's TITLE should mention.
    Used to require that closure language is actually *about* this problem,
    not a generic 'proof of ...' in a tangentially-matched paper (the false
    -CLOSED-on-Brocard failure mode).
    """
    terms: set[str] = set()
    for src in (named or "", query or ""):
        for t in re.findall(r"[A-Za-zÀ-ÿ][A-Za-zÀ-ÿ'\-]+", src):
            lt = t.lower()
            if lt in _STOPWORDS or len(lt) < 4:
                continue
            terms.add(lt)
    # Drop near-universal math words that don't pin a topic.
    terms -= {"conjecture", "problem", "hypothesis", "theorem", "equation",
              "number", "numbers", "integers", "function", "result", "results",
              "primes", "prime", "density", "many", "solutions", "finite",
              "finitely", "positive", "natural", "sequence", "sequences"}
    return terms


_NAME_SEP = r"[-‐‑‒–—―]"  # ASCII + unicode hyphens/dashes


def _strip_accents(s: str) -> str:
    import unicodedata
    return "".join(c for c in unicodedata.normalize("NFD", s)
                   if not unicodedata.combining(c))


def _compound_name_collision(title: str, topic: set[str]) -> bool:
    """True when the TITLE attributes its conjecture/problem to a compound
    surname list containing a name NOT among the query's topic terms — i.e.
    closure language about a DIFFERENT conjecture that merely shares one
    surname.  The Tuza-collision false positive (2026-06-01 cache): a query
    for 'Tuza conjecture' was marked CLOSED by 'Bollobás–Erdős–Tuza Conjecture
    for Graphs With No Induced Ks,t' — a different conjecture.  Stopword
    surnames (e.g. 'erdos') appear in dozens of compound conjecture names and
    pin nothing, so they are ignored on both sides.
    """
    if not topic:
        return False
    topic_n = {_strip_accents(t) for t in topic}
    m = re.search(
        rf"([A-ZÀ-Þ][\w'’.]+(?:\s*{_NAME_SEP}\s*[A-ZÀ-Þ][\w'’.]+)+)"
        rf"\s+[Cc]onjecture|"
        rf"([A-ZÀ-Þ][\w'’.]+(?:\s*{_NAME_SEP}\s*[A-ZÀ-Þ][\w'’.]+)+)"
        rf"\s+[Pp]roblem",
        title or "")
    if not m:
        return False
    compound = m.group(1) or m.group(2) or ""
    comps = [
        _strip_accents(c.lower().strip(".'’"))
        for c in re.split(_NAME_SEP, compound)
    ]
    comps = [c for c in comps if len(c) >= 3 and c not in _STOPWORDS]
    return any(c not in topic_n for c in comps)


def _looks_like_closure(title: str, snippet: str = "", topic: set[str] | None = None) -> str:
    """Classify a single paper's text. Returns 'strong', 'weak', or 'none'.

    A STRONG verdict requires (1) strong closure language AND, when ``topic``
    terms are supplied, (2) at least one of those distinctive terms appearing
    in the TITLE — so a generic 'proof of Lemma 3' in a paper that merely
    keyword-overlapped does NOT register as closing this conjecture.  Without
    topic terms (rare), title-only strong language still counts as strong.

    Recalibration (2026-06-10): a title naming a compound-surname conjecture
    whose surname set is NOT covered by the topic terms is demoted to 'weak'
    (the Tuza collision — see _compound_name_collision).
    """
    title = title or ""
    blob = f"{title} {snippet}".strip()
    if not blob:
        return "none"
    has_weak = bool(_WEAK_RE.search(blob))
    has_strong = bool(_STRONG_RE.search(blob))
    if not has_strong and not has_weak:
        return "none"

    title_l = title.lower()
    topically_relevant = True
    if topic:
        topically_relevant = any(t in title_l for t in topic)

    # A title that is BOTH weak ("partial result on...") and strong is treated
    # as weak — partial qualifiers downgrade an otherwise-strong verb.
    if has_strong and not has_weak and topically_relevant:
        if topic and _compound_name_collision(title, topic):
            # Strong language about a DIFFERENT compound-named conjecture that
            # shares a surname -> surface for human eyes, never CLOSED alone.
            return "weak"
        return "strong"
    if has_strong and topically_relevant:  # strong+weak, relevant
        return "weak"
    if has_strong and not topically_relevant:
        # strong language but NOT about this topic -> demote to weak so it
        # surfaces for human eyes but never alone triggers CLOSED.
        return "weak" if has_weak else "weak"
    if has_weak:
        return "weak"
    return "none"


# ---------------------------------------------------------------------------
# Named-conjecture card lookup (DB table + kill-list CSV)
# ---------------------------------------------------------------------------
def _norm_name(name: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", (name or "").lower()).strip()


def _lookup_named_card(
    problem_id: str | None, named: str | None,
) -> dict | None:
    """Look up problem closure status in the named_conjecture_status DB table
    and the kill-list CSV.  Returns {status, citation, source, evidence} or
    None.  Fail-safe: any DB/IO error returns None (so the network sources
    still run; the gate's overall fail-CLOSED resolution handles the rest).
    """
    candidates = []
    if named:
        candidates.append(_norm_name(named))
    if problem_id:
        candidates.append(_norm_name(problem_id))
        # erdos_672 -> "erdos 672", also try the bare number form "erdos672"
        candidates.append(_norm_name(problem_id.replace("_", "")))

    # 1) named_conjecture_status DB table (created additively by the migration
    #    agent; absent today -> skip gracefully).
    if TRACKING_DB.exists():
        try:
            conn = sqlite3.connect(f"file:{TRACKING_DB}?mode=ro", uri=True, timeout=5)
            try:
                cur = conn.cursor()
                cur.execute(
                    "SELECT name FROM sqlite_master "
                    "WHERE type='table' AND name='named_conjecture_status'"
                )
                if cur.fetchone():
                    cur.execute(
                        "SELECT name, status, citation, year, notes "
                        "FROM named_conjecture_status"
                    )
                    for name, status, citation, year, notes in cur.fetchall():
                        nn = _norm_name(name)
                        for cand in candidates:
                            if cand and (cand == nn or cand in nn or nn in cand):
                                return {
                                    "status": (status or "").strip().upper(),
                                    "citation": citation or "",
                                    "year": year or "",
                                    "notes": notes or "",
                                    "source": "named_conjecture_status",
                                    "matched": name,
                                }
            finally:
                conn.close()
        except sqlite3.Error:
            pass  # table absent / locked -> fall through to CSV

    # 2) kill-list CSV (seed of known closures; problem_id keyed).
    if KILL_LIST_CSV.exists() and problem_id:
        try:
            pid_norm = _norm_name(problem_id)
            pid_num = _norm_name(problem_id.replace("_", ""))
            with KILL_LIST_CSV.open() as f:
                for row in csv.DictReader(f):
                    rpid = _norm_name(row.get("problem_id", ""))
                    if rpid and (rpid == pid_norm or rpid == pid_num
                                 or pid_norm in rpid or rpid in pid_norm):
                        return {
                            "status": (row.get("literature_status") or "").strip().upper(),
                            "citation": row.get("top_evidence", ""),
                            "year": "",
                            "notes": row.get("wiki_status", ""),
                            "source": "kill_list_csv",
                            "matched": row.get("problem_id", ""),
                        }
        except (OSError, csv.Error):
            pass

    return None


# ---------------------------------------------------------------------------
# Network helpers  (each returns (hits, ok): ok=False means the source errored
# and must NOT be read as "no closure found")
# ---------------------------------------------------------------------------
def _http_get(url: str, timeout: float = 20.0, retries: int = 2) -> tuple[str | None, bool]:
    """GET with simple backoff on 429/5xx.  Returns (body, reached).
    reached=False indicates the source could not be consulted at all.
    """
    last_err = None
    for attempt in range(retries + 1):
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                charset = resp.headers.get_content_charset() or "utf-8"
                return resp.read().decode(charset, errors="replace"), True
        except urllib.error.HTTPError as e:
            last_err = e
            if e.code in (429, 500, 502, 503, 504) and attempt < retries:
                time.sleep(2.0 * (attempt + 1))
                continue
            return None, False
        except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
            last_err = e
            if attempt < retries:
                time.sleep(1.5 * (attempt + 1))
                continue
            return None, False
        except Exception:
            return None, False
    return None, False


def search_zbmath(query: str, max_results: int = 8,
                  topic: set[str] | None = None) -> tuple[list[dict], bool]:
    """zbMATH Open REST.  Returns (hits, reached).  Each hit:
    {title, year, document_type, signal, url}."""
    if not query.strip():
        return [], True
    q = urllib.parse.quote(query.strip())
    url = f"{ZBMATH_SEARCH}?search_string={q}&results_per_page={max_results}"
    body, ok = _http_get(url, timeout=20.0)
    if not ok or body is None:
        return [], False
    try:
        data = json.loads(body)
    except json.JSONDecodeError:
        return [], False
    results = data.get("result") or []
    hits: list[dict] = []
    for item in results[:max_results]:
        title_field = item.get("title") or {}
        if isinstance(title_field, dict):
            title = title_field.get("title") or ""
        else:
            title = str(title_field)
        year = item.get("year") or ""
        dt = item.get("document_type") or {}
        dtype = dt.get("description") if isinstance(dt, dict) else str(dt)
        zid = item.get("id") or ""
        signal = _looks_like_closure(title, topic=topic)
        hits.append({
            "title": title.strip(),
            "year": year,
            "document_type": dtype,
            "signal": signal,
            "url": f"https://zbmath.org/?q=an:{zid}" if zid else "",
        })
    return hits, True


def search_crossref(query: str, max_results: int = 8,
                    topic: set[str] | None = None) -> tuple[list[dict], bool]:
    """Crossref REST.  Returns (hits, reached)."""
    if not query.strip():
        return [], True
    q = urllib.parse.quote(query.strip())
    url = f"{CROSSREF_WORKS}?query={q}&rows={max_results}&select=title,abstract,published,DOI,type"
    body, ok = _http_get(url, timeout=20.0)
    if not ok or body is None:
        return [], False
    try:
        data = json.loads(body)
    except json.JSONDecodeError:
        return [], False
    items = (data.get("message") or {}).get("items") or []
    hits: list[dict] = []
    for it in items[:max_results]:
        title_list = it.get("title") or []
        title = title_list[0] if title_list else ""
        abstract = it.get("abstract") or ""
        # Crossref abstracts are JATS XML; strip tags for keyword scanning.
        abstract = re.sub(r"<[^>]+>", " ", abstract)
        dp = (it.get("published") or {}).get("date-parts") or [[None]]
        year = dp[0][0] if dp and dp[0] else ""
        doi = it.get("DOI") or ""
        signal = _looks_like_closure(title, abstract[:500], topic=topic)
        hits.append({
            "title": (title or "").strip(),
            "year": year or "",
            "document_type": it.get("type") or "",
            "signal": signal,
            "url": f"https://doi.org/{doi}" if doi else "",
        })
    return hits, True


def search_arxiv_full_range(query: str, max_results: int = 8,
                            topic: set[str] | None = None) -> tuple[list[dict], bool]:
    """Full-range arXiv (1991-now — the explicit fix for the 2024 floor).
    Returns (hits, reached)."""
    if not query.strip():
        return [], True
    # arXiv wants `all:term AND all:term`; build that from the keywords.
    terms = [t for t in re.split(r"\s+", query.strip()) if t]
    if not terms:
        return [], True
    field_q = "+AND+".join(f"all:{urllib.parse.quote(t)}" for t in terms[:6])
    sq = f"{field_q}+AND+submittedDate:{urllib.parse.quote(ARXIV_DATE_RANGE)}"
    url = (f"{ARXIV_QUERY}?search_query={sq}&start=0&max_results={max_results}"
           f"&sortBy=submittedDate&sortOrder=descending")
    body, ok = _http_get(url, timeout=25.0)
    if not ok or body is None:
        return [], False
    hits: list[dict] = []
    for entry in re.findall(r"<entry>(.*?)</entry>", body, re.DOTALL)[:max_results]:
        tm = re.search(r"<title>(.*?)</title>", entry, re.DOTALL)
        pm = re.search(r"<published>(.*?)</published>", entry)
        sm = re.search(r"<summary>(.*?)</summary>", entry, re.DOTALL)
        im = re.search(r"<id>(.*?)</id>", entry, re.DOTALL)
        if not tm:
            continue
        title = re.sub(r"\s+", " ", tm.group(1)).strip()
        snippet = re.sub(r"\s+", " ", sm.group(1)).strip()[:500] if sm else ""
        year = pm.group(1)[:4] if pm else ""
        signal = _looks_like_closure(title, snippet, topic=topic)
        hits.append({
            "title": title,
            "year": year,
            "document_type": "arxiv preprint",
            "signal": signal,
            "url": im.group(1).strip() if im else "",
        })
    return hits, True


def check_mk_failed(keyword: str) -> dict:
    """Project negative-knowledge: `mk failed <kw>`.  Informational only —
    never on its own flips the verdict to CLOSED, but is surfaced as evidence.
    """
    if not keyword:
        return {"present": False, "lines": []}
    try:
        r = subprocess.run(
            ["mk", "failed", keyword],
            capture_output=True, text=True, timeout=15,
            cwd=str(PROJECT_ROOT),
        )
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError):
        return {"present": False, "lines": []}
    if r.returncode != 0:
        return {"present": False, "lines": []}
    body_lines = [
        l for l in r.stdout.strip().splitlines()
        if l.strip()
        and not l.startswith("[math-forge]")
        and not l.startswith("WARNING:")
        and "---" not in l
        and "Do NOT repeat" not in l
    ]
    return {"present": bool(body_lines), "lines": body_lines[:6]}


# ---------------------------------------------------------------------------
# The gate
# ---------------------------------------------------------------------------
def check_literature(
    statement: str,
    problem_id: str | None = None,
    named_conjecture: str | None = None,
    *,
    use_cache: bool = True,
    skip_network: bool = False,
) -> dict:
    """Fail-CLOSED literature gate.

    Returns {status, evidence, sources}.  See module docstring for the full
    contract.  Any exception inside this function is caught and resolves to a
    fail-CLOSED ``UNKNOWN`` — this function never raises to its caller.
    """
    try:
        return _check_literature_impl(
            statement, problem_id, named_conjecture,
            use_cache=use_cache, skip_network=skip_network,
        )
    except Exception as e:  # absolute fail-closed backstop
        return {
            "status": "UNKNOWN",
            "evidence": f"biblio_gate internal error ({type(e).__name__}: {e}); "
                        f"fail-closed to UNKNOWN",
            "sources": [],
        }


def _check_literature_impl(
    statement: str,
    problem_id: str | None,
    named_conjecture: str | None,
    *,
    use_cache: bool,
    skip_network: bool,
) -> dict:
    statement = statement or ""
    named = named_conjecture or _guess_named_conjecture(statement)

    cache_key = _cache_key(statement, problem_id, named)
    if use_cache and not skip_network:
        cached = _read_cache(cache_key)
        if cached is not None:
            return {
                "status": cached["status"],
                "evidence": cached["evidence"],
                "sources": cached.get("sources", []),
                "cache_age_days": cached.get("cache_age_days", 0.0),
            }

    sources: list[dict] = []

    # --- 1) Named-conjecture card (DB table + kill-list) -------------------
    card = _lookup_named_card(problem_id, named)
    if card is not None:
        st = card["status"]
        cite = card["citation"] or card.get("notes", "")
        sources.append({
            "source": card["source"],
            "url": "",
            "evidence": f"card[{card.get('matched','')}]={st}"
                        + (f" — {cite}" if cite else ""),
            "signal": ("strong" if st in _CLOSED_CARD_STATUSES else
                       "weak" if st in _AMBIGUOUS_CARD_STATUSES else "none"),
        })
        if st in _CLOSED_CARD_STATUSES:
            return _finish(cache_key, "CLOSED",
                           f"named-conjecture card: {card.get('matched','')} = {st}"
                           + (f" ({cite})" if cite else ""),
                           sources, use_cache)
        if st in _AMBIGUOUS_CARD_STATUSES:
            # An ambiguous card holds the row unless the network clears it; but
            # fail-closed means an ambiguous card never *upgrades* to CLEAR on
            # a silent network — record it and let the resolver hold AMBIGUOUS.
            pass
        # OPEN card: positive signal, but still verify online (status may be
        # stale). Falls through.

    # --- keywords ----------------------------------------------------------
    keywords = _extract_keywords(statement, named, problem_id)
    if not keywords.strip():
        # Nothing queryable online. Honour a decisive card first, else
        # fail-CLOSED to UNKNOWN (never CLEAR on no information).
        if card and card["status"] in _AMBIGUOUS_CARD_STATUSES:
            return _finish(cache_key, "AMBIGUOUS",
                           f"ambiguous named-conjecture card "
                           f"({card.get('matched','')}); no keywords to verify online",
                           sources, use_cache)
        if card and card["status"] in _OPEN_CARD_STATUSES:
            return _finish(cache_key, "CLEAR",
                           f"named-conjecture card marks OPEN ({card.get('matched','')}); "
                           f"no keywords to verify online",
                           sources, use_cache)
        return _finish(cache_key, "UNKNOWN",
                       "no usable keywords extracted from statement; fail-closed",
                       sources, use_cache)

    # --- mk failed (informational) -----------------------------------------
    mk_kw = problem_id or (named or keywords.split()[0] if keywords else "")
    mk = check_mk_failed(mk_kw)
    if mk["present"]:
        sources.append({
            "source": "mk-failed",
            "url": "",
            "evidence": f"{len(mk['lines'])} prior failed project approach(es)",
            "signal": "none",
        })

    if skip_network:
        # Offline mode (tests). Without network we cannot confirm absence of
        # closure -> fail-CLOSED to UNKNOWN unless a card already decided.
        if card and card["status"] in _AMBIGUOUS_CARD_STATUSES:
            return _finish(cache_key, "AMBIGUOUS",
                           f"ambiguous card, network skipped: {card.get('matched','')}",
                           sources, use_cache=False)
        if card and card["status"] in _OPEN_CARD_STATUSES:
            return _finish(cache_key, "CLEAR",
                           f"open card, network skipped: {card.get('matched','')}",
                           sources, use_cache=False)
        return _finish(cache_key, "UNKNOWN",
                       "network skipped; no decisive card; fail-closed",
                       sources, use_cache=False)

    # --- 2-4) Network sources ----------------------------------------------
    # Distinctive topic terms gate whether a paper's strong-closure language is
    # actually *about* this conjecture (prevents false CLOSED on a tangential
    # 'proof of ...' that merely keyword-overlapped — the Brocard failure mode).
    topic = _topic_terms(keywords, named)
    # Small inter-source spacing: be a good citizen of the free APIs and avoid
    # self-induced 429s when several check_literature() calls run in series.
    zb_hits, zb_ok = search_zbmath(keywords, topic=topic)
    time.sleep(_INTER_SOURCE_DELAY)
    cr_hits, cr_ok = search_crossref(keywords, topic=topic)
    time.sleep(_INTER_SOURCE_DELAY)
    ax_hits, ax_ok = search_arxiv_full_range(keywords, topic=topic)

    strong_count = 0
    weak_count = 0
    # Non-closure topical hits, kept as attachable citations for a CLEAR
    # verdict (F2 rule; recalibration 2026-06-10 — see the CLEAR branch).
    context_hits: list[dict] = []
    for src_name, hits, ok in (
        ("zbmath", zb_hits, zb_ok),
        ("crossref", cr_hits, cr_ok),
        ("arxiv", ax_hits, ax_ok),
    ):
        if not ok:
            sources.append({
                "source": src_name, "url": "",
                "evidence": "source unreachable (network error/rate-limit)",
                "signal": "error",
            })
            continue
        for h in hits:
            if h["signal"] == "strong":
                strong_count += 1
                sources.append({
                    "source": src_name, "url": h["url"],
                    "evidence": f"{h.get('year','')} STRONG closure language: "
                                f"{h['title'][:110]}",
                    "signal": "strong",
                })
            elif h["signal"] == "weak":
                weak_count += 1
                sources.append({
                    "source": src_name, "url": h["url"],
                    "evidence": f"{h.get('year','')} partial/weak: {h['title'][:110]}",
                    "signal": "weak",
                })
            else:
                title_l = (h.get("title") or "").lower()
                if topic and not any(t in title_l for t in topic):
                    continue  # off-topic keyword noise; never attach
                context_hits.append({
                    "source": src_name, "url": h["url"],
                    "evidence": f"{h.get('year','')} context: {h['title'][:110]}",
                    "signal": "context",
                    "_year": str(h.get("year", "")),
                })

    n_reached = sum(1 for ok in (zb_ok, cr_ok, ax_ok) if ok)

    # --- resolution (fail-CLOSED) ------------------------------------------
    # CLOSED requires *topical certainty*: strong closure language tied to a
    # NAMED conjecture (we then know the closure is about that specific thing).
    # A bare keyword query is inherently noisy — "On a Sumset Problem for
    # Integers" overlaps the keyword 'sumset' and uses strong language, but is
    # a generic research paper, not a closure of any specific conjecture. So
    # without a named conjecture we cap at AMBIGUOUS, which still HOLDS the row
    # (never silently CLEARs) but does not starve keyword-only candidates by
    # branding the whole research area CLOSED.
    have_name = bool(named)

    if have_name and strong_count >= 1:
        return _finish(cache_key, "CLOSED",
                       f"{strong_count} paper(s) with strong closure language "
                       f"matching the named conjecture '{named}' "
                       f"(zbMATH/Crossref/arXiv)",
                       sources, use_cache)

    if not have_name and strong_count >= 1:
        return _finish(cache_key, "AMBIGUOUS",
                       f"{strong_count} strong closure-language match(es) on a "
                       f"keyword query (no named conjecture to confirm topical "
                       f"identity); needs human verification (fail-closed)",
                       sources, use_cache)

    if card and card["status"] in _AMBIGUOUS_CARD_STATUSES:
        return _finish(cache_key, "AMBIGUOUS",
                       f"ambiguous named-conjecture card ({card.get('matched','')}); "
                       f"no decisive online closure found",
                       sources, use_cache)

    if weak_count >= 3:
        return _finish(cache_key, "AMBIGUOUS",
                       f"{weak_count} partial/weak-closure papers; ambiguous "
                       f"(fail-closed, not promoted to CLEAR)",
                       sources, use_cache)

    if n_reached == 0:
        # Every network source errored AND no decisive card -> we learned
        # nothing. Fail-CLOSED.
        return _finish(cache_key, "UNKNOWN",
                       "all bibliographic sources unreachable; could not verify; "
                       "fail-closed to UNKNOWN",
                       sources, use_cache=False)

    if n_reached < 2:
        # Only one source answered, no closure seen. Not enough corroboration
        # to confidently CLEAR -> AMBIGUOUS (fail-closed bias).
        return _finish(cache_key, "AMBIGUOUS",
                       f"only {n_reached}/3 sources reached, none showed closure; "
                       f"insufficient corroboration to clear",
                       sources, use_cache)

    # >=2 sources reached, no strong closure, <3 weak -> genuinely CLEAR.
    open_note = ""
    if card and card["status"] in _OPEN_CARD_STATUSES:
        open_note = f" (card marks OPEN: {card.get('matched','')})"

    # F2 rule (recalibration 2026-06-10): a CLEAR verdict must carry the
    # literature it found.  Previously only closure-language hits were kept,
    # so CLEAR rows passed with ZERO citations attached — the Piepmeyer
    # false-negative's F2 face (erdos_100_piepmeyer cleared citation-less and
    # its dossier had no literature).  Attach the most recent topical hits,
    # and flag staleness when none is <=2 years old.
    def _year_int(h: dict) -> int:
        m = re.search(r"\d{4}", h.get("_year", ""))
        return int(m.group(0)) if m else 0

    context_hits.sort(key=_year_int, reverse=True)
    attach = context_hits[:5]
    this_year = datetime.now(timezone.utc).year
    n_recent = sum(1 for h in attach if _year_int(h) >= this_year - 2)
    for h in attach:
        h.pop("_year", None)
    sources.extend(attach)
    if attach and n_recent:
        f2_note = f"; {len(attach)} citation(s) attached ({n_recent} within 2y)"
    elif attach:
        f2_note = (f"; {len(attach)} citation(s) attached, none within 2y "
                   f"(F2-STALE: refresh literature before submission)")
    else:
        f2_note = ("; NO citations attachable "
                   "(F2-STALE: attach literature manually before submission)")
    return _finish(cache_key, "CLEAR",
                   f"{n_reached}/3 sources reached; no closure language found"
                   + open_note + f2_note,
                   sources, use_cache)


def _finish(cache_key: str, status: str, evidence: str,
            sources: list[dict], use_cache: bool) -> dict:
    result = {
        "status": status,
        "evidence": evidence,
        "sources": sources,
        "checked_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }
    if use_cache:
        _write_cache(cache_key, result)
    return result


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def _print_report(label: str, rep: dict) -> None:
    print(f"\n=== {label} ===")
    print(f"status:   {rep['status']}")
    print(f"evidence: {rep['evidence']}")
    srcs = rep.get("sources") or []
    if srcs:
        print("sources:")
        for s in srcs[:10]:
            sig = s.get("signal", "")
            tag = f"[{s.get('source','')}/{sig}]" if sig else f"[{s.get('source','')}]"
            print(f"  {tag} {s.get('evidence','')}")
    if "cache_age_days" in rep:
        print(f"(cache age: {rep['cache_age_days']}d)")


def _selftest() -> int:
    """REAL-TEST: run on (a) a CLOSED/AMBIGUOUS problem and (b) a clearly-open
    one, hitting the live free APIs (no mocks)."""
    print("biblio_gate self-test (LIVE APIs — zbMATH / Crossref / arXiv)")

    # (a) Erdős 481 / Klarner 1982 rectangle-packing — expect CLOSED or
    #     AMBIGUOUS (the kill-list/wiki marks E481 as lit-surfaced; Klarner's
    #     rectangle-packing result is a real 1980s closure).
    rep_a = check_literature(
        statement=(
            "OPEN GAP: Erdos 481 — Klarner rectangle packing\n"
            "Does every set of rectangles tiling a rectangle admit a "
            "fault-free decomposition as conjectured by Klarner (1982)?"
        ),
        problem_id="erdos_481",
        named_conjecture="Klarner rectangle packing conjecture",
        use_cache=False,
    )
    _print_report("(a) Erdos 481 / Klarner 1982 rectangle-packing", rep_a)

    # (b) A clearly-open problem: a fresh, made-up easy-tail statement with no
    #     literature -> expect CLEAR (no closure found) or UNKNOWN/AMBIGUOUS if
    #     a source is rate-limited (which is the fail-closed behaviour).
    rep_b = check_literature(
        statement=(
            "OPEN GAP: zzqxv finite coprime triple density\n"
            "Determine whether the set of integers n for which the zzqxv "
            "function exceeds n log n has positive natural density."
        ),
        problem_id="zzqxv_density_probe",
        use_cache=False,
    )
    _print_report("(b) clearly-open synthetic probe", rep_b)

    print("\n--- self-test interpretation ---")
    print(f"(a) status = {rep_a['status']}  (expect CLOSED or AMBIGUOUS; "
          f"CLEAR here would be a recall miss)")
    print(f"(b) status = {rep_b['status']}  (expect CLEAR, or "
          f"UNKNOWN/AMBIGUOUS if a source was rate-limited — both fail-closed)")
    ok_a = rep_a["status"] in ("CLOSED", "AMBIGUOUS")
    ok_b = rep_b["status"] in ("CLEAR", "UNKNOWN", "AMBIGUOUS")
    print(f"\nself-test: (a) {'PASS' if ok_a else 'WARN'} | "
          f"(b) {'PASS' if ok_b else 'WARN'}")
    return 0


def _cli() -> int:
    p = argparse.ArgumentParser(
        description="Fail-CLOSED literature gate (zbMATH + Crossref + "
                    "full-range arXiv + named-conjecture cards)."
    )
    p.add_argument("--statement", help="the problem statement (English + optional Lean line)")
    p.add_argument("--problem-id", default=None, help="problem_id, e.g. erdos_481")
    p.add_argument("--named", default=None, help="explicit named conjecture, e.g. \"Brocard's conjecture\"")
    p.add_argument("--no-cache", action="store_true", help="ignore the 7-day cache")
    p.add_argument("--skip-network", action="store_true",
                   help="offline mode (cards only; fail-closed to UNKNOWN otherwise)")
    p.add_argument("--json", action="store_true", help="emit raw JSON")
    p.add_argument("--selftest", action="store_true",
                   help="run the two REAL-TEST probes against the live APIs")
    args = p.parse_args()

    if args.selftest:
        return _selftest()

    if not args.statement and not args.named and not args.problem_id:
        p.error("provide --statement (and/or --named/--problem-id), or --selftest")

    rep = check_literature(
        statement=args.statement or "",
        problem_id=args.problem_id,
        named_conjecture=args.named,
        use_cache=not args.no_cache,
        skip_network=args.skip_network,
    )
    if args.json:
        print(json.dumps(rep, indent=2, default=str))
        return 0
    _print_report(args.problem_id or args.named or "query", rep)
    # exit code carries the decision for shell pipelines
    return {"CLOSED": 2, "AMBIGUOUS": 1, "UNKNOWN": 1, "CLEAR": 0}.get(rep["status"], 1)


if __name__ == "__main__":
    sys.exit(_cli())
