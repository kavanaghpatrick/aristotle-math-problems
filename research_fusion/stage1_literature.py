#!/usr/bin/env python3
"""Stage 1 — Literature Breadth.

For a given problem_id, build a per-problem dossier of recent (2020-2026)
papers from arXiv across the home and adjacent domains, plus (for Erdős
problems) the erdosproblems.com forum thread and the formal-conjectures
source file.

Usage:
    python3 -m research_fusion.stage1_literature --problem-id erdos_938
    python3 -m research_fusion.stage1_literature \\
        --problem-id erdos_938 --force --max-papers 50

Outputs:
    research_fusion/runs/<problem_id>/01_literature.md
    research_fusion/runs/<problem_id>/01_literature.json
    research_fusion/runs/<problem_id>/problem_card.json   (auto-derived for
                                                          Erdős problems if
                                                          absent)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable
from xml.etree import ElementTree as ET

# Root paths
THIS_DIR = Path(__file__).resolve().parent
RUNS_DIR = THIS_DIR / "runs"
CACHE_TTL = 7 * 24 * 60 * 60  # 7 days

# ARXIV API endpoint — free, no auth, but throttled to ~1 req/3s.
# HTTPS is required (HTTP returns 301 which urllib does follow, but some
# arXiv mirrors break the redirect).
ARXIV_API = "https://export.arxiv.org/api/query"

# Map domain -> arXiv categories (broad enough to catch adjacent work)
DOMAIN_TO_ARXIV_CATS = {
    "nt": ["math.NT", "math.AC", "math.AG"],
    "combinatorics": ["math.CO", "math.PR"],
    "analysis": ["math.CA", "math.AP", "math.FA"],
    "algebra": ["math.RA", "math.GR", "math.RT"],
    "geometry": ["math.DG", "math.MG", "math.AG"],
    "additive_combinatorics": ["math.CO", "math.NT"],
    "analytic_nt": ["math.NT", "math.CA"],
    "diophantine": ["math.NT", "math.AG"],
    "arithmetic_geometry": ["math.AG", "math.NT"],
    "discrete": ["math.CO", "cs.DM"],
    "probability": ["math.PR"],
    "topology": ["math.AT", "math.GT"],
    "logic": ["math.LO"],
}

# Domain adjacency hints for problems that need broader nets.
ADJACENT_BY_DOMAIN = {
    "nt": [
        "analytic_nt",
        "additive_combinatorics",
        "diophantine",
        "arithmetic_geometry",
        "combinatorics",
    ],
    "combinatorics": [
        "additive_combinatorics",
        "nt",
        "probability",
        "discrete",
        "analysis",
    ],
    "algebra": ["combinatorics", "geometry", "nt", "topology"],
    "analysis": ["combinatorics", "probability", "nt"],
    "geometry": ["topology", "analysis", "algebra"],
    "discrete": ["combinatorics", "probability"],
    "probability": ["combinatorics", "analysis"],
    "logic": ["combinatorics", "discrete"],
    "topology": ["geometry", "algebra"],
}


# ─────────────────────────────────────────────────────────────────────────
# Problem-card discovery
# ─────────────────────────────────────────────────────────────────────────

def _formal_conjectures_path(problem_id: str) -> Path | None:
    """For erdos_NNN, return the formal-conjectures Lean source."""
    m = re.match(r"^erdos_(\d+)$", problem_id)
    if not m:
        return None
    n = m.group(1)
    project_root = THIS_DIR.parent
    candidate = (
        project_root
        / "formal-conjectures"
        / "FormalConjectures"
        / "ErdosProblems"
        / f"{n}.lean"
    )
    return candidate if candidate.exists() else None


def _extract_english_blurb(lean_text: str) -> str:
    """Extract the docstring above the theorem from a formal-conjectures file."""
    # The /-- ... -/ block immediately preceding the theorem.
    m = re.search(r"/--\s*(.*?)\s*-/\s*\n\s*@\[category", lean_text, re.DOTALL)
    if m:
        return m.group(1).strip()
    return ""


def _extract_lean_theorem(lean_text: str) -> str:
    """Grab the theorem statement (from `theorem ... := by sorry` block)."""
    m = re.search(
        r"(theorem\s+\w+[\s\S]*?:= by\s+sorry)", lean_text
    )
    if m:
        return m.group(1).strip()
    return ""


def _extract_erdos_number(lean_text: str) -> str | None:
    # Erdős uses ő (o-double-acute, U+0151); also tolerate ö, o, õ.
    m = re.search(r"Erd[oöőõ]s Problem (\d+)", lean_text)
    return m.group(1) if m else None


def derive_problem_card(problem_id: str) -> dict:
    """Best-effort: build a minimal problem_card.json from formal-conjectures."""
    lean_path = _formal_conjectures_path(problem_id)
    if lean_path is None:
        raise SystemExit(
            f"[stage1] No formal-conjectures source for '{problem_id}'. "
            f"Pre-write runs/{problem_id}/problem_card.json by hand."
        )
    text = lean_path.read_text(encoding="utf-8")
    blurb = _extract_english_blurb(text)
    statement = _extract_lean_theorem(text)
    n = _extract_erdos_number(text)
    # Domain hint: very crude — look for AMS tag.
    ams = re.search(r"AMS\s+(\d+)", text)
    ams_num = int(ams.group(1)) if ams else None
    domain = "nt"
    if ams_num == 5:
        domain = "combinatorics"
    elif ams_num in (26, 28, 30, 31, 32, 33, 34, 35, 39, 40, 42, 46):
        domain = "analysis"
    elif ams_num in (12, 13, 14, 15, 16, 17, 18, 19, 20):
        domain = "algebra"
    elif ams_num in (51, 52, 53, 54, 55):
        domain = "geometry"
    # Keyword heuristic: split blurb words >5 chars + erdos number
    words = re.findall(r"[A-Za-z][a-z]{4,}", blurb)
    keywords = sorted(set(w.lower() for w in words))[:8]
    if n:
        keywords.append(f"erdos {n}")
    card = {
        "problem_id": problem_id,
        "title": f"Erdős Problem {n}" if n else problem_id,
        "source_file": str(lean_path.relative_to(THIS_DIR.parent))
            if lean_path else "",
        "external_urls": (
            [f"https://www.erdosproblems.com/{n}"] if n else []
        ),
        "domain": domain,
        "adjacent_domains": ADJACENT_BY_DOMAIN.get(domain, []),
        "bare_statement": statement or "(failed to extract)",
        "keywords": keywords,
        "open_status": "open",
        "what_is_known": blurb[:500],
    }
    return card


def load_problem_card(problem_id: str, runs_dir: Path) -> dict:
    """Load or derive the problem card for this id."""
    pdir = runs_dir / problem_id
    pdir.mkdir(parents=True, exist_ok=True)
    card_path = pdir / "problem_card.json"
    if card_path.exists():
        return json.loads(card_path.read_text())
    card = derive_problem_card(problem_id)
    card_path.write_text(json.dumps(card, indent=2))
    print(f"[stage1] derived problem_card.json -> {card_path}", file=sys.stderr)
    return card


# ─────────────────────────────────────────────────────────────────────────
# Cache helpers
# ─────────────────────────────────────────────────────────────────────────

def _cache_dir(problem_id: str) -> Path:
    d = RUNS_DIR / problem_id / ".cache"
    d.mkdir(parents=True, exist_ok=True)
    return d


def _cache_key(*parts: str) -> str:
    raw = "|".join(parts)
    return hashlib.sha256(raw.encode()).hexdigest()[:16]


def _cache_get(problem_id: str, key: str) -> str | None:
    p = _cache_dir(problem_id) / f"{key}.json"
    if not p.exists():
        return None
    age = time.time() - p.stat().st_mtime
    if age > CACHE_TTL:
        return None
    return p.read_text()


def _cache_put(problem_id: str, key: str, payload: str) -> None:
    p = _cache_dir(problem_id) / f"{key}.json"
    p.write_text(payload)


# ─────────────────────────────────────────────────────────────────────────
# arXiv fetcher (atom XML)
# ─────────────────────────────────────────────────────────────────────────

ATOM_NS = {
    "a": "http://www.w3.org/2005/Atom",
    "arxiv": "http://arxiv.org/schemas/atom",
}


def _arxiv_query(
    keywords: list[str],
    arxiv_cats: list[str],
    year_min: int = 2020,
    year_max: int = 2026,
    max_results: int = 12,
) -> str:
    """Build an arXiv API URL."""
    kw_clause = " OR ".join(f'all:"{k}"' for k in keywords if k)
    cat_clause = " OR ".join(f"cat:{c}" for c in arxiv_cats)
    query = (
        f"({kw_clause}) AND ({cat_clause}) AND submittedDate:"
        f"[{year_min}01010000 TO {year_max}12312359]"
    )
    params = urllib.parse.urlencode({
        "search_query": query,
        "start": "0",
        "max_results": str(max_results),
        "sortBy": "submittedDate",
        "sortOrder": "descending",
    })
    return f"{ARXIV_API}?{params}"


def _arxiv_parse(xml_text: str) -> list[dict]:
    out = []
    root = ET.fromstring(xml_text)
    for entry in root.findall("a:entry", ATOM_NS):
        eid_node = entry.find("a:id", ATOM_NS)
        title_node = entry.find("a:title", ATOM_NS)
        summary_node = entry.find("a:summary", ATOM_NS)
        published_node = entry.find("a:published", ATOM_NS)
        if eid_node is None or title_node is None:
            continue
        eid = (eid_node.text or "").strip()
        # arXiv id at the tail: http://arxiv.org/abs/2401.12345v2
        arxiv_id = eid.rsplit("/", 1)[-1].split("v", 1)[0] if eid else None
        title = " ".join((title_node.text or "").split())
        summary = " ".join((summary_node.text or "").split()) \
                  if summary_node is not None else ""
        year = None
        if published_node is not None and published_node.text:
            year_match = re.match(r"(\d{4})", published_node.text)
            year = int(year_match.group(1)) if year_match else None
        authors = []
        for a in entry.findall("a:author/a:name", ATOM_NS):
            if a.text:
                authors.append(a.text.strip())
        out.append({
            "title": title,
            "authors": authors,
            "arxiv_id": arxiv_id,
            "year": year,
            "summary": summary[:1200],
            "url": eid,
        })
    return out


def _http_get(url: str, timeout: int = 30) -> str:
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "research-fusion-stage1/0.1"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read().decode("utf-8", errors="replace")


def fetch_arxiv_for_domain(
    problem_id: str,
    keywords: list[str],
    domain: str,
    cats: list[str],
    max_results: int = 10,
    force: bool = False,
    max_retries: int = 4,
) -> list[dict]:
    """Pull arXiv papers for one domain. Cached 7 days. Backs off on 429."""
    key = _cache_key("arxiv", domain, ",".join(sorted(keywords)),
                     ",".join(sorted(cats)))
    if not force:
        hit = _cache_get(problem_id, key)
        if hit:
            return json.loads(hit)
    url = _arxiv_query(keywords, cats, max_results=max_results)
    papers: list[dict] = []
    last_exc: Exception | None = None
    for attempt in range(max_retries):
        try:
            xml = _http_get(url, timeout=30)
            papers = _arxiv_parse(xml)
            break
        except urllib.error.HTTPError as exc:
            last_exc = exc
            if exc.code == 429:
                # Exponential backoff: 5s, 10s, 20s, 40s.
                wait = 5 * (2 ** attempt)
                print(
                    f"[stage1] arxiv 429 for {domain}, sleeping {wait}s "
                    f"(attempt {attempt+1}/{max_retries})", file=sys.stderr,
                )
                time.sleep(wait)
                continue
            print(f"[stage1] arxiv HTTPError {exc.code} for {domain}: {exc}",
                  file=sys.stderr)
            break
        except (urllib.error.URLError, ET.ParseError, TimeoutError,
                OSError) as exc:
            last_exc = exc
            wait = 4 * (attempt + 1)
            print(f"[stage1] arxiv error for {domain} (attempt {attempt+1}): "
                  f"{exc}; sleeping {wait}s", file=sys.stderr)
            time.sleep(wait)
            continue
    if not papers and last_exc is not None:
        print(f"[stage1] arxiv giving up on {domain} after {max_retries} "
              f"attempts: {last_exc}", file=sys.stderr)
    # Throttle to be polite — arXiv API recommends >=3s between requests.
    time.sleep(3.5)
    # Tag every paper with the domain it was retrieved for.
    for p in papers:
        p["domain_tag"] = domain
    _cache_put(problem_id, key, json.dumps(papers))
    return papers


# ─────────────────────────────────────────────────────────────────────────
# erdosproblems.com forum thread (best effort, plain GET)
# ─────────────────────────────────────────────────────────────────────────

def fetch_erdos_forum(problem_id: str, force: bool = False) -> str | None:
    m = re.match(r"^erdos_(\d+)$", problem_id)
    if not m:
        return None
    n = m.group(1)
    key = _cache_key("erdos_forum", n)
    if not force:
        hit = _cache_get(problem_id, key)
        if hit:
            return hit
    url = f"https://www.erdosproblems.com/{n}"
    try:
        html = _http_get(url, timeout=10)
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        print(f"[stage1] erdosproblems.com fetch failed for {n}: {exc}",
              file=sys.stderr)
        return None
    # Crude text extraction — strip tags.
    text = re.sub(r"<script[\s\S]*?</script>", " ", html)
    text = re.sub(r"<style[\s\S]*?</style>", " ", text)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"\s+", " ", text).strip()
    _cache_put(problem_id, key, text[:8000])
    return text[:8000]


# ─────────────────────────────────────────────────────────────────────────
# Aggregation + emit
# ─────────────────────────────────────────────────────────────────────────

def _normalize_keywords(card: dict) -> list[str]:
    raw = list(card.get("keywords", []))
    # Add the problem title's standalone words (length >=4).
    if card.get("title"):
        for w in re.findall(r"[A-Za-z]{4,}", card["title"]):
            raw.append(w.lower())
    # Drop super-generic words that flood arxiv.
    BAN = {
        "problem", "theorem", "conjecture", "open", "known", "result",
        "number", "numbers", "integer", "integers", "function", "case",
        "show", "every", "given", "where", "which", "their", "there",
        "above", "below", "called", "erdos", "sequence", "terms",
        "cdots", "finitely",
    }
    out: list[str] = []
    seen = set()
    for w in raw:
        wl = w.strip().lower()
        if not wl or wl in BAN or wl in seen or len(wl) < 4:
            continue
        seen.add(wl)
        out.append(wl)
    return out[:4]  # arXiv API behaves better with fewer keywords.


def run_stage1(problem_id: str, max_papers: int = 50,
               force: bool = False,
               keyword_override: list[str] | None = None) -> dict:
    """End-to-end Stage 1 execution. Returns the structured payload."""
    runs_dir = RUNS_DIR
    card = load_problem_card(problem_id, runs_dir)
    pdir = runs_dir / problem_id
    if keyword_override:
        keywords = keyword_override
        # Update the problem card with the override so the dossier is honest.
        card["keywords"] = keyword_override
        (pdir / "problem_card.json").write_text(json.dumps(card, indent=2))
    else:
        keywords = _normalize_keywords(card)
        if not keywords:
            keywords = [card.get("title", problem_id).lower()]
    domains: list[str] = [card.get("domain", "nt")]
    for d in card.get("adjacent_domains", []) or []:
        if d not in domains:
            domains.append(d)
    if not domains:
        domains = ["nt"]

    per_domain_cap = max(2, max_papers // max(1, len(domains)))
    all_papers: list[dict] = []
    for d in domains:
        cats = DOMAIN_TO_ARXIV_CATS.get(d, DOMAIN_TO_ARXIV_CATS["nt"])
        papers = fetch_arxiv_for_domain(
            problem_id, keywords, d, cats,
            max_results=per_domain_cap, force=force,
        )
        # Deduplicate by arxiv_id within this run.
        seen_ids = {p["arxiv_id"] for p in all_papers if p.get("arxiv_id")}
        for p in papers:
            if p.get("arxiv_id") and p["arxiv_id"] in seen_ids:
                continue
            all_papers.append(p)
            seen_ids.add(p.get("arxiv_id"))
        if len(all_papers) >= max_papers:
            break
    all_papers = all_papers[:max_papers]

    forum_blurb = fetch_erdos_forum(problem_id, force=force) or ""

    # Build relevance for each paper as a simple heuristic until Grok pass is
    # wired in: cite that the summary mentions ANY of the keywords.
    for p in all_papers:
        summ = p.get("summary", "").lower()
        hits = [kw for kw in keywords if kw in summ]
        if hits:
            p["relevance"] = (
                f"Mentions {', '.join(hits[:3])}; potential structural overlap."
            )
        else:
            p["relevance"] = "No direct keyword match; flagged as adjacent."

    payload = {
        "problem_id": problem_id,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "paper_count": len(all_papers),
        "domains_covered": domains,
        "keywords_used": keywords,
        "papers": all_papers,
        "erdos_forum_excerpt": forum_blurb[:2000] if forum_blurb else "",
        "lean_source_path": card.get("source_file", ""),
    }

    # Write JSON
    (pdir / "01_literature.json").write_text(json.dumps(payload, indent=2))

    # Write markdown
    md_lines: list[str] = []
    md_lines.append(f"# Literature breadth — {problem_id}")
    md_lines.append(
        f"Date: {datetime.utcnow().strftime('%Y-%m-%d')}  Stage: 1"
    )
    md_lines.append(f"Domains queried: {', '.join(domains)}")
    md_lines.append(f"Keywords used: {', '.join(keywords)}")
    md_lines.append(f"Papers retrieved: {len(all_papers)}")
    if card.get("source_file"):
        md_lines.append(f"Lean source: `{card['source_file']}`")
    md_lines.append("")
    if card.get("external_urls"):
        md_lines.append("## External references")
        for u in card["external_urls"]:
            md_lines.append(f"- {u}")
        md_lines.append("")
    if forum_blurb:
        md_lines.append("## erdosproblems.com excerpt")
        md_lines.append("```")
        md_lines.append(forum_blurb[:1200])
        md_lines.append("```")
        md_lines.append("")

    # Group papers by domain tag
    by_domain: dict[str, list[dict]] = {}
    for p in all_papers:
        by_domain.setdefault(p.get("domain_tag", "unknown"), []).append(p)

    for d in domains:
        ps = by_domain.get(d, [])
        md_lines.append(f"## Domain: {d} ({len(ps)}/{per_domain_cap})")
        if not ps:
            md_lines.append("No 2020-2026 papers found for this domain.")
            md_lines.append("")
            continue
        for p in ps:
            title = p.get("title", "(untitled)")
            aid = p.get("arxiv_id") or "n/a"
            md_lines.append(f"### {title} (arxiv:{aid})")
            authors = p.get("authors") or []
            if authors:
                md_lines.append(
                    f"- Authors: {', '.join(authors[:6])}"
                    + (" et al." if len(authors) > 6 else "")
                )
            md_lines.append(f"- Year: {p.get('year', 'n/a')}")
            md_lines.append(
                f"- Abstract: {p.get('summary', '')[:1000]}"
            )
            md_lines.append(f"- Relevance: {p.get('relevance', '')}")
            md_lines.append("")
    md_text = "\n".join(md_lines)
    (pdir / "01_literature.md").write_text(md_text)

    print(
        f"[stage1] {problem_id}: {len(all_papers)} papers, "
        f"{len(domains)} domains -> {pdir / '01_literature.md'}",
        file=sys.stderr,
    )
    return payload


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Stage 1 — Literature Breadth")
    p.add_argument("--problem-id", required=True)
    p.add_argument("--max-papers", type=int, default=50)
    p.add_argument("--force", action="store_true",
                   help="Bypass the 7-day cache.")
    p.add_argument("--keywords", default=None,
                   help="Comma-separated override for keyword list (skips "
                        "auto-extraction).")
    args = p.parse_args(argv)
    kw_override = None
    if args.keywords:
        kw_override = [k.strip().lower() for k in args.keywords.split(",")
                       if k.strip()]
    try:
        run_stage1(args.problem_id, args.max_papers, args.force, kw_override)
    except KeyboardInterrupt:
        return 130
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
