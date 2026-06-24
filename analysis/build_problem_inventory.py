#!/usr/bin/env python3
"""
Build canonical problem inventory across all sources.

Output:
  - /Users/patrickkavanagh/math/analysis/problem_inventory_may30.csv
  - /Users/patrickkavanagh/math/analysis/problem_inventory_summary_may30.md

Sources:
  1. formal-conjectures (Lean files under formal-conjectures/FormalConjectures/**)
  2. problem-databases/problems.db
  3. submissions/tracking.db (for already_tried + count aggregation)
  4. math-forge knowledge.db (for additional problem IDs)
  5. docs/research/*.md (manual targets)
"""
import csv
import os
import re
import sqlite3
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path("/Users/patrickkavanagh/math")
ANALYSIS = ROOT / "analysis"
ANALYSIS.mkdir(parents=True, exist_ok=True)

CSV_PATH = ANALYSIS / "problem_inventory_may30.csv"
MD_PATH = ANALYSIS / "problem_inventory_summary_may30.md"

# ---------------------------------------------------------------------------
# Step 1: Aggregate per-problem submission stats from tracking.db
# ---------------------------------------------------------------------------
tracking_db = ROOT / "submissions" / "tracking.db"
con_tr = sqlite3.connect(str(tracking_db))
cur_tr = con_tr.cursor()

# Map problem_id -> {status: count}
prob_status_counts = defaultdict(lambda: defaultdict(int))
cur_tr.execute(
    """SELECT problem_id, status, COUNT(*) FROM submissions
       WHERE problem_id IS NOT NULL AND problem_id != ''
       GROUP BY problem_id, status"""
)
for pid, status, cnt in cur_tr.fetchall():
    prob_status_counts[pid][status or "unknown"] += cnt

# Also collect contribution flags / target_resolved for "near miss"
cur_tr.execute(
    """SELECT problem_id, target_resolved, status, COUNT(*)
       FROM submissions
       WHERE problem_id IS NOT NULL AND problem_id != ''
       GROUP BY problem_id, target_resolved, status"""
)
prob_near_miss = defaultdict(int)
for pid, target_resolved, status, cnt in cur_tr.fetchall():
    # Near miss = compiled_partial OR (compiled_no_advance with target_resolved=NULL)
    if status == "compiled_partial":
        prob_near_miss[pid] += cnt

def get_counts(pid):
    """Return (advance, disproof, no_advance, partial, total)."""
    sc = prob_status_counts.get(pid, {})
    advance = sc.get("compiled_advance", 0)
    disproof = sc.get("disproven", 0)
    no_advance = sc.get("compiled_no_advance", 0)
    partial = sc.get("compiled_partial", 0)
    fail = sc.get("compile_failed", 0)
    submitted = sc.get("submitted", 0)
    total = sum(sc.values())
    return advance, disproof, no_advance, partial, fail, submitted, total

# ---------------------------------------------------------------------------
# Step 2: Parse formal-conjectures Lean files
# ---------------------------------------------------------------------------
FC_ROOT = ROOT / "formal-conjectures" / "FormalConjectures"

CATEGORY_RE = re.compile(r"@\[category\s+([a-zA-Z_]+(?:\s+[a-zA-Z_]+)*)")
THEOREM_RE = re.compile(r"theorem\s+([A-Za-z_][\w\.\']*)")

# Domain hints from AMS codes
AMS_RE = re.compile(r"AMS\s+(\d+)")
AMS_TO_DOMAIN = {
    "05": "combinatorics",
    "11": "nt",
    "12": "algebra",
    "13": "algebra",
    "14": "algebra",
    "15": "algebra",
    "16": "algebra",
    "17": "algebra",
    "18": "algebra",
    "19": "algebra",
    "20": "algebra",
    "26": "analysis",
    "28": "analysis",
    "30": "analysis",
    "31": "analysis",
    "32": "analysis",
    "33": "analysis",
    "34": "analysis",
    "35": "analysis",
    "37": "dynamics",
    "39": "analysis",
    "40": "analysis",
    "41": "analysis",
    "42": "analysis",
    "43": "analysis",
    "44": "analysis",
    "45": "analysis",
    "46": "analysis",
    "47": "analysis",
    "49": "analysis",
    "51": "geometry",
    "52": "geometry",
    "53": "geometry",
    "54": "topology",
    "55": "topology",
    "57": "topology",
    "58": "geometry",
    "60": "probability",
    "62": "stats",
    "65": "numerical",
    "68": "cs",
    "70": "physics",
    "76": "physics",
    "81": "physics",
    "82": "physics",
    "90": "operations",
    "91": "social",
    "94": "info-theory",
    "97": "education",
}

def infer_domain_from_text(text, fname):
    """Heuristic domain inference."""
    ams_codes = AMS_RE.findall(text)
    for c in ams_codes:
        if c in AMS_TO_DOMAIN:
            return AMS_TO_DOMAIN[c]
    # Fallback heuristics from name
    nlow = fname.lower() + " " + text.lower()
    if any(k in nlow for k in ["prime", "fermat", "perfect", "totient", "carmichael", "divisor", "number theor", "diophant", "modular"]):
        return "nt"
    if any(k in nlow for k in ["graph", "ramsey", "hypergraph", "combinat", "cover", "tuza", "tournament"]):
        return "combinatorics"
    if any(k in nlow for k in ["group", "ring", "field", "algebra", "polynomial", "ideal", "matrix"]):
        return "algebra"
    if any(k in nlow for k in ["analytic", "measure", "integral", "differential", "fourier", "function"]):
        return "analysis"
    if any(k in nlow for k in ["topolog", "manifold", "homotopy", "homolog"]):
        return "topology"
    if any(k in nlow for k in ["dynamic", "ergodic", "chaos"]):
        return "dynamics"
    if any(k in nlow for k in ["probability", "stochastic", "random"]):
        return "probability"
    if any(k in nlow for k in ["geometr", "polytope", "rupert"]):
        return "geometry"
    return "unknown"

def parse_lean_file(path):
    """
    Yield (theorem_name, is_open, title_hint, domain) for each theorem in file.
    is_open = True iff @[category research open] appears.
    """
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return
    domain = infer_domain_from_text(text, path.stem)

    # Find #-heading title
    title = path.stem
    m = re.search(r"^#\s+(.+?)$", text, re.MULTILINE)
    if m:
        title = m.group(1).strip()[:200]

    # Find each @[category ...] block followed by a theorem name
    # We pair them up by scanning the file:
    pos = 0
    while True:
        cm = CATEGORY_RE.search(text, pos)
        if not cm:
            break
        cat = cm.group(1).strip()
        is_open = "research open" in cat
        is_research = "research" in cat
        # find next theorem after this category block
        # category attribute ends at ]; find next theorem keyword
        end_attr = text.find("]", cm.end())
        if end_attr == -1:
            pos = cm.end()
            continue
        tm = THEOREM_RE.search(text, end_attr)
        if not tm:
            pos = cm.end()
            continue
        thm = tm.group(1)
        yield (thm, is_open, is_research, cat, title, domain)
        pos = tm.end()

# Map subfolder -> source label
def source_label(subdir):
    if subdir == "ErdosProblems":
        return "formal-conjectures-erdos"
    if subdir == "Wikipedia":
        return "formal-conjectures-wikipedia"
    return f"formal-conjectures-other-{subdir.lower()}"

# Collect all formal-conjectures theorems
fc_theorems = []  # (source, problem_id, title, domain, formal_path, is_open, is_research)
for subdir in sorted(os.listdir(FC_ROOT)):
    subpath = FC_ROOT / subdir
    if not subpath.is_dir() or subdir == "Util":
        continue
    src = source_label(subdir)
    for lean_file in subpath.rglob("*.lean"):
        rel = str(lean_file.relative_to(ROOT))
        for thm, is_open, is_research, cat, title, domain in parse_lean_file(lean_file):
            # problem_id from the theorem name
            pid = thm
            fc_theorems.append({
                "source": src,
                "problem_id": pid,
                "title": title,
                "domain": domain,
                "formal_path": rel,
                "is_open": is_open,
                "is_research": is_research,
                "category_raw": cat,
                "lean_file_stem": lean_file.stem,
                "subdir": subdir,
            })

print(f"Parsed {len(fc_theorems)} theorems from formal-conjectures", file=sys.stderr)

# ---------------------------------------------------------------------------
# Step 3: Parse problem-databases/problems.db
# ---------------------------------------------------------------------------
pd_db = ROOT / "problem-databases" / "problems.db"
con_pd = sqlite3.connect(str(pd_db))
cur_pd = con_pd.cursor()

DOMAIN_NORMALIZE = {
    "number": "nt",
    "number theory": "nt",
    "nt": "nt",
    "nt.number-theory": "nt",
    "combinatorics": "combinatorics",
    "co.combinatorics": "combinatorics",
    "graph": "combinatorics",
    "graph theory": "combinatorics",
    "algebra": "algebra",
    "ag.algebraic-geometry": "algebra",
    "gr.group-theory": "algebra",
    "rt.representation-theory": "algebra",
    "analysis": "analysis",
    "fa.functional-analysis": "analysis",
    "ca.classical-analysis-and-odes": "analysis",
    "ap.analysis-of-pdes": "analysis",
    "geometry": "geometry",
    "mg.metric-geometry": "geometry",
    "dg.differential-geometry": "geometry",
    "topology": "topology",
    "at.algebraic-topology": "topology",
    "gn.general-topology": "topology",
    "logic": "logic",
    "lo.logic": "logic",
    "set-theory": "logic",
    "dynamics": "dynamics",
    "ergodic-theory": "dynamics",
    "probability": "probability",
    "pr.probability": "probability",
    "computer": "cs",
    "cs": "cs",
}

def norm_domain(d):
    if not d:
        return "unknown"
    d = d.strip().lower()
    if d in DOMAIN_NORMALIZE:
        return DOMAIN_NORMALIZE[d]
    # Pick first token
    tok = d.split()[0]
    return DOMAIN_NORMALIZE.get(tok, tok)

pd_rows = []
cur_pd.execute(
    """SELECT id, source, source_id, name, domain, lean_file_path, status FROM problems"""
)
for rid, src, sid, name, dom, lean_path, status in cur_pd.fetchall():
    pd_rows.append({
        "db_id": rid,
        "source": src,
        "source_id": sid,
        "name": name or "",
        "domain": norm_domain(dom),
        "lean_file_path": lean_path or "",
        "status": status or "open",
    })
print(f"Parsed {len(pd_rows)} rows from problems.db", file=sys.stderr)

# ---------------------------------------------------------------------------
# Step 4: math-forge knowledge.db problems
# ---------------------------------------------------------------------------
kb_db = ROOT / "math-forge" / "data" / "knowledge.db"
con_kb = sqlite3.connect(str(kb_db))
cur_kb = con_kb.cursor()
kb_rows = []
cur_kb.execute("SELECT id, name, domain_id, status, statement FROM problems")
for pid, name, dom, status, stmt in cur_kb.fetchall():
    kb_rows.append({
        "problem_id": pid,
        "name": name or pid,
        "domain": dom or "unknown",
        "status": status or "open",
    })
print(f"Parsed {len(kb_rows)} rows from knowledge.db", file=sys.stderr)

# ---------------------------------------------------------------------------
# Step 5: Build canonical inventory rows
# ---------------------------------------------------------------------------
rows = []

# 5a. formal-conjectures rows (only research-tagged: open OR solved)
# We restrict to research-tagged theorems to filter out infrastructure variants.
for fc in fc_theorems:
    if not fc["is_research"]:
        continue
    pid = fc["problem_id"]
    # Possible matching IDs in tracking.db
    candidates = set()
    candidates.add(pid)
    candidates.add(pid.lower())
    candidates.add(pid.replace(".", "_"))
    # Try ErdosProblems naming: file 203.lean → erdos203 / erdos_203 / Erdos203 / 203
    if fc["subdir"] == "ErdosProblems":
        stem = fc["lean_file_stem"]
        candidates.update({
            f"erdos{stem}",
            f"erdos_{stem}",
            f"Erdos{stem}",
            stem,
        })
        # Strip variants suffix: erdos_647.variants.tau_ge_two → match against erdos_647 / erdos647
        base = pid.split(".")[0]
        candidates.add(base)
        candidates.add(base.replace("_", ""))
    # For Wikipedia/Other: match by lower-snake stem (BrocardConjecture → brocard / brocard_conjecture)
    if fc["subdir"] != "ErdosProblems":
        stem = fc["lean_file_stem"]
        snake = re.sub(r"(?<!^)(?=[A-Z])", "_", stem).lower()
        candidates.add(snake)
        candidates.add(stem.lower())
        # Also strip trailing "_conjecture", "_problem" to match short forms
        for suffix in ("_conjecture", "_problem", "_problems", "_question"):
            if snake.endswith(suffix):
                candidates.add(snake[:-len(suffix)])
        # Match the base of the theorem name
        base = pid.split(".")[0]
        candidates.add(base)
        for suffix in ("_conjecture", "_problem", "_problems", "_primes", "_groups"):
            if base.endswith(suffix):
                candidates.add(base[:-len(suffix)])
        # Match first 1-3 tokens of theorem snake_case (feit_thompson_primes → feit_thompson)
        tokens = base.split("_")
        if len(tokens) >= 2:
            candidates.add("_".join(tokens[:2]))
        if len(tokens) >= 3:
            candidates.add("_".join(tokens[:3]))
        # Also try the snake stem 1-2 tokens (Leinster → leinster)
        snake_tokens = snake.split("_")
        if snake_tokens:
            candidates.add(snake_tokens[0])
            if len(snake_tokens) >= 2:
                candidates.add("_".join(snake_tokens[:2]))
    matched_ids = []
    advance = disproof = no_advance = partial = 0
    near_miss = 0
    fail = submitted = total = 0
    for c in candidates:
        if c and c in prob_status_counts:
            matched_ids.append(c)
            a, d, na, p, f, s, t = get_counts(c)
            advance += a
            disproof += d
            no_advance += na
            partial += p
            fail += f
            submitted += s
            total += t
            near_miss += prob_near_miss.get(c, 0)
    matched = matched_ids[0] if matched_ids else None
    already_tried = 1 if total > 0 else 0
    # Status summary
    parts = []
    if "research open" in fc["category_raw"]:
        parts.append("OPEN")
    if "research solved" in fc["category_raw"]:
        parts.append("SOLVED_UPSTREAM")
    if total:
        parts.append(f"tried_{total}")
        if advance:
            parts.append(f"adv_{advance}")
        if disproof:
            parts.append(f"dis_{disproof}")
        if no_advance:
            parts.append(f"no_adv_{no_advance}")
        if partial:
            parts.append(f"part_{partial}")
        if fail:
            parts.append(f"fail_{fail}")
    status_summary = ";".join(parts) if parts else "open"

    rows.append({
        "source": fc["source"],
        "problem_id": pid,
        "title": fc["title"],
        "domain": fc["domain"],
        "formal_path": fc["formal_path"],
        "already_tried": already_tried,
        "advance_count": advance,
        "disproof_count": disproof,
        "near_miss_count": near_miss + partial,
        "no_advance_count": no_advance,
        "status_summary": status_summary,
        "_is_open": "research open" in fc["category_raw"],
        "_matched_tracking_id": matched,
        "_matched_all": matched_ids,
        "_lean_file_stem": fc["lean_file_stem"],
        "_subdir": fc["subdir"],
    })

# Track FC pids to avoid pd duplicates
fc_pids = {r["problem_id"] for r in rows}

# 5b. problem-databases rows for sources OTHER than 'formal-conjectures' or 'erdos'
# (those are largely covered by the Lean parsing above)
for pd_r in pd_rows:
    src_lower = (pd_r["source"] or "").lower()
    if src_lower in ("formal-conjectures", "erdos"):
        # Skip - covered by Lean parsing. But include rows where lean file is NOT present
        # so we have entries for problems without Lean formalizations.
        if pd_r["lean_file_path"]:
            continue
        # For Erdős problems without Lean files, include as problem-databases
        pid = f"erdos_{pd_r['source_id']}" if src_lower == "erdos" else f"{pd_r['source']}_{pd_r['source_id']}"
        # Skip if FC already has it (avoid duplicate row)
        if pid in fc_pids:
            continue
        source = "problem-databases"
    else:
        source = "problem-databases"
        pid = f"{src_lower}_{pd_r['source_id']}"

    # Check tracking
    candidates = [pid, pd_r.get("source_id"), pd_r["name"]]
    advance = disproof = no_advance = partial = fail = submitted = total = 0
    near_miss = 0
    matched = None
    for c in candidates:
        if c and c in prob_status_counts:
            matched = c
            a, d, na, p, f, s, t = get_counts(c)
            advance += a
            disproof += d
            no_advance += na
            partial += p
            fail += f
            submitted += s
            total += t
            near_miss += prob_near_miss.get(c, 0)
    already_tried = 1 if total > 0 else 0
    parts = [pd_r["status"]]
    if total:
        parts.append(f"tried_{total}")
        if advance: parts.append(f"adv_{advance}")
        if disproof: parts.append(f"dis_{disproof}")
    status_summary = ";".join(parts)

    rows.append({
        "source": source,
        "problem_id": pid,
        "title": pd_r["name"][:200],
        "domain": pd_r["domain"],
        "formal_path": pd_r["lean_file_path"],
        "already_tried": already_tried,
        "advance_count": advance,
        "disproof_count": disproof,
        "near_miss_count": near_miss + partial,
        "no_advance_count": no_advance,
        "status_summary": status_summary,
        "_is_open": pd_r["status"] == "open",
        "_matched_tracking_id": matched,
        "_lean_file_stem": "",
        "_subdir": src_lower,
    })

# 5c. knowledge.db additional problems (small set)
existing_pids = {r["problem_id"] for r in rows}
for kb_r in kb_rows:
    pid = kb_r["problem_id"]
    if pid in existing_pids:
        continue
    a, d, na, p, f, s, t = (0,)*7
    near_miss = 0
    matched = None
    if pid in prob_status_counts:
        matched = pid
        a, d, na, p, f, s, t = get_counts(pid)
        near_miss = prob_near_miss.get(pid, 0)
    already_tried = 1 if t > 0 else 0
    rows.append({
        "source": "docs-research",
        "problem_id": pid,
        "title": kb_r["name"],
        "domain": kb_r["domain"],
        "formal_path": "",
        "already_tried": already_tried,
        "advance_count": a,
        "disproof_count": d,
        "near_miss_count": near_miss + p,
        "no_advance_count": na,
        "status_summary": kb_r["status"] + (f";tried_{t}" if t else ""),
        "_is_open": kb_r["status"] == "open",
        "_matched_tracking_id": matched,
        "_lean_file_stem": "",
        "_subdir": "",
    })

# 5d. Also dump submissions that have problem_ids NOT yet in inventory
matched_pids = set()
for r in rows:
    if r.get("_matched_all"):
        matched_pids.update(r["_matched_all"])
    if r.get("_matched_tracking_id"):
        matched_pids.add(r["_matched_tracking_id"])
unmatched = []
for pid in prob_status_counts:
    if pid in matched_pids:
        continue
    # Skip uuid-shaped
    if re.match(r"^[0-9a-f]{8}-[0-9a-f]{4}", pid):
        continue
    a, d, na, p, f, s, t = get_counts(pid)
    rows.append({
        "source": "tracking-only",
        "problem_id": pid,
        "title": pid,
        "domain": "unknown",
        "formal_path": "",
        "already_tried": 1,
        "advance_count": a,
        "disproof_count": d,
        "near_miss_count": prob_near_miss.get(pid, 0) + p,
        "no_advance_count": na,
        "status_summary": f"tried_{t};fail_{f};no_adv_{na};adv_{a};dis_{d};part_{p};sub_{s}",
        "_is_open": True,
        "_matched_tracking_id": pid,
        "_lean_file_stem": "",
        "_subdir": "",
    })
    unmatched.append(pid)

# ---------------------------------------------------------------------------
# Step 6: Write CSV
# ---------------------------------------------------------------------------
CSV_FIELDS = [
    "source",
    "problem_id",
    "title",
    "domain",
    "formal_path",
    "already_tried",
    "advance_count",
    "disproof_count",
    "near_miss_count",
    "no_advance_count",
    "status_summary",
]

# Final domain normalization pass over all rows
for r in rows:
    r["domain"] = norm_domain(r["domain"])

with open(CSV_PATH, "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=CSV_FIELDS, quoting=csv.QUOTE_MINIMAL)
    w.writeheader()
    for r in rows:
        w.writerow({k: r[k] for k in CSV_FIELDS})

print(f"Wrote {len(rows)} rows to {CSV_PATH}", file=sys.stderr)

# ---------------------------------------------------------------------------
# Step 7: Aggregate stats and write summary MD
# ---------------------------------------------------------------------------
from collections import Counter

by_source = Counter(r["source"] for r in rows)
already_tried = sum(1 for r in rows if r["already_tried"])
untouched = sum(1 for r in rows if not r["already_tried"])
by_domain = Counter(r["domain"] for r in rows)
open_rows = [r for r in rows if r["_is_open"]]
open_untouched = [r for r in open_rows if not r["already_tried"]]

# Recent Mathlib formalization candidates
# Heuristic: untouched OPEN problems in formal-conjectures, with file stem == small integer
# (recent Erdős problems and Wikipedia conjectures formalized recently)
def is_recent_mathlib(r):
    if r["already_tried"]:
        return False
    if not r["_is_open"]:
        return False
    if r["source"] not in ("formal-conjectures-erdos", "formal-conjectures-wikipedia"):
        return False
    return True

recent_candidates_raw = [r for r in rows if is_recent_mathlib(r)]
# Prefer "primary" theorems over variants/parts
def is_primary(r):
    pid = r["problem_id"]
    return ".variants." not in pid and ".parts." not in pid

# Dedupe by lean file - keep primary if available, else first variant
by_file = {}
for r in recent_candidates_raw:
    key = r["formal_path"]
    if key not in by_file:
        by_file[key] = r
    else:
        cur = by_file[key]
        if is_primary(r) and not is_primary(cur):
            by_file[key] = r

recent_candidates = list(by_file.values())

def rank_recent(r):
    domain_pref = {"nt": 0, "combinatorics": 1, "algebra": 2, "analysis": 3}.get(r["domain"], 5)
    primary_pref = 0 if is_primary(r) else 1
    # Wikipedia has lower numeric value than Erdős stems; prefer Erdős with low numbers
    stem = r.get("_lean_file_stem", "")
    try:
        stem_num = int(stem)
    except Exception:
        stem_num = 99999
    src_pref = 0 if r["source"] == "formal-conjectures-erdos" else 1
    return (primary_pref, domain_pref, src_pref, stem_num)

recent_candidates.sort(key=rank_recent)

# Near-miss candidates (attempted but compiled_partial or low advance)
# Filter to real problems (skip slot infrastructure IDs, helper lemmas)
def is_real_problem(r):
    pid = r["problem_id"]
    if pid.startswith("slot"):
        return False
    if any(pid.startswith(p) for p in ("PROOF_TEMPLATE", "M_edge", "cycle4_", "cycle_4_", "nu4_", "nu_4_", "tuza_split", "tuza_counter", "tuza_tau", "frontier")):
        return False
    if "_RESUB" in pid or "_v2" in pid or "_v3" in pid:
        return False
    if re.match(r"^\d+$", pid):
        return False
    return True

near_miss_rows = [
    r for r in rows
    if r["already_tried"]
    and is_real_problem(r)
    and (r["near_miss_count"] > 0 or (r["no_advance_count"] >= 3 and r["advance_count"] == 0))
]
near_miss_rows.sort(key=lambda r: (-r["near_miss_count"], -r["no_advance_count"]))

with open(MD_PATH, "w") as fh:
    fh.write("# Problem Inventory Summary (May 30, 2026)\n\n")
    fh.write(f"Total rows: **{len(rows)}**\n\n")
    fh.write(f"Already attempted (>=1 submission): **{already_tried}**\n\n")
    fh.write(f"Untouched: **{untouched}**\n\n")
    fh.write("## Source breakdown\n\n")
    fh.write("| Source | Count |\n|---|---:|\n")
    for src, n in by_source.most_common():
        fh.write(f"| {src} | {n} |\n")
    fh.write("\n## Domain distribution\n\n")
    fh.write("| Domain | Count |\n|---|---:|\n")
    for dom, n in by_domain.most_common():
        fh.write(f"| {dom} | {n} |\n")

    fh.write("\n## Open problems only (research open tag or status=open)\n\n")
    fh.write(f"- Open total: **{len(open_rows)}**\n")
    fh.write(f"- Open and untouched: **{len(open_untouched)}**\n\n")

    # Extract one-line descriptions from Lean files
    def _short_desc(rec):
        try:
            text = (ROOT / rec["formal_path"]).read_text()
        except Exception:
            return ""
        ms = list(re.finditer(r"/--\s*\n(.*?)\n-/", text, re.DOTALL))
        for mt in ms:
            body = mt.group(1).strip()
            if "Reference:" in body or "Wikipedia" in body or len(body) < 20:
                continue
            line = body.split("\n")[0].strip()
            return line[:140].replace("|", "/")
        return ""

    fh.write("\n## Top 20 untouched 'recent Mathlib formalization' candidates\n\n")
    fh.write("Research-open theorems formalized in formal-conjectures with no Aristotle submissions yet. One per Lean file (primary theorem preferred over variants).\n\n")
    fh.write("| Rank | source | problem_id | domain | one-line statement | formal_path |\n|---:|---|---|---|---|---|\n")
    for i, r in enumerate(recent_candidates[:20], 1):
        desc = _short_desc(r) or r["title"][:80]
        fh.write(f"| {i} | {r['source']} | `{r['problem_id']}` | {r['domain']} | {desc} | `{r['formal_path']}` |\n")

    fh.write("\n## Top 10 attempted-but-near-miss candidates (re-try candidates with post-May-30 methodology)\n\n")
    fh.write("Already-submitted problems that produced compiled_partial outputs OR ≥3 compiled_no_advance with 0 advance.\n\n")
    fh.write("| Rank | source | problem_id | domain | near_miss | no_advance | advance | status_summary |\n|---:|---|---|---|---:|---:|---:|---|\n")
    for i, r in enumerate(near_miss_rows[:10], 1):
        fh.write(f"| {i} | {r['source']} | `{r['problem_id']}` | {r['domain']} | {r['near_miss_count']} | {r['no_advance_count']} | {r['advance_count']} | {r['status_summary']} |\n")

    # Data quality issues
    fh.write("\n## Data quality issues\n\n")
    pid_counts = Counter(r["problem_id"] for r in rows)
    dups = [pid for pid, n in pid_counts.items() if n > 1]
    fh.write(f"- problem_id collisions across rows: **{len(dups)}** (top 10: {dups[:10]})\n")
    fh.write(f"- tracking-only rows (in tracking.db but not matched to any source): **{sum(1 for r in rows if r['source'] == 'tracking-only')}**\n")
    fh.write(f"- Submissions matched to UUIDs (excluded): handled via regex filter\n")
    # Erdős problem IDs that appear in tracking.db but no Lean file found
    unmatched_erdos = []
    for r in rows:
        if r["source"] == "tracking-only" and r["problem_id"].startswith(("erdos", "Erdos")):
            unmatched_erdos.append(r["problem_id"])
    fh.write(f"- Erdős-shaped tracking-only problem_ids: **{len(unmatched_erdos)}** ({unmatched_erdos[:15]})\n")

print(f"Wrote summary to {MD_PATH}", file=sys.stderr)

# Print final stats
print("\n--- TOTALS ---", file=sys.stderr)
print(f"rows={len(rows)} tried={already_tried} untouched={untouched}", file=sys.stderr)
print(f"by source: {dict(by_source.most_common())}", file=sys.stderr)
print(f"by domain (top 10): {dict(by_domain.most_common(10))}", file=sys.stderr)
print(f"top 20 untouched recent candidates: {[(r['source'], r['problem_id'], r['domain']) for r in recent_candidates[:20]]}", file=sys.stderr)
