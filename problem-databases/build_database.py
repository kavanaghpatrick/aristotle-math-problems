#!/usr/bin/env python3
"""
Build Unified Open Problems SQLite Database

Sources:
1. erdosproblems (Terence Tao) - 1,111 problems
2. formal-conjectures (DeepMind) - 448 Lean 4 files
3. Open Problem Garden - 710+ problems
4. Wikipedia unsolved problems - hundreds
5. OEIS conjectures - thousands
6. Polymath - collaborative targets
"""

import sqlite3
import json
import yaml
import os
import re
import hashlib
from pathlib import Path
from datetime import datetime
from urllib.request import urlopen, Request
from urllib.error import URLError
import time

BASE_DIR = Path(__file__).parent
DB_PATH = BASE_DIR / "problems.db"

class ProblemDatabase:
    def __init__(self, db_path=DB_PATH):
        self.db_path = db_path
        self.conn = None

    def connect(self):
        """Connect to database."""
        self.conn = sqlite3.connect(self.db_path)
        self.conn.row_factory = sqlite3.Row
        return self

    def __enter__(self):
        return self.connect()

    def __exit__(self, *args):
        if self.conn:
            self.conn.close()

    def init_schema(self):
        """Initialize database schema."""
        with open(BASE_DIR / "schema.sql", 'r') as f:
            schema = f.read()
        self.conn.executescript(schema)
        self.conn.commit()
        print("✓ Schema initialized")

    def add_source(self, name, url, description):
        """Register a data source."""
        self.conn.execute("""
            INSERT OR REPLACE INTO sources (name, url, description, last_scraped)
            VALUES (?, ?, ?, ?)
        """, (name, url, description, datetime.now().isoformat()))
        self.conn.commit()

    def add_problem(self, **kwargs):
        """Add a problem to the database."""
        # Generate slug if not provided
        if 'slug' not in kwargs or not kwargs['slug']:
            source = kwargs.get('source', 'unknown')
            source_id = kwargs.get('source_id', '')
            name = kwargs.get('name', '')
            slug_base = f"{source}-{source_id or name}".lower()
            kwargs['slug'] = re.sub(r'[^a-z0-9]+', '-', slug_base)[:100]

        columns = ', '.join(kwargs.keys())
        placeholders = ', '.join(['?' for _ in kwargs])

        try:
            self.conn.execute(f"""
                INSERT OR REPLACE INTO problems ({columns})
                VALUES ({placeholders})
            """, list(kwargs.values()))
        except sqlite3.IntegrityError as e:
            # Handle duplicate slug
            kwargs['slug'] = kwargs['slug'] + '-' + hashlib.md5(str(kwargs).encode()).hexdigest()[:6]
            columns = ', '.join(kwargs.keys())
            placeholders = ', '.join(['?' for _ in kwargs])
            self.conn.execute(f"""
                INSERT OR REPLACE INTO problems ({columns})
                VALUES ({placeholders})
            """, list(kwargs.values()))

    def add_tag(self, problem_slug, tag_name, category=None):
        """Add a tag to a problem."""
        # Ensure tag exists
        self.conn.execute("""
            INSERT OR IGNORE INTO tags (name, category) VALUES (?, ?)
        """, (tag_name, category))

        # Get IDs
        problem = self.conn.execute(
            "SELECT id FROM problems WHERE slug = ?", (problem_slug,)
        ).fetchone()
        tag = self.conn.execute(
            "SELECT id FROM tags WHERE name = ?", (tag_name,)
        ).fetchone()

        if problem and tag:
            self.conn.execute("""
                INSERT OR IGNORE INTO problem_tags (problem_id, tag_id)
                VALUES (?, ?)
            """, (problem['id'], tag['id']))

    def commit(self):
        """Commit changes."""
        self.conn.commit()

    def get_stats(self):
        """Get database statistics."""
        stats = {}
        stats['total'] = self.conn.execute("SELECT COUNT(*) FROM problems").fetchone()[0]
        stats['open'] = self.conn.execute("SELECT COUNT(*) FROM problems WHERE status='open'").fetchone()[0]
        stats['with_lean4'] = self.conn.execute("SELECT COUNT(*) FROM problems WHERE has_lean4=1").fetchone()[0]
        stats['open_with_lean4'] = self.conn.execute(
            "SELECT COUNT(*) FROM problems WHERE status='open' AND has_lean4=1"
        ).fetchone()[0]

        stats['by_source'] = {}
        for row in self.conn.execute("SELECT source, COUNT(*) as cnt FROM problems GROUP BY source"):
            stats['by_source'][row['source']] = row['cnt']

        return stats


def ingest_erdos_problems(db: ProblemDatabase):
    """Ingest Erdős problems from Tao's repo."""
    print("\n" + "="*60)
    print("INGESTING ERDŐS PROBLEMS")
    print("="*60)

    yaml_path = BASE_DIR / "erdosproblems/data/problems.yaml"
    with open(yaml_path, 'r') as f:
        problems = yaml.safe_load(f)

    db.add_source(
        'erdos',
        'https://github.com/teorth/erdosproblems',
        "Terence Tao's Erdős problems collection"
    )

    count = 0
    for p in problems:
        num = p.get('number', '')
        status_info = p.get('status', {})
        formalized_info = p.get('formalized', {})

        # Map status
        status_map = {
            'open': 'open',
            'proved': 'solved',
            'disproved': 'disproved',
            'verifiable': 'open',  # Computationally verifiable
            'falsifiable': 'open',  # Could be disproved
        }
        status = status_map.get(status_info.get('state', 'unknown'), 'unknown')

        # Prize
        prize = p.get('prize', 'no')
        prize_amount = 0
        if prize and prize != 'no':
            try:
                prize_amount = int(str(prize).replace('$', '').replace(',', ''))
            except:
                pass

        # Check for Lean file
        lean_path = BASE_DIR / f"formal-conjectures/FormalConjectures/ErdosProblems/{num}.lean"
        has_lean4 = lean_path.exists()
        lean_content = None
        if has_lean4:
            try:
                with open(lean_path, 'r') as f:
                    lean_content = f.read()
            except:
                pass

        # Calculate tractability
        tractability = calculate_tractability(
            has_lean4=has_lean4,
            tags=p.get('tags', []),
            prize=prize_amount,
            oeis=p.get('oeis', []),
            status=status
        )

        # Ensure all values are JSON serializable
        oeis_list = p.get('oeis', [])
        if not isinstance(oeis_list, list):
            oeis_list = [oeis_list] if oeis_list else []

        db.add_problem(
            source='erdos',
            source_id=str(num),
            name=f"Erdős Problem {num}",
            status=status,
            status_date=status_info.get('last_update'),
            has_lean4=has_lean4,
            lean_file_path=str(lean_path) if has_lean4 else None,
            lean_content=lean_content,
            formalization_quality='complete' if has_lean4 else 'none',
            domain=categorize_domain(p.get('tags', [])),
            prize_amount=prize_amount,
            oeis_ids=json.dumps(oeis_list),
            urls=json.dumps([f"https://www.erdosproblems.com/{num}"]),
            tractability_score=tractability,
            is_bounded=has_lean4,  # Assume formalized means bounded
            notes=str(p.get('comments', '') or '')
        )

        # Add tags
        slug = f"erdos-{num}"
        for tag in p.get('tags', []):
            db.add_tag(slug, tag, 'domain')

        count += 1

    db.commit()
    print(f"✓ Ingested {count} Erdős problems")


def ingest_formal_conjectures(db: ProblemDatabase):
    """Ingest DeepMind's formal-conjectures."""
    print("\n" + "="*60)
    print("INGESTING FORMAL CONJECTURES")
    print("="*60)

    base = BASE_DIR / "formal-conjectures/FormalConjectures"

    db.add_source(
        'formal-conjectures',
        'https://github.com/google-deepmind/formal-conjectures',
        "DeepMind's formalized conjectures in Lean 4"
    )

    count = 0
    for lean_file in base.rglob("*.lean"):
        if lean_file.name == "All.lean" or "Util" in str(lean_file):
            continue

        rel_path = lean_file.relative_to(base)
        category = rel_path.parts[0] if len(rel_path.parts) > 1 else "Other"

        # Skip Erdős (already ingested with more metadata)
        if category == "ErdosProblems":
            continue

        name = lean_file.stem

        try:
            with open(lean_file, 'r') as f:
                content = f.read()
        except:
            content = ""

        # Extract problem info from Lean file
        is_open = '@[category research open' in content
        is_solved = '@[category research solved' in content

        # Extract description from comments
        description = ""
        if '/-!' in content:
            match = re.search(r'/-!(.*?)-/', content, re.DOTALL)
            if match:
                description = match.group(1).strip()

        # Determine domain from category
        domain_map = {
            'Wikipedia': 'various',
            'Arxiv': 'research',
            'Mathoverflow': 'various',
            'Paper': 'research',
            'Oeis': 'sequences',
            'GreensOpenProblems': 'combinatorics',
            'WrittenOnTheWallII': 'graph theory',
            'Books': 'various',
            'ForMathlib': 'foundations',
        }

        db.add_problem(
            source='formal-conjectures',
            source_id=f"{category}/{name}",
            name=name,
            status='open' if is_open else ('solved' if is_solved else 'unknown'),
            has_lean4=True,
            lean_file_path=str(lean_file),
            lean_content=content,
            formalization_quality='complete',
            domain=domain_map.get(category, 'various'),
            subdomain=category,
            statement=description[:1000] if description else None,
            tractability_score=80,  # Pre-formalized is high tractability
            is_bounded=True,
        )

        count += 1

    db.commit()
    print(f"✓ Ingested {count} formal conjectures")


def ingest_open_problem_garden(db: ProblemDatabase):
    """Scrape Open Problem Garden."""
    print("\n" + "="*60)
    print("INGESTING OPEN PROBLEM GARDEN")
    print("="*60)

    # Note: This requires actual web scraping. For now, we'll add the source
    # and some known problems.

    db.add_source(
        'opg',
        'http://www.openproblemgarden.org/',
        "Open Problem Garden - 710+ curated problems"
    )

    # Known categories and approximate counts
    opg_categories = [
        ('graph theory', 228),
        ('algebra', 295),
        ('number theory', 49),
        ('combinatorics', 50),
        ('analysis', 30),
        ('geometry', 25),
        ('topology', 20),
        ('logic', 13),
    ]

    # Add placeholder for now - full scraping would need more work
    count = 0
    for domain, expected in opg_categories:
        db.add_problem(
            source='opg',
            source_id=f"category-{domain}",
            name=f"Open Problem Garden: {domain.title()} ({expected} problems)",
            status='open',
            has_lean4=False,
            domain=domain,
            tractability_score=50,
            notes=f"Placeholder - need to scrape {expected} problems from OPG",
            urls=json.dumps([f"http://www.openproblemgarden.org/category/{domain.replace(' ', '_')}"])
        )
        count += 1

    db.commit()
    print(f"✓ Added {count} OPG category placeholders (full scrape pending)")
    print("  TODO: Implement full OPG scraper")


def ingest_wikipedia_problems(db: ProblemDatabase):
    """Add Wikipedia unsolved problems."""
    print("\n" + "="*60)
    print("INGESTING WIKIPEDIA PROBLEMS")
    print("="*60)

    # These are from formal-conjectures/Wikipedia/
    # Already ingested via formal-conjectures, but let's add the source

    db.add_source(
        'wikipedia',
        'https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics',
        "Wikipedia's list of unsolved problems"
    )

    # Count Wikipedia problems from formal-conjectures
    wiki_path = BASE_DIR / "formal-conjectures/FormalConjectures/Wikipedia"
    if wiki_path.exists():
        count = len(list(wiki_path.glob("*.lean")))
        print(f"✓ {count} Wikipedia problems (via formal-conjectures)")
    else:
        print("  Wikipedia problems already ingested via formal-conjectures")


def ingest_oeis_conjectures(db: ProblemDatabase):
    """Add OEIS conjectures."""
    print("\n" + "="*60)
    print("INGESTING OEIS CONJECTURES")
    print("="*60)

    db.add_source(
        'oeis',
        'https://oeis.org/',
        "Online Encyclopedia of Integer Sequences - conjectures"
    )

    # OEIS problems from formal-conjectures
    oeis_path = BASE_DIR / "formal-conjectures/FormalConjectures/Oeis"
    if oeis_path.exists():
        count = 0
        for lean_file in oeis_path.glob("*.lean"):
            oeis_id = lean_file.stem

            try:
                with open(lean_file, 'r') as f:
                    content = f.read()
            except:
                content = ""

            db.add_problem(
                source='oeis',
                source_id=f"A{oeis_id}",
                name=f"OEIS A{oeis_id}",
                status='open',
                has_lean4=True,
                lean_file_path=str(lean_file),
                lean_content=content,
                formalization_quality='complete',
                domain='sequences',
                tractability_score=85,  # OEIS problems are often bounded
                is_bounded=True,
                is_computational=True,
                urls=json.dumps([f"https://oeis.org/A{oeis_id}"])
            )
            count += 1

        db.commit()
        print(f"✓ Ingested {count} OEIS conjectures with Lean 4")

    # Note: Could add more OEIS conjectures via API
    print("  TODO: Scrape more OEIS conjectures via API")


def calculate_tractability(has_lean4=False, tags=None, prize=0, oeis=None, status='open'):
    """Calculate tractability score 0-100."""
    score = 50

    if has_lean4:
        score += 30

    if oeis and oeis != ['N/A']:
        score += 10

    tags = tags or []
    tractable_tags = ['combinatorics', 'graph theory', 'sidon', 'additive']
    hard_tags = ['primes', 'twin prime', 'riemann']

    for tag in tags:
        tag_lower = tag.lower()
        if any(t in tag_lower for t in tractable_tags):
            score += 5
        if any(t in tag_lower for t in hard_tags):
            score -= 10

    if prize >= 5000:
        score -= 15
    elif prize >= 1000:
        score -= 5
    elif prize == 0:
        score += 5

    return max(0, min(100, score))


def categorize_domain(tags):
    """Categorize domain from tags."""
    tags_lower = [t.lower() for t in tags]

    if any('graph' in t for t in tags_lower):
        return 'graph theory'
    if any('combinat' in t for t in tags_lower):
        return 'combinatorics'
    if any('number' in t for t in tags_lower):
        return 'number theory'
    if any('algebra' in t for t in tags_lower):
        return 'algebra'
    if any('geometry' in t or 'distance' in t for t in tags_lower):
        return 'geometry'
    if any('prime' in t for t in tags_lower):
        return 'number theory'

    return 'various'


def print_summary(db: ProblemDatabase):
    """Print database summary."""
    print("\n" + "="*60)
    print("DATABASE SUMMARY")
    print("="*60)

    stats = db.get_stats()

    print(f"\nTotal problems: {stats['total']}")
    print(f"Open problems: {stats['open']}")
    print(f"With Lean 4: {stats['with_lean4']}")
    print(f"Open + Lean 4: {stats['open_with_lean4']} ⭐")

    print("\nBy source:")
    for source, count in sorted(stats['by_source'].items(), key=lambda x: -x[1]):
        print(f"  {source}: {count}")

    # Top candidates
    print("\nTop 10 candidates (Open + Lean 4, by tractability):")
    cursor = db.conn.execute("""
        SELECT source, source_id, name, tractability_score, domain
        FROM problems
        WHERE status = 'open' AND has_lean4 = 1
        ORDER BY tractability_score DESC
        LIMIT 10
    """)
    for i, row in enumerate(cursor, 1):
        print(f"  {i:2}. [{row['source']}] {row['source_id'] or row['name'][:30]} "
              f"| Score: {row['tractability_score']} | {row['domain'] or 'various'}")


def main():
    """Build the complete database."""
    print("="*60)
    print("BUILDING UNIFIED PROBLEMS DATABASE")
    print("="*60)
    print(f"Database: {DB_PATH}")
    print(f"Time: {datetime.now().isoformat()}")

    # Remove old database
    if DB_PATH.exists():
        DB_PATH.unlink()
        print("✓ Removed old database")

    with ProblemDatabase() as db:
        db.init_schema()

        # Ingest all sources
        ingest_erdos_problems(db)
        ingest_formal_conjectures(db)
        ingest_open_problem_garden(db)
        ingest_wikipedia_problems(db)
        ingest_oeis_conjectures(db)

        print_summary(db)

    print(f"\n✅ Database saved to: {DB_PATH}")
    print(f"   Size: {DB_PATH.stat().st_size / 1024:.1f} KB")


if __name__ == "__main__":
    main()
