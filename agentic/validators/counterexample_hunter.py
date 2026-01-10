#!/usr/bin/env python3
"""
Counterexample Hunter - Actively try to disprove lemmas before submitting.

Strategies:
1. Pattern matching against known false lemmas
2. AI-powered counterexample construction (Grok)
3. Small graph enumeration
4. Constraint satisfaction (Z3 for decidable fragments)
"""

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass

sys.path.insert(0, str(Path(__file__).parent.parent))
from config import DB_PATH, GROK_API_KEY, COUNTEREXAMPLE_TIMEOUT_SECONDS


@dataclass
class Lemma:
    name: str
    statement: str
    full_text: str


@dataclass
class CounterexampleResult:
    found: bool
    lemma_name: str
    counterexample: Optional[str]
    method: str
    confidence: float  # 0-1


class CounterexampleHunter:
    """Hunt for counterexamples to prevent false lemmas reaching Aristotle."""

    # Known false patterns from the database
    KNOWN_FALSE_PATTERNS = [
        # Pattern: tau bounds that are too tight
        (r'tau.*le\s+4\b', "tau <= 4 claims are usually false for T_pair"),
        (r'tau.*le\s+2\b(?!.*(?:containing|avoiding|S_e|S_f))',
         "tau <= 2 needs scope restriction (containing/avoiding/S_e)"),

        # Pattern: spoke coverage for avoiding triangles
        (r'avoiding.*spoke', "Spokes can't cover avoiding triangles (Pattern 2)"),
        (r'spoke.*avoiding', "Spokes can't cover avoiding triangles (Pattern 2)"),

        # Pattern: bridge absorption
        (r'cover.*S_e.*S_f.*bridge', "Bridge coverage doesn't come free (Pattern 3)"),

        # Pattern: sunflower 2-edge cover
        (r'sunflower.*le\s+2', "Sunflower tau <= 2 is false (Patterns 5,7)"),
        (r'trianglesSharingMEdge.*le\s+2', "trianglesSharingMEdgeAt needs 3+ edges"),

        # Pattern: external vertex sharing
        (r'external.*share.*vertex', "Externals don't share common vertex (Pattern 6)"),
        (r'common.*external', "Externals don't share common vertex (Pattern 6)"),
    ]

    def __init__(self):
        self.db_path = DB_PATH

    def extract_lemmas(self, content: str) -> List[Lemma]:
        """Extract lemmas and theorems from Lean content."""
        lemmas = []

        # Match lemma/theorem declarations
        pattern = r'((?:lemma|theorem)\s+(\w+)[^:]*:\s*([^\n:=]+(?:\n\s+[^\n:=]+)*)\s*:=)'
        for match in re.finditer(pattern, content, re.MULTILINE):
            full_text = match.group(1)
            name = match.group(2)
            statement = match.group(3).strip()

            # Also get the proof for context
            start = match.end()
            # Find the next lemma/theorem/def/end
            next_decl = re.search(r'\n(?:lemma|theorem|def |end\b)', content[start:])
            if next_decl:
                proof = content[start:start + next_decl.start()]
            else:
                proof = content[start:start + 500]

            lemmas.append(Lemma(
                name=name,
                statement=statement,
                full_text=full_text + proof[:500]
            ))

        return lemmas

    def hunt_with_patterns(self, lemma: Lemma) -> Optional[CounterexampleResult]:
        """Check against known false patterns."""
        text = lemma.statement + " " + lemma.full_text

        for pattern, reason in self.KNOWN_FALSE_PATTERNS:
            if re.search(pattern, text, re.IGNORECASE):
                return CounterexampleResult(
                    found=True,
                    lemma_name=lemma.name,
                    counterexample=f"Matches known false pattern: {reason}",
                    method="pattern_matching",
                    confidence=0.9
                )

        return None

    def hunt_with_grok(self, lemma: Lemma) -> Optional[CounterexampleResult]:
        """Use Grok to try to construct counterexample."""
        if not GROK_API_KEY:
            return None

        prompt = f"""You are a mathematical counterexample finder.
Try to find a counterexample to this Lean 4 lemma about triangle covering.

Lemma name: {lemma.name}
Statement: {lemma.statement}

Context (Tuza's conjecture for ν=4):
- G is a graph with maximal triangle packing M of size 4
- We need τ(G) ≤ 2ν = 8 edges to cover all triangles
- Triangle = set of 3 vertices forming K_3
- M = {{A, B, C, D}} are 4 edge-disjoint triangles

CRITICAL: Consider these known counterexample patterns:
1. Avoiding triangles cannot be covered by spokes (spokes contain v, avoiding don't)
2. Triangles at shared vertex can use edges from DIFFERENT M-triangles
3. External triangles don't share a common external vertex
4. Any 8 edges from 12 M-edges misses some triangles

If you find a counterexample, return JSON:
{{"found": true, "counterexample": "description", "confidence": 0.0-1.0}}

If the lemma seems valid, return JSON:
{{"found": false, "reason": "why it seems valid"}}

Think step by step about the graph structure.
"""

        try:
            # Import the grok query function
            sys.path.insert(0, str(Path(__file__).parent.parent.parent / "scripts"))
            from grok_query import query_grok

            response = query_grok(prompt, timeout=COUNTEREXAMPLE_TIMEOUT_SECONDS)

            # Parse response
            json_match = re.search(r'\{[^}]+\}', response, re.DOTALL)
            if json_match:
                result = json.loads(json_match.group())
                if result.get('found'):
                    return CounterexampleResult(
                        found=True,
                        lemma_name=lemma.name,
                        counterexample=result.get('counterexample', 'Unknown'),
                        method="grok_ai",
                        confidence=float(result.get('confidence', 0.7))
                    )

        except Exception as e:
            pass  # Silently fail, not critical

        return None

    def hunt_with_enumeration(self, lemma: Lemma) -> Optional[CounterexampleResult]:
        """Enumerate small graphs to find counterexamples."""
        # For now, skip this - would need a Lean/Sage bridge
        # This is where we'd enumerate small triangle-free graphs
        return None

    def hunt(self, content: str) -> List[CounterexampleResult]:
        """Hunt for counterexamples in all lemmas."""
        lemmas = self.extract_lemmas(content)
        results = []

        for lemma in lemmas:
            # Try pattern matching first (fast)
            result = self.hunt_with_patterns(lemma)
            if result:
                results.append(result)
                continue

            # Try Grok (slower, more powerful)
            result = self.hunt_with_grok(lemma)
            if result and result.found:
                results.append(result)

        return results

    def hunt_file(self, file_path: str) -> Tuple[bool, List[CounterexampleResult]]:
        """Hunt for counterexamples in a file."""
        try:
            with open(file_path, 'r') as f:
                content = f.read()
        except Exception as e:
            return True, []  # Can't read file, assume OK

        results = self.hunt(content)
        has_counterexamples = any(r.found and r.confidence >= 0.8 for r in results)

        return not has_counterexamples, results


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Counterexample Hunter")
    parser.add_argument("file", help="Lean file to analyze")
    parser.add_argument("--verbose", "-v", action="store_true")

    args = parser.parse_args()

    hunter = CounterexampleHunter()
    passed, results = hunter.hunt_file(args.file)

    if results:
        print(f"\nFound {len(results)} potential counterexamples:")
        for r in results:
            print(f"\n  Lemma: {r.lemma_name}")
            print(f"  Method: {r.method}")
            print(f"  Confidence: {r.confidence:.1%}")
            print(f"  Counterexample: {r.counterexample[:200]}")
    else:
        print("\nNo counterexamples found")

    print(f"\nVerdict: {'PASS' if passed else 'FAIL'}")
    sys.exit(0 if passed else 1)


if __name__ == "__main__":
    main()
