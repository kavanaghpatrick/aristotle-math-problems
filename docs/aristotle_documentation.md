# Aristotle by Harmonic - Comprehensive Documentation

## Overview

Aristotle is a mathematical superintelligence AI system developed by Harmonic that combines formal verification with informal reasoning. It achieved gold-medal-equivalent performance on the 2025 International Mathematical Olympiad (IMO) by solving 5 out of 6 problems with formally verified Lean 4 proofs.

**Key Achievement**: Aristotle is the first AI model built from the ground up as a Mathematical Superintelligence (MSI), designed to deliver provably correct solutions without hallucinations.

## Company Background

- **Founded**: By Vlad Tenev (Robinhood CEO) and team
- **Funding History**:
  - Series A (Sept 2024): $75 million led by Sequoia Capital
  - Series B (July 2025): $100 million led by Kleiner Perkins with Paradigm
  - Series C (Nov 2025): $120 million led by Ribbit Capital
  - **Valuation**: $1.45 billion (as of Nov 2025)

## Core Capabilities

### 1. Autoformalization
- Converts natural language mathematical statements and proofs into formally verified Lean 4 code
- Accepts input in multiple formats: LaTeX, Markdown, or plain English
- Automatically translates informal mathematical reasoning into formal proofs
- Enables collaboration with mathematicians and educators who may not know Lean

### 2. Formal Verification
- Generates proofs that are formally verified down to foundational axioms using Lean 4
- Eliminates the need for human verification of mathematical correctness
- Every solution is proven correct before being presented to users
- No hallucinations - all results are mathematically guaranteed

### 3. Counterexample Generation
- When a statement is incorrect, Aristotle provides explicit counterexamples
- Helps identify logical errors, missed edge cases, or misformalizations
- Discovered four errors in Terence Tao's Analysis textbook with counterexamples

### 4. Seamless Integration
- Automatically leverages your entire library of theorems and definitions
- Works with Lake dependencies and Mathlib
- Integrates into existing Lean 4 projects without manual configuration

### 5. Code Verification
- Achieved 96.8% on the VERINA benchmark (not 98.6% as sometimes cited)
- Successfully proved 160 correct and 23 false specifications out of 189 total
- Can verify correctness of algorithms and implementations:
  - In-place selection sort implementations
  - Run-length encoding algorithms
  - Longest increasing subsequence calculations
  - Bug detection in k-most-frequent entry selection

## Technical Architecture

Aristotle integrates three major subsystems:

### 1. Lean Proof Search System
- **Algorithm**: Monte Carlo Graph Search (MCGS)
- **Model**: Large transformer scaled beyond 200B parameters
- **Function**: Unified policy and value function
- **Search Strategy**:
  - Uses PUCT formula with exploration weighted by prior policy
  - Implements AND/OR logic for branching proof states
  - Identifies equivalent states/actions to convert proof hypertrees into hypergraphs
  - Reduces redundant computation through graph-based deduplication

#### REPL Architecture
The REPL is a program written in Lean itself that manages Lean goal states and applies tactics:

**Basic Operations**:
1. Run Lean code - takes a Lean file and produces states for incomplete proofs
2. Run tactic - takes a state and produces new states
3. Export state - returns serialized representation of state data

**Proof State Management**:
- Supports initializing from Lean files with `sorry` placeholders
- Each incomplete proof generates a goal state
- Proof states contain available variables, proven facts, and remaining goals

**Verification Process**:
- Found proofs are rendered as self-contained Lean files
- Run through Lean kernel to check for errors
- Verifies which axioms are used and which lemmas are necessary
- Ensures proof terms produced by tactics are well-typed

**Infrastructure**:
- REPL hosted on many CPU-only machines
- Operates in stateless manner for scalability

### 2. Lemma-based Informal Reasoning System
- Generates informal proofs of mathematical statements
- Breaks proofs down into lemmas
- Formalizes each lemma into Lean
- Iterates based on formal feedback from Lean
- Co-evolves hidden chain-of-thought, informal comments, and formal code during training

**English Mode**: This system enables "English mode" - the ability to work with natural language mathematics and automatically translate to formal proofs.

### 3. Geometry Solver (Yuclid & Newclid 3.0)
- Solves plane geometry problems outside of Lean
- Based on AlphaGeometry approach but significantly enhanced
- **Performance**: Up to 500x faster than AlphaGeometry-1
- **Implementation**: High-performance C++ solver

**Yuclid Capabilities**:
- Uses deductive databases and algebraic reasoning
- Gaussian elimination for numerical processing
- Scans diagrams for standard configurations:
  - Midpoints
  - Bisectors
  - Similar triangles
- Numeric rule matching for geometric patterns
- Encodes configurations into equations and inequalities
- Algebraic rule tables for geometric reasoning

**Success**: Solved IMO 2025 Problem 2 (plane geometry)

### 4. Advanced Features

**Test-Time Training**:
- Iteratively retrains on search traces during inference
- Specializes on specific problems dynamically

**Graph Search Optimization**:
- Converts proof trees into graphs by identifying equivalent states
- Dramatically reduces redundant computation

**Scaling Requirements**:
- Required scaling across three dimensions:
  1. Large model size (200B+ parameters)
  2. Parallel pipeline instances
  3. Formal feedback iterations

## Performance Benchmarks

### International Mathematical Olympiad (IMO) 2025
- **Score**: 5 out of 6 problems solved
- **Performance Level**: Gold medal equivalent
- **Verification**: All solutions formally verified in Lean 4
- **Problems Solved**: Problems 1-5 (all except Problem 6)

### MiniF2F Benchmark
- **Score**: 90% (as of July 2024)

### VERINA Benchmark
- **Score**: 96.8% (183 out of 189 specifications resolved)
  - 160 specifications proved correct
  - 23 specifications proved false
- **Comparison**: Best previous model (OpenAI o4-mini) achieved only 3.6% successful proofs

### Notable Mathematical Achievements
- Solved Erdős Problem #124 in 6 hours (problem open since 1990s)
- Contributed novel lemmas to Mathlib:
  - Niven's theorem
  - Gauss-Lucas theorem
  - Eigenvalue proofs
- Demonstrated proficiency in advanced topics:
  - Homological algebra
  - Category theory
  - Eisenstein series

## Access Methods

### 1. Web Interface
- **URL**: https://aristotle.harmonic.fun
- Submit LaTeX, Markdown, or natural language questions
- Receive formally verified Lean 4 proofs with explanations

### 2. Mobile Apps
**iOS Beta**: Available at aristotle.harmonic.fun
- Photo-based problem solving (take picture of math problem)
- Parallel query capabilities (solve multiple questions simultaneously)
- Clean interface with natural conversation flow
- Shows both English solution and Lean verification code

**Android**: Also available (launched alongside iOS)

### 3. API Access
- **URL**: https://aristotle.harmonic.fun
- Sign up required for API key
- Python SDK available via `aristotlelib` package
- Terms of Use available at: https://aristotle.harmonic.fun/api-terms-of-use

### 4. Python SDK (aristotlelib)

**Installation**:
```bash
pip install aristotlelib
```

**Version**: 0.1.2 (latest as of documentation date)

**Compatibility**:
- Lean Toolchain: leanprover/lean4:v4.20.0-rc5
- Mathlib: d62eab0cc36ea522904895389c301cf8d844fd69
- Note: Projects using different versions may encounter compatibility issues

#### API Setup

Set API key via environment variable or function call:

```python
import aristotlelib

# Option 1: Set via function
aristotlelib.set_api_key("your-api-key-here")

# Option 2: Set via environment variable
# export ARISTOTLE_API_KEY="your-api-key-here"
```

#### Basic Usage Examples

**Create Project and Solve**:
```python
import asyncio
import aristotlelib
from pathlib import Path

async def main():
    # Create a new project
    project = await aristotlelib.Project.create()
    print(f"Created project: {project.project_id}")

    # Add context files (your existing Lean code)
    await project.add_context([
        "path/to/context1.lean",
        "path/to/context2.lean"
    ])

    # Solve with input content
    await project.solve(
        input_content="theorem my_theorem : True := trivial"
    )

    # Wait for completion and get solution
    while project.status not in [
        aristotlelib.ProjectStatus.COMPLETE,
        aristotlelib.ProjectStatus.FAILED
    ]:
        await asyncio.sleep(30)  # Poll every 30 seconds
        await project.refresh()
        print(f"Status: {project.status}")

    if project.status == aristotlelib.ProjectStatus.COMPLETE:
        solution_path = await project.get_solution()
        print(f"Solution saved to: {solution_path}")

asyncio.run(main())
```

**List Projects**:
```python
import asyncio
import aristotlelib

async def list_projects():
    # Get first page of projects
    projects, pagination_key = await aristotlelib.Project.list_projects(
        limit=10
    )

    for project in projects:
        print(f"Project {project.project_id}: {project.status}")

    # Get next page if available
    if pagination_key:
        more_projects, pagination_key = \
            await aristotlelib.Project.list_projects(
                pagination_key=pagination_key
            )
        print(f"Found {len(more_projects)} more projects")

asyncio.run(list_projects())
```

#### Logging

The SDK uses Python's standard logging module:

```python
import logging

# Configure logging to see debug messages
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
```

## Use Cases and Applications

### Mathematics Research
- Automated theorem proving at IMO level
- Verification of mathematical proofs
- Solving previously unsolved problems (e.g., Erdős problems)
- Contributing new lemmas to Mathlib
- Discovering errors in mathematical textbooks

### Education
- Helping students solve complex math problems with verified solutions
- Teaching formal verification and proof techniques
- Providing step-by-step explanations with guaranteed correctness
- Enabling non-Lean users to benefit from formal verification
- Democratizing access to advanced mathematics

### Software Engineering
- Verifying algorithm correctness
- Proving properties of code implementations
- Finding bugs through counterexample generation
- Formal verification of critical systems

### Future Applications (mentioned by Harmonic)
- Statistical analysis and data science
- Cryptography
- Industrial design
- Medical technology

### Research Applications
- Collaborative work with mathematicians who don't know Lean
- Checking mathematical work automatically
- Filling in proof details with formal grounding
- Exploring mathematical conjectures with guaranteed correctness

## Key Features and Modes

### English Mode (Natural Language Processing)
- Submit problems in plain English, LaTeX, or Markdown
- Aristotle automatically formalizes into Lean 4
- Returns both formal proof and natural language explanation
- Enables mathematicians to work without learning Lean syntax

### Parallel Processing
- Mobile app supports solving multiple questions simultaneously
- "Just a couple taps" to solve multiple problems in parallel

### Photo-Based Input
- iOS app can solve problems from photographs
- Take picture of math problem and receive verified solution

### Interactive Problem Solving
- Conversation flow that encourages deeper understanding
- Probes users with "why" and "how" questions, not just "what"
- Follow-up questions to guide mathematical thinking

## Integration with Lean Ecosystem

### Mathlib Integration
- Automatically leverages all theorems and definitions from Mathlib
- Contributed novel proofs back to Mathlib community
- Works with latest Mathlib versions (though specific version compatibility required)

### Lake Dependencies
- Seamlessly works with Lake package manager
- Automatically includes all project dependencies:
  - plausible
  - LeanSearchClient
  - import-graph
  - ProofWidgets4
  - aesop
  - quote4
  - batteries
  - lean4-cli

### Project Structure
Aristotle works with standard Lean 4 project files:
- `lean-toolchain` - specifies Lean version
- `lakefile.toml` - project configuration and dependencies
- `lake-manifest.json` - auto-generated dependency versions

### Adding Context Files
Upload your existing Lean code as context:
- Aristotle analyzes your theorems and definitions
- Uses your project-specific lemmas in proofs
- Maintains consistency with your codebase

## User Experiences and Reception

### Social Media Feedback
- Generally positive reception on Reddit and Twitter
- Enthusiasm for mathematical verification capabilities
- Praise for potential in STEM education and research
- Discussion of "hallucination-free" claims

### Notable User Testimonial
A mathematician on Twitter stated:
> "One cool part of this experience is that I *would not have made the Claude Deep Research query resulting in the connection to Erdos 106 if not for Aristotle's exact implementation*."

This user successfully contributed to Terry Tao's blog with Aristotle assistance.

### Expert Opinion
- Widely discussed by tech and AI experts
- Recognized as significant advancement in AI reasoning
- Potential to revolutionize AI's role in STEM fields
- Interest from both academia and industry

## Open Source Contributions

Harmonic has released several open source tools:

1. **Yuclid** - Geometric solver (500x faster than AlphaGeometry)
2. **Newclid 3.0** - Improved theorem prover for geometry
3. **Updated MiniF2F dataset** - In Lean 4 format
4. **Synthetic data generation algorithm** - For auxiliary constructions
5. **IMO 2025 Solutions Repository** - https://github.com/harmonic-ai/IMO2025

## API Terms and Compliance

### Key Definitions (from API Terms of Use)
- **API Key**: Security credential for accessing Aristotle API
- **API Documentation**: Harmonic's documentation including usage limits
- **AI Customer Input**: Files, prompts, code, Lean4 source files submitted
- **AI Customer Output**: Content generated by the service (e.g., Lean4 proof steps)

### Access
- Sign up required at https://aristotle.harmonic.fun
- API key issued upon approval
- Terms of Use must be accepted

## Technical Infrastructure

### REPL Hosting
- Distributed across many CPU-only machines
- Stateless operation for scalability
- Each machine can handle multiple concurrent proof searches

### Model Architecture
- Transformer-based with 200B+ parameters
- Unified policy and value function
- Trained with co-evolution of informal and formal reasoning
- Test-time training for problem specialization

### Verification Pipeline
1. Problem submitted in natural language
2. Autoformalized into Lean 4
3. Proof search using MCGS algorithm
4. Generated proof verified by Lean kernel
5. Result checked for axiom usage and dependencies
6. Natural language explanation generated
7. Both formal and informal results returned to user

## Limitations and Considerations

### Version Compatibility
- Requires specific Lean toolchain version (v4.20.0-rc5)
- Requires specific Mathlib commit (d62eab0cc36ea522904895389c301cf8d844fd69)
- Projects with different versions may have compatibility issues

### Performance
- Some problems may take significant time to solve
- IMO Problem 6 was not solved (only 5 out of 6)
- Polling required for async API (30-second intervals recommended)

### Scope
- Primarily focused on mathematical reasoning
- Geometry problems may require specialized solver
- Not all mathematical domains equally supported

## Documentation and Resources

### Official Resources
- Main Website: https://harmonic.fun
- API Portal: https://aristotle.harmonic.fun
- Terms of Use: https://aristotle.harmonic.fun/api-terms-of-use
- News & Updates: https://harmonic.fun/news

### Research Papers
- **ArXiv Paper**: [Aristotle: IMO-level Automated Theorem Proving](https://arxiv.org/abs/2510.01346)
- **PDF**: [Technical Report](https://harmonic.fun/pdf/Aristotle_IMO_Level_Automated_Theorem_Proving.pdf)

### Code Repositories
- **IMO 2025 Solutions**: https://github.com/harmonic-ai/IMO2025
- **PyPI Package**: https://pypi.org/project/aristotlelib/

### Learning Resources
- **Xena Project Blog**: Examples of using Aristotle for autoformalization
  - https://xenaproject.wordpress.com/
- **Lean Community**: General Lean 4 resources
  - https://leanprover-community.github.io/

### Social Media
- **Twitter**: @HarmonicMath
- **Company**: Harmonic on LinkedIn

## Benchmarks Referenced

### VERINA (Verifiable Code Generation Arena)
- Developed by UC Berkeley and Meta researchers
- 189 manually curated coding tasks in Lean
- Includes problem descriptions, reference implementations, formal specifications
- Extensive test suites for verification
- Aristotle: 96.8% success rate
- Previous best (o4-mini): 3.6% success rate

### MiniF2F
- Mathematical theorem proving benchmark
- Aristotle: 90% success rate (July 2024)
- Updated dataset contributed by Harmonic in Lean 4 format

### IMO (International Mathematical Olympiad)
- Premier mathematics competition for high school students
- 6 problems spanning algebra, combinatorics, geometry, number theory
- Aristotle: 5/6 problems solved (gold medal equivalent)

## Pricing and Access

**Note**: Specific pricing information is not publicly available in documentation.

### Access Levels
1. **Beta App Access**: Available through iOS/Android apps
2. **API Access**: Requires sign-up and approval
3. **Free Tier**: Unknown if available

### How to Get Access
1. Visit https://aristotle.harmonic.fun
2. Fill out access request form (typeform)
3. Await approval for API key
4. Download mobile app from app stores (for app access)

For pricing details, contact Harmonic directly through their website.

## Example Problems and Demonstrations

### IMO 2001 Question 6 Example
Harmonic provided unmodified examples of Aristotle working on Q6 from 2001 IMO:
- Natural language problem statement provided
- Informal proof generated
- Formal statement in Lean 4 created
- Complete Lean 4 proof verified

### Code Verification Examples
Successfully verified:
- In-place selection sort is valid sorting algorithm
- Run-length encoding implementation correctness
- Longest increasing subsequence algorithms
- Bug identification in k-most-frequent implementations

### Geometry Problem Example
IMO 2025 Problem 2 (plane geometry):
- Solved using Yuclid and Newclid 3.0
- Demonstrates geometry-specific solver capabilities

## Community and Ecosystem

### Integration with Lean Community
- Contributes to Mathlib
- Works with standard Lean 4 project structure
- Compatible with Lake package manager ecosystem
- Uses community-standard toolchain versions

### Educational Impact
- Makes formal verification accessible to non-experts
- Enables new teaching methods for mathematics
- Opens advanced mathematics to broader participation
- Provides verified learning resources

### Research Impact
- Solving previously unsolved mathematical problems
- Finding errors in established mathematical texts
- Contributing to mathematical formalization efforts
- Advancing automated theorem proving research

## Future Directions

### Announced Plans
- Continued improvement of mathematical capabilities
- Expansion into software engineering applications
- Industrial and medical technology applications
- Further API and tool development

### Potential Applications
- Statistical analysis with guaranteed correctness
- Cryptographic verification
- Critical system verification
- Scientific computing validation

## Technical Support and Documentation

### For API Users
- API Documentation available after sign-up
- Usage limits specified in documentation
- Implementation guidance provided
- Terms of Use govern API usage

### For App Users
- In-app help and tutorials
- Clean interface designed for ease of use
- Visual feedback showing both English and Lean code
- Support through Harmonic website

### For Developers
- Python SDK (`aristotlelib`) with async API
- Standard logging for debugging
- Project-based workflow
- Context file support for custom libraries

## Conclusion

Aristotle represents a breakthrough in automated theorem proving and mathematical AI. By combining large-scale neural networks with formal verification in Lean 4, it achieves provably correct solutions to complex mathematical problems without hallucinations. Its multi-modal approach (natural language, formal proofs, geometry solving) and impressive benchmark performance (IMO gold medal, 96.8% on VERINA) demonstrate significant advancement in AI reasoning capabilities.

The system is accessible through multiple channels (web, mobile, API) and serves diverse use cases from education to research to software verification. With strong backing ($295M+ in funding), open source contributions, and integration with the Lean ecosystem, Aristotle is positioned to significantly impact how mathematics and formal verification are practiced.

---

## Sources

This documentation was compiled from the following sources:

1. [Aristotle Lean API](https://aristotle.harmonic.fun)
2. [Harmonic News](https://harmonic.fun/news)
3. [Harmonic Homepage](https://harmonic.fun)
4. [Aristotle: IMO-level Automated Theorem Proving (ArXiv)](https://arxiv.org/abs/2510.01346)
5. [Aristotle: IMO-level Automated Theorem Proving (HTML)](https://arxiv.org/html/2510.01346v1)
6. [Aristotle Technical Report (PDF)](https://harmonic.fun/pdf/Aristotle_IMO_Level_Automated_Theorem_Proving.pdf)
7. [aristotlelib PyPI Package](https://pypi.org/project/aristotlelib/0.1.2/)
8. [GitHub - harmonic-ai/IMO2025](https://github.com/harmonic-ai/IMO2025)
9. [Verina: Benchmarking Verifiable Code Generation](https://verina.io/)
10. [Verina: Benchmarking Verifiable Code Generation (ArXiv)](https://arxiv.org/html/2505.23135v1)
11. [Harmonic Announces IMO Gold Medal Performance (BusinessWire)](https://www.businesswire.com/news/home/20250728394917/en/Harmonic-Announces-IMO-Gold-Medal-Level-Performance-Launch-of-First-Mathematical-Superintelligence-MSI-AI-App)
12. [Harmonic launches AI chatbot app (TechCrunch)](https://techcrunch.com/2025/07/28/harmonic-the-robinhood-ceos-ai-math-startup-launches-an-ai-chatbot-app/)
13. [Solving the AI Reasoning Gap (Index Ventures)](https://www.indexventures.com/perspectives/solving-the-ai-reasoning-gap-how-harmonic-is-building-mathematical-superintelligence/)
14. [Xena Project Blog](https://xenaproject.wordpress.com/)
15. [Using mathlib4 as a dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
16. [Aristotle Terms of Use](https://aristotle.harmonic.fun/api-terms-of-use)
17. Various news articles and blog posts cited throughout

**Last Updated**: December 11, 2025
**Documentation Version**: 1.0
