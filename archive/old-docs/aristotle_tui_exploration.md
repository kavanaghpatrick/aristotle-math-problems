# Aristotle TUI Exploration

## Summary
Aristotle SDK v0.6.0 is a "Mathematical Superintelligence by Harmonic" that provides automated theorem proving for Lean. It has both a TUI (Text User Interface) and CLI (Command-Line Interface).

## TUI Interface

### Launch Command
```bash
ARISTOTLE_API_KEY="your_api_key_here" aristotle
```

### Main Menu Options

The TUI displays a centered menu with 4 modes:

```
╔══════════════════════════════════════════════╗
║            ARISTOTLE SDK v0.6.0              ║
║  Mathematical Superintelligence by Harmonic  ║
╚══════════════════════════════════════════════╝

╭─ Available Modes ────────────────────────────────────────────────────╮
│                                                                      │
│  [1] Fill sorries in a lean file (.lean)                             │
│  [2] Prove and formalize from an existing file (.tex, .md, .txt)     │
│  [3] Direct Aristotle in English (.lean optional)                    │
│  [4] View history                                                    │
│                                                                      │
╰───────────────────────────────────────────────────── ctrl+c to exit ─╯
```

### Mode Descriptions

1. **Fill sorries in a lean file (.lean)** - Automatically fills in `sorry` placeholders in Lean proof files
2. **Prove and formalize from an existing file (.tex, .md, .txt)** - Takes LaTeX, Markdown, or text files with mathematical content and converts them to formal Lean proofs
3. **Direct Aristotle in English (.lean optional)** - Allows you to describe mathematical problems in natural English and optionally provide a Lean context file
4. **View history** - Shows previous Aristotle sessions/proofs

## CLI Interface

### Basic Usage
```bash
aristotle [OPTIONS] {prove-from-file} ...
```

### prove-from-file Command

The main CLI command for proving theorems:

```bash
aristotle prove-from-file [OPTIONS] input_file
```

#### Key Options:
- `--informal` - Use informal/English input instead of formal Lean
- `--output-file OUTPUT_FILE` - Specify where to save the solution (default: [input]_aristotle.lean)
- `--context-files [FILES...]` - Additional context files to include
- `--formal-input-context FILE` - Lean file with formal context (works with --informal)
- `--context-folder FOLDER` - Folder with context files (.lean, .md, .txt, .tex)
- `--no-wait` - Don't wait for completion; just kick off the proof
- `--polling-interval SECONDS` - How often to check for completion (default: 30s)
- `--silent` - Don't print output to console
- `--no-auto-add-imports` - Disable automatic import resolution
- `--no-validate-lean-project` - Skip Lean project validation

### Examples

**Formal Lean input:**
```bash
aristotle prove-from-file problem.lean
```

**Informal English input:**
```bash
aristotle prove-from-file --informal problem.md
```

**English with Lean context:**
```bash
aristotle prove-from-file --informal problem.txt --formal-input-context definitions.lean
```

## TUI Interaction Notes

- The TUI uses ANSI escape codes for a full-screen terminal interface
- Background is dark gray (color 233)
- Uses box-drawing characters for borders
- Interactive, requires keyboard input (1-4 to select modes)
- Exit with Ctrl+C
- Standard piping/redirection doesn't work with the TUI (it requires a real TTY)

## English Mode (#3)

This appears to be the most flexible mode:
- Describe mathematical problems in natural English
- Optionally provide a `.lean` file for context/definitions
- Aristotle will formalize and prove the theorem
- Useful for converting informal math into rigorous formal proofs

## How to Submit Problems in English Mode

### Via TUI:
1. Launch: `ARISTOTLE_API_KEY="..." aristotle`
2. Press `3` to select "Direct Aristotle in English (.lean optional)"
3. Follow the prompts to either:
   - Describe your problem in natural language
   - Optionally provide a .lean file with context/definitions

### Via CLI:
```bash
# Create a text/markdown file with your problem description
echo "Prove that the square root of 2 is irrational" > problem.txt

# Run Aristotle with informal mode
aristotle prove-from-file --informal problem.txt

# Or with Lean context:
aristotle prove-from-file --informal problem.txt --formal-input-context definitions.lean
```

## Visual Interface

The TUI features:
- Centered layout with decorative borders
- Blue accent color for the header box
- Light gray for menu borders
- Dark gray background throughout
- Clear visual hierarchy
- Professional, mathematical aesthetic

## Additional Features

- **Automatic import resolution** - Aristotle can automatically figure out what Lean imports are needed
- **Project validation** - Validates Lean project structure before proving
- **Async operation** - Can kick off proofs and check back later with `--no-wait`
- **History tracking** - Keeps history of previous proofs (Mode 4)

## Website
https://aristotle.harmonic.fun
