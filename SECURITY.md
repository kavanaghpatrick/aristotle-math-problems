# Security Best Practices

## Environment Variables

**NEVER commit API keys or secrets to git.** This repository uses environment variables for all sensitive data.

### Setup

1. Copy the example environment file:
   ```bash
   cp .env.example .env
   ```

2. Edit `.env` and add your actual API keys:
   ```bash
   ARISTOTLE_API_KEY=your_actual_key_here
   GROK_API_KEY=your_actual_key_here  # optional
   ```

3. The `.env` file is in `.gitignore` and will never be committed.

### Required Environment Variables

| Variable | Required | Where to Get |
|----------|----------|--------------|
| `ARISTOTLE_API_KEY` | Yes | https://aristotle.harmonic.fun |
| `GROK_API_KEY` | No (optional) | https://x.ai |

### GitHub Authentication

The `gh` CLI tool uses macOS keyring authentication, not environment variables.

Run once: `gh auth login`

## Files Protected by .gitignore

The following files/patterns are automatically ignored:

- `.env`, `.env.local`, `.env.*.local` - Environment variables
- `*.key`, `*_secrets.*`, `*_credentials.*` - Secret files
- `.aristotle_submit.lock` - Submission lockfile

## Code Standards

### ✅ CORRECT - Use environment variables

```python
import os
from aristotlelib import set_api_key

set_api_key(os.environ["ARISTOTLE_API_KEY"])
```

### ❌ WRONG - Hardcoded API keys

```python
# NEVER DO THIS
set_api_key("os.environ["ARISTOTLE_API_KEY"]")
```

### ✅ CORRECT - Relative paths

```python
from pathlib import Path

# Auto-detect repository root
REPO_ROOT = Path(__file__).resolve().parent.parent
```

### ❌ WRONG - Hardcoded personal paths

```python
# NEVER DO THIS
MATH_DIR = Path("/Users/patrickkavanagh/math")
```

## Pre-Commit Checklist

Before committing:

- [ ] No API keys or secrets in code
- [ ] No hardcoded personal paths
- [ ] All scripts use environment variables
- [ ] `.env` file is in `.gitignore`
- [ ] Tested with environment variables loaded

## What to Do If You Accidentally Commit a Secret

1. **Immediately rotate the secret** (get a new API key)
2. Update your `.env` file with the new key
3. The old key is now useless even if it's in git history

**Note**: Rewriting git history (git filter-branch) is complex and can break things for collaborators. It's safer and faster to just rotate the credential.

## Security Audit Commands

Check for potential secrets:
```bash
# Search for common secret patterns
grep -r "api_key\|API_KEY\|token\|password\|secret" . \
  --include="*.py" --include="*.sh" --include="*.md" \
  --exclude-dir=.git --exclude-dir=archive

# Check for hardcoded paths
grep -r "/Users/" . \
  --include="*.py" --include="*.sh" \
  --exclude-dir=.git --exclude-dir=archive
```

## Reporting Security Issues

If you find a security vulnerability, please do NOT open a public issue.

Contact: [Your contact method here]
