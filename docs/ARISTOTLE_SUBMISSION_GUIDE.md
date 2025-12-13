# Aristotle Submission Guide - Preventing Duplicates

**Last Updated**: December 12, 2025

## ⚠️ PROBLEM: Double Submissions

**What happened**: On Dec 12, we accidentally submitted the same task twice:
- First submission: `771e9804` (19 seconds earlier, went to IN_PROGRESS)
- Second submission: `841ddada` (duplicate, stayed in QUEUED)

**Root cause**: Script error AFTER API call succeeded
- API call launched project successfully
- Then script crashed trying to access `project.id`
- Script was fixed and re-run
- Second run submitted again

## ✅ SOLUTION: Defense-in-Depth Safety Checks

Use `safe_aristotle_submit.py` instead of direct API calls.

### Four-Layer Safety Protocol:

1. **🔒 Lockfile** - Prevents concurrent submissions
2. **🔍 Duplicate Detection** - Checks if same task submitted recently (10min window)
3. **📊 Queue Capacity** - Aborts if queue is full (5/5 slots)
4. **💾 Atomic ID Save** - Saves project ID immediately after API call

### Transaction Logging:

All submissions are logged to `aristotle_submission_log.jsonl`:
```json
{"timestamp": "2025-12-12T01:05:00", "action": "pre_submit", "details": {...}}
{"timestamp": "2025-12-12T01:05:05", "action": "submitted", "details": {...}}
```

## 📖 HOW TO USE

### Method 1: CLI (Recommended for Scripts)

```bash
python3 safe_aristotle_submit.py \\
  unknotting/batch1.txt \\
  BATCH1_PROJECT_ID.txt \\
  "First batch of 10 knots at 9 crossings"
```

**What it does**:
1. Computes SHA256 hash of input file
2. Checks if that hash was submitted in last 10 minutes
3. Checks if queue has capacity
4. Submits and immediately saves project ID
5. Logs everything to transaction log

### Method 2: Python API

```python
import asyncio
from pathlib import Path
from safe_aristotle_submit import safe_submit

async def my_submission():
    project_id = await safe_submit(
        input_file=Path("unknotting/batch1.txt"),
        project_id_file=Path("BATCH1_ID.txt"),
        description="First batch of 10 knots",
        force=False  # Set to True to skip safety checks
    )
    print(f"Submitted: {project_id}")

asyncio.run(my_submission())
```

### Method 3: With Retry Logic

```python
from safe_aristotle_submit import submit_with_retry

# Retries on network errors, NOT on duplicates/full queue
project_id = await submit_with_retry(
    input_file=Path("batch.txt"),
    project_id_file=Path("ID.txt"),
    description="My task",
    max_retries=3,      # Default: 3
    retry_delay=30      # Default: 30s, exponential backoff
)
```

## 🚨 SAFETY CHECK FAILURES

The script will ABORT (not retry) if:

1. **Lockfile exists** - Another submission in progress
   ```
   ❌ Another submission is in progress (lockfile exists)
   ```
   **Fix**: Wait a few minutes or check `.aristotle_submit.lock`

2. **Recent duplicate** - Same task submitted <10min ago
   ```
   ❌ Task already submitted in last 10 minutes! Found 1 matching submission(s)
   ```
   **Fix**: This is GOOD - it prevented a duplicate!

3. **Queue full** - All 5 slots occupied
   ```
   ❌ Queue is full (5/5 slots used). Wait for a slot to free up.
   ```
   **Fix**: Wait for a project to complete, or use `monitor_and_launch.py`

4. **Invalid file** - File missing, empty, or too large
   ```
   ❌ Input file does not exist: batch.txt
   ```
   **Fix**: Check file path

## 🔧 TROUBLESHOOTING

### Stale Lockfile

If lockfile is >5 minutes old, it's automatically removed.

Manual removal:
```bash
rm /Users/patrickkavanagh/math/.aristotle_submit.lock
```

### False Duplicate Detection

If you REALLY want to resubmit the same file:

**Option 1**: Wait 10 minutes (duplicate window expires)

**Option 2**: Modify the input file slightly (changes hash)
```bash
echo "" >> batch.txt  # Add blank line
```

**Option 3**: Use `--force` flag (DANGEROUS!)
```bash
python3 safe_aristotle_submit.py batch.txt ID.txt "Desc" --force
```

### Check Transaction Log

```bash
# View all submissions
cat aristotle_submission_log.jsonl

# View last 5 submissions
tail -5 aristotle_submission_log.jsonl | python3 -m json.tool

# Find submissions by hash
grep "abc123" aristotle_submission_log.jsonl
```

## 📋 UPDATING EXISTING SCRIPTS

### Before (Unsafe):
```python
project = await Project.prove_from_file(
    input_file_path="batch.txt",
    project_input_type=ProjectInputType.INFORMAL,
    wait_for_completion=False
)
project_id = project.id  # ❌ Could fail here, but project already submitted!
```

### After (Safe):
```python
from safe_aristotle_submit import safe_submit

project_id = await safe_submit(
    input_file=Path("batch.txt"),
    project_id_file=Path("ID.txt"),
    description="My batch"
)
# ✅ ID saved atomically, no duplicates possible
```

## 🎯 BEST PRACTICES

1. **Always use `safe_aristotle_submit.py`** for production submissions
2. **Never run submission scripts manually twice** - let the safety checks handle it
3. **Check transaction log** before debugging "missing" submissions
4. **Save project IDs immediately** - use the built-in ID file mechanism
5. **Use descriptive descriptions** - helps in logs and issue tracking

## 📊 MONITORING

### Check Recent Submissions
```bash
python3 check_recent_submissions.py
```

### Check Queue Status
```bash
python3 check_queue.py
```

### Automated Launch When Queue Opens
```bash
# Monitors queue and auto-launches when a slot opens
python3 monitor_and_launch.py batch.txt ID.txt "Description"
```

## ✅ INTEGRATION WITH GITHUB WORKFLOW

When creating issues for Aristotle batches:

```bash
# 1. Prepare batch
python3 prepare_aristotle_batch.py

# 2. SAFE submission
PROJECT_ID=$(python3 safe_aristotle_submit.py \\
  unknotting/batch1.txt \\
  BATCH1_ID.txt \\
  "Batch 1: 10 knots at 9 crossings" | grep "Project ID:" | awk '{print $3}')

# 3. Update GitHub
gh issue comment 49 --body "✅ Batch 1 submitted: ${PROJECT_ID}"
```

## 🚀 FUTURE IMPROVEMENTS

Potential enhancements:

1. **Database backend** - SQLite instead of JSONL
2. **Web dashboard** - Visualize all submissions
3. **Slack/email notifications** - Alert on submission success/failure
4. **Automatic queue monitoring** - Submit when slots open
5. **Project deduplication** - Cancel duplicates automatically via API

---

**Remember**: The goal is to NEVER manually submit twice. Let the automation handle it!
