# Duplicate Submission Prevention System

**Created**: December 12, 2025
**Reason**: Prevented future double submissions after incident (771e9804 + 841ddada)

---

## 🎯 QUICK START

### For Future Batches:

```bash
# 1. Prepare your batch
python3 prepare_aristotle_batch.py

# 2. Submit using safe wrapper (ONE command, handles everything)
./submit_batch.sh 9crossing_test "First test batch: 10 knots at 9 crossings"

# 3. Monitor
python3 check_queue.py
```

That's it! The wrapper handles all safety checks automatically.

---

## 📊 THE PROBLEM (What Happened)

**Date**: December 12, 2025 01:04
**Incident**: Double submission of same batch

**Timeline**:
- 01:03:49 - First submission succeeded (project `771e9804`)
- Script crashed with `AttributeError: 'str' object has no attribute 'id'`
- Fixed script
- 01:04:08 - Re-ran script, submitted again (project `841ddada`)
- **Result**: Two identical projects running (19 seconds apart)

**Root Cause**:
- First submission completed API call successfully
- Script then crashed trying to print/save the project ID
- Script appeared to have failed, so we re-ran it
- Second run submitted again since there was no saved ID file

---

## ✅ THE SOLUTION (Defense-in-Depth)

### Four Safety Layers:

#### 1. 🔒 Lockfile Prevention
- Creates `.aristotle_submit.lock` before submission
- Prevents concurrent submissions from multiple terminals
- Auto-expires after 5 minutes (prevents stale locks)

#### 2. 🔍 Duplicate Detection
- Computes SHA256 hash of input file
- Checks if same hash submitted in last 10 minutes
- Searches both transaction log (fast) and API (authoritative)
- **Result**: Same file = instant abort, no API call made

#### 3. 📊 Queue Capacity Check
- Checks current queue status (max 5 concurrent projects)
- Aborts if queue is full
- Shows available slots
- **Result**: No wasted submissions when queue full

#### 4. 💾 Atomic ID Save
- Saves project ID IMMEDIATELY after API call
- Before any other operations that might fail
- Includes metadata (description, hash, timestamp)
- **Result**: Even if script crashes later, ID is saved

### Transaction Logging:

All submissions logged to `aristotle_submission_log.jsonl`:

```json
{"timestamp": "2025-12-12T01:05:00", "action": "pre_submit", "details": {"task_hash": "abc123", ...}}
{"timestamp": "2025-12-12T01:05:05", "action": "submitted", "details": {"project_id": "771e9804", ...}}
```

**Benefits**:
- Full audit trail of all submissions
- Can search by hash to find duplicates
- Debugging aid for "where did I submit this?"

---

## 🛠️ TOOLS PROVIDED

### 1. `safe_aristotle_submit.py` (Core)
**Purpose**: Safe submission with all safety checks
**Usage**:
```bash
python3 safe_aristotle_submit.py input.txt ID.txt "Description"
```

**Features**:
- All 4 safety layers enabled by default
- `--force` flag to bypass checks (use with caution!)
- Retry logic with exponential backoff (network errors only)
- Clear error messages for each safety check failure

### 2. `submit_batch.sh` (Wrapper)
**Purpose**: Simple wrapper for common case
**Usage**:
```bash
./submit_batch.sh batch_name "Description"
```

**What it does**:
- Checks if input file exists
- Calls `safe_aristotle_submit.py`
- Displays success/failure clearly
- Prints next steps

### 3. `ARISTOTLE_SUBMISSION_GUIDE.md` (Docs)
**Purpose**: Complete reference guide
**Contains**:
- Problem explanation
- Solution details
- Usage examples
- Troubleshooting guide
- Best practices

### 4. `check_recent_submissions.py` (Monitoring)
**Purpose**: Find duplicates after the fact
**Usage**:
```bash
python3 check_recent_submissions.py
```

**Shows**:
- All submissions in last hour
- Duplicate detection (submissions <60s apart)
- Project IDs and statuses

---

## 📋 SAFETY CHECK BEHAVIORS

### ✅ PASS - Submission Proceeds

```
🔒 SAFE SUBMISSION PROTOCOL
==================================================
1️⃣  Checking lockfile...
   ✅ Lock acquired
2️⃣  Checking for recent duplicates...
   ✅ No recent duplicates found
3️⃣  Checking queue capacity...
   ✅ Queue has capacity (2 slots available)
4️⃣  Validating input file...
   ✅ File valid (28,045 bytes)

🚀 All safety checks passed! Submitting to Aristotle...
✅ SUBMISSION SUCCESSFUL!
   Project ID: 771e9804-7c02-4c86-b767-ac1b9f9742e1
```

### ❌ FAIL - Duplicate Detected (GOOD!)

```
1️⃣  Checking lockfile...
   ✅ Lock acquired
2️⃣  Checking for recent duplicates...
❌ Submission aborted: Task already submitted in last 10 minutes!
   Found 1 matching submission(s)
```

**This is the desired behavior!** Prevented a duplicate.

### ❌ FAIL - Queue Full

```
3️⃣  Checking queue capacity...
❌ Submission aborted: Queue is full (5/5 slots used).
   Wait for a slot to free up.
```

**Correct behavior** - Use `monitor_and_launch.py` to auto-submit when queue opens.

---

## 🔧 HOW IT WORKS INTERNALLY

### Hash-Based Deduplication:

```python
# Compute SHA256 of entire input file
task_hash = hashlib.sha256(file_contents).hexdigest()[:16]
# Example: "a3f5c8d91e4b2679"

# Search transaction log for matching hash in last 10 minutes
recent_submissions = filter(lambda x: x['task_hash'] == task_hash)

# If found → ABORT
if recent_submissions:
    raise SubmissionError("Duplicate detected!")
```

**Why this works**:
- Same input file = same hash = guaranteed duplicate
- Different input file = different hash = allowed
- Adding even one character changes the hash
- 10-minute window balances safety vs. flexibility

### Atomic ID Save:

```python
# Submit to API
result = await Project.prove_from_file(...)

# Extract ID immediately
project_id = result if isinstance(result, str) else result.project_id

# SAVE IT RIGHT NOW (before anything else)
with open(id_file, 'w') as f:
    f.write(f"{project_id}\n")

# Now safe to do other things (they might fail, but ID is saved)
log_transaction("submitted", {...})
print(f"Success! {project_id}")
```

**Why this works**:
- Even if script crashes after this point, ID is saved
- Next run will find the ID file and know submission succeeded
- No orphaned projects with unknown IDs

---

## 🎓 LESSONS LEARNED

### What We Learned:

1. **Never trust script success** - Save critical data IMMEDIATELY
2. **Idempotency is key** - Same request multiple times = same result
3. **Hash-based deduplication** - Simple, fast, reliable
4. **Multiple safety layers** - Defense-in-depth prevents all scenarios
5. **Transaction logging** - Invaluable for debugging

### Anti-Patterns to Avoid:

❌ **Saving ID at end of script** - Crash before save = orphaned project
❌ **No duplicate detection** - Same request = multiple projects
❌ **No queue checks** - Submit when full = wasted submission
❌ **Manual retries** - Human error = duplicates
❌ **No audit trail** - Can't debug "where did I submit this?"

### Best Practices:

✅ **Use `safe_aristotle_submit.py` always** - Never use raw API
✅ **Save critical data atomically** - First thing after API call
✅ **Log everything** - Transaction log is your friend
✅ **Check queue before submit** - Respect the 5-project limit
✅ **Let automation retry** - Exponential backoff for transient errors

---

## 🚀 FUTURE ENHANCEMENTS

Possible improvements:

1. **API-based duplicate detection** - Cancel duplicates automatically
2. **Database backend** - SQLite instead of JSONL
3. **Web dashboard** - Visualize all submissions
4. **Queue monitoring** - Auto-submit when slots open
5. **Slack notifications** - Alert on success/failure
6. **Batch dependencies** - Wait for batch 1 before launching batch 2

---

## 📖 USAGE EXAMPLES

### Example 1: Simple Batch

```bash
# Prepare
python3 prepare_aristotle_batch.py  # Creates batch file

# Submit safely
./submit_batch.sh 10crossing_batch1 "Batch 1: 50 knots at 10 crossings"

# Output:
# ✅ SUCCESS! Project submitted and running.
#    Project ID: abc123-def456-...
```

### Example 2: Duplicate Prevention in Action

```bash
# First submission
./submit_batch.sh test_batch "Test"
# ✅ Success! Project ID: abc123

# Accidental second submission (same file)
./submit_batch.sh test_batch "Test"
# ❌ Task already submitted in last 10 minutes!
# (GOOD - prevented duplicate!)
```

### Example 3: Queue Full Handling

```bash
# Submit when queue full
./submit_batch.sh batch "Description"
# ❌ Queue is full (5/5 slots used)

# Use monitor to auto-submit when queue opens
python3 monitor_and_launch.py \
    unknotting/batch.txt \
    BATCH_ID.txt \
    "Description"
# 🔄 Monitoring queue... will submit when slot opens
```

---

## ✅ VERIFICATION

To verify the system is working:

```bash
# 1. Check safe_aristotle_submit.py exists and is executable
ls -la safe_aristotle_submit.py
# Should show: -rwxr-xr-x

# 2. Check transaction log is initialized
cat aristotle_submission_log.jsonl
# Should show recent submissions (if any)

# 3. Test with a dry run (optional)
python3 safe_aristotle_submit.py --help
# Should show usage

# 4. Verify CLAUDE.md has been updated
grep "safe_aristotle_submit" CLAUDE.md
# Should find the warning section
```

---

## 📞 SUPPORT

**If you encounter issues**:

1. Check `ARISTOTLE_SUBMISSION_GUIDE.md` for troubleshooting
2. Review transaction log: `cat aristotle_submission_log.jsonl`
3. Check for stale lockfile: `ls -la .aristotle_submit.lock`
4. Verify queue status: `python3 check_queue.py`
5. Look for recent duplicates: `python3 check_recent_submissions.py`

**Common fixes**:
- Stale lock: `rm .aristotle_submit.lock`
- Queue full: Wait or use `monitor_and_launch.py`
- False duplicate: Wait 10 minutes or modify input file

---

**Remember**: The goal is to NEVER manually submit twice. Let the automation prevent it! 🚀
