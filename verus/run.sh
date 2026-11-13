#!/bin/sh
# Verify the model and the conformance proofs, then check the copied code against the original source.
set -e
cd "$(dirname "$0")"
VERUS=${VERUS:-/hdd1/sichangheagent/vl_meeting_work/tools/verus-x86-linux/verus}
$VERUS --crate-type lib lib.rs 2>&1 | grep -E "^error|verification results"
python3 -I check_diff.py
