#!/bin/sh
# Verify the model and the conformance proofs, then check the copied code against the original source.
set -e
cd "$(dirname "$0")"
VERUS=${VERUS:-verus}
$VERUS --crate-type lib lib.rs 2>&1 | grep -E "^error|verification results"
python3 -I check_diff.py
