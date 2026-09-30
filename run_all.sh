#!/usr/bin/env bash
# Re-run the whole audit, keep one log per step, and fail loudly if any check does not pass.
set -euo pipefail
cd "$(dirname "$0")"
REC=data/lambda4-campaign.json
WANT=a3cae1ee336d7c4e7fb9f56b4f125333728347ffeb9f6b2518a1a2aee7461a6e
GOT=$( (sha256sum "$REC" 2>/dev/null || shasum -a 256 "$REC") | cut -d' ' -f1)
[ "$GOT" = "$WANT" ] || { echo "record checksum mismatch: $GOT"; exit 1; }

mkdir -p logs
run() { echo "== $1"; python3 "$@" | tee "logs/$(basename "$1" .py).log"; }
run step0_value.py
run step1_generic.py
run step2_family_d2c.py "$REC"
run step3_families_L3.py "$REC"
run step4_L45_families.py "$REC"
run step5_family_d2b.py "$REC"
run step6_family_2d2cb.py "$REC"
run step7_family_2d3c.py "$REC"
run step8_global_sweep.py 80

# Every failure mode the scripts can print:
FAIL='MISMATCH|identical: False|record match: False|matches record: False|one-to-one match: False'
FAIL+='|divides the resultant exactly: False|failures \[\(|failures: \[|search failures\): \['
FAIL+='|[1-9][0-9]* NOT certified| FAIL$'
if grep -E -n "$FAIL" logs/*.log; then echo "AUDIT FAILED"; exit 1; fi
echo "ALL CHECKS PASSED"
