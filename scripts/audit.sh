#!/bin/sh
# Trust audit for the Sendov development.  See docs/design.md §8 for the policy.
#
#   1. no forbidden tokens anywhere in Sendov/
#   2. the top-level results depend on the three standard axioms only
#
# Resource knobs (maxHeartbeats / maxRecDepth) are listed, not flagged: they are recorded
# deliberately and are not escape hatches.
cd "$(dirname "$0")/.." || exit 1
rc=0

echo "=== 1. forbidden tokens ==="
hits=$(grep -rnE '\bsorry\b|^ *axiom |native_decide|\bunsafe \b|\bpartial def\b|Float' \
         Sendov/ --include=*.lean | grep -vE ':[0-9]+: *--' | grep -vE '`sorry`')
if [ -n "$hits" ]; then
  echo "$hits"
  rc=1
else
  echo "none"
fi

echo
echo "=== 2. resource knobs in use (informational) ==="
grep -rn "set_option max" Sendov/ --include=*.lean \
  | sed 's/:.*set_option/  set_option/' | sort | uniq -c | sort -rn | head -20

echo
echo "=== 3. axioms of the top-level results ==="
out=$(lake env lean scripts/axioms.lean 2>&1)
echo "$out"
if echo "$out" | grep -qE "sorryAx|ofReduceBool|ofReduceNat"; then
  echo "!! non-standard axiom present"
  rc=1
fi

echo
echo "=== audit finished (rc=$rc) ==="
exit $rc
