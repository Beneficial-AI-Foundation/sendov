#!/bin/sh
# Trust audit for the Sendov development.  See docs/design.md §8 for the policy.
#
#   1. no forbidden tokens anywhere in Sendov/ or in Solution.lean
#   2. Challenge.lean holds exactly the two deliberate holes it is supposed to
#   3. the top-level results depend on the three standard axioms only
#
# Resource knobs (maxHeartbeats / maxRecDepth) are listed, not flagged: they are recorded
# deliberately and are not escape hatches.
cd "$(dirname "$0")/.." || exit 1
rc=0

echo "=== 1. forbidden tokens ==="
# Challenge.lean is excluded here and audited separately in step 2: it is the Palomar
# statement of record, and Comparator requires its declarations to be deliberate holes.
hits=$(grep -rnE '\bsorry\b|^ *axiom |native_decide|\bunsafe \b|\bpartial def\b|Float' \
         Sendov/ Solution.lean --include=*.lean | grep -vE ':[0-9]+: *--' | grep -vE '`sorry`')
if [ -n "$hits" ]; then
  echo "$hits"
  rc=1
else
  echo "none"
fi

echo
echo "=== 2. Challenge.lean: deliberate holes only ==="
# The Challenge states the result and does not prove it; Comparator checks that Solution
# supplies proofs of exactly these statements.  Two holes, one per compared theorem, and
# nothing else forbidden.
holes=$(grep -cE '\bsorry\b' Challenge.lean)
other=$(grep -nE '^ *axiom |native_decide|\bunsafe \b|\bpartial def\b|Float' Challenge.lean \
          | grep -vE ':[0-9]+: *--')
echo "deliberate holes: $holes (expected 2, one per compared theorem)"
if [ "$holes" != "2" ] || [ -n "$other" ]; then
  echo "$other"
  echo "!! Challenge.lean does not have exactly its two deliberate holes"
  rc=1
fi

echo
echo "=== 3. resource knobs in use (informational) ==="
grep -rn "set_option max" Sendov/ --include=*.lean \
  | sed 's/:.*set_option/  set_option/' | sort | uniq -c | sort -rn | head -20

echo
echo "=== 4. axioms of the top-level results ==="
out=$(lake env lean scripts/axioms.lean 2>&1)
echo "$out"
if echo "$out" | grep -qE "sorryAx|ofReduceBool|ofReduceNat"; then
  echo "!! non-standard axiom present"
  rc=1
fi

echo
echo "=== audit finished (rc=$rc) ==="
exit $rc
