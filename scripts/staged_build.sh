#!/bin/sh
# Lake in this toolchain has no --jobs flag, and a simultaneous rebuild of all 31 batch
# files exhausts memory (Lean exits 0xC0000409, reported as `failed to read file ...olean`).
# Build them a few at a time instead.  Note that any edit to Statement.lean, even to a
# docstring, invalidates every one of them.
cd "$(dirname "$0")/.." || exit 1
set -- \
  "Sendov.Common.Basic Sendov.Common.Rpow Sendov.FiniteRange.Batch" \
  "Sendov.FiniteRange.Moments Sendov.FiniteRange.OddBound Sendov.FiniteRange.Pack" \
  "Sendov.FiniteRange.Recurrence Sendov.FiniteRange.PackBridge Sendov.FiniteRange.Reduce" \
  "Sendov.FiniteRange.Degree5 Sendov.FiniteRange.Degree6 Sendov.FiniteRange.Degree7" \
  "Sendov.FiniteRange.Degree8 Sendov.FiniteRange.Degree20" \
  "Sendov.FiniteRange.Degree20Packed Sendov.FiniteRange.Degree53Packed" \
  "Sendov.FiniteRange.Degree97Packed" \
  "Sendov.FiniteRange.Degree6_6 Sendov.FiniteRange.Degree8_9 Sendov.FiniteRange.Degree10_11" \
  "Sendov.FiniteRange.Degree12_13 Sendov.FiniteRange.Degree14_15 Sendov.FiniteRange.Degree16_18" \
  "Sendov.FiniteRange.Degree18_20 Sendov.FiniteRange.Degree20_22 Sendov.FiniteRange.Degree22_24" \
  "Sendov.FiniteRange.Degree24_26 Sendov.FiniteRange.Degree26_27 Sendov.FiniteRange.Degree28_29" \
  "Sendov.FiniteRange.Degree30_31 Sendov.FiniteRange.Degree32_33" \
  "Sendov.FiniteRange.Degree34_35 Sendov.FiniteRange.Degree36_37" \
  "Sendov.FiniteRange.Degree38_39 Sendov.FiniteRange.Degree40_41" \
  "Sendov.FiniteRange.Degree42_43 Sendov.FiniteRange.Degree44_45" \
  "Sendov.FiniteRange.Degree46_47 Sendov.FiniteRange.Degree48_49" \
  "Sendov.FiniteRange.Degree50_51 Sendov.FiniteRange.Degree52_53" \
  "Sendov.FiniteRange.Degree54_55 Sendov.FiniteRange.Degree56_58" \
  "Sendov.FiniteRange.Degree58_60 Sendov.FiniteRange.Degree60_63" \
  "Sendov.FiniteRange.Degree64_69" \
  "Sendov.FiniteRange.Degree70_79" \
  "Sendov.FiniteRange.Degree80_100" \
  "Sendov.FiniteRange.Cover" \
  "Sendov.LargeDegree.Beta Sendov.LargeDegree.Tail" \
  "Sendov.LargeDegree.Monotone" \
  "Sendov.LargeDegree.Endgame" \
  "Sendov.Main" \
  "Sendov"
fail=0
for g in "$@"; do
  out=$(lake build $g 2>&1)
  if echo "$out" | grep -q "^error"; then
    echo "=== FAILED: $g"
    echo "$out" | grep -v "^info" \
      | grep -viE "longLine|linter|missing space|should be written|This part of the code|This line exceeds" \
      | tail -30
    fail=1
  else
    echo "ok: $g"
  fi
done
echo "=== staged build finished (fail=$fail) ==="
