#!/bin/sh
# Mutation test: corrupt one *load-bearing* datum and confirm the build fails.
#
# Which occurrence is mutated matters.  Each certificate coefficient appears twice in a
# generated file: once in a `have hⱼ : 0 ≤ Gⱼ αʲ (U-α)^(d-j)` and once in the identity `hid`.
# Perturbing the first is invisible — `linarith` only uses those hypotheses as "this quantity
# is nonnegative", and a positive rescaling of a nonnegative quantity is still nonnegative.
# The identity is what carries the content, so that is the occurrence to corrupt.  Likewise
# the moment data (`Nmomc`) is load-bearing and is checked against the packed recurrence.
cd "$(dirname "$0")/.." || exit 1
rc=0

mutate () {
  file=$1; from=$2; to=$3; nth=$4; label=$5; target=$6
  python - "$file" "$from" "$to" "$nth" <<'PY' || exit 1
import io, sys
p, a, b, nth = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
s = io.open(p, encoding="utf-8").read()
assert s.count(a) >= nth, f"only {s.count(a)} occurrences of {a}, wanted #{nth}"
i = -1
for _ in range(nth):
    i = s.index(a, i + 1)
io.open(p, "w", encoding="utf-8", newline="\n").write(s[:i] + b + s[i+len(a):])
PY
  if lake build "$target" >/dev/null 2>&1; then
    echo "!! SURVIVED: $label"
    rc=1
  else
    echo "ok, build fails: $label"
  fi
  git checkout -- "$file"
}

# the Bernstein identity of the smallest batch (2nd occurrence = inside `hid`)
mutate Sendov/FiniteRange/Degree6_6.lean "69425" "69426" 2 \
  "Degree6_6, Bernstein identity coefficient" Sendov.FiniteRange.Degree6_6

# a coefficient of the certified polynomial P itself
mutate Sendov/FiniteRange/Degree6_6.lean "2345" "2346" 1 \
  "Degree6_6, coefficient of P" Sendov.FiniteRange.Degree6_6

# a moment datum, checked against the packed recurrence rather than against a certificate
mutate Sendov/FiniteRange/Degree6_6.lean "def Nmomc : List ℤ :=" "def Nmomc : List ℤ := [0] ++" 1 \
  "Degree6_6, moment data" Sendov.FiniteRange.Degree6_6

# the degree-58 endgame certificate
mutate Sendov/LargeDegree/Endgame.lean "1939200000" "1939200001" 1 \
  "Endgame, the T1 constant" Sendov.LargeDegree.Endgame

# the tail-1 monotonicity certificate.  Here the 1st occurrence is in the module docstring
# and the 2nd is the inert `have h2`, so the identity is the 3rd.
mutate Sendov/LargeDegree/Monotone.lean "27356448" "27356449" 3 \
  "Monotone, tail1_poly identity coefficient" Sendov.LargeDegree.Monotone

echo "=== mutation test finished (rc=$rc) ==="
exit $rc
