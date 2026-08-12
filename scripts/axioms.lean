import Sendov.Reduction.Main
import Sendov.Interior
import Sendov.Boundary
import Sendov.Conjecture

/-!
Run with `lake env lean scripts/axioms.lean`.  This file is deliberately *not* part of the
library: it exists so that the axiom check is an explicit, separately-run audit step rather
than something buried in a build log.

Every result below must depend on `propext`, `Classical.choice` and `Quot.sound` only.  In
particular `sorryAx` must not appear, and neither must `Lean.ofReduceBool` (which is what
`native_decide` introduces).
-/

#print axioms Sendov.stat_lt_one
#print axioms Sendov.stat_contradiction
#print axioms Sendov.finite_range
#print axioms Sendov.finite_range_le_100
#print axioms Sendov.large_degree
#print axioms Sendov.polar_origin_incompatible
#print axioms Sendov.alpha_le_seventeen
#print axioms Sendov.sendov_interior
#print axioms Sendov.sendov_center
#print axioms Sendov.sendov_interior_real
#print axioms Sendov.rubinstein_one
#print axioms Sendov.sendov_boundary_one
#print axioms Sendov.phelps_rodriguez
#print axioms Sendov.sendov
