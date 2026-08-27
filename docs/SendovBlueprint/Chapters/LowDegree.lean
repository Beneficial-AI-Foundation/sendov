import Verso
import VersoManual
import VersoBlueprint
import Sendov

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Low degrees" =>

This chapter is the Blueprint rendering of `docs/plan-low-degrees.md`: Sendov's
conjecture in degrees $`2 \le n \le 5`, proved by branching off the interior
argument immediately after the exact polar identity. The Lean code lives in
`Sendov/Analytic/LowDegree.lean`. Neither Brannan's nor Rubinstein's classical
argument is formalized; only elementary real inequalities and integrals of
polynomials of degree at most four are used.

:::group "low_degree"
For a normalized interior obstruction of size m = n - 1 at most 4, the polar
branch point (star) is already contradictory: 1 <= J(a) < 1.
:::

# The input from the polar channel

:::definition "ld_setup" (parent := "low_degree") (lean := "Sendov.lowX, Sendov.lowJ")
For $`0 < a < 1`, write $`X_a(t) = a + (1 - a^2)t` and
$`J_m(a) = \int_0^1 X_a(t)^m\,dt`. In Lean: `Sendov.lowX` and `Sendov.lowJ`.
:::

:::theorem "ld_one_le_J" (parent := "low_degree") (lean := "Sendov.one_le_lowJ")
Suppose $`q_1, \dots, q_m` lie in the closed unit disk and the branch point
$`(\star)` holds, $`1 \le \int_0^1 \prod_j |a + t(1-a^2)q_j|\,dt`. Then
$`1 \le J_m(a)`. In Lean: `Sendov.one_le_lowJ`. Uses {uses "ld_setup"}[] and
{uses "in_polar_star"}[].
:::

:::proof "ld_one_le_J"
Pointwise, $`|a + t(1-a^2)q_j| \le a + t(1-a^2)|q_j| \le X_a(t)` because
$`a, t, 1 - a^2 \ge 0`; multiply over $`j` (`Sendov.prod_norm_le_lowX_pow`) and
integrate. *(Deviation from the plan.)* The plan's wrapper started from the
complex polar identity; the implementation starts one step later, from the
named real intermediate $`(\star)` exported by `Sendov.Analytic.Polar`, which the
design notes require the polar channel to expose precisely so that this branch
need not repeat the Möbius bound or the integral triangle inequality.
:::

# The scalar quartic estimate

:::lemma_ "ld_J4_identity" (parent := "low_degree") (lean := "Sendov.lowJ_four_identity")
$$`1 - J_4(a) = \frac{(1-a)^3(1+a)}5\left(a^4 - 3a^3 + 3a + 4\right).`
In Lean: `Sendov.lowJ_four_identity`, via the explicit fourth moment
`Sendov.lowJ_four` obtained by expanding $`X_a(t)^4` into five monomials and
integrating each. Uses {uses "ld_setup"}[].
:::

:::lemma_ "ld_quartic_pos" (parent := "low_degree") (lean := "Sendov.quartic_aux_pos")
For $`0 < a < 1`, $`a^4 - 3a^3 + 3a + 4 > 0`, because
$`a^4 - 3a^3 + 3a + 4 = 2 + 3a + (1-a)\bigl(2 + 2a + a^2(2-a)\bigr)`.
In Lean: `Sendov.quartic_aux_pos`.
:::

:::theorem "ld_J4_lt_one" (parent := "low_degree") (lean := "Sendov.lowJ_four_lt_one")
$`J_4(a) < 1` for $`0 < a < 1`. In Lean: `Sendov.lowJ_four_lt_one`. Uses
{uses "ld_J4_identity"}[] and {uses "ld_quartic_pos"}[].
:::

# Dominating exponents one through four

:::lemma_ "ld_pow_le_quartic" (parent := "low_degree") (lean := "Sendov.pow_le_quartic_average")
For $`X \ge 0` and $`1 \le m \le 4`,
$$`X^m \le 1 - \frac m4 + \frac m4 X^4.`
In Lean: `Sendov.pow_le_quartic_average`.
:::

:::proof "ld_pow_le_quartic"
Split the four values of $`m`. The nontrivial cases are the identities
$`X^4 - 4X + 3 = (X-1)^2(X^2 + 2X + 3)`,
$`X^4 - 2X^2 + 1 = (X^2 - 1)^2`, and
$`3X^4 - 4X^3 + 1 = (X-1)^2(3X^2 + 2X + 1)`; the case $`m = 4` is equality.
No weighted AM–GM library is built for this.
:::

:::theorem "ld_J_lt_one" (parent := "low_degree") (lean := "Sendov.lowJ_lt_one")
For $`0 < a < 1` and $`1 \le m \le 4`, $`J_m(a) < 1`. In Lean:
`Sendov.lowJ_lt_one`. Uses {uses "ld_pow_le_quartic"}[] and
{uses "ld_J4_lt_one"}[].
:::

:::proof "ld_J_lt_one"
$`X_a(t) \ge 0` on $`[0,1]`, so the pointwise bound integrates to
$`J_m(a) \le 1 - \tfrac m4 + \tfrac m4 J_4(a)`; since $`m > 0` and
$`J_4(a) < 1`, this is strictly below one.
:::

# The contradiction

:::theorem "ld_main" (parent := "low_degree") (lean := "Sendov.low_degree_contradiction")
*The low-degree claim.* For $`2 \le n \le 5`, $`0 < a < 1`, and points
$`q_1, \dots, q_{n-1}` of the closed unit disk, the branch point $`(\star)`
is impossible. In Lean: `Sendov.low_degree_contradiction`. Blog: Section 4, the $`n \le 4` cases, and Remark 16. Uses
{uses "ld_one_le_J"}[] and {uses "ld_J_lt_one"}[].
:::

:::proof "ld_main"
Combine $`1 \le J_{n-1}(a)` with $`J_{n-1}(a) < 1`. The obstruction size is
$`m = n - 1`, so $`n = 2, 3, 4, 5` correspond to $`m = 1, 2, 3, 4`; the
off-by-one is recorded in the statement through `q.card = n - 1`.
:::

# Notes

The strictness comes entirely from $`a < 1`: at $`a = 1` one has
$`J_m(1) = 1`, matching the regular-polygon equality cases. Degree five is
covered both here and by the finite-range certificate `Sendov.finite_range_five`;
the interior assembly `Sendov.sendov_interior` branches on $`n \le 5` versus
$`n \ge 5`, so the two proofs overlap at degree five as a redundancy check.
