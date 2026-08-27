import Verso
import VersoManual
import VersoBlueprint
import Sendov

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Rubinstein's boundary theorem" =>

This chapter is the Blueprint rendering of `docs/plan-boundary-rubinstein.md`:
Sendov's conjecture for a zero on the unit circle, with the equality
classification. The Lean code lives in `Sendov/Boundary.lean`, normalized to the
zero $`a = 1`; the rotation back to a general unimodular $`a` is done in
`Sendov/Conjecture.lean`.

The polar identity is useless here: at $`a = 1` the reflected point $`1/a`
coincides with $`a` and $`1 - a^2 = 0`. One elementary identity obtained from
$`p''(1)/p'(1)` replaces it. No polar integral, origin identity, defect lemma,
numerical certificate, or Gauss–Lucas theorem is used.

:::group "boundary"
If p has degree at least 2, all zeroes in the closed unit disk, and p(1) = 0,
then p' has a zero in the open disk D(1,1) unless p = c(z^n - 1).
:::

# Setup

:::definition "bd_setup" (parent := "boundary")
Write $`p = c(X - 1)\prod_j (X - z_j)` with $`|z_j| \le 1`, and, under the
contradiction hypothesis that every critical point $`w` has $`|1 - w| \ge 1`,
$`p' = nc\prod_j (X - w_j)`. Both families have $`n - 1` members counted with
multiplicity, provided by `Sendov.exists_root_multiset` and
`Sendov.exists_crit_multiset` of `Sendov/Counterexample/Factor.lean` — the only
part shared with the interior argument. The reciprocal coordinates are
$`q_j = 1/(1 - w_j)`, so $`|q_j| \le 1`. Uses {uses "in_factor"}[].
:::

:::lemma_ "bd_repeated_root" (parent := "boundary")
If $`1` is a multiple zero of $`p` then $`p'(1) = 0` and $`\zeta = 1` is a
strict witness. Hence under the contradiction hypothesis $`p'(1) \ne 0`, so
$`1` is simple and every $`z_j \ne 1`. This case split is made before any
division, inside `Sendov.rubinstein_one`. Uses {uses "bd_setup"}[].
:::

# The boundary reciprocal identity

:::theorem "bd_reciprocal" (parent := "boundary") (lean := "Sendov.boundary_reciprocal")
*(BR)* With $`Q = \prod_j (X - z_j)` and $`R = \prod_j (X - w_j)`, evaluating
$`p = c(X-1)Q` and $`p' = ncR` at $`1` gives $`Q(1) = nR(1)` and
$`2Q'(1) = nR'(1)` — the factor $`2` from $`p''(1) = 2Q'(1)` — whence
$$`\sum_j q_j = 2\sum_j \frac1{1 - z_j}.`
In Lean: `Sendov.boundary_reciprocal`, stated division-free in terms of
$`\sum_j\prod_{k\ne j}` (`Sendov.sumEraseProd`) with the products
$`\prod_j(1 - z_j)` and $`\prod_j(1 - w_j)` as inputs, so no junk value of
$`0^{-1}` is ever evaluated. Blog: [Lemma 15 (Meir–Sharma identity) at $`a = 1`](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#meir). Uses {uses "bd_setup"}[] and
{uses "bd_repeated_root"}[].
:::

:::proof "bd_reciprocal"
Evaluate $`\prod_j(X - s_j)` and its derivative at $`1`
(`Sendov.eval_prod_at`, `Sendov.eval_deriv_prod_at`), compare the two
factorizations of $`p'` at $`1` for both the value and the derivative, and
cancel the common nonzero factor $`p'(1)`. *(Deviation from the plan.)* The plan
offered a logarithmic-derivative route; the implementation takes the second,
division-free route and only divides at the very end.
:::

# The disk inequality

:::lemma_ "bd_half_le_re" (parent := "boundary") (lean := "Sendov.half_le_re_inv_one_sub")
For $`|z| \le 1` and $`z \ne 1`,
$$`\operatorname{Re}\frac1{1-z} - \frac12 = \frac{1 - |z|^2}{2|1-z|^2} \ge 0.`
In Lean: `Sendov.half_le_re_inv_one_sub`. Worked with squared norms throughout;
no square roots.
:::

:::lemma_ "bd_eq_one" (parent := "boundary") (lean := "Sendov.eq_one_of_re_eq_one_of_norm_le_one")
If $`\operatorname{Re} q = 1` and $`|q| \le 1` then $`q = 1`. In Lean:
`Sendov.eq_one_of_re_eq_one_of_norm_le_one`.
:::

# Sandwiching the reciprocal sum

:::theorem "bd_all_q_eq_one" (parent := "boundary") (lean := "Sendov.all_q_eq_one")
Let $`q_1,\dots,q_N` and $`z_1,\dots,z_N` lie in the closed unit disk with
every $`z_j \ne 1` and $`\sum_j q_j = 2\sum_j (1 - z_j)^{-1}`. Then every
$`q_j = 1`. In Lean: `Sendov.all_q_eq_one`. Uses {uses "bd_reciprocal"}[],
{uses "bd_half_le_re"}[], and {uses "bd_eq_one"}[].
:::

:::proof "bd_all_q_eq_one"
From $`\operatorname{Re} q_j \le |q_j| \le 1` the real part of the left side
is at most $`N`; from the disk inequality the real part of the right side is
at least $`N`. So $`\sum_j (1 - \operatorname{Re} q_j) = 0` with nonnegative
terms (`Sendov.eq_zero_of_sum_eq_zero`), forcing $`\operatorname{Re} q_j = 1`
and then $`q_j = 1` term by term.
:::

# Classification

:::theorem "bd_rubinstein_one" (parent := "boundary") (lean := "Sendov.rubinstein_one")
*The strict-or-extremal alternative at $`a = 1`.* If $`p` has degree
$`n \ge 2`, all zeroes in the closed unit disk, and $`p(1) = 0`, then either
$`p'` has a zero $`\zeta` with $`|\zeta - 1| < 1`, or
$`p = \operatorname{lc}(p)\,(X^n - 1)`. In Lean: `Sendov.rubinstein_one`. Blog: [Theorem 14 (Rubinstein's theorem), Section 3](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#meir). Uses
{uses "bd_repeated_root"}[] and {uses "bd_all_q_eq_one"}[].
:::

:::proof "bd_rubinstein_one"
Suppose no strict witness exists. Then every $`q_j = 1`, so every
$`w_j = 0` and $`p' = nc\,X^{n-1}`. Hence $`p - cX^n` has zero derivative and is
constant in characteristic zero; evaluating at $`1` identifies the constant as
$`-c`.
:::

:::corollary "bd_sendov_one" (parent := "boundary") (lean := "Sendov.sendov_boundary_one")
*Closed-disk form.* Under the same hypotheses $`p'` has a zero $`\zeta` with
$`|\zeta - 1| \le 1`. In the strict branch weaken $`<` to $`\le`; in the
extremal branch take $`\zeta = 0`. In Lean: `Sendov.sendov_boundary_one`. Uses
{uses "bd_rubinstein_one"}[].
:::

# Notes

Rotating back from $`1` to a general zero $`a` with $`|a| = 1` produces the
extremal polynomial $`c\,\omega^{-n}(z^n - a^n)`, not $`z^n - a`; that step is
`Sendov.phelps_rodriguez` in the top-level chapter. The theorem only asserts
existence of some nonzero scalar, so the scalar is not simplified.
