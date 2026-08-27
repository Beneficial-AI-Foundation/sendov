import Verso
import VersoManual
import VersoBlueprint
import Sendov

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The finite Sendov range" =>

This chapter and the next refute the real inequality `stat` that the interior
argument ({bpref "in_stat"}[]) extracts from a counterexample; together they
give {bpref "main_stat_lt_one"}[]. This chapter defines the right-hand side
$`R_n(\alpha)` of `stat` and certifies $`R_n(\alpha) < 1` for
$`5 \le n \le 100`; the next handles $`n \ge 101` analytically. It is the
Blueprint rendering of `docs/plan-finite-range.md`: the finite-dimensional
numerical implication left open in the blog post. Where the
implementation deviates from the original plan, the deviation is noted on the
node. The corresponding Lean code lives under `Sendov/FiniteRange/` with the
basic definitions in `Sendov/Defs.lean`.

:::group "finite_range"
The finite-range numerical certification: for degrees 5 to 97 and alpha
between 0 and 17, subject to feasibility, the right-hand side of the blog
post's equation `stat` is strictly below one.
:::

# Setup

:::definition "fr_setup" (parent := "finite_range") (lean := "Sendov.M, Sendov.A, Sendov.c, Sendov.Q")
Write $`M = n - 1`, $`A = 1 - \frac{2\alpha}{M}`,
$`B = \frac{\alpha}{3+\alpha}`,
$`c = 1 - \frac{\alpha}{M} - \frac{\alpha}{2(3+\alpha)}`, and
$`Q(t) = 1 - 2ct + At^2`.
In Lean these are `Sendov.M`, `Sendov.A`, `Sendov.c`, and `Sendov.Q`
(`Sendov/Defs.lean`).
:::

:::definition "fr_rhs" (parent := "finite_range") (lean := "Sendov.R")
The right-hand side of equation `stat` is

$$`R_n(\alpha) = \frac16 + \frac1{4(3+\alpha)} + \frac1{2M} + \frac1{4M(3+\alpha)} + \frac{A^2 n M (n-2)}{4(3+\alpha)} \int_0^1 t^3 Q(t)^{(n-4)/2}\,dt.`

Here $`A = a^2`, so the factor $`A^2` is the blog post's $`a^4`. In Lean this
is `Sendov.R`. Blog: [eq. (22)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#stat). Uses {uses "fr_setup"}[].
:::

:::definition "fr_domain" (parent := "finite_range")
The certified domain is $`5 \le n \le 97`, $`0 \le \alpha \le 17`, together
with the feasibility condition $`c^2 \le A` from the blog post. The plan
originally aimed at $`n \le 200`; the large-degree argument of
`Sendov.LargeDegree` later moved the crossover, so the finite certification
runs to $`100` (three degrees of overlap past the exported $`97`).
Including $`\alpha = 0` is harmless: the bound extends continuously there.
Uses {uses "fr_setup"}[].
:::

:::lemma_ "fr_q_bounds" (parent := "finite_range") (lean := "Sendov.Q_nonneg, Sendov.Q_one, Sendov.Q_le_one")
On the feasible domain, $`Q(t) = (1-ct)^2 + (A-c^2)t^2 \ge 0`; moreover $`Q`
is convex with $`Q(0) = 1` and $`Q(1) = B < 1`, hence $`0 \le Q(t) \le 1` for
$`0 \le t \le 1`. All denominator positivity ($`M > 0`, $`3 + \alpha > 0`)
is recorded explicitly. Uses {uses "fr_setup"}[] and {uses "fr_domain"}[].
:::

# Eliminating numerical integration

:::definition "fr_moments" (parent := "finite_range") (lean := "Sendov.mom")
For an integer $`k \ge 0`, the moment
$`I_k(n,\alpha) = \int_0^1 t^3 Q(t)^k\,dt` — in Lean, `Sendov.mom`
(`Sendov/FiniteRange/Moments.lean`), defined by the exact rational
multinomial sum

$$`I_k = \sum_{i+j\le k} \frac{k!}{i!\,j!\,(k-i-j)!} \frac{(-2c)^i A^j}{4+i+2j}.`

Uses {uses "fr_setup"}[].
:::

:::theorem "fr_moment_formula" (parent := "finite_range") (lean := "Sendov.integral_moment")
The rational sum equals the interval integral: for even $`n` with
$`k = (n-4)/2`, the integral in $`R_n` is exactly $`I_k`. In Lean:
`Sendov.integral_moment`. Uses {uses "fr_moments"}[] and
{uses "fr_q_bounds"}[].
:::

:::proof "fr_moment_formula"
Expand $`(1 + (-2c)t + At^2)^k` by the multinomial theorem and integrate each
monomial over $`[0,1]`. The implementation also provides a recurrence for the
coefficient vector of $`Q^k` (`Sendov/FiniteRange/Recurrence.lean`) to keep
elaboration tractable.
:::

:::theorem "fr_odd_bound" (parent := "finite_range") (lean := "Sendov.integral_rpow_le")
If $`n \ge 7` is odd, put $`k = (n-5)/2`. Then

$$`\int_0^1 t^3 Q(t)^{(n-4)/2}\,dt \le \frac{I_k + I_{k+1}}2,`

removing every square root. In Lean: `Sendov.integral_rpow_le`
(`Sendov/FiniteRange/OddBound.lean`). Uses {uses "fr_q_bounds"}[] and
{uses "fr_moments"}[].
:::

:::proof "fr_odd_bound"
From $`2\sqrt u \le 1 + u` on $`0 \le u \le 1` and the bounds
$`0 \le Q \le 1`, one gets
$`Q^{k+1/2} \le \tfrac12(Q^k + Q^{k+1})`; integrate.
:::

:::theorem "fr_degree_five" (parent := "finite_range") (lean := "Sendov.finite_range_five")
For $`n = 5` the averaged-moment bound is too wasteful. Convexity gives the
chord bound $`Q(t) \le 1 - (1-B)t`, so
$`\int_0^1 t^3\sqrt{Q(t)}\,dt \le H(B)` with an explicit rational-in-$`\sqrt B`
expression $`H`. In Lean: `Sendov.finite_range_five`
(`Sendov/FiniteRange/Degree5.lean`). Uses {uses "fr_q_bounds"}[] and
{uses "fr_rhs"}[].
:::

:::proof "fr_degree_five"
Substitute $`r = \sqrt B`, so $`B = r^2` and $`\alpha = 3r^2/(1-r^2)`; the
degree-five instance becomes rational in $`r`, and $`\alpha \le 17` is
contained in $`r \le 19/20`.
:::

# Reduction to polynomial positivity

:::theorem "fr_reduction" (parent := "finite_range") (lean := "Sendov.finite_range_of_bound")
Replacing the integral by its exact value (even $`n`), the averaged bound
(odd $`n \ge 7`), or the chord bound ($`n = 5`) yields a rational upper bound
$`\operatorname{upperRHS}_n(\alpha) \ge R_n(\alpha)`; after clearing a
known-positive denominator, $`R_n(\alpha) < 1` reduces to a polynomial
positivity claim $`P_n(\alpha) > 0`, and feasibility to $`G_n(\alpha) \ge 0`.
A box is closed by proving either $`G_n < 0` (infeasible) or $`P_n > 0`
(bound) throughout. In Lean: `Sendov.finite_range_of_bound`
(`Sendov/FiniteRange/Reduce.lean`). Uses {uses "fr_moment_formula"}[],
{uses "fr_odd_bound"}[], and {uses "fr_domain"}[].
:::

:::theorem "fr_batch" (parent := "finite_range") (lean := "Sendov.R_le_batch")
*(Deviation from the plan.)* Instead of one certificate per degree, the
implementation proves monotonicity in $`n`: the integrand is antitone in the
degree, so one certificate can cover a batch of consecutive degrees
$`n_0 \le n \le n_1`. In Lean: `Sendov.R_le_batch`
(`Sendov/FiniteRange/Batch.lean`); the degree files
`Sendov/FiniteRange/Degree*.lean` are organized in these batches.
Uses {uses "fr_q_bounds"}[] and {uses "fr_rhs"}[].
:::

:::definition "fr_certificates" (parent := "finite_range")
The certificate data: rational subdivisions of $`[0,17]` with, per box, an
exact positivity witness for $`P_n` or $`-G_n`. Generated by the untrusted
scripts `scripts/gen_*.py` and re-verified inside Lean by exact rational
arithmetic; large certificates are stored packed
(`Sendov/FiniteRange/Pack.lean`, decoded by a proved-correct unpacker).
*(Deviation from the plan: the plan recommended Bernstein-basis certificates;
the implementation verifies the positivity witnesses directly through the
packed polynomial evaluators.)* Uses {uses "fr_reduction"}[].
:::

# The finite-range theorem

:::theorem "fr_cover" (parent := "finite_range") (lean := "Sendov.finite_range_le_100")
For $`5 \le n \le 100`, $`0 \le \alpha \le 17`, and $`c^2 \le A`, one has
$`R_n(\alpha) < 1`. In Lean: `Sendov.finite_range_le_100`
(`Sendov/FiniteRange/Cover.lean`). Uses {uses "fr_reduction"}[],
{uses "fr_degree_five"}[], {uses "fr_batch"}[], and
{uses "fr_certificates"}[].
:::

:::proof "fr_cover"
Dispatch the finite range of degrees into batches; each batch invokes its
checked certificate, combined with the integral upper-bound theorems.
:::

:::theorem "fr_main" (parent := "finite_range") (lean := "Sendov.finite_range")
*The finite-range claim.* For $`5 \le n \le 97`, $`0 \le \alpha \le 17`,
and $`c^2 \le A`: $`R_n(\alpha) < 1`. This is the original challenge
statement, a special case of {uses "fr_cover"}[]. In Lean:
`Sendov.finite_range`.
:::

:::corollary "fr_main_contradiction" (parent := "finite_range") (lean := "Sendov.finite_range_contradiction")
Equation `stat` of the blog post, which asserts $`1 \le R_n(\alpha)`, is
infeasible on the finite range: together with the hypotheses of
{uses "fr_main"}[] it yields `False`. In Lean:
`Sendov.finite_range_contradiction` — the exported interface consumed by the
rest of the formalization.
:::

# Trust policy

The certification is deliberately conservative: no `sorry`, no new axioms, no
`native_decide`, no floating-point literals in the proof path; the generator
scripts are outside the trusted base because Lean re-checks their output with
exact arithmetic. CI runs `#print axioms` on the exported theorem and a
forbidden-token audit.
