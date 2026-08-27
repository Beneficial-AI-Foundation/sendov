import Verso
import VersoManual
import VersoBlueprint
import Sendov

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The large-degree range" =>

This chapter is the Blueprint rendering of `docs/proof-large-degree.md`
(Sections 1–8): equation `stat` of the blog post is impossible for $`n \ge 101`
and $`0 \le \alpha \le 17`. The Lean code lives under `Sendov/LargeDegree/`,
resting on the shared `Sendov/Common/` layer. The write-up's Sections 9–10 (a
hybrid strategy for lowering the finite cutoff) were never part of the proved
argument and have no node here.

The informal write-up was followed in outline but not in detail: using the sharp
Beta constant $`6/((r+1)(r+2)(r+3)(r+4))` instead of $`6/r^4` makes almost
every downstream step easier, and those deviations are noted on the nodes.

:::group "large_degree"
For degrees n at least 101 and alpha between 0 and 17, subject to feasibility,
the right-hand side of `stat` is strictly below one.
:::

# Preliminary bounds

:::lemma_ "lg_prelim" (parent := "large_degree") (lean := "Sendov.Q_nonneg, Sendov.Q_one, Sendov.c_ge_of_large, Sendov.c_le_one")
On the domain: $`Q_n(t) = (1 - c_nt)^2 + (A_n - c_n^2)t^2 \ge 0` by
feasibility; $`Q_n(1) = B = \alpha/(3+\alpha) \le 17/20`; and for
$`n \ge 101`, $`c_n \ge 81/200 > 0` while $`c_n \le 1` always. In Lean:
`Sendov.Q_nonneg`, `Sendov.Q_one` (`Sendov/Common/Basic.lean`),
`Sendov.c_ge_of_large`, `Sendov.c_le_one` (`Sendov/LargeDegree/Tail.lean`).
Uses {uses "fr_setup"}[].
:::

# The integral upper bound

:::theorem "lg_tail_gen" (parent := "large_degree") (lean := "Sendov.integral_le_tail_gen")
*The split at the vertex.* For $`c^2 \le A`, $`0 < c \le 1`, $`r > 0`, and any
$`k`,
$$`\int_0^1 t^k\,QQ(t)^r\,dt \le \int_0^{1/c} t^k (1 - ct)^r\,dt + \frac{QQ(1)^r}{k+1},`
where $`QQ(t) = 1 - 2ct + At^2`. On $`[0, c/A]` the quadratic lies below its
tangent chord $`1 - ct` (`Sendov.QQ_le_chord`); on $`[c/A, 1]` it is increasing
so is at most $`QQ(1)` (`Sendov.QQ_le_at_one`). In Lean:
`Sendov.integral_le_tail_gen` (`Sendov/Common/Chord.lean`). Uses
{uses "lg_prelim"}[].
:::

:::theorem "lg_tail" (parent := "large_degree") (lean := "Sendov.integral_le_tail")
For $`n \ge 2`, $`\alpha \ge 0`, feasibility, $`c_n > 0`, and $`r > 0`,
$$`\int_0^1 t^3 Q_n(t)^r\,dt \le \frac{6}{c_n^4\,(r+1)(r+2)(r+3)(r+4)} + \frac14 B^r.`
In Lean: `Sendov.integral_le_tail`. Uses {uses "lg_tail_gen"}[].
:::

:::proof "lg_tail"
*(Deviation from the write-up.)* The write-up bounds $`1 - ct \le e^{-ct}` and
uses the Gamma integral $`\int_0^\infty t^3 e^{-rct}\,dt = 6/(rc)^4`. Keeping
the chord as a *power* instead gives the Beta integral
$`\int_0^{1/c} t^3(1-ct)^r\,dt = 6/(c^4(r+1)(r+2)(r+3)(r+4))`
(`Sendov.integral_cube_mul_rpow`): no improper integral, no `Real.exp`, and
strictly sharper, so every constant downstream survives unchanged.
:::

:::definition "lg_U" (parent := "large_degree") (lean := "Sendov.U")
The elementary bound $`U_n(\alpha)`: the four elementary terms of
$`R_n(\alpha)` plus the prefactor $`A_n^2 n M (n-2)/(4(3+\alpha))` times the
right-hand side of the tail bound at $`r = (n-4)/2`. In Lean: `Sendov.U`
(`Sendov/LargeDegree/Tail.lean`). Uses {uses "fr_rhs"}[].
:::

:::theorem "lg_R_le_U" (parent := "large_degree") (lean := "Sendov.R_le_U")
For $`n \ge 5`, $`\alpha \ge 0`, feasibility, and $`c_n > 0`:
$`R_n(\alpha) \le U_n(\alpha)`. In Lean: `Sendov.R_le_U`, via
`Sendov.R_le_of_integral_le`. Uses {uses "lg_tail"}[] and {uses "lg_U"}[].
:::

# Closed form of the bound

:::definition "lg_T1T2" (parent := "large_degree") (lean := "Sendov.T1, Sendov.T2")
With $`r = (n-4)/2` one has $`(r+1)(r+2)(r+3)(r+4) = (n-2)n(n+2)(n+4)/16`,
and the $`n(n-2)` cancels the prefactor of $`R` *exactly*. The first tail term
collapses to the rational function
$$`T_{1,n}(\alpha) = \frac{24\,(n - 1 - 2\alpha)^2}{(3+\alpha)\,c_n^4\,(n-1)(n+2)(n+4)},`
and, writing $`b = \sqrt B`, the second is
$$`T_{2,n}(\alpha) = \frac{A_n^2\,n(n-1)(n-2)}{16(3+\alpha)}\,b^{\,n-4}`
with a *natural* exponent. In Lean: `Sendov.T1`, `Sendov.T2`
(`Sendov/LargeDegree/Monotone.lean`). Uses {uses "lg_U"}[].
:::

:::lemma_ "lg_U_eq" (parent := "large_degree") (lean := "Sendov.U_eq")
For $`n \ge 5`, $`\alpha \ge 0`, $`c_n \ne 0`:
$`U_n(\alpha) = \frac16 + \frac1{4(3+\alpha)} + \frac1{2M} + \frac1{4M(3+\alpha)} + T_{1,n}(\alpha) + T_{2,n}(\alpha)`.
The identity $`B^{(n-4)/2} = (\sqrt B)^{n-4}` is `Sendov.rpow_B_eq`. In Lean:
`Sendov.U_eq`. Uses {uses "lg_T1T2"}[].
:::

# Discrete monotonicity in the degree

:::lemma_ "lg_tail1_poly" (parent := "large_degree") (lean := "Sendov.tail1_poly")
*The 1% allowance.* For $`j \ge 0` and $`0 \le \alpha \le 17`,
$$`108150000\,(100 + j - 2\alpha)^2 \le 101\,(100 - 2\alpha)^2\,(100+j)(103+j)(105+j).`
A Bernstein certificate in $`\alpha` on $`[0,17]` whose coefficients are
polynomials in $`j`; the top one has a negative linear coefficient and is
handled by completing the square. In Lean: `Sendov.tail1_poly`.
:::

:::theorem "lg_T1_le" (parent := "large_degree") (lean := "Sendov.T1_le")
For $`n \ge 101` and $`0 \le \alpha \le 17`:
$`T_{1,n}(\alpha) \le \tfrac{101}{100}\,T_{1,101}(\alpha)`. In Lean:
`Sendov.T1_le`. Uses {uses "lg_tail1_poly"}[], {uses "lg_T1T2"}[], and
{uses "lg_prelim"}[].
:::

:::proof "lg_T1_le"
*(Deviation from the write-up.)* The write-up's (16)–(18) claim $`T_{1,n}`
decreases outright; it does not — at $`\alpha = 17` the factor
$`(n-1-2\alpha)^2/((n-1)(n+2)(n+4))` increases up to $`n \approx 108`. It is
$`c_n^4` in the denominator that pays for this, since $`c_n` is monotone in
$`n` (`Sendov.c_mono`). Rather than couple the two, a flat 1% allowance is
taken and discharged by its own certificate; the write-up's degree-8 certificate
(18) is for the $`6/r^4` version and is not needed.
:::

:::lemma_ "lg_T2_step" (parent := "large_degree") (lean := "Sendov.T2_step, Sendov.sqrtB_le, Sendov.tail2_poly")
For $`n \ge 101`: $`T_{2,n+1}(\alpha) \le T_{2,n}(\alpha)`. The step ratio is
$`(A_{n+1}/A_n)^2\,\frac{n+1}{n-2}\,\sqrt B`, and $`\sqrt B \le 12/13`
(`Sendov.sqrtB_le`, since $`B \le 17/20 \le (12/13)^2`) keeps it rational and
below one; `Sendov.tail2_poly` is the all-positive certificate. In Lean:
`Sendov.T2_step`. Uses {uses "lg_T1T2"}[] and {uses "lg_prelim"}[].
:::

:::theorem "lg_T2_le" (parent := "large_degree") (lean := "Sendov.T2_le")
For $`n \ge 101`: $`T_{2,n}(\alpha) \le T_{2,101}(\alpha)`, by induction on
$`n` from the step. Because the exponent $`n - 4` is natural, this is an
ordinary induction with no `rpow` reasoning. In Lean: `Sendov.T2_le`. Uses
{uses "lg_T2_step"}[].
:::

:::definition "lg_Ut" (parent := "large_degree") (lean := "Sendov.Ut")
The degree-free bound
$$`\widetilde U(\alpha) = \frac16 + \frac1{4(3+\alpha)} + \frac1{200} + \frac1{400(3+\alpha)} + \frac{101}{100}T_{1,101}(\alpha) + \frac{(100-2\alpha)^2\cdot 101\cdot 99}{100\cdot 16(3+\alpha)}\,B^{48}.`
At $`n = 101` the exponent $`97/2` has been replaced by $`48` using
$`B^{97/2} = B^{48}\sqrt B \le B^{48}`. In Lean: `Sendov.Ut`. Uses
{uses "lg_T1T2"}[].
:::

:::theorem "lg_U_le_Ut" (parent := "large_degree") (lean := "Sendov.U_le_Ut")
For $`n \ge 101` and $`0 \le \alpha \le 17`: $`U_n(\alpha) \le \widetilde U(\alpha)`.
The four elementary terms plainly decrease with $`n`. In Lean:
`Sendov.U_le_Ut`. Uses {uses "lg_U_eq"}[], {uses "lg_T1_le"}[],
{uses "lg_T2_le"}[], and {uses "lg_Ut"}[].
:::

# The endgame at degree 101

:::theorem "lg_Ut_lt_one" (parent := "large_degree") (lean := "Sendov.Ut_lt_one")
$`\widetilde U(\alpha) < 1` on $`0 \le \alpha \le 17`. In Lean:
`Sendov.Ut_lt_one` (`Sendov/LargeDegree/Endgame.lean`). Uses {uses "lg_Ut"}[].
:::

:::proof "lg_Ut_lt_one"
With $`\gamma = 300 + 47\alpha - \alpha^2` one has
$`c_{101} = \gamma/(100(3+\alpha))` and
$`T_{1,101} = 1600000\,(100-2\alpha)^2(3+\alpha)^3/(721\gamma^4)`. Multiplying
$`1 - \widetilde U` by $`D = 865200\,(3+\alpha)^{49}\gamma^4 > 0` gives a single
polynomial $`F` of degree 58 (`Sendov.F_pos`), and its Bernstein certificate on
$`[0,17]` has all 59 coefficients positive. *(Deviation from the write-up.)*
Section 7's split at $`\alpha = 16` with separate endpoint estimates is
unnecessary once the sharp Beta constant is used: $`\widetilde U` peaks at
$`\alpha = 17` with value $`0.9229`, leaving 7.7% of room against the 0.15%
the write-up's route leaves there. The multiplication by $`D` is distributed
by hand, term by term, to keep every `ring` call at degree at most 62.
:::

:::theorem "lg_main" (parent := "large_degree") (lean := "Sendov.large_degree")
*The large-degree claim.* For $`n \ge 101`, $`0 \le \alpha \le 17`, and
$`c^2 \le A`: $`R_n(\alpha) < 1`. In Lean: `Sendov.large_degree`. Blog: [the elimination of $`n > 200`, Section 0](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#stat). Uses
{uses "lg_R_le_U"}[], {uses "lg_U_le_Ut"}[], {uses "lg_Ut_lt_one"}[], and
{uses "lg_prelim"}[].
:::

# Notes

The seam with the finite range is at $`100/101`, not the write-up's $`97/98`:
the finite side was pushed three degrees further so the analytic side starts
with margin $`0.122` at $`n = 101` instead of $`0.048` at $`n = 98`. Margins
on the final bound: $`\widetilde U(0) = 0.3305`, $`\widetilde U(8) = 0.3456`,
$`\widetilde U(16) = 0.7598`, $`\widetilde U(17) = 0.9229`.
