import Verso
import VersoManual
import VersoBlueprint
import Sendov
import SendovBlueprint.Figures

open Verso.Genre
open Verso.Genre.Manual
open Informal
open SendovBlueprint.Figures

#doc (Manual) "Sendov's conjecture in the interior" =>

This chapter is the Blueprint rendering of the complex-analytic half of the
project, following `docs/design.md` §6b–6c: for $`n \ge 5` and a real zero
$`0 < a < 1`, a counterexample yields the four identities of the blog post's
Lemma 6; those give the raw polar inequality $`(1Q)` and the raw origin
inequality $`(\text{origin-exact})`; and a chain of real inequalities shows the
two cannot hold together. The Lean code lives under `Sendov/Counterexample/`,
`Sendov/Analytic/`, `Sendov/Reduction/`, and `Sendov/Interior.lean`.

Roots and critical points are multisets throughout, so repeated roots need no
special treatment.

The chapter ends by reducing a counterexample to the real inequality `stat`,
$`1 \le R_n(\alpha)`, in the degree $`n` and the single parameter
$`\alpha = \frac{n-1}{2}(1 - a^2)`. The function $`R_n` is defined in
{bpref "fr_rhs"}[] at the start of the next chapter, and the two chapters that
follow this one show $`R_n(\alpha) < 1` on the whole range, which is the
contradiction.

:::group "interior"
If p has degree at least 2, all zeroes in the closed unit disk, and a real zero
a with 0 <= a < 1, then p' has a zero zeta with dist(zeta, a) < 1.
:::

# The two factorizations

:::theorem "in_factor" (parent := "interior") (lean := "Sendov.exists_root_multiset, Sendov.exists_crit_multiset")
Let $`p` have degree $`n`, all zeroes in the closed unit disk, and $`p(a) = 0`.
Then $`p = \operatorname{lc}(p)\,(X - a)\prod_j (X - z_j)` with $`n - 1`
points $`|z_j| \le 1`. If moreover every critical point $`w` satisfies
$`|w - a| \ge 1`, then writing $`w_j = a - 1/q_j`,
$`p' = n\operatorname{lc}(p)\prod_j (X - (a - q_j^{-1}))` with $`n - 1` points
$`0 < |q_j| \le 1`. In Lean: `Sendov.exists_root_multiset`,
`Sendov.exists_crit_multiset` (`Sendov/Counterexample/Factor.lean`). This layer
is hypothesis-light on purpose — $`a < 1` and $`a \ne 0` enter only above it —
so that the boundary chapter can share it.
:::

# The four identities of Lemma 6

:::definition "in_sumEraseProd" (parent := "interior") (lean := "Sendov.sumEraseProd")
$`\sum_j \prod_{k \ne j} s_k`, the division-free form of
$`(\prod s)(\sum 1/s_j)`, defined whether or not some $`s_j` vanishes. In Lean:
`Sendov.sumEraseProd`. The blog post's convention that singularities are removed
when some $`z_j = 0` thereby becomes unnecessary.
:::

:::theorem "in_centroid" (parent := "interior") (lean := "Sendov.centroid_identity")
*Centroid identity.* $`(n-1)(a + \sum_j z_j) = n\sum_j (a - q_j^{-1})`: the
centroid of the zeroes is the centroid of the critical points. From the
coefficient of $`X^{n-1}` in $`p` and of $`X^{n-2}` in $`p'`. In Lean:
`Sendov.centroid_identity`. Blog: [Lemma 6(i), eq. (7)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#centroid-ident). Uses {uses "in_factor"}[].
:::

:::theorem "in_second_origin" (parent := "interior") (lean := "Sendov.second_origin_identity")
*Second origin identity.* $`n\prod_j(1 - aq_j) = (-1)^{n-1}\prod_j q_j\,\bigl(\prod_j z_j + a\sum_j\prod_{k\ne j}z_k\bigr)`,
from $`p'(0)` computed two ways. In Lean: `Sendov.second_origin_identity`. Blog: [Lemma 6(iv), eq. (10)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#second-origin). Uses
{uses "in_factor"}[] and {uses "in_sumEraseProd"}[].
:::

:::theorem "in_first_origin" (parent := "interior") (lean := "Sendov.first_origin_identity")
*First origin identity.* For $`a \ne 0`,
$`n\int_0^1 \prod_j (1 - atq_j)\,dt = (-1)^{n-1}\prod_j q_j\prod_j z_j`, from
$`p(0) = p(a) - \int_0^a p'` and $`p(a) = 0`. In Lean:
`Sendov.first_origin_identity`. Blog: [Lemma 6(iii), eq. (9)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#first-origin). Uses {uses "in_factor"}[].
:::

:::theorem "in_polar_identity" (parent := "interior") (lean := "Sendov.polar_identity")
*Polar identity.* For $`a \ne 0` and $`a^2 \ne 1`,
$$`\prod_j q_j\prod_j (1 - az_j) = n\int_0^1 \prod_j \bigl(a + t(1-a^2)q_j\bigr)\,dt,`
from $`p(1/a)` computed via the fundamental theorem of calculus along the
segment from $`a` to $`1/a`. In Lean: `Sendov.polar_identity`. Blog: [Lemma 6(ii), eq. (8)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#polar-ident). Uses
{uses "in_factor"}[].
:::

# The polar channel

:::theorem "in_polar_star" (parent := "interior") (lean := "Sendov.one_le_integral_prod_norm")
*The branch point $`(\star)`.* For $`|a| \le 1`, from the polar identity and
$`p'(a)` two ways ($`\prod_j q_j\prod_j (a - z_j) = n`), the disk-Möbius bound
$`|a - z| \le |1 - az|` (`Sendov.norm_sub_le_norm_one_sub_mul`) and the integral
triangle inequality give
$$`1 \le \int_0^1 \prod_j \bigl|a + t(1-a^2)q_j\bigr|\,dt.`
In Lean: `Sendov.one_le_integral_prod_norm` (`Sendov/Analytic/Polar.lean`). Blog: [eq. (23)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#polar-lower-bound).
Exposed as a named intermediate because the low-degree chapter branches off
here. Uses {uses "in_polar_identity"}[].
:::

:::definition "in_Ppolar" (parent := "interior") (lean := "Sendov.Ppolar")
With $`x = \operatorname{Re}\bigl(\sum_j q_j\bigr)/(n-1)`, the quadratic mean
$`P(t) = a^2 + 2atx(1-a^2) + t^2(1-a^2)^2`. In Lean: `Sendov.Ppolar`
(`Sendov/Reduction/Setup.lean`).
:::

:::theorem "in_1Q" (parent := "interior") (lean := "Sendov.one_le_integral_Ppolar")
*The raw polar inequality $`(1Q)`.* From $`(\star)`, AM–GM on the $`n-1`
factors and $`\sum_j |a + t(1-a^2)q_j|^2 \le (n-1)P(t)` give
$$`1 \le \int_0^1 P(t)^{(n-1)/2}\,dt.`
In Lean: `Sendov.one_le_integral_Ppolar`. Blog: [Proposition 10(i), eq. (16)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#1Q). Uses {uses "in_polar_star"}[],
{uses "in_Ppolar"}[], and {uses "in_maclaurin"}[].
:::

# Two general inequalities

:::theorem "in_maclaurin" (parent := "interior") (lean := "Sendov.Multiset.prod_le_mean_pow, Sendov.Multiset.esymm_card_pred_le")
*AM–GM and the top case of Maclaurin's inequality for multisets.* For
nonnegative $`b_1,\dots,b_N`: $`\prod b \le \mu^N` and
$`e_{N-1}(b) \le N\mu^{N-1}`, $`\mu` the mean. In Lean:
`Sendov.Multiset.prod_le_mean_pow`, `Sendov.Multiset.esymm_card_pred_le`
(`Sendov/Analytic/Maclaurin.lean`). Blog: [eq. (24) and the Maclaurin step of Section 2](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#amgm).
:::

:::proof "in_maclaurin"
Neither Newton's inequalities nor Rolle are needed: splitting off one element
and applying the inductive hypothesis leaves $`1 + N(w-1) \le w^N`, which is
Bernoulli. AM–GM is proved the same way rather than imported (Mathlib states
it for `Finset`-indexed families), so the file imports no AM–GM at all.
:::

:::theorem "in_defect" (parent := "interior") (lean := "Sendov.defect")
*The defect lemma.* For $`w_1,\dots,w_N` in the closed unit disk,
$$`\prod_j |w_j|\;\sum_j \bigl|w_j^{-1} - \overline{w_j}\bigr| \le 1 - \prod_j |w_j|^2.`
In Lean: `Sendov.defect` (`Sendov/Analytic/Defect.lean`). Blog: Lemma 13 (Defect lemma).
:::

:::proof "in_defect"
*(Deviation from the write-up.)* The write-up sets $`|w_j| = e^{-a_j}`,
computes $`2\sinh a_j`, and uses superadditivity of $`\sinh`. Splitting off one
point instead leaves $`(1-r)(1-P)(1-rP) \ge 0`: no $`\sinh`, no logarithms. The
origin $`w_j = 0` needs no limiting argument, since the pointwise fact
$`|w|\,|w^{-1} - \bar w| \le 1 - |w|^2` carries a factor $`|w|` that kills
Lean's junk $`0^{-1}`.
:::

# The origin channel

:::definition "in_Fprod" (parent := "interior") (lean := "Sendov.Fprod")
$`F(t) = \prod_j (1 - atq_j)`, and the quadratic $`\beta(t) = QQ(ax, a^2, t) = 1 - 2axt + a^2t^2`.
In Lean: `Sendov.Fprod` (`Sendov/Analytic/Origin.lean`), `Sendov.QQ`
(`Sendov/Common/Quadratic.lean`). Blog: [eqs. (6), (14)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#F-def).
:::

:::theorem "in_error_bound" (parent := "interior") (lean := "Sendov.sumEraseProdMap_norm_le, Sendov.norm_deriv_add_le")
*The pointwise error bound.* With $`x + iy = \sum_j q_j/(n-1)`,
$$`\bigl\|F'(t) + (n-1)a(x+iy)F(t)\bigr\| \le a^2t(n-1)\,\beta(t)^{(n-2)/2}.`
In Lean: `Sendov.norm_deriv_add_le`, via `Sendov.sumEraseProdMap_norm_le`. Blog: [Section 2, the bound on $`F'(t)` preceding eq. (32)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#origin). Uses
{uses "in_Fprod"}[] and {uses "in_maclaurin"}[].
:::

:::proof "in_error_bound"
Three steps: $`\sum_j |1 - atq_j|^2 \le (n-1)\beta(t)`
(`Sendov.sum_norm_sq_one_sub_le`, where $`x` enters); Cauchy–Schwarz
$`(\sum b)^2 \le N\sum b^2`; and Maclaurin,
$`\sum_j\prod_{k\ne j} b_k \le N\mu^{N-1}`. The derivative
$`F'(t) = -a\sum_j q_j\prod_{k\ne j}(1 - atq_k)` (`Sendov.hasDerivAt_Fprod`) is
split via $`1 - (1 - atq_j) = atq_j` into the main term and the residual.
:::

:::theorem "in_tri" (parent := "interior") (lean := "Sendov.one_le_tri")
*The triangle inequality $`(\text{tri})`.*
$$`1 \le \Bigl\|F(1) + (n-1)a(x+iy)\int_0^1 F\Bigr\| + a^2(n-1)\int_0^1 t\,\beta(t)^{(n-2)/2}\,dt,`
from the fundamental theorem of calculus, $`F(0) = 1`, and the error bound.
In Lean: `Sendov.one_le_tri`. Blog: [eq. (32)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#tri). Uses {uses "in_error_bound"}[].
:::

:::theorem "in_Jsum" (parent := "interior") (lean := "Sendov.Jsum_estimate")
*The defect estimate for $`J\sum_j 1/z_j`.* With $`J = \prod_j q_j\prod_j z_j`,
$$`\Bigl\|\prod_j q_j\sum_j\prod_{k\ne j}z_k - \bigl(a(n-1) - n(x+iy)\bigr)J\Bigr\| \le \frac{n}{n-1}\bigl(1 - |J|^2\bigr),`
using the centroid identity to rewrite $`\sum_j z_j` and the defect lemma. In
Lean: `Sendov.Jsum_estimate` (`Sendov/Analytic/Jsum.lean`). Blog: [Section 2, the estimate for $`J\sum_j 1/z_j` following Lemma 13](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#tri-2). Uses
{uses "in_centroid"}[], {uses "in_defect"}[], and {uses "in_sumEraseProd"}[].
:::

:::theorem "in_grow" (parent := "interior") (lean := "Sendov.grow")
*$`(\text{grow})`.* With $`W = a^2(n-1) + 1 - a(x+iy)` (`Sendov.Worigin`), for
$`n \ge 5`, $`a > 0`, $`x \le 1`: $`\|W\| \ge 2an/(n-1)`. This reduces to
$`(n-1)^2a^2 - (3n-1)a + (n-1) > 0`, whose discriminant
$`(3n-1)^2 - 4(n-1)^3` is negative exactly from $`n \ge 5` on. *This is the
only place the hypothesis $`n \ge 5` is used.* In Lean: `Sendov.grow`. Blog: [eq. (35)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#grow).
:::

:::theorem "in_origin_exact" (parent := "interior") (lean := "Sendov.origin_exact")
*The raw origin inequality $`(\text{origin-exact})`.* For $`n \ge 5`,
$`0 < a < 1`, and $`\alpha = M(1 - a^2)/2`,
$$`2\alpha + ax \le \frac{1 - x^2}{2M} + a^2 nM\int_0^1 t\,\beta(t)^{(n-2)/2}\,dt.`
In Lean: `Sendov.origin_exact` (`Sendov/Analytic/OriginExact.lean`). Blog: [Proposition 11(i), eq. (19)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#origin-exact). Uses
{uses "in_tri"}[], {uses "in_first_origin"}[], {uses "in_second_origin"}[],
{uses "in_Jsum"}[], and {uses "in_grow"}[].
:::

:::proof "in_origin_exact"
The two origin identities express $`F(1) + (n-1)a(x+iy)\int_0^1 F` exactly in
terms of $`J` and $`\sum_j 1/z_j`; the defect estimate collapses this to
$`JW/n` plus an error of size $`a(1 - |J|^2)/(n-1)`. By $`(\text{grow})` the
resulting bound is non-decreasing in $`|J|` on $`[0,1]`, so $`|J|` may be
replaced by $`1`. Finally $`y` is eliminated by $`|s + it| \le s + t^2/(2s)`
applied to $`W`, whose real part is at least $`a^2(n-1)` and whose imaginary
part is $`-ay` with $`y^2 \le 1 - x^2`.
:::

# The reduction chain

:::theorem "in_polar_exp" (parent := "interior") (lean := "Sendov.polar_exp")
*$`(1Q) \Rightarrow (\text{lt})`.* With $`\alpha = M(1-a^2)/2`,
$`(1Q)` implies $`1 \le \int_0^1 \exp\bigl(\alpha(-1 + (2 - \beta(1))t)\bigr)\,dt`.
The pointwise bound is an identity up to $`t^2 \le t`. In Lean:
`Sendov.polar_exp` (`Sendov/Reduction/Polar.lean`). Blog: [Proposition 10(ii), eq. (17)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#lt). Uses {uses "in_1Q"}[].
:::

:::theorem "in_beta_bound" (parent := "interior") (lean := "Sendov.beta_le, Sendov.log_le_alpha_mul")
*$`(\text{lt}) \Rightarrow (\text{beta-bound})`.* From $`(\text{lt})` with
$`\alpha > 0`: the rational half $`\beta(1) \le \alpha/(3+\alpha)` and the
logarithmic half $`\log\alpha \le \alpha(1 - \beta(1))`. Both are stated
non-strictly; no strict integral monotonicity is needed anywhere. The integral
evaluates to $`e^{-u}\sinh h/h` with $`u = \alpha\beta(1)/2`, $`h = \alpha(2-\beta(1))/2`,
so $`(\text{lt})` says $`e^u \le \sinh h/h`. In Lean: `Sendov.beta_le`,
`Sendov.log_le_alpha_mul` (`Sendov/Reduction/BetaBound.lean`). Blog: [Proposition 10(iii), eq. (18)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#beta-bound). Uses
{uses "in_polar_exp"}[] and {uses "in_sinh"}[].
:::

:::theorem "in_alpha17" (parent := "interior") (lean := "Sendov.alpha_le_seventeen")
*$`(\text{beta-bound}) + (\text{origin-exact}) \Rightarrow \alpha \le 17`.*
In Lean: `Sendov.alpha_le_seventeen` (`Sendov/Reduction/Alpha17.lean`). Blog: [Proposition 11(ii), eq. (20), Section 2.1](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#17).
*(Deviation from the write-up.)* The chord bound $`\beta(t) \le 1 - axt` plus
the Beta identity $`\int_0^{1/c} t(1-ct)^s\,dt = 1/(c^2(s+1)(s+2))` reuses the
large-degree machinery, avoids an improper integral, and improves the margin
from $`1.948` to $`1.817`. Uses {uses "in_beta_bound"}[],
{uses "in_origin_exact"}[], and {uses "lg_tail_gen"}[].
:::

:::theorem "in_one_le" (parent := "interior") (lean := "Sendov.one_le_of_origin")
*$`(\text{origin-exact}) \Rightarrow (\text{1le})`.* For $`n \ge 5` and
$`\beta(1) < 1`, the origin inequality yields the blog post's $`(\text{1le})`,
a lower bound of $`1` on an explicit expression in $`\beta(1)`, $`\alpha`,
$`M`, and $`\int_0^1 t^3\beta(t)^{(n-4)/2}\,dt`. In Lean:
`Sendov.one_le_of_origin` (`Sendov/Reduction/Simplified.lean`). Blog: [Proposition 11(iii), eq. (21), Section 2.2](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#1le). *(Deviation
from the write-up.)* The mean value theorem is replaced by Bernoulli:
$`(P+Q)^p \le P^p + pQ(P+Q)^{p-1}` is Mathlib's
`one_add_mul_self_le_rpow_one_add` at $`\theta = P/(P+Q)`. Uses
{uses "in_origin_exact"}[].
:::

:::lemma_ "in_sinh" (parent := "interior") (lean := "Sendov.sinh_sq_le, Sendov.sqrt_mul_sub_le, Sendov.log_sinh_div_le")
*The $`\sinh` lemma.* The elementary estimates on $`\sinh` needed to turn
$`e^u \le \sinh h/h` into the two halves of $`(\text{beta-bound})`, chiefly
$`\log(\sinh h/h) \le \sqrt{h^2 + 9} - 3`, proved by iterated differentiation
against explicit polynomial comparison functions. In Lean:
`Sendov/Common/Sinh.lean`. Blog: [eqs. (27), (28)](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#lsh).
:::

:::theorem "in_stat" (parent := "interior") (lean := "Sendov.stat_of_one_le")
*$`(\text{1le}) + (\text{beta-bound}) \Rightarrow \text{stat}`.* For
$`n \ge 5`, substituting $`\beta(1) \le \alpha/(3+\alpha)` into $`(\text{1le})`
gives $`1 \le R_n(\alpha)`; the same bound yields feasibility $`c^2 \le A`
(`Sendov.feasible_of_beta`). In Lean: `Sendov.stat_of_one_le`
(`Sendov/Reduction/Stat.lean`). Blog: [eq. (22), `stat`](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#stat). Uses {uses "in_one_le"}[],
{uses "in_beta_bound"}[], and {uses "fr_rhs"}[].
:::

The two channels, seen together (second diagram of the blog post's
[Section 2.2](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#1le)):

:::clickable_figure "channels"
Polar feasible region (blue, {bpref "in_polar_exp"}[], bounded by
{bpref "in_beta_bound"}[]) against the origin feasible region (red,
{bpref "in_one_le"}[]); the gap between them is what the next theorem
certifies for every $`n \ge 5`.
:::

:::theorem "in_incompatible" (parent := "interior") (lean := "Sendov.polar_origin_incompatible")
*$`(1Q)` and $`(\text{origin-exact})` are incompatible.* For $`n \ge 5`,
$`0 < a < 1`, $`x^2 \le 1`, and $`\alpha = M(1-a^2)/2`, the two raw
inequalities have no common solution. A statement in real variables alone,
with no polynomial or complex number in it. In Lean:
`Sendov.polar_origin_incompatible` (`Sendov/Reduction/Main.lean`). Uses
{uses "in_alpha17"}[], {uses "in_stat"}[], and {uses "main_stat_lt_one"}[].
:::

# Assembly

:::theorem "in_sendov_interior" (parent := "interior") (lean := "Sendov.sendov_interior")
For degree $`n \ge 2`, all zeroes in the closed unit disk, and a real zero
$`0 < a < 1`: $`p'` has a zero $`\zeta` with $`|\zeta - a| < 1`. In Lean:
`Sendov.sendov_interior` (`Sendov/Interior.lean`). Blog: [Conjecture 3](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#interior). Uses {uses "in_factor"}[],
{uses "in_polar_star"}[], {uses "in_1Q"}[], {uses "in_origin_exact"}[],
{uses "in_incompatible"}[], and {uses "ld_main"}[].
:::

:::proof "in_sendov_interior"
Suppose not. The two factorizations give $`z_j`, $`q_j`, and the branch point
$`(\star)`. For $`n \ge 5`, AM–GM gives $`(1Q)`, the identities give
$`(\text{origin-exact})`, and the two are incompatible. For $`n \le 5`,
$`(\star)` is contradictory on its own by the low-degree chapter. The branches
overlap at degree five.
:::

:::theorem "in_sendov_center" (parent := "interior") (lean := "Sendov.sendov_center")
*The zero $`a = 0`.* Excluded above because the polar identity divides by
$`a`, but needing none of the machinery: $`p'(a)` two ways says
$`(\prod_j q_j)(\prod_j (a - z_j)) = n`, and at $`a = 0` both factors have norm
at most one. In Lean: `Sendov.sendov_center`. Blog: [the paragraph ruling out $`a = 0` before Lemma 6](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/#identities). Uses {uses "in_factor"}[].
:::

:::corollary "in_sendov_interior_real" (parent := "interior") (lean := "Sendov.sendov_interior_real")
The two combined: the conjecture, strictly, for every real zero
$`0 \le a < 1`. In Lean: `Sendov.sendov_interior_real`. Uses
{uses "in_sendov_interior"}[] and {uses "in_sendov_center"}[].
:::
