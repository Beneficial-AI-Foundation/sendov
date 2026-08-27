import Verso
import VersoManual
import VersoBlueprint
import Sendov

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The digested proof" =>

This chapter retells the argument in the order and spirit of Terence Tao's
digestion,
[*A digestion of the proof of Sendov's conjecture*](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/)
(12 August 2026), whose numbering of lemmas and equations is used throughout
this blueprint. The later chapters are organised by Lean module; this one is
organised by idea, and each idea is linked to the node that formalizes it.
Nothing here is proved: it is a reading guide.

# What is being proved

Let $`n \ge 2` and let $`p` be a degree-$`n` polynomial with all zeroes in the
closed unit disk. Sendov's conjecture (blog Conjecture 1,
{bpref "main_sendov"}[]) says that every zero $`a` has a critical point
$`\zeta` with $`|\zeta - a| \le 1`. The Phelps–Rodriguez conjecture (blog
Conjecture 2, {bpref "main_phelps_rodriguez"}[]) sharpens this to
$`|\zeta - a| < 1` unless $`|a| = 1` and $`p` is a scalar multiple of
$`z^n - a^n`.

Rotating the variable ({bpref "main_rotate"}[]) normalises $`a` to a real
number in $`[0, 1]`. Rubinstein's theorem settles $`a = 1`
({bpref "bd_rubinstein_one"}[], blog Theorem 14), so both conjectures follow
from

*Conjecture 3 (Sendov's conjecture in the interior).* If $`0 \le a < 1` is a
zero of $`p`, then $`p'` has a zero $`\zeta` with $`|\zeta - a| < 1`.

This is {bpref "in_sendov_interior_real"}[]. Before 2026 it was known for
$`n \le 8` (Brown–Xiang) and for $`n` sufficiently large (Tao, 2020), with
no effective threshold. The proof below is uniform in $`n \ge 2` and, in the
words of the blog post, "remarkably elementary": the only complex analysis is
the fundamental theorem of algebra plus the fact that a disk Möbius map
preserves the disk, and the deepest input is the top case of Maclaurin's
inequality.

# The setup: two families of points that barely talk to each other

Suppose Conjecture 3 fails for some $`n \ge 5` (degrees $`n \le 5` are
handled separately, see below). Normalise $`p` to be monic with zeroes
$`a, z_1, \dots, z_{n-1}`, all $`|z_j| \le 1`, and suppose every critical
point is at distance at least $`1` from $`a`. Then the critical points can be
written
$$`a - \frac{1}{q_1}, \;\dots,\; a - \frac{1}{q_{n-1}}`
for nonzero $`q_j` in the closed unit disk. This is
{bpref "in_factor"}[]: two factorizations of the same polynomial,
$$`p(z) = (z - a)\prod_j (z - z_j), \qquad p'(z) = n\prod_j\Bigl(z - a + \frac{1}{q_j}\Bigr).`

*The motivating near-counterexample* (blog Example 4). For $`p(z) = z^n - 1`
and $`a = 1`, the $`z_j` are the nontrivial $`n`-th roots of unity and every
$`q_j = 1`. This is not a counterexample to Conjecture 3 because $`a` is not
strictly inside the disk, but it sits on the boundary of every inequality
below and is what makes the regime $`a = 1 - O(1/n)` delicate (blog Example 5
studies the perturbations $`p(z) = (z + c_2/n)^{n-m}P(z) - (\cdots)`).

The two families $`\{z_j\}` and $`\{q_j\}` "communicate" only through
$`p` and $`p'`, and the whole proof extracts four identities by evaluating
these at a handful of natural points (blog Lemma 6). With
$`F(t) := \prod_j (1 - atq_j)`:

* *Centroid identity* (7), from the $`z^{n-2}` coefficient of $`p'`:
  $$`\frac1n\Bigl(a + \sum_j z_j\Bigr) = \frac{1}{n-1}\sum_j\Bigl(a - \frac1{q_j}\Bigr).`
  Formalized as {bpref "in_centroid"}[].
* *Polar identity* (8), from $`p(1/a)/p'(a)`, comparing $`a` with its
  reflection $`1/a` across the circle:
  $$`\prod_j \frac{1 - az_j}{a - z_j} = \int_0^1 \prod_j\bigl(t(1-a^2)q_j + a\bigr)\,dt.`
  Formalized as {bpref "in_polar_identity"}[].
* *First origin identity* (9), from $`p(0)`:
  $$`(-1)^{n-1}\prod_j z_j = \frac{n}{\prod_j q_j}\int_0^1 F(t)\,dt.`
  Formalized as {bpref "in_first_origin"}[].
* *Second origin identity* (10), from $`p'(0)`:
  $$`(-1)^{n-1}\prod_j z_j\Bigl(1 + a\sum_j \frac1{z_j}\Bigr) = \frac{n}{\prod_j q_j}F(1).`
  Formalized as {bpref "in_second_origin"}[]; the division-free form uses
  {bpref "in_sumEraseProd"}[], which removes the blog post's convention about
  cancelling singularities when some $`z_j = 0`.

After this point the polynomial $`p` plays no further role: the four
identities, together with $`0 < a < 1` and $`|z_j|, |q_j| \le 1`, are
contradictory on their own. (The case $`a = 0` is dismissed immediately from
$`p'(0)` two ways, {bpref "in_sendov_center"}[].)

# The two parameters

Everything is measured by two real numbers. The first,
$$`\alpha := \frac{n-1}{2}(1 - a^2),`
(blog (11)) measures how close $`a` is to $`1` at scale $`1/n`; the delicate
regime is $`\alpha = O(1)`. The second is built from the mean
$`x + iy := \frac{1}{n-1}\sum_j q_j` of the $`q_j` through the quadratic
$$`\beta(t) := 1 - 2atx + a^2t^2, \qquad \beta(1) = (1-a)^2 + 2a(1-x),`
(blog (14), (15)); $`\beta(1)` measures how close $`x` is to $`1`. In the
near-counterexample $`x = 1` and $`\beta(1) = 0`. The proof produces two
incompatible constraints between $`\alpha` and $`\beta(1)`.

# The polar channel: an upper bound on beta(1)

Blog Proposition 10. The Möbius map $`z \mapsto (a - z)/(1 - az)` preserves the
disk, so every factor on the left of the polar identity has modulus at least
$`1`. The triangle inequality then gives the *branch point* $`(\star)`, blog
(23),
$$`1 \le \int_0^1 \prod_j \bigl|t(1-a^2)q_j + a\bigr|\,dt,`
which is {bpref "in_polar_star"}[]. Applying AM–GM to the product and
expanding $`\sum_j |t(1-a^2)q_j + a|^2` in terms of $`x` gives the *raw polar
inequality* (16)
$$`1 \le \int_0^1 \bigl(a^2 + 2atx(1-a^2) + t^2(1-a^2)^2\bigr)^{\frac{n-1}{2}}\,dt,`
which is {bpref "in_1Q"}[] with the integrand {bpref "in_Ppolar"}[]. Bounding
$`t^2 \le t` and $`1 + y \le e^y` yields the exponential form (17)
$$`1 < \int_0^1 \exp\bigl(\alpha(-1 + (2 - \beta(1))t)\bigr)\,dt`
({bpref "in_polar_exp"}[]), and evaluating the integral as
$`e^{-u}\sinh h / h` with $`u = \alpha\beta(1)/2`, $`h = \alpha(2 - \beta(1))/2`
and the elementary estimate $`\log(\sinh h / h) \le \sqrt{h^2 + 9} - 3`
(blog (27), {bpref "in_sinh"}[]) gives the *simplified polar inequality* (18)
$$`0 < \beta(1) < \min\Bigl(\frac{\alpha}{3 + \alpha},\; 1 - \frac{\log\alpha}{\alpha}\Bigr),`
which is {bpref "in_beta_bound"}[]. In words: if $`a` is within $`O(1/n)` of
$`1` then the mean of the $`q_j` is forced very close to $`1` as well.

# The origin channel: a lower bound on beta(1)

Blog Proposition 11, the harder half. Heuristically
$`F(t) \approx \exp(-(n-1)a(x+iy)t)`, so $`\int_0^1 F \approx (1 - F(1))/((n-1)a(x+iy))`;
this ties the two origin identities together. Made rigorous:
$`F(0) = 1` and the exact derivative of $`F` give the pointwise *error
bound*
$$`\bigl|F'(t) + (n-1)a(x+iy)F(t)\bigr| \le a^2t(n-1)\beta(t)^{\frac{n-2}{2}},`
proved with Maclaurin's inequality and Cauchy–Schwarz in place of AM–GM
({bpref "in_error_bound"}[], {bpref "in_maclaurin"}[]). Integrating gives the
triangle inequality (32), {bpref "in_tri"}[].

The origin identities express $`F(1) + (n-1)a(x+iy)\int_0^1 F` exactly in
terms of $`J := \prod_j z_jq_j` and $`\sum_j 1/z_j`. If every $`z_j, q_j` were
on the unit circle one could use $`1/z_j = \overline{z_j}` and the centroid
identity to evaluate that sum. In general one pays a defect proportional to
$`1 - |J|^2`, controlled by the *defect lemma* (blog Lemma 13)
$$`\prod_j |w_j|\;\sum_j\Bigl|\frac1{w_j} - \overline{w_j}\Bigr| \le 1 - \prod_j |w_j|^2`
for points of the closed disk ({bpref "in_defect"}[]; the blog post proves it
by superadditivity of $`\sinh`, the formalization by a direct induction). The
resulting estimate is {bpref "in_Jsum"}[]. A small lower bound (35),
{bpref "in_grow"}[] — the *only* place $`n \ge 5` is used — shows the bound is
monotone in $`|J|`, so $`|J|` may be set to $`1`; eliminating $`y` via
$`|s + it| \le s + t^2/(2s)` yields the *raw origin inequality* (19)
$$`2\alpha + ax \le \frac{1 - x^2}{2(n-1)} + a^2n(n-1)\int_0^1 t\,\beta(t)^{\frac{n-2}{2}}\,dt,`
which is {bpref "in_origin_exact"}[].

Two consequences. First, combined with the polar bound (18), a crude estimate
of the integral forces (20), $`\alpha \le 17` ({bpref "in_alpha17"}[]), so
$`a` really is within $`O(1/n)` of $`1`. Second, an elementary rearrangement
gives the form (21) in which $`\beta(1)` appears as a lower bound,
$$`1 \le \frac{\beta(1)}{2\alpha(1 - \beta(1))} + \frac{\beta(1)}{4\alpha} + \frac{1}{2(n-1)} + \frac{\beta(1)}{4\alpha(n-1)} + \frac{a^4n(n-1)(n-2)\beta(1)}{4\alpha}\int_0^1 t^3\beta(t)^{\frac{n-4}{2}}\,dt,`
which is {bpref "in_one_le"}[]. Roughly: the origin channel needs
$`\beta(1) \gtrsim \alpha`, the polar channel needs
$`\beta(1) \lesssim \alpha/3`.

# Closing the gap: an inequality in n and alpha alone

The right side of (21) is increasing in $`\beta(1)`, so substituting the polar
bound $`\beta(1) \le \alpha/(3 + \alpha)` yields blog equation `stat`, (22):
$$`1 \le R_n(\alpha) := \frac16 + \frac{1}{4(3+\alpha)} + \frac{1}{2(n-1)} + \frac{1}{4(n-1)(3+\alpha)} + \frac{a^4n(n-1)(n-2)}{4(3+\alpha)}\int_0^1 t^3\bigl(1 - 2c(\alpha)t + a^2t^2\bigr)^{\frac{n-4}{2}}\,dt`
with $`c(\alpha) = 1 - \frac{\alpha}{n-1} - \frac{\alpha}{2(3+\alpha)}`, under
the feasibility constraint $`c(\alpha)^2 \le a^2` ({bpref "in_stat"}[],
{bpref "fr_rhs"}[]). This is a statement about two real parameters with no
polynomial in sight, and it is false on the whole range $`n \ge 5`,
$`0 \le \alpha \le 17`:

* for large $`n` the blog post bounds the quadratic by an exponential and
  computes $`R_n(\alpha) \le 0.399` for $`n > 200`; the formalization sharpens
  the Beta-function constant and pushes the threshold down to $`n \ge 101`
  ({bpref "lg_main"}[]);
* for $`5 \le n \le 100` the blog post appeals to numerics (its worst case is
  $`n = 53`, where $`R_n(\alpha)` reaches about $`0.853`); the formalization
  certifies each degree by explicit polynomial arithmetic on Bernstein-type
  certificates ({bpref "fr_cover"}[], {bpref "fr_certificates"}[]).

Together these are {bpref "main_stat_lt_one"}[], and the incompatibility of the
two channels is {bpref "in_incompatible"}[]. Assembling everything gives
{bpref "in_sendov_interior"}[].

# Low degrees

Blog Section 4. For $`n \le 5` the branch point $`(\star)` already fails: by
the triangle inequality $`1 \le \int_0^1 (a + (1-a^2)t)^{n-1}\,dt`, and the
right side is an explicit polynomial in $`a` that is strictly below $`1` for
$`0 \le a < 1`. This is {bpref "ld_main"}[]; the blueprint reduces all four
exponents to the quartic ({bpref "ld_pow_le_quartic"}[],
{bpref "ld_J4_lt_one"}[]). The blog post notes the same argument works for
$`n = 5` but not beyond (Remark 16); here degree five is proved twice, once
in this branch and once by the finite-range certificate, as a consistency
check.

# The boundary: Rubinstein's theorem

Blog Section 3, Theorem 14. At $`a = 1` the polar identity degenerates
($`1/a = a`), and is replaced by the Meir–Sharma identity (blog Lemma 15),
obtained from $`p''(a)/p'(a)` two ways:
$$`\sum_j q_j = 2\sum_j \frac{1}{a - z_j}.`
This is {bpref "bd_reciprocal"}[]. For $`a = 1` and $`|z_j| \le 1` the right
side has real part at least $`n - 1` ({bpref "bd_half_le_re"}[]) while the
left has real part at most $`n - 1`, so every $`q_j = 1`
({bpref "bd_all_q_eq_one"}[]), all critical points are at the origin, and
$`p = c(z^n - 1)`. This is exactly the exceptional case of Phelps–Rodriguez,
and it is why the formalization obtains the strong form of the conjecture at
no extra cost ({bpref "bd_rubinstein_one"}[]).

# Where the formalization departs from the blog post

The nodes carry "(Deviation from the write-up)" notes where the Lean proof
takes a different route. The main ones:

* multisets of roots and critical points, and the division-free
  {bpref "in_sumEraseProd"}[], remove every "removing singularities"
  convention and every junk value of $`0^{-1}`;
* AM–GM and Maclaurin are proved from Bernoulli's inequality by induction
  ({bpref "in_maclaurin"}[]) rather than imported;
* the defect lemma is proved without $`\sinh` ({bpref "in_defect"}[]);
* the $`\alpha \le 17` step reuses the large-degree tail bound and improves
  the numerical margin ({bpref "in_alpha17"}[]);
* the mean value theorem in (21) is replaced by Bernoulli
  ({bpref "in_one_le"}[]);
* the finite/large crossover is at $`n = 100/101` instead of $`200/201`, and
  the finite range is certified rather than checked numerically.

The blog post's variable $`a^2` is the blueprint's $`A`, and $`n - 1` is
written $`M` in the numerical chapters.
