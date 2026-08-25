import Verso
import VersoManual
import VersoBlueprint
import Sendov

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The conjecture" =>

The top of the development: the numerical claim for every degree
(`Sendov/Main.lean`), and Sendov's conjecture together with the
Phelps–Rodriguez conjecture for an arbitrary zero (`Sendov/Conjecture.lean`).
Nothing mathematical happens in the second file; it removes the normalization
$`a \in [0,1)` by rotating the variable.

:::group "conjecture"
Let n be at least 2 and let p be a degree-n polynomial with all zeroes in the
closed unit disk. Then for every zero a of p there is a critical point zeta
with dist(zeta, a) at most 1 (Sendov), and in fact strictly less than 1 unless
a lies on the unit circle and p is a scalar multiple of z^n - a^n
(Phelps–Rodriguez).
:::

# The numerical claim for every degree

:::theorem "main_stat_lt_one" (parent := "conjecture") (lean := "Sendov.stat_lt_one")
For every $`n \ge 5`, $`0 \le \alpha \le 17`, and $`c^2 \le A`:
$`R_n(\alpha) < 1`. The finite range $`5 \le n \le 100` is certified by
explicit polynomial arithmetic and $`n \ge 101` analytically; the seam is at
$`100/101`. In Lean: `Sendov.stat_lt_one`. Uses {uses "fr_cover"}[] and
{uses "lg_main"}[].
:::

:::corollary "main_stat_contradiction" (parent := "conjecture") (lean := "Sendov.stat_contradiction")
Equation `stat` of the blog post, $`1 \le R_n(\alpha)`, is unsatisfiable
outright: no range is left open. In Lean: `Sendov.stat_contradiction`. Uses
{uses "main_stat_lt_one"}[].
:::

# Rotating the variable

:::definition "main_rotate" (parent := "conjecture") (lean := "Sendov.rotate")
$`(\operatorname{rotate}_\omega p)(z) = p(\omega z)`. For $`|\omega| = 1` it
preserves the degree, keeps all zeroes in the closed unit disk
(`Sendov.roots_rotate`), sends the zero $`a = \omega r` to the real point $`r`,
and its critical points are the $`\omega^{-1}\zeta` with
$`|\omega^{-1}\zeta - r| = |\zeta - a|`. In Lean: `Sendov.rotate`
(`Sendov/Conjecture.lean`).
:::

# The two conjectures

:::theorem "main_phelps_rodriguez" (parent := "conjecture") (lean := "Sendov.phelps_rodriguez")
*The Phelps–Rodriguez conjecture.* For degree $`n \ge 2`, all zeroes in the
closed unit disk, and any zero $`a`: either $`p'` has a zero $`\zeta` with
$`|\zeta - a| < 1`, or $`|a| = 1` and $`p = c(X^n - a^n)` for some
$`c \ne 0`. In Lean: `Sendov.phelps_rodriguez`. Uses {uses "main_rotate"}[],
{uses "in_sendov_interior_real"}[], and {uses "bd_rubinstein_one"}[].
:::

:::proof "main_phelps_rodriguez"
Three cases by the position of $`a`. At $`a = 0`, `Sendov.sendov_center`. For
$`0 < |a| < 1`, rotate to the real zero $`r = |a|` and apply
`Sendov.sendov_interior_real`. For $`|a| = 1`, rotate to $`1` and apply
`Sendov.rubinstein_one`; its extremal polynomial $`c(z^n - 1)` rotates back to
$`c\,\omega^{-n}(z^n - a^n)`.
:::

:::theorem "main_sendov" (parent := "conjecture") (lean := "Sendov.sendov")
*Sendov's conjecture.* For degree $`n \ge 2`, all zeroes in the closed unit
disk, and any zero $`a`: $`p'` has a zero $`\zeta` with $`|\zeta - a| \le 1`.
In the extremal branch the critical point $`\zeta = 0` is at distance exactly
one. In Lean: `Sendov.sendov`. Uses {uses "main_phelps_rodriguez"}[].
:::

# Interface

`Solution.lean` restates both theorems in the form of the challenge file
`Challenge.lean` (`SendovConjecture.sendov`, `SendovConjecture.phelps_rodriguez`),
with the degree hypothesis as $`2 \le \deg p` and the zero hypothesis
quantified over all $`w` with $`p(w) = 0`; the two differences are bookkeeping
only. CI runs `#print axioms` on the exported theorems: they depend on
`propext`, `Classical.choice`, and `Quot.sound` alone.
