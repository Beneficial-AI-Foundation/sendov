/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The finite-range numerical claim in the proof of Sendov's conjecture

This file states, with a `sorry`, the one numerical claim left open in the blog post
*A digestion of the proof of Sendov's conjecture*.  Nothing else from that post is
formalized here: the polynomial argument that produces the claim is deliberately kept
outside this file, so that the numerical statement can be audited on its own.

## Background

In the blog post one argues by contradiction from a degree `n` polynomial with all zeroes
in the unit disk, a zero `0 ≤ a < 1`, and all critical points at distance `≥ 1` from `a`.
Writing `α := (n-1)(1-a²)/2` and `β(1) := 1 - 2ax + a²` (where `x` is the real part of the
mean of the reciprocal critical-point data), the post derives:

* `0 < β(1) < α/(3+α)` (the simplified polar inequality);
* `α ≤ 17` and an inequality `(1le)`, valid for `n ≥ 5`;
* the elimination of every degree `n > 100` by an asymptotic argument.

Monotonicity in `β(1)` lets one replace `β(1)` by `α/(3+α)` in `(1le)`, which replaces
`a x` by `c` and `β(t)` by `Q t` below.  The resulting inequality is equation `stat` of the
post, namely `1 ≤ R n α`.  The upper bound `c ≤ a x` moreover forces the feasibility
constraint `c ^ 2 ≤ A`, which is what keeps `α` away from its formal upper limit `(n-1)/2`.

What is left open is that `stat` is infeasible on the remaining range

`5 ≤ n ≤ 100`,  `0 ≤ α ≤ 17`,  `c ^ 2 ≤ A`,

which is exactly `Sendov.finite_range` below.

## Main statements

* `Sendov.finite_range`: on the range above, `R n α < 1`.
* `Sendov.finite_range_contradiction`: consequently the post's equation `stat`,
  `1 ≤ R n α`, is contradictory on that range.  This is the form in which the claim is
  applied; it is *derived* from `Sendov.finite_range`, so this file contains one `sorry`.

## Implementation notes

* `α = 0` is allowed, although the blog post has `α > 0` (an earlier inequality there was
  divided by `α`).  This makes the statement slightly stronger and is harmless: the bound
  extends continuously to `α = 0` and stays below `1` there.
* No upper bound on `α` in terms of `n` is assumed: `hfeas` already forces `0 ≤ A n α`,
  hence `α ≤ (n-1)/2`.
* The exponent `((n:ℝ) - 4) / 2` is a half-integer for odd `n`, so `Q n α t ^ _` is
  `Real.rpow`.  Under `hfeas` one has `0 ≤ Q n α t` for `0 ≤ t ≤ 1`, so no junk values of
  `rpow` at negative bases arise; the integrand is continuous, so no integrability
  hypothesis is needed either.

## Numerical diagnostics

These are *not* inputs to the proof, and must not be used as hypotheses; they are recorded
only to indicate the size of the margin.  Numerically, `R n α` attains a maximum of about
`0.8529` over the feasible range, at `n = 53`, `α = 17` — which remains inside the range
below, so shortening it does not make the claim easier.  For comparison, `R 5 0 ≈ 0.6458`
and `R 100 17 ≈ 0.2763`.  The feasibility constraint is binding at low degree: it caps
`α ≲ 1.68` when `n = 5` and `α ≲ 2.19` when `n = 6`, and only ceases to cut into
`[0, 17]` from `n = 36` onwards.

## References

* T. Tao, *A digestion of the proof of Sendov's conjecture*, blog post, 2026.
-/

namespace Sendov

/-- `M n = n - 1`.  All of the quantities below are naturally expressed in terms of it. -/
noncomputable def M (n : ℕ) : ℝ := (n : ℝ) - 1

/-- `A n α = a ^ 2 = 1 - 2α/(n-1)`, from the definition `α = (n-1)(1-a²)/2` of `α`.
The blog post's `a ^ 4` is therefore `A n α ^ 2`. -/
noncomputable def A (n : ℕ) (α : ℝ) : ℝ := 1 - 2 * α / M n

/-- `c n α = 1 - α/(n-1) - α/(2(3+α))`: the value taken by `a * x` after the substitution
of `α/(3+α)` for `β(1)`.  This is `c(α)` in the blog post. -/
noncomputable def c (n : ℕ) (α : ℝ) : ℝ := 1 - α / M n - α / (2 * (3 + α))

/-- `Q n α t = 1 - 2 c t + A t ^ 2`: the quadratic replacing `β(t) = 1 - 2 a x t + a² t²`
after the substitution of `α/(3+α)` for `β(1)`.  Note `Q n α 1 = α/(3+α)`. -/
noncomputable def Q (n : ℕ) (α : ℝ) (t : ℝ) : ℝ := 1 - 2 * c n α * t + A n α * t ^ 2

/-- `R n α` is the right-hand side of equation `stat` of the blog post:
`1/6 + 1/(4(3+α)) + 1/(2(n-1)) + 1/(4(n-1)(3+α))
    + a⁴ n (n-1) (n-2)/(4(3+α)) * ∫ t in 0..1, t³ (1 - 2c(α)t + a²t²) ^ ((n-4)/2)`. -/
noncomputable def R (n : ℕ) (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α)) +
    A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) *
      ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)

/-- **The finite-range claim.**  The right-hand side of equation `stat` of the blog post is
strictly less than `1` on the range of degrees and of `α` left open there, that is, on
`5 ≤ n ≤ 100`, `0 ≤ α ≤ 17`, subject to the feasibility constraint `c ^ 2 ≤ A`. -/
theorem finite_range (n : ℕ) (α : ℝ) (hn : 5 ≤ n) (hn' : n ≤ 100)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) :
    R n α < 1 := by
  sorry

/-- Equation `stat` of the blog post is infeasible on the remaining range
`5 ≤ n ≤ 100`, `0 ≤ α ≤ 17`, `c ^ 2 ≤ A`.  This is the form in which the claim is used. -/
theorem finite_range_contradiction (n : ℕ) (α : ℝ) (hn : 5 ≤ n) (hn' : n ≤ 100)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) (hstat : 1 ≤ R n α) :
    False :=
  absurd hstat (not_le.2 (finite_range n α hn hn' hα hα' hfeas))

end Sendov
