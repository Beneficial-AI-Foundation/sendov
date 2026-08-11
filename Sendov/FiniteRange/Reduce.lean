/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Moments
import Sendov.FiniteRange.OddBound

/-!
# Reduction of a single degree to a numerical inequality

This file assembles the general machinery.  For any degree `n`, proving `R n α < 1` reduces
to a numerical inequality in `α` alone, with no integrals and no square roots left:

* `Sendov.integral_eq_mom`: if `(n-4)/2` is the natural number `k` (that is, `n` is even),
  the integral in `Sendov.R` *equals* `Sendov.mom n α k`;
* `Sendov.integral_le_mom`: if `(n-4)/2 = k + 1/2` (that is, `n` is odd), the integral is at
  most `mom n α (k+1) / (2w) + w/2 * mom n α k`, for any `w > 0`;
* `Sendov.finite_range_of_bound`: given any upper bound `J` for the integral, `R n α < 1`
  follows from an inequality between explicit rational functions of `α`.

So each degree of the finite range needs exactly three things: the exponent identity
(`norm_num`), an evaluation of `Sendov.mom` for the relevant `k` (a finite sum, expanded by
`Finset.sum_range_succ`), and a positivity proof for the resulting rational function on
`0 ≤ α ≤ min 17 ((n-1)/2)`, the bound on `α` coming from `Sendov.alpha_le_half_M`.

`Sendov.mom_one` and `Sendov.mom_two` record the first two evaluations, which also serve as
a check on the general formula.
-/

namespace Sendov

open MeasureTheory Finset

variable {n : ℕ} {α w : ℝ}

/-- **Even degrees.**  The integral in `Sendov.R` is exactly a moment. -/
lemma integral_eq_mom (k : ℕ) (hk : ((n : ℝ) - 4) / 2 = (k : ℕ)) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) = mom n α k := by
  rw [hk]
  simp only [Real.rpow_natCast]
  exact integral_moment n α k

/-- **Odd degrees.**  After `Sendov.integral_rpow_le` has removed the square root, the
integral in `Sendov.R` is bounded by a combination of two moments. -/
lemma integral_le_mom (hfeas : c n α ^ 2 ≤ A n α) (k : ℕ)
    (hk : ((n : ℝ) - 4) / 2 = (k : ℝ) + 1 / 2) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ mom n α (k + 1) / (2 * w) + w / 2 * mom n α k := by
  refine (integral_rpow_le hfeas k hk hw).trans (le_of_eq ?_)
  have hfun : (fun t : ℝ => t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2)))
      = fun t : ℝ => 1 / (2 * w) * (t ^ 3 * Q n α t ^ (k + 1))
          + w / 2 * (t ^ 3 * Q n α t ^ k) := by
    funext t
    rw [pow_succ]
    ring
  have hi : ∀ j : ℕ, ∀ a : ℝ,
      IntervalIntegrable (fun t : ℝ => a * (t ^ 3 * Q n α t ^ j)) volume 0 1 := by
    intro j a
    exact (by simp only [Q]; fun_prop :
      Continuous fun t : ℝ => a * (t ^ 3 * Q n α t ^ j)).intervalIntegrable _ _
  rw [hfun, intervalIntegral.integral_add (hi (k + 1) _) (hi k _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_moment, integral_moment]
  ring

/-- **The reduction.**  Any upper bound `J` for the integral turns `R n α < 1` into an
inequality between explicit rational functions of `α`. -/
theorem finite_range_of_bound (hn : 2 ≤ n) (hα : 0 ≤ α) {J : ℝ}
    (hJ : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) ≤ J)
    (h : 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      + A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) * J < 1) :
    R n α < 1 :=
  lt_of_le_of_lt (R_le_of_integral_le hn hα hJ) h

/-- `∫ t in 0..1, t ^ 3 * Q` -/
lemma mom_one (n : ℕ) (α : ℝ) : mom n α 1 = 1 / 4 - 2 * c n α / 5 + A n α / 6 := by
  simp [mom, Finset.sum_range_succ]
  ring

/-- `∫ t in 0..1, t ^ 3 * Q ^ 2` -/
lemma mom_two (n : ℕ) (α : ℝ) :
    mom n α 2 = 1 / 4 - 4 * c n α / 5 + (2 * c n α ^ 2 / 3 + A n α / 3)
      - 4 * c n α * A n α / 7 + A n α ^ 2 / 8 := by
  simp [mom, Finset.sum_range_succ]
  ring

end Sendov
