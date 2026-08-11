/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Statement
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Polynomial moments

The integrals `∫ t in 0..1, t ^ 3 * Q ^ k` appearing in `Sendov.R` are, for natural `k`,
integrals of polynomials, hence exactly computable.  This file isolates that computation.

For now it provides only `Sendov.integral_poly7`, which covers `k ≤ 2` and so serves
degrees six and seven.  The general even-degree argument will need the `Finset.sum` version
of the same statement, together with the multinomial expansion of `Q ^ k`; this file is
where that belongs.
-/

namespace Sendov

open MeasureTheory

/-- Every monomial is interval integrable on `[0,1]`. -/
lemma intervalIntegrable_const_mul_pow (a : ℝ) (m : ℕ) :
    IntervalIntegrable (fun t : ℝ => a * t ^ m) volume 0 1 :=
  (by fun_prop : Continuous fun t : ℝ => a * t ^ m).intervalIntegrable _ _

/-- The moments of a polynomial supported in degrees three to seven.  This covers
`∫ t in 0..1, t ^ 3 * Q ^ k` for `k ≤ 2`. -/
lemma integral_poly7 (a₀ a₁ a₂ a₃ a₄ : ℝ) :
    (∫ t in (0 : ℝ)..1, (a₀ * t ^ 3 + a₁ * t ^ 4 + a₂ * t ^ 5 + a₃ * t ^ 6 + a₄ * t ^ 7))
      = a₀ / 4 + a₁ / 5 + a₂ / 6 + a₃ / 7 + a₄ / 8 := by
  have h₀ := intervalIntegrable_const_mul_pow a₀ 3
  have h₁ := intervalIntegrable_const_mul_pow a₁ 4
  have h₂ := intervalIntegrable_const_mul_pow a₂ 5
  have h₃ := intervalIntegrable_const_mul_pow a₃ 6
  have h₄ := intervalIntegrable_const_mul_pow a₄ 7
  rw [intervalIntegral.integral_add (((h₀.add h₁).add h₂).add h₃) h₄,
    intervalIntegral.integral_add ((h₀.add h₁).add h₂) h₃,
    intervalIntegral.integral_add (h₀.add h₁) h₂,
    intervalIntegral.integral_add h₀ h₁,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow, integral_pow, integral_pow]
  norm_num
  ring

end Sendov
