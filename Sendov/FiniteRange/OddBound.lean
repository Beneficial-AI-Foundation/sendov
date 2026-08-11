/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Basic

/-!
# The odd-degree bound

For odd `n ≥ 7` the exponent `(n-4)/2` is the half-integer `k + 1/2` with `k = (n-5)/2`, and
`Sendov.R` involves a genuine square root.  Writing `Q ^ (k+1/2) = Q ^ k * √Q` and using
`2√u ≤ 1 + u` replaces it by the average of two polynomial moments,

  `∫ t in 0..1, t ^ 3 * Q ^ (k+1/2) ≤ ∫ t in 0..1, t ^ 3 * (Q ^ k + Q ^ (k+1)) / 2`,

which is `(O)` in the informal plan.  This is the only place where `Real.sqrt` appears; the
statement `Sendov.integral_rpow_le` is already free of it.

Note that only `0 ≤ Q` is needed, not `Q ≤ 1`: the inequality `2√u ≤ 1 + u` is just
`(1 - √u) ^ 2 ≥ 0` and holds for every `u ≥ 0`.
-/

namespace Sendov

open MeasureTheory

variable {n : ℕ} {α q : ℝ}

lemma two_mul_sqrt_le_one_add (hq : 0 ≤ q) : 2 * Real.sqrt q ≤ 1 + q := by
  nlinarith [sq_nonneg (Real.sqrt q - 1), Real.sq_sqrt hq, Real.sqrt_nonneg q]

/-- The half-integer power bound `q ^ (k + 1/2) ≤ (q ^ k + q ^ (k+1)) / 2`. -/
lemma rpow_add_half_le (hq : 0 ≤ q) (k : ℕ) :
    q ^ ((k : ℝ) + 1 / 2) ≤ (q ^ k + q ^ (k + 1)) / 2 := by
  rcases hq.lt_or_eq with h | h
  · have he : q ^ ((k : ℝ) + 1 / 2) = q ^ k * Real.sqrt q := by
      rw [Real.rpow_add h, Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [he, pow_succ]
    nlinarith [two_mul_sqrt_le_one_add hq, pow_nonneg hq k]
  · rw [← h, Real.zero_rpow (by positivity)]
    positivity

/-- `fun x ↦ x ^ e` is continuous on all of `ℝ` for a nonnegative real exponent `e`. -/
lemma continuous_rpow_const {e : ℝ} (he : 0 ≤ e) : Continuous fun x : ℝ => x ^ e :=
  continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x e (Or.inr he)

lemma continuous_integrand (n : ℕ) (α : ℝ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ 3 * Q n α t ^ e := by
  have hQ : Continuous fun t : ℝ => Q n α t := by
    simp only [Q]; fun_prop
  have h3 : Continuous fun t : ℝ => t ^ 3 := by fun_prop
  exact h3.mul ((continuous_rpow_const he).comp hQ)

/-- **The odd-degree bound (O).**  The square root is eliminated in favour of two
polynomial moments. -/
lemma integral_rpow_le (hfeas : c n α ^ 2 ≤ A n α) (k : ℕ)
    (hk : ((n : ℝ) - 4) / 2 = (k : ℝ) + 1 / 2) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * ((Q n α t ^ k + Q n α t ^ (k + 1)) / 2) := by
  have he : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by rw [hk]; positivity
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_integrand n α he).intervalIntegrable _ _)
    ((by simp only [Q]; fun_prop : Continuous fun t : ℝ =>
      t ^ 3 * ((Q n α t ^ k + Q n α t ^ (k + 1)) / 2)).intervalIntegrable _ _) ?_
  intro t ht
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht.1 3)
  rw [hk]
  exact rpow_add_half_le (Q_nonneg hfeas t) k

end Sendov
