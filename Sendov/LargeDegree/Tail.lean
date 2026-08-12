/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.LargeDegree.Beta

/-!
# The tail bound

The large-degree argument replaces the integral in `Sendov.R` by an elementary expression.
`Q` is a convex parabola with vertex at `t₀ = c/A`, so on `[0, t₀]` it lies below the chord
`1 - ct`, and on `[t₀, 1]` it is increasing and hence at most `Q 1 = B`.  Splitting `∫₀¹`
there and using `Sendov.integral_chord_pow` on the first piece gives

  `∫₀¹ t³ Q^r dt ≤ 6 / (c⁴ (r+1)(r+2)(r+3)(r+4)) + Bʳ / 4`.

This is the only part of the large-degree argument that touches integration; everything after
it is elementary inequalities in `α` and `n`.

Two points shape the proof.  The chord bound needs `1 - ct ≥ 0`, which comes from
`ct ≤ c²/A ≤ 1` — feasibility again, in the form `c² ≤ A`.  And the vertex may lie outside
`[0,1]`: the split is therefore made at `s = min t₀ 1`, after which the first piece is
enlarged to `[0, 1/c]` (legitimate because `s ≤ 1/c`, again by feasibility) and the second
piece is empty when `t₀ > 1`.

## Main statements

* `Sendov.Q_le_chord`: `Q t ≤ 1 - ct` below the vertex;
* `Sendov.Q_le_B`: `Q t ≤ B` above it;
* `Sendov.integral_le_tail`: the bound above.
-/

namespace Sendov

open MeasureTheory

variable {n : ℕ} {α t : ℝ}

/-- Below the vertex, `Q` lies under the chord `1 - ct`. -/
lemma Q_le_chord (ht0 : 0 ≤ t) (ht : A n α * t ≤ c n α) : Q n α t ≤ 1 - c n α * t := by
  simp only [Q]
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht)]

/-- Above the vertex, `Q` is increasing, so it is at most its value `B` at `t = 1`. -/
lemma Q_le_B (hn : 2 ≤ n) (hα : 0 ≤ α) (hA : 0 ≤ A n α) (ht : c n α ≤ A n α * t)
    (ht1 : t ≤ 1) : Q n α t ≤ α / (3 + α) := by
  rw [← Q_one hn hα]
  have hkey : 0 ≤ A n α * (1 + t) - 2 * c n α := by nlinarith [ht, hA, ht1]
  simp only [Q]
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) hkey]

/-- `c ≤ 1`, so the chord's zero `1/c` is at least `1`. -/
lemma c_le_one (hn : 2 ≤ n) (hα : 0 ≤ α) : c n α ≤ 1 := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  simp only [c]
  have h1 : 0 ≤ α / M n := by positivity
  have h2 : 0 ≤ α / (2 * (3 + α)) := by positivity
  linarith

/-- **The tail bound.** -/
theorem integral_le_tail (hn : 2 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α)
    (hc : 0 < c n α) {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ r)
      ≤ 6 / (c n α ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4)))
        + (α / (3 + α)) ^ r / 4 := by
  have hA : 0 < A n α := lt_of_lt_of_le (by positivity) hfeas
  have hc1 : c n α ≤ 1 := c_le_one hn hα
  set t₀ : ℝ := c n α / A n α with ht₀def
  have ht₀pos : 0 < t₀ := by positivity
  set s : ℝ := min t₀ 1 with hsdef
  have hs0 : 0 < s := lt_min ht₀pos one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hcont : Continuous fun u : ℝ => u ^ 3 * Q n α u ^ r := continuous_integrand n α hr.le
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => u ^ 3 * Q n α u ^ r) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hchordcont : Continuous fun u : ℝ => u ^ 3 * (1 - c n α * u) ^ r :=
    (by fun_prop : Continuous fun u : ℝ => u ^ 3).mul
      ((continuous_rpow_const hr.le).comp (by fun_prop))
  -- `s ≤ 1/c`, from feasibility below the vertex and from `c ≤ 1` otherwise
  have hsc : s ≤ 1 / c n α := by
    rcases min_cases t₀ 1 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hsdef, h, ht₀def, le_div_iff₀ hc, div_mul_eq_mul_div, div_le_one hA]
      nlinarith [hfeas]
    · rw [hsdef, h, le_div_iff₀ hc]
      linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s 1)]
  have hfirst : (∫ u in (0 : ℝ)..s, u ^ 3 * Q n α u ^ r)
      ≤ 6 / (c n α ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4))) := by
    have hle : (∫ u in (0 : ℝ)..s, u ^ 3 * Q n α u ^ r)
        ≤ ∫ u in (0 : ℝ)..s, u ^ 3 * (1 - c n α * u) ^ r := by
      refine intervalIntegral.integral_mono_on hs0.le (hint 0 s)
        (hchordcont.intervalIntegrable _ _) ?_
      intro u hu
      obtain ⟨hu0, hus⟩ := hu
      have huv : A n α * u ≤ c n α := by
        have hut : u ≤ t₀ := le_trans hus (min_le_left _ _)
        rw [ht₀def, le_div_iff₀ hA] at hut
        linarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Q_nonneg hfeas u) (Q_le_chord hu0 huv) hr.le) (pow_nonneg hu0 3)
    refine hle.trans ?_
    rw [← integral_chord_pow hr hc]
    have hrest : 0 ≤ ∫ u in s..1 / c n α, u ^ 3 * (1 - c n α * u) ^ r := by
      refine intervalIntegral.integral_nonneg hsc ?_
      intro u hu
      have : 0 ≤ 1 - c n α * u := by
        have := hu.2
        rw [le_div_iff₀ hc] at this
        linarith
      exact mul_nonneg (pow_nonneg (le_trans hs0.le hu.1) 3) (Real.rpow_nonneg this _)
    have hadd : (∫ u in (0 : ℝ)..s, u ^ 3 * (1 - c n α * u) ^ r)
        + (∫ u in s..1 / c n α, u ^ 3 * (1 - c n α * u) ^ r)
        = ∫ u in (0 : ℝ)..1 / c n α, u ^ 3 * (1 - c n α * u) ^ r :=
      intervalIntegral.integral_add_adjacent_intervals
        (hchordcont.intervalIntegrable 0 s) (hchordcont.intervalIntegrable s (1 / c n α))
    linarith
  have hsecond : (∫ u in s..1, u ^ 3 * Q n α u ^ r) ≤ (α / (3 + α)) ^ r / 4 := by
    have hBnn : (0 : ℝ) ≤ (α / (3 + α)) ^ r :=
      Real.rpow_nonneg (by positivity) _
    have hQB : ∀ u ∈ Set.Icc s 1, Q n α u ≤ α / (3 + α) := by
      intro u hu
      rcases le_or_gt t₀ u with h | h
      · rw [ht₀def, div_le_iff₀ hA] at h
        exact Q_le_B hn hα hA.le (by linarith) hu.2
      · -- `u < t₀` forces `s = 1`, hence `u = 1`
        have hu1 : u = 1 := by
          rcases min_cases t₀ 1 with ⟨he, _⟩ | ⟨he, _⟩
          · rw [hsdef, he] at hu; linarith [hu.1]
          · rw [hsdef, he] at hu; linarith [hu.1, hu.2]
        rw [hu1, Q_one hn hα]
    have hle : (∫ u in s..1, u ^ 3 * Q n α u ^ r)
        ≤ ∫ u in s..1, (α / (3 + α)) ^ r * u ^ 3 := by
      refine intervalIntegral.integral_mono_on hs1 (hint s 1)
        ((by fun_prop : Continuous fun u : ℝ => (α / (3 + α)) ^ r * u ^ 3).intervalIntegrable _ _)
        ?_
      intro u hu
      have := Real.rpow_le_rpow (Q_nonneg hfeas u) (hQB u hu) hr.le
      nlinarith [pow_nonneg (le_trans hs0.le hu.1) 3, this, hBnn]
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hs4 : 0 ≤ s ^ 4 := by positivity
    nlinarith [hBnn, hs4]
  linarith

/-! ### The elementary upper bound `U`

Everything after this point in the large-degree argument is an inequality in `α` and `n`
alone; no integral survives. -/

/-- The elementary bound replacing `Sendov.R`: `(11)` of the informal write-up, but with the
sharper Beta constant `6/((r+1)(r+2)(r+3)(r+4))` in place of `6/r⁴`. -/
noncomputable def U (n : ℕ) (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
    + A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
      * (6 / (c n α ^ 4 *
            ((((n : ℝ) - 4) / 2 + 1) * (((n : ℝ) - 4) / 2 + 2) * (((n : ℝ) - 4) / 2 + 3)
              * (((n : ℝ) - 4) / 2 + 4)))
        + (α / (3 + α)) ^ (((n : ℝ) - 4) / 2) / 4)

/-- On the large-degree range `c` is bounded below, hence positive.  For `n ≥ 101` and
`α ≤ 17` this gives `c ≥ 81/200`, which is `(3)` of the write-up. -/
lemma c_ge_of_large (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : 81 / 200 ≤ c n α := by
  have hM : (100 : ℝ) ≤ M n := by
    have : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simp only [M]; linarith
  have hM0 : (0 : ℝ) < M n := by linarith
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  simp only [c]
  have h1 : α / M n ≤ 17 / 100 := by
    rw [div_le_iff₀ hM0]
    nlinarith
  have h2 : α / (2 * (3 + α)) ≤ 17 / 40 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (3 + α))]
    nlinarith
  linarith

/-- **`R` is bounded by the elementary expression `U`.**  This is the bridge out of
integration: from here the large-degree argument is elementary. -/
theorem R_le_U (hn : 5 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α) (hc : 0 < c n α) :
    R n α ≤ U n α := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : (0 : ℝ) < ((n : ℝ) - 4) / 2 := by linarith
  exact R_le_of_integral_le (by omega) hα (integral_le_tail (by omega) hα hfeas hc hr)

end Sendov
