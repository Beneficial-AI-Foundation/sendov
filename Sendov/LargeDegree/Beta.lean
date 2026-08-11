/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Beta integral `∫₀¹ t³ (1-t)ˢ dt`

The large-degree argument bounds the integral in `Sendov.R` on `[0, c/A]` by replacing `Q`
with the chord `1 - ct`, which leads to `∫₀¹ t³ (1-t)ˢ dt` for a real exponent `s > 0`.

The informal write-up reaches the same place through `Q ≤ exp(-ct)` and the Gamma integral
`∫₀^∞ t³ e^{-rct} dt = 6/(rc)⁴`.  The Beta route taken here is preferable in Lean: it needs
no improper integral and no `Real.exp`, only `integral_rpow`.  It is also strictly sharper,
since

  `6/((s+1)(s+2)(s+3)(s+4)) ≤ 6/s⁴`,

so every numerical constant downstream of the Gamma bound remains valid
(`Sendov.beta_le_six_div_pow`).

## Main statements

* `Sendov.integral_cube_mul_rpow`: `∫₀¹ t³(1-t)ˢ dt = 6/((s+1)(s+2)(s+3)(s+4))`;
* `Sendov.integral_chord_pow`: the same after scaling by `c`, over `[0, 1/c]`;
* `Sendov.beta_le_six_div_pow`: the weakening to `6/s⁴` used by the informal argument.
-/

namespace Sendov

open MeasureTheory

/-- `∫₀¹ xˢ dx = 1/(s+1)` for `s > -1`. -/
lemma integral_rpow_zero_one {s : ℝ} (hs : -1 < s) :
    (∫ x in (0 : ℝ)..1, x ^ s) = 1 / (s + 1) := by
  rw [integral_rpow (Or.inl hs), Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

/-- `x ^ (s + m) = x ^ s * x ^ m` for positive `x` and a natural `m`. -/
lemma rpow_add_nat_pos {x : ℝ} (hx : 0 < x) (s : ℝ) (m : ℕ) :
    x ^ (s + (m : ℝ)) = x ^ s * x ^ m := by
  rw [Real.rpow_add hx, Real.rpow_natCast]

/-- The Beta integral `B(4, s+1)`. -/
lemma integral_cube_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = 6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) := by
  have h1 : (0 : ℝ) < s + 1 := by linarith
  have h2 : (0 : ℝ) < s + 2 := by linarith
  have h3 : (0 : ℝ) < s + 3 := by linarith
  have h4 : (0 : ℝ) < s + 4 := by linarith
  -- reflect `x ↦ 1 - x`
  have hrefl : (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = ∫ x in (0 : ℝ)..1, (1 - x) ^ 3 * x ^ s := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => (1 - y) ^ 3 * y ^ s) 1
    simpa using this
  -- expand `(1-x)³` and split the real power
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (1 - x) ^ 3 * x ^ s
        = x ^ s - 3 * x ^ (s + (1 : ℕ)) + 3 * x ^ (s + (2 : ℕ)) - x ^ (s + (3 : ℕ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]
      rw [Real.zero_rpow (by positivity), Real.zero_rpow (by push_cast; linarith),
        Real.zero_rpow (by push_cast; linarith), Real.zero_rpow (by push_cast; linarith)]
      ring
    · rw [rpow_add_nat_pos h, rpow_add_nat_pos h, rpow_add_nat_pos h]
      ring
  rw [hrefl, intervalIntegral.integral_congr hcongr]
  have hi' : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi : ∀ m : ℕ, IntervalIntegrable (fun x : ℝ => x ^ (s + (m : ℕ))) volume 0 1 := by
    intro m
    apply intervalIntegral.intervalIntegrable_rpow'
    push_cast
    linarith
  have hc : ∀ (a : ℝ) (m : ℕ),
      IntervalIntegrable (fun x : ℝ => a * x ^ (s + (m : ℕ))) volume 0 1 :=
    fun a m => (hi m).const_mul a
  rw [intervalIntegral.integral_sub ((hi'.sub (hc 3 1)).add (hc 3 2)) (hi 3),
    intervalIntegral.integral_add (hi'.sub (hc 3 1)) (hc 3 2),
    intervalIntegral.integral_sub hi' (hc 3 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_rpow_zero_one (by linarith), integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring

/-- The Beta value is at most `6/s⁴`; this is the form the informal argument uses, obtained
there from the Gamma integral. -/
lemma beta_le_six_div_pow {s : ℝ} (hs : 0 < s) :
    6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) ≤ 6 / s ^ 4 := by
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [hs.le, sq_nonneg s, sq_nonneg (s + 1)]

/-- The chord integral over `[0, 1/c]`, after scaling out `c`. -/
lemma integral_chord_pow {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t ^ 3 * (1 - c * t) ^ s)
      = 6 / (c ^ 4 * ((s + 1) * (s + 2) * (s + 3) * (s + 4))) := by
  have hc' : c ≠ 0 := hc.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / c)
    (fun y : ℝ => (y / c) ^ 3 * (1 - y) ^ s) hc'
  have hfun : (fun t : ℝ => ((c * t) / c) ^ 3 * (1 - c * t) ^ s)
      = fun t : ℝ => t ^ 3 * (1 - c * t) ^ s := by
    funext t
    rw [mul_div_cancel_left₀ t hc']
  simp only [hfun] at h
  rw [show c * (1 / c) = 1 by field_simp, mul_zero] at h
  have hg : (fun y : ℝ => (y / c) ^ 3 * (1 - y) ^ s)
      = fun y : ℝ => (1 / c ^ 3) * (y ^ 3 * (1 - y) ^ s) := by
    funext y
    field_simp
  rw [hg, intervalIntegral.integral_const_mul, integral_cube_mul_rpow hs] at h
  rw [h]
  simp only [smul_eq_mul]
  field_simp

end Sendov
