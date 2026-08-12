/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# `log (sinh h / h) ≤ √(h² + 9) - 3`

This is the sharp estimate behind the simplified polar inequality `β(1) ≤ α/(3+α)` of the blog
post: applied at `u = αβ(1)/2`, `h = α(2-β(1))/2`, it is exactly what turns

  `1 ≤ ∫₀¹ exp(α(-1 + (2-β(1))t)) dt = e^{-u} sinh h / h`

into `β(1) ≤ α/(3+α)`.  The constant `3` cannot be improved: at `B = α/(3+α)` the slack in the
integral inequality is `-α⁵/540 + α⁶/648`, so the bound is tight to three orders at `α = 0`.

## The proof

Differentiating, it suffices to prove `coth h - 1/h ≤ h/√(h²+9)`, which after clearing
denominators is

  `G(h) := h⁴ sinh²h - (h²+9) (h cosh h - sinh h)² ≥ 0`.

The informal write-up gets this from the Taylor expansion
`G(h) = Σ_{k≥4} 2^{2k-3} (2k-1) (2k-6)² / (2k)! · h^{2k}`, all of whose coefficients are
nonnegative.  Formalizing an infinite series with nonnegative coefficients is unpleasant, and
unnecessary.  Setting

  `Φ(y) := e^{2y} P₁(y) - e^y P₂(y) - P₃(y)`,
  `P₁ = y³-10y²+36y-36`,  `P₂ = y⁴+16y²-72`,  `P₃ = y³+10y²+36y+36`,

one has the algebraic identity `Φ(2h) = 16 e^{2h} G(h)`, so `G ≥ 0` iff `Φ ≥ 0` on `[0,∞)`.
And `Φ` is *closed* under differentiation in the family

  `Sf u v w y = e^{2y} u(y) - e^y v(y) - w(y)`,  `u` cubic, `v` quartic, `w` cubic,

under `u ↦ 2u + u'`, `v ↦ v + v'`, `w ↦ w'`.  Eight steps of that recurrence reach

  `Φ⁽⁸⁾(y) = 256 e^{2y} (y³+2y²-2y+10) - e^y (y⁴+32y³+352y²+1600y+2504)`,

and `Φ⁽ʲ⁾(0) = 0` for `j ≤ 7`.  So it is enough to prove `Φ⁽⁸⁾ ≥ 0` and integrate eight times.
For `Φ⁽⁸⁾`, divide by `e^y` and use just three terms of the exponential series: what is left is

  `56 + 448 * y + 928 * y ^ 2 + 480 * y ^ 3 + 511 * y ^ 4 + 128 * y ^ 5`,

every coefficient of which is positive.  No certificate, no series manipulation — one `ring`
identity and eight applications of "vanishes at `0` and has nonnegative derivative".

## Main statements

* `Sendov.sinh_sq_le`: `(h²+9)(h cosh h - sinh h)² ≤ h⁴ sinh²h`;
* `Sendov.log_sinh_div_le`: the displayed inequality;
* `Sendov.sinh_le_mul_exp`: the form actually used, `sinh h ≤ h exp (√(h²+9) - 3)`.
-/

namespace Sendov

open Real

/-- `f` vanishes at `0` and has nonnegative derivative on `[0,∞)`, hence is nonnegative there. -/
private lemma nonneg_of_deriv {f g : ℝ → ℝ} (hd : ∀ z, HasDerivAt f (g z) z)
    (h0 : f 0 = 0) (hg : ∀ z, 0 ≤ z → 0 ≤ g z) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ f y := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z hz => (hd z).differentiableAt.differentiableWithinAt) (fun z hz => ?_)
    rw [(hd z).deriv]
    rw [interior_Ici] at hz
    exact hg z (le_of_lt hz)
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  rwa [h0] at this

/-- `1 + y + y²/2 ≤ exp y` for `y ≥ 0`: three terms of the exponential series. -/
private lemma quad_le_exp {y : ℝ} (hy : 0 ≤ y) : 1 + y + y ^ 2 / 2 ≤ exp y := by
  have key : ∀ z : ℝ, 0 ≤ z → 0 ≤ exp z - 1 - z - z ^ 2 / 2 := by
    intro z hz
    refine nonneg_of_deriv (f := fun t => exp t - 1 - t - t ^ 2 / 2)
      (g := fun t => exp t - 1 - t) (fun t => ?_) (by norm_num) (fun t ht => ?_) hz
    · have h := (((hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id' t)).sub
        ((hasDerivAt_pow 2 t).div_const 2)
      refine h.congr_deriv ?_
      norm_num
    · have := add_one_le_exp t
      linarith
  linarith [key y hy]

/-- The family closed under differentiation: `e^{2y} u(y) - e^y v(y) - w(y)` with `u`, `w`
cubic and `v` quartic. -/
private noncomputable def Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) : ℝ :=
  exp (2 * y) * (u₃ * y ^ 3 + u₂ * y ^ 2 + u₁ * y + u₀)
    - exp y * (v₄ * y ^ 4 + v₃ * y ^ 3 + v₂ * y ^ 2 + v₁ * y + v₀)
    - (w₃ * y ^ 3 + w₂ * y ^ 2 + w₁ * y + w₀)

private lemma hasDerivAt_Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) :
    HasDerivAt (fun t : ℝ => Sf u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ t)
      (Sf (2 * u₃) (2 * u₂ + 3 * u₃) (2 * u₁ + 2 * u₂) (2 * u₀ + u₁)
          v₄ (v₃ + 4 * v₄) (v₂ + 3 * v₃) (v₁ + 2 * v₂) (v₀ + v₁)
          0 (3 * w₃) (2 * w₂) w₁ y) y := by
  simp only [Sf]
  have he2 : HasDerivAt (fun t : ℝ => exp (2 * t)) (exp (2 * y) * 2) y := by
    have h := ((hasDerivAt_id' y).const_mul (2 : ℝ)).exp
    refine h.congr_deriv ?_
    ring
  have he1 : HasDerivAt (fun t : ℝ => exp t) (exp y) y := hasDerivAt_exp y
  have hu : HasDerivAt (fun t : ℝ => u₃ * t ^ 3 + u₂ * t ^ 2 + u₁ * t + u₀)
      (3 * u₃ * y ^ 2 + 2 * u₂ * y + u₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul u₃).add
      ((hasDerivAt_pow 2 y).const_mul u₂)).add ((hasDerivAt_id' y).const_mul u₁)).add_const u₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hv : HasDerivAt (fun t : ℝ => v₄ * t ^ 4 + v₃ * t ^ 3 + v₂ * t ^ 2 + v₁ * t + v₀)
      (4 * v₄ * y ^ 3 + 3 * v₃ * y ^ 2 + 2 * v₂ * y + v₁) y := by
    have h := (((((hasDerivAt_pow 4 y).const_mul v₄).add
      ((hasDerivAt_pow 3 y).const_mul v₃)).add
      ((hasDerivAt_pow 2 y).const_mul v₂)).add ((hasDerivAt_id' y).const_mul v₁)).add_const v₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hw : HasDerivAt (fun t : ℝ => w₃ * t ^ 3 + w₂ * t ^ 2 + w₁ * t + w₀)
      (3 * w₃ * y ^ 2 + 2 * w₂ * y + w₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul w₃).add
      ((hasDerivAt_pow 2 y).const_mul w₂)).add ((hasDerivAt_id' y).const_mul w₁)).add_const w₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have h := ((he2.mul hu).sub (he1.mul hv)).sub hw
  refine h.congr_deriv ?_
  ring

/-- The base of the induction, `Φ⁽⁸⁾ ≥ 0`.  Three terms of the exponential series leave a
polynomial with every coefficient positive. -/
private lemma step8 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 256 512 (-512) 2560 1 32 352 1600 2504 0 0 0 0 y := by
  have hA : (0 : ℝ) ≤ 256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560 := by
    nlinarith [sq_nonneg (y - 1), pow_nonneg hy 3, sq_nonneg y]
  have h1 : (1 + y + y ^ 2 / 2) * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560) :=
    mul_le_mul_of_nonneg_right (quad_le_exp hy) hA
  have h2 : (0 : ℝ) ≤ 56 + 448 * y + 928 * y ^ 2 + 480 * y ^ 3 + 511 * y ^ 4 + 128 * y ^ 5 := by
    nlinarith [pow_nonneg hy 5, pow_nonneg hy 4, pow_nonneg hy 3, sq_nonneg y, hy]
  have h3 : (0 : ℝ) ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      - (2504 + 1600 * y + 352 * y ^ 2 + 32 * y ^ 3 + 1 * y ^ 4) := by
    nlinarith [h1, h2]
  have hexp : exp (2 * y) = exp y * exp y := by rw [two_mul, exp_add]
  have h4 := mul_nonneg (exp_pos y).le h3
  calc (0 : ℝ) ≤ exp y * (exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
        - (2504 + 1600 * y + 352 * y ^ 2 + 32 * y ^ 3 + 1 * y ^ 4)) := h4
    _ = Sf 256 512 (-512) 2560 1 32 352 1600 2504 0 0 0 0 y := by
        simp only [Sf, hexp]
        ring

private lemma step7 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 256 512 (-512) 2560 1 32 352 1600 2504 0 0 0 0)
    (fun z => ?_) ?_ step8 hy
  · have h := hasDerivAt_Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0 z
    refine h.congr_deriv ?_
    simp only [Sf]
    ring
  · simp only [Sf]
    norm_num
private lemma step6 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0)
    (fun z => ?_) ?_ step7 hy
  · have h := hasDerivAt_Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0 z
    refine h.congr_deriv ?_
    simp only [Sf]
    ring
  · simp only [Sf]
    norm_num
private lemma step5 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0)
    (fun z => ?_) ?_ step6 hy
  · have h := hasDerivAt_Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0 z
    refine h.congr_deriv ?_
    simp only [Sf]
    ring
  · simp only [Sf]
    norm_num
private lemma step4 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0)
    (fun z => ?_) ?_ step5 hy
  · have h := hasDerivAt_Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0 z
    refine h.congr_deriv ?_
    simp only [Sf]
    ring
  · simp only [Sf]
    norm_num
private lemma step3 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6 y := by
  refine nonneg_of_deriv (g := Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0)
    (fun z => ?_) ?_ step4 hy
  · have h := hasDerivAt_Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6 z
    refine h.congr_deriv ?_
    simp only [Sf]
    ring
  · simp only [Sf]
    norm_num
private lemma step2 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20 y := by
  refine nonneg_of_deriv (g := Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6)
    (fun z => ?_) ?_ step3 hy
  · have h := hasDerivAt_Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20 z
    refine h.congr_deriv ?_
    simp only [Sf]
    ring
  · simp only [Sf]
    norm_num
private lemma step1 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36 y := by
  refine nonneg_of_deriv (g := Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20)
    (fun z => ?_) ?_ step2 hy
  · have h := hasDerivAt_Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36 z
    refine h.congr_deriv ?_
    simp only [Sf]
    ring
  · simp only [Sf]
    norm_num
private lemma step0 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 y := by
  refine nonneg_of_deriv (g := Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36)
    (fun z => ?_) ?_ step1 hy
  · have h := hasDerivAt_Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 z
    refine h.congr_deriv ?_
    simp only [Sf]
    ring
  · simp only [Sf]
    norm_num

/-- The algebraic bridge: `Φ(2h) = 16 e^{2h} G(h)`. -/
private lemma Sf_eq (h : ℝ) :
    Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 (2 * h)
    = 16 * exp h ^ 2 * (h ^ 4 * sinh h ^ 2 - (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2) := by
  have hE : exp h ≠ 0 := (exp_pos h).ne'
  have e4 : exp (2 * (2 * h)) = exp h ^ 4 := by
    rw [show (2 : ℝ) * (2 * h) = h + h + h + h by ring, exp_add, exp_add, exp_add]
    ring
  have e2 : exp (2 * h) = exp h ^ 2 := by
    rw [show (2 : ℝ) * h = h + h by ring, exp_add]; ring
  simp only [Sf, sinh_eq, cosh_eq, e4, e2, exp_neg]
  field_simp
  ring

/-- **The key inequality.**  Equivalent to `coth h - 1/h ≤ h/√(h²+9)`. -/
theorem sinh_sq_le {h : ℝ} (hh : 0 ≤ h) :
    (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2 ≤ h ^ 4 * sinh h ^ 2 := by
  have h0 := step0 (2 * h) (by linarith)
  rw [Sf_eq] at h0
  have : (0 : ℝ) < 16 * exp h ^ 2 := by positivity
  by_contra hc
  push Not at hc
  nlinarith

/-- `sinh h ≤ h cosh h` for `h ≥ 0`; equivalently `h cosh h - sinh h ≥ 0`, which is what makes
the square root below legitimate. -/
private lemma sinh_le_mul_cosh {h : ℝ} (hh : 0 ≤ h) : sinh h ≤ h * cosh h := by
  have : 0 ≤ h * cosh h - sinh h := by
    refine nonneg_of_deriv (f := fun t => t * cosh t - sinh t) (g := fun t => t * sinh t)
      (fun t => ?_) (by simp) (fun t ht => mul_nonneg ht (sinh_nonneg_iff.2 ht)) hh
    exact (((hasDerivAt_id' t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)).congr_deriv
      (by ring)
  linarith

/-- `√(h²+9) (h cosh h - sinh h) ≤ h² sinh h`: the square root of `Sendov.sinh_sq_le`, which is
the derivative inequality `coth h - 1/h ≤ h/√(h²+9)` cleared of denominators. -/
theorem sqrt_mul_sub_le {h : ℝ} (hh : 0 ≤ h) :
    sqrt (h ^ 2 + 9) * (h * cosh h - sinh h) ≤ h ^ 2 * sinh h := by
  have hd : (0 : ℝ) ≤ h * cosh h - sinh h := by linarith [sinh_le_mul_cosh hh]
  have : (0 : ℝ) ≤ h ^ 2 * sinh h := mul_nonneg (sq_nonneg h) (sinh_nonneg_iff.2 hh)
  have hroot : sqrt (h ^ 2 + 9) ^ 2 = h ^ 2 + 9 := sq_sqrt (by positivity)
  have : (0 : ℝ) ≤ sqrt (h ^ 2 + 9) * (h * cosh h - sinh h) :=
    mul_nonneg (sqrt_nonneg _) hd
  have : (sqrt (h ^ 2 + 9) * (h * cosh h - sinh h)) ^ 2 ≤ (h ^ 2 * sinh h) ^ 2 := by
    calc (sqrt (h ^ 2 + 9) * (h * cosh h - sinh h)) ^ 2
        = (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2 := by rw [mul_pow, hroot]
      _ ≤ h ^ 4 * sinh h ^ 2 := sinh_sq_le hh
      _ = (h ^ 2 * sinh h) ^ 2 := by ring
  nlinarith

/-- **The sharp bound.**  This is `(lsh)` of the blog post. -/
theorem log_sinh_div_le {h : ℝ} (hh : 0 < h) :
    log (sinh h / h) ≤ sqrt (h ^ 2 + 9) - 3 := by
  set ψ : ℝ → ℝ := fun z => sqrt (z ^ 2 + 9) - 3 - (log (sinh z) - log z) with hψdef
  -- `ψ` has nonnegative derivative on `(0,∞)`
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt ψ (z / sqrt (z ^ 2 + 9) - (cosh z / sinh z - 1 / z)) z := by
    intro z hz
    have hs9 : (0 : ℝ) < z ^ 2 + 9 := by positivity
    have hsq : sqrt (z ^ 2 + 9) ≠ 0 := by positivity
    have hsinh : sinh z ≠ 0 := ne_of_gt (sinh_pos_iff.2 hz)
    have h1 : HasDerivAt (fun t : ℝ => sqrt (t ^ 2 + 9) - 3)
        (z / sqrt (z ^ 2 + 9)) z := by
      have h := (((hasDerivAt_pow 2 z).add_const 9).sqrt (ne_of_gt hs9)).sub_const 3
      refine h.congr_deriv ?_
      field_simp
      ring
    have h2 : HasDerivAt (fun t : ℝ => log (sinh t) - log t)
        (cosh z / sinh z - 1 / z) z := by
      have ha := (hasDerivAt_sinh z).log hsinh
      have hb := (hasDerivAt_id' z).log (ne_of_gt hz)
      have h := ha.sub hb
      refine h.congr_deriv ?_
      field_simp
    exact h1.sub h2
  have hmono : MonotoneOn ψ (Set.Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun z hz => (hderiv z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hderiv z (by rwa [interior_Ioi] at hz)).differentiableAt.differentiableWithinAt)
      (fun z hz => ?_)
    rw [interior_Ioi] at hz
    have hz0 : (0 : ℝ) < z := hz
    rw [(hderiv z hz0).deriv]
    have hsinh : (0 : ℝ) < sinh z := sinh_pos_iff.2 hz0
    have hsq : (0 : ℝ) < sqrt (z ^ 2 + 9) := by positivity
    rw [sub_nonneg, div_sub_div _ _ (ne_of_gt hsinh) (ne_of_gt hz0),
      div_le_div_iff₀ (by positivity) hsq]
    have := sqrt_mul_sub_le (le_of_lt hz0)
    nlinarith [this, hsq, hsinh, hz0]
  -- `ψ → 0` as `z → 0⁺`
  have hslope : Filter.Tendsto (fun z : ℝ => sinh z / z) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
    have h := hasDerivAt_sinh 0
    rw [hasDerivAt_iff_tendsto_slope] at h
    simpa [slope_fun_def, sinh_zero, cosh_zero, div_eq_inv_mul] using h
  have hlog : Filter.Tendsto ψ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hsub : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin 0 {(0 : ℝ)}ᶜ :=
      nhdsWithin_mono _ (fun z hz => ne_of_gt hz)
    have h1 : Filter.Tendsto (fun z : ℝ => log (sinh z / z))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := (continuousAt_log one_ne_zero).tendsto.comp (hslope.mono_left hsub)
      simpa [Function.comp_def] using this
    have h2 : Filter.Tendsto (fun z : ℝ => sqrt (z ^ 2 + 9) - 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h9 : sqrt (9 : ℝ) = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
      have hc : ContinuousAt (fun z : ℝ => sqrt (z ^ 2 + 9) - 3) 0 := by fun_prop
      simpa [ContinuousWithinAt, h9] using hc.continuousWithinAt (s := Set.Ioi (0 : ℝ))
    have heq : ∀ᶠ z : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ψ z = (sqrt (z ^ 2 + 9) - 3) - log (sinh z / z) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : (0 : ℝ) < z := hz
      rw [hψdef]
      rw [log_div (ne_of_gt (sinh_pos_iff.2 hz0)) (ne_of_gt hz0)]
    rw [Filter.tendsto_congr' heq]
    simpa using h2.sub h1
  -- combine
  have hev : ∀ᶠ z : ℝ in nhdsWithin 0 (Set.Ioi 0), ψ z ≤ ψ h := by
    have hmem : Set.Ioo (0 : ℝ) h ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsGT_iff_exists_Ioo_subset.2 (Exists.intro h (And.intro (Set.mem_Ioi.2 hh) subset_rfl))
    filter_upwards [hmem] with z hz
    exact hmono (Set.mem_Ioi.2 hz.1) (Set.mem_Ioi.2 hh) (le_of_lt hz.2)
  have h0 : (0 : ℝ) ≤ ψ h := le_of_tendsto hlog hev
  have hpos : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hh) hh
  rw [hψdef] at h0
  rw [log_div (ne_of_gt (sinh_pos_iff.2 hh)) (ne_of_gt hh)]
  linarith

/-- The form in which the estimate is used: `sinh h ≤ h exp (√(h²+9) - 3)`. -/
theorem sinh_le_mul_exp {h : ℝ} (hh : 0 ≤ h) :
    sinh h ≤ h * exp (sqrt (h ^ 2 + 9) - 3) := by
  rcases eq_or_lt_of_le hh with rfl | hpos
  · simp
  · have hlog := log_sinh_div_le hpos
    have hd : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hpos) hpos
    have := (log_le_iff_le_exp hd).1 hlog
    calc sinh h = (sinh h / h) * h := by field_simp
      _ ≤ exp (sqrt (h ^ 2 + 9) - 3) * h :=
          mul_le_mul_of_nonneg_right this (le_of_lt hpos)
      _ = h * exp (sqrt (h ^ 2 + 9) - 3) := by ring

end Sendov
