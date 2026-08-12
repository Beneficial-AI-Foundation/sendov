/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Counterexample.Identities

/-!
# The polar inequality, up to the branch point

The polar identity says

  `(∏ q) ∏ⱼ (1 - a zⱼ) = n ∫₀¹ ∏ⱼ (t(1-a²)qⱼ + a) dt`,   `(∏ q) ∏ⱼ (a - zⱼ) = n`.

The Möbius estimate `|a - zⱼ| ≤ |1 - a zⱼ|`, valid because `zⱼ` lies in the closed unit disk
and `a` is real with `|a| ≤ 1`, therefore gives

  `n = |(∏ q) ∏ (a - zⱼ)| ≤ |(∏ q) ∏ (1 - a zⱼ)| = n |∫₀¹ ∏ⱼ (t(1-a²)qⱼ + a) dt|`,

and after the integral triangle inequality

  `1 ≤ ∫₀¹ ∏ⱼ |a + t(1-a²)qⱼ| dt`.                                    (⋆)

**`(⋆)` is the branch point of the whole argument.**  The high-degree route relaxes it by
AM–GM into the raw polar inequality `(1Q)` of `Sendov.Reduction.Setup`; the low-degree route
for `2 ≤ n ≤ 5` (see `docs/plan-low-degrees.md`) instead bounds each factor by `a + (1-a²)t`
and integrates a quartic.  Neither may be folded into the other, so `(⋆)` is stated on its own.

Note that no division occurs anywhere: splitting the blog post's quotient
`∏(1-azⱼ)/(a-zⱼ)` into its numerator and denominator identities is what makes that possible,
and `p'(a) ≠ 0` is never needed.

## Main statements

* `Sendov.norm_sub_le_norm_one_sub_mul`: the Möbius estimate;
* `Sendov.one_le_integral_prod_norm`: the branch point `(⋆)`.
-/

namespace Sendov

open Polynomial MeasureTheory

/-! ### The Möbius estimate -/

/-- `|a - z| ≤ |1 - a z|` for real `a` with `|a| ≤ 1` and `z` in the closed unit disk.  The
difference of squares is `(1-a²)(1-|z|²)`, which is why `a` must be real: for complex `a` the
cross terms contribute `(conj a - a)(z - conj z)`, which need not vanish. -/
lemma norm_sub_le_norm_one_sub_mul {a : ℝ} (ha : |a| ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(a : ℂ) - z‖ ≤ ‖1 - (a : ℂ) * z‖ := by
  have hkey : Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z)
      = (1 - a ^ 2) * (1 - Complex.normSq z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have ha2 : a ^ 2 ≤ 1 := by
    have := abs_le.1 ha
    nlinarith [this.1, this.2]
  have hz2 : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hdiff : 0 ≤ Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z) := by
    rw [hkey]
    have h1 : (0 : ℝ) ≤ 1 - a ^ 2 := by linarith
    have h2 : (0 : ℝ) ≤ 1 - Complex.normSq z := by linarith
    positivity
  have hsq : ‖(a : ℂ) - z‖ ^ 2 ≤ ‖1 - (a : ℂ) * z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  nlinarith [norm_nonneg ((a : ℂ) - z), norm_nonneg (1 - (a : ℂ) * z), hsq]

/-! ### Products of norms over a multiset -/

lemma norm_multiset_prod (s : Multiset ℂ) : ‖s.prod‖ = (s.map (fun w => ‖w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih => simp [ih]

lemma prod_map_le_of_le {s : Multiset ℂ} {f g : ℂ → ℂ} (h : ∀ w ∈ s, ‖f w‖ ≤ ‖g w‖) :
    (s.map (fun w => ‖f w‖)).prod ≤ (s.map (fun w => ‖g w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih =>
    have hw := h w (Multiset.mem_cons_self w t)
    have ht : ∀ u ∈ t, ‖f u‖ ≤ ‖g u‖ := fun u hu => h u (Multiset.mem_cons_of_mem hu)
    have hnn : (0 : ℝ) ≤ (t.map (fun u => ‖f u‖)).prod :=
      Multiset.prod_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact norm_nonneg _)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_le_mul hw (ih ht) hnn (norm_nonneg _)

/-! ### The branch point -/

/-- Norms distribute over a mapped multiset product. -/
lemma norm_prod_map (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun w => ‖f w‖)).prod := by
  rw [norm_multiset_prod, Multiset.map_map]
  rfl

lemma prod_map_norm_nonneg (s : Multiset ℂ) (f : ℂ → ℂ) :
    0 ≤ (s.map (fun w => ‖f w‖)).prod := by
  refine Multiset.prod_nonneg ?_
  intro y hy
  obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
  exact norm_nonneg _

/-- **The branch point `(⋆)`.**  `1 ≤ ∫₀¹ ∏ⱼ |a + t(1-a²)qⱼ| dt`.

The high-degree argument relaxes this by AM–GM to the raw polar inequality; the low-degree
argument bounds each factor by `a + (1-a²)t`.  It is stated separately so that neither route
has to reproduce the other's work. -/
theorem one_le_integral_prod_norm {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : |a| ≤ 1)
    {z q : Multiset ℂ} (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hpolar : q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod)
    (hdenom : q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) :
    1 ≤ ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  -- the Möbius estimate, multiplied over the multiset
  have hmob : (z.map (fun w => ‖(a : ℂ) - w‖)).prod
      ≤ (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod :=
    prod_map_le_of_le (fun w hw => norm_sub_le_norm_one_sub_mul ha (hz w hw))
  -- take norms in the two identities
  have h1 : (n : ℝ) = ‖q.prod‖ * (z.map (fun w => ‖(a : ℂ) - w‖)).prod := by
    have := congrArg (fun w : ℂ => ‖w‖) hdenom
    simpa [norm_mul, norm_prod_map] using this.symm
  have h2 : ‖q.prod‖ * (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod
      = (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have := congrArg (fun w : ℂ => ‖w‖) hpolar
    simpa [norm_mul, norm_prod_map] using this
  -- so the integral has norm at least one
  have h3 : (1 : ℝ) ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have hstep : (n : ℝ) ≤ (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
        (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
      rw [← h2, h1]
      exact mul_le_mul_of_nonneg_left hmob (norm_nonneg _)
    nlinarith [hstep, hnpos]
  -- and the triangle inequality moves the norm inside
  refine h3.trans ?_
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans_eq ?_
  refine intervalIntegral.integral_congr ?_
  intro t _
  simp only []
  exact norm_prod_map q _

end Sendov
