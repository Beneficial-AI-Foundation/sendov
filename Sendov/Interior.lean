/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Analytic.OriginExact
import Sendov.Analytic.Polar
import Sendov.Counterexample.Factor
import Sendov.Reduction.Main

/-!
# Sendov's conjecture for a real interior zero, `n ≥ 5`

This file assembles everything: if `p` has degree `n ≥ 5`, all zeroes in the closed unit disk,
and a zero at a real `a` with `0 < a < 1`, then `p'` has a zero within distance `1` of `a`.

The proof is by contradiction.  Suppose not; then every critical point `w` satisfies
`‖w - a‖ ≥ 1`, so `Sendov.exists_crit_multiset` writes `p'` over points `qⱼ` of the closed unit
disk, and `Sendov.exists_root_multiset` writes `p` over the other zeroes `zⱼ`.  Setting
`x + iy = (∑ⱼ qⱼ)/(n-1)`, the two channels are:

* **polar**: the polar identity and `p'(a)` two ways feed the branch point `(⋆)`, which
  AM–GM relaxes to the raw polar inequality `(1Q)`;
* **origin**: the centroid identity and the two origin identities feed `(origin-exact)`.

`Sendov.polar_origin_incompatible` says the two cannot hold together for `n ≥ 5`.

## Main statements

* `Sendov.sendov_interior`: the conjecture for a real interior zero, `n ≥ 5`.
-/

namespace Sendov

open Polynomial
open Complex (I)

/-- **Sendov's conjecture for a real interior zero, `n ≥ 5`.**  If every zero of `p` lies in the
closed unit disk and `p(a) = 0` for a real `a` with `0 < a < 1`, then some zero of `p'` lies
within distance `1` of `a`. -/
theorem sendov_interior {n : ℕ} (hn : 5 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hpa : p.eval (a : ℂ) = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - (a : ℂ)‖ < 1 := by
  have hn2 : 2 ≤ n := by omega
  by_contra hcon
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - (a : ℂ)‖ := by
    intro w hw
    by_contra hlt
    exact hcon ⟨w, hw, not_le.1 hlt⟩
  -- the two factorizations
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hpa
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn2 hdeg hcrit
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (a : ℂ) - v⁻¹)).map (fun w => X - C w)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- basic numerology
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hne : ((n : ℂ) - 1) ≠ 0 := by
    intro h
    have h1 : (n : ℂ) = 1 := by linear_combination h
    have h2 : n = 1 := by exact_mod_cast h1
    omega
  have hqne : q ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hqcard
    omega
  have haC0 : ((a : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt ha0
  have haC2 : ((a : ℝ) : ℂ) ^ 2 ≠ 1 := by
    intro h
    have : (a : ℂ) ^ 2 = ((a ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this] at h
    have h1 : a ^ 2 = 1 := by exact_mod_cast h
    nlinarith [h1, ha0, ha1]
  -- `x + iy` is the centroid of the `qⱼ`
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I) := by
    refine ⟨(q.sum / ((n : ℂ) - 1)).re, (q.sum / ((n : ℂ) - 1)).im, ?_⟩
    rw [Complex.re_add_im, mul_div_cancel₀ _ hne]
  obtain ⟨hxre, hx2⟩ := xy_bounds hn2 hqcard hq1 hxy
  -- the polar channel
  have hpolar_id := polar_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 haC0 haC2 hzcard hqcard hq0 hpa hpz hpq'
  have hdenom := prod_sub_mul_prod (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 hq0 hpz hpq'
  have hstar := one_le_integral_prod_norm hn2 (a := a)
    (by rw [abs_of_nonneg (le_of_lt ha0)]; linarith) hz1 hpolar_id hdenom
  have hpolar := one_le_integral_Ppolar hn2 (a := a) (x := x) hqcard hq1 hxre hstar
  -- the origin channel
  have hcent := centroid_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hn2 hc0 hzcard hqcard hpz hpq'
  have hfirst := first_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 haC0 hzcard hq0 hpa hpz hpq'
  have hsecond := second_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 hzcard hq0 hpz hpq'
  have horigin := origin_exact (n := n) (α := M n * (1 - a ^ 2) / 2) hn ha0 ha1 hqcard hqne
    hz1 hq1 hxy hcent hfirst hsecond rfl
  -- the two are incompatible
  exact polar_origin_incompatible hn ha0 ha1 (by nlinarith [hx2, sq_nonneg y]) rfl hpolar horigin

end Sendov
