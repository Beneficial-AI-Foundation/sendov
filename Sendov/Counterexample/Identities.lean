/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Counterexample.Factor

/-!
# The centroid and second origin identities

Two of the four identities of the blog post's Lemma 1 come from comparing the two
factorizations of `Sendov.Counterexample.Factor` coefficient by coefficient, or by evaluating
them at a point.  Neither needs any integration.

* the **centroid identity**, from the coefficient of `X^{n-2}` in `p'`, equivalently from
  `p.coeff (n-1)` and `p'.coeff (n-2)`;
* the **second origin identity**, from `p'(0)`.

Everything is stated **division-free**.  The blog post writes the second origin identity as

  `(-1)^{n-1} (∏ zⱼ) (1 + a ∑ⱼ 1/zⱼ) = (n / ∏ qⱼ) F(1)`,

with a convention that singularities are removed when some `zⱼ` vanishes.  Multiplying out,
`(∏ zⱼ)(∑ⱼ 1/zⱼ)` is `∑ⱼ ∏_{k≠j} z_k`, which is defined whether or not any `zⱼ` is zero, and
`∏ qⱼ` clears the other denominator.  So the convention becomes unnecessary rather than being
formalized: no junk value of `0⁻¹` is ever evaluated.

## Main statements

* `Sendov.sumEraseProd`: `∑ⱼ ∏_{k≠j} sₖ`, the division-free form of `(∏ s)(∑ 1/sⱼ)`;
* `Sendov.centroid_identity`.
-/

namespace Sendov

open Polynomial Multiset

open scoped Classical in
/-- `∑ⱼ ∏_{k≠j} sₖ`.  This is `(∏ s) · (∑ⱼ 1/sⱼ)` with the denominators cleared, and unlike
that expression it is well defined when some `sⱼ` vanishes. -/
noncomputable def sumEraseProd (s : Multiset ℂ) : ℂ :=
  (s.map (fun j => (s.erase j).prod)).sum

variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ}

/-! ### Two rewritings of the factorizations -/

/-- The factorization of `p`, with `a` put back into the multiset. -/
lemma prod_cons_eq (a : ℂ) (z : Multiset ℂ) :
    (X - C a) * (z.map (fun w => X - C w)).prod
      = ((a ::ₘ z).map (fun w => X - C w)).prod := by
  rw [Multiset.map_cons, Multiset.prod_cons]

/-! ### The centroid identity -/

/-- **The centroid identity.**  `(n-1)(a + ∑ zⱼ) = n ∑ⱼ (a - 1/qⱼ)`: the centroid of the
zeroes equals the centroid of the critical points. -/
theorem centroid_identity (hn : 2 ≤ n) {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    ((n : ℂ) - 1) * (a + z.sum) = (n : ℂ) * (q.map (fun v => a - v⁻¹)).sum := by
  have hcard1 : (a ::ₘ z).card = n := by
    simp only [Multiset.card_cons, hzcard]
    omega
  have hcard2 : (q.map (fun v => a - v⁻¹)).card = n - 1 := by
    rw [Multiset.card_map, hqcard]
  -- the coefficient of `X^{n-1}` in `p`
  have hp1 : p.coeff (n - 1) = c * (-(a + z.sum)) := by
    rw [hpz, prod_cons_eq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (a ::ₘ z) (by rw [hcard1]; omega)
    rw [hcard1] at this
    rw [this, Multiset.sum_cons]
  -- the coefficient of `X^{n-2}` in `p'`
  have hp2 : (derivative p).coeff (n - 2)
      = (n : ℂ) * c * (-((q.map (fun v => a - v⁻¹)).sum)) := by
    rw [hpq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (q.map (fun v => a - v⁻¹))
      (by rw [hcard2]; omega)
    rw [hcard2] at this
    have hn2 : n - 1 - 1 = n - 2 := by omega
    rwa [hn2] at this
  -- and `p'.coeff (n-2) = (n-1) p.coeff (n-1)`
  have hlink : (derivative p).coeff (n - 2) = p.coeff (n - 1) * ((n : ℂ) - 1) := by
    have hsucc : n - 2 + 1 = n - 1 := by omega
    have h1 : ((n - 2 : ℕ) : ℂ) + 1 = (n : ℂ) - 1 := by
      have h2 : (2 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h2]
      ring
    rw [coeff_derivative, hsucc, h1]
  rw [hp1, hp2] at hlink
  refine mul_left_cancel₀ hc0 ?_
  linear_combination hlink

end Sendov
