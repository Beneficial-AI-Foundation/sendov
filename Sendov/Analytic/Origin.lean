/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Counterexample.Identities
import Sendov.Analytic.Maclaurin
import Sendov.Analytic.Defect
import Sendov.Common.Quadratic
import Sendov.Analytic.Polar

/-!
# The origin inequality: the pointwise estimate

The origin argument controls `F(t) = ∏ⱼ (1 - a t qⱼ)` through its derivative,

  `F'(t) = -(n-1) a (x+iy) F(t) - a² t ∑ⱼ qⱼ² ∏_{k≠j} (1 - a t q_k)`,

and the error term is bounded by `a² t (n-1) β(t)^{(n-2)/2}`.  That bound is what this file
establishes; the integration and the `J`-algebra follow in later files.

Three steps, in increasing order of depth:

* `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`, the same expansion that produced the quadratic mean in the
  polar channel — this is where `x` enters;
* Cauchy–Schwarz, `(∑ b)² ≤ N ∑ b²`;
* **Maclaurin's inequality**, `∑ⱼ ∏_{k≠j} bₖ ≤ N (mean b)^{N-1}` — the one ingredient absent
  from Mathlib, proved in `Sendov.Analytic.Maclaurin`.

The blog post applies Maclaurin to `(1/(n-1)) ∑ⱼ ∏_{k≠j} |1 - a t q_k|` and then Cauchy–Schwarz;
the order is immaterial and it is done the same way here.

A note on the bookkeeping.  The quantity `∑ⱼ ∏_{k≠j} f(qⱼ)` is written as a sum over erasures
of `q`, whereas `Multiset.esymm` — which Maclaurin is stated for — is a sum over sub-multisets
of the *image* `q.map f`.  Rather than relate erasure and `map` directly, which needs `f`
injective, the two are matched through the recurrence they share.

## Main statements

* `Sendov.sumEraseProdMap_eq_esymm`: the two forms of `∑ⱼ ∏_{k≠j}` agree;
* `Sendov.sum_norm_sq_one_sub_le`: `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`;
* `Sendov.sumEraseProdMap_norm_le`: the error bound `(n-1) β(t)^{(n-2)/2}`.
-/

namespace Sendov

/-! ### `∑ⱼ ∏_{k≠j}` over erasures, and `esymm` -/

open scoped Classical in
/-- `∑ⱼ ∏_{k≠j} f(sₖ)`, as a sum over erasures of `s`. -/
noncomputable def sumEraseProdMap {α : Type*} (s : Multiset α) (f : α → ℝ) : ℝ :=
  (s.map (fun j => ((s.erase j).map f).prod)).sum

open scoped Classical in
lemma sumEraseProdMap_cons {α : Type*} (v : α) (t : Multiset α) (f : α → ℝ) :
    sumEraseProdMap (v ::ₘ t) f = (t.map f).prod + f v * sumEraseProdMap t f := by
  simp only [sumEraseProdMap, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]

/-- The erasure form and `Multiset.esymm` agree, matched through their common recurrence. -/
theorem sumEraseProdMap_eq_esymm {α : Type*} : ∀ (s : Multiset α) (f : α → ℝ), s ≠ 0 →
    sumEraseProdMap s f = (s.map f).esymm ((s.map f).card - 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; exact absurd rfl h
  | cons v t ih =>
    intro f _
    rcases eq_or_ne t 0 with rfl | ht
    · simp [sumEraseProdMap, Multiset.esymm]
    · rw [sumEraseProdMap_cons, ih f ht, Multiset.map_cons, Multiset.card_cons]
      rw [show (t.map f).card + 1 - 1 = (t.map f).card from by omega]
      rw [esymm_card_cons (f v) (t.map f) (by simpa using ht)]

/-! ### The quadratic mean -/

/-- `‖1 + s v‖² = 1 + 2 s Re v + s² ‖v‖²` for real `s`. -/
lemma norm_sq_one_add_real_mul (s : ℝ) (v : ℂ) :
    ‖1 + (s : ℂ) * v‖ ^ 2 = 1 + 2 * s * v.re + s ^ 2 * ‖v‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

lemma sum_norm_sq_one_sub_split (s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖1 + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) + 2 * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [ih, norm_sq_one_add_real_mul]
    push_cast
    ring

/-- `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`, where `β(t) = 1 - 2 a x t + a² t²`. -/
theorem sum_norm_sq_one_sub_le {n : ℕ} {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (hn : 1 ≤ n)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ ^ 2)).sum
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
  have hNcast : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    push_cast [Nat.cast_sub hn]
    ring
  have hcast : ∀ v : ℂ, 1 - (a : ℂ) * (t : ℂ) * v = 1 + ((-(a * t) : ℝ) : ℂ) * v := by
    intro v
    push_cast
    ring
  simp only [hcast]
  rw [sum_norm_sq_one_sub_split, hx, hNcast]
  have hsum2 := sum_norm_sq_le_card q hq1
  rw [hNcast] at hsum2
  simp only [QQ]
  nlinarith [hsum2, sq_nonneg (a * t)]

/-! ### Cauchy–Schwarz and the error bound -/

lemma sq_sum_le_card_mul_sum_sq (s : Multiset ℝ) (hs : ∀ b ∈ s, 0 ≤ b) :
    (s.sum) ^ 2 ≤ (s.card : ℝ) * (s.map (fun b => b ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b t ih =>
    have hb := hs b (Multiset.mem_cons_self b t)
    have ht : ∀ u ∈ t, 0 ≤ u := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · have hIH := ih ht
      have hcard : (0 : ℝ) < (t.card : ℕ) := by
        have := Multiset.card_pos.2 ht0
        exact_mod_cast this
      have hsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
      have hQ : (0 : ℝ) ≤ (t.map (fun b => b ^ 2)).sum :=
        Multiset.sum_nonneg (by
          intro y hy
          obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
          exact sq_nonneg u)
      simp only [Multiset.sum_cons, Multiset.card_cons, Multiset.map_cons]
      push_cast
      nlinarith [hIH, sq_nonneg (t.sum - (t.card : ℝ) * b), hcard, hsum, hb, hQ]

/-- **The error bound.**  `∑ⱼ ∏_{k≠j} ‖1 - a t q_k‖ ≤ (n-1) β(t)^{(n-2)/2}`: Maclaurin's
inequality, then Cauchy–Schwarz, then the quadratic mean.  Nonnegativity of `β(t)` is not
assumed — it follows from the quadratic-mean bound, `β(t)` dominating an average of squares. -/
theorem sumEraseProdMap_norm_le {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖)
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set f : ℂ → ℝ := fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ with hf
  set bs : Multiset ℝ := q.map f with hbs
  have hbcard : bs.card = n - 1 := by rw [hbs, Multiset.card_map, hqcard]
  have hNcast : ((bs.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hbcard]
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  have hNpos : (0 : ℝ) < (bs.card : ℕ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbs0 : bs ≠ 0 := by
    rw [hbs]
    simpa using hq0
  have hbnn : ∀ b ∈ bs, 0 ≤ b := by
    intro b hb
    rw [hbs] at hb
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hb
    exact norm_nonneg _
  have hsumnn : 0 ≤ bs.sum := Multiset.sum_nonneg hbnn
  -- the quadratic mean
  have hsq : (bs.map (fun b => b ^ 2)).sum ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
    rw [hbs, Multiset.map_map]
    exact sum_norm_sq_one_sub_le hqcard hq1 (by omega) hx
  have hβ0 : 0 ≤ QQ (a * x) (a ^ 2) t := by
    have hnn : (0 : ℝ) ≤ (bs.map (fun b => b ^ 2)).sum :=
      Multiset.sum_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact sq_nonneg u)
    nlinarith [hsq, hnn, hNcast, hNpos]
  -- Cauchy–Schwarz
  have hcs : (bs.sum) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 * QQ (a * x) (a ^ 2) t := by
    have h := sq_sum_le_card_mul_sum_sq bs hbnn
    rw [hNcast] at h
    nlinarith [h, hsq, hNcast, hNpos]
  have hmean : bs.sum / (bs.card : ℕ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) := by
    rw [div_le_iff₀ hNpos, hNcast]
    have hsqrt : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ 2 = QQ (a * x) (a ^ 2) t :=
      Real.sq_sqrt hβ0
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by rw [← hNcast]; exact hNpos
    have hprodnn : (0 : ℝ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) * ((n : ℝ) - 1) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hn1)
    nlinarith [hcs, hsqrt, hsumnn, hprodnn, hn1]
  -- Maclaurin
  have hmac := Multiset.esymm_card_pred_le bs hbnn hbs0
  rw [sumEraseProdMap_eq_esymm q f hq0, ← hbs]
  refine hmac.trans ?_
  have hpow : (bs.sum / (bs.card : ℕ)) ^ (bs.card - 1)
      ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
    refine pow_le_pow_left₀ (by positivity) hmean _
  have hfin : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1)
      = QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (QQ (a * x) (a ^ 2) t ^ ((1 : ℝ) / 2))
      (bs.card - 1), ← Real.rpow_mul hβ0]
    congr 1
    have hcast2 : ((bs.card - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [hbcard]
      have h2 : n - 1 - 1 = n - 2 := by omega
      rw [h2]
      push_cast [Nat.cast_sub (by omega : (2 : ℕ) ≤ n)]
      ring
    rw [hcast2]
    ring
  rw [hNcast] at *
  calc ((n : ℝ) - 1) * (bs.sum / ((n : ℝ) - 1)) ^ (bs.card - 1)
      ≤ ((n : ℝ) - 1) * Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [← hNcast] at hpow ⊢
        exact hpow
    _ = ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by rw [hfin]

end Sendov
