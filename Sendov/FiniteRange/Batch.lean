/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Common.Rpow

/-!
# Batching adjacent degrees

Every term of `Sendov.R` is monotone in `n`, and the directions cooperate: the elementary
part decreases, the prefactor increases, and the moment decreases.  So for a whole range of
degrees `n₀ ≤ n ≤ n₁` one bound suffices,

  `R n α ≤ base n₀ α + pref n₁ α * I n₀ α`,

needing one moment and one certificate for the batch rather than one per degree.

The key identity is

  `Q (n+1) α t = Q n α t - (2α / (n(n-1))) * t * (1-t)`,

so `Q` decreases with `n` on `[0,1]`; combined with `Q ≤ 1` and the exponent `(n-4)/2`
increasing, the moment decreases too.

This pays most where it costs most.  Batch sizes track the slack in `R n α`, which is
smallest near its maximum at `n = 53` and grows away from it, so the expensive high degrees
batch into the largest groups: measured, `n ∈ [62,97]` costs 12.5× less batched, against 2.8×
in the tight middle.  Note also that the certificate's degree is set by `n₀`, the *smallest*
member, so a batch is cheaper than any single degree it covers except the first.

## Main statements

* `Sendov.Q_succ_sub`: the identity above;
* `Sendov.Q_anti`: `Q` decreases with `n` on `[0,1]`;
* `Sendov.A_mono`: `A` increases with `n`.
-/

namespace Sendov

variable {α t : ℝ}

lemma M_mono {m n : ℕ} (h : m ≤ n) : M m ≤ M n := by
  simp only [M]
  have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  linarith

/-- `A` increases with `n`: raising the degree moves `a²` towards `1`. -/
lemma A_mono {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α) : A m α ≤ A n α := by
  have hMm : 0 < M m := M_pos hm
  have hMn : 0 < M n := lt_of_lt_of_le hMm (M_mono h)
  simp only [A]
  have : 2 * α / M n ≤ 2 * α / M m :=
    div_le_div_of_nonneg_left (by linarith) hMm (M_mono h)
  linarith

/-- **The degree step.**  Raising `n` by one lowers `Q` by a multiple of `t(1-t)`. -/
lemma Q_succ_sub (n : ℕ) (hn : 2 ≤ n) (hα : 0 ≤ α) (t : ℝ) :
    Q (n + 1) α t = Q n α t - (2 * α / ((n : ℝ) * ((n : ℝ) - 1))) * t * (1 - t) := by
  have h1 : ((n : ℝ) - 1) ≠ 0 := by
    have := M_pos hn; simp only [M] at this; linarith
  have h2 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hM1 : M (n + 1) = (n : ℝ) := by simp only [M]; push_cast; ring
  have hMn : M n = (n : ℝ) - 1 := by simp only [M]
  simp only [Q, c, A, hM1, hMn]
  field_simp
  ring

/-- `Q` decreases with `n` on `[0,1]`. -/
lemma Q_anti {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Q n α t ≤ Q m α t := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have hmn : m ≤ n := by omega
      have hn2 : 2 ≤ n := le_trans hm hmn
      have hstep : Q (n + 1) α t ≤ Q n α t := by
        rw [Q_succ_sub n hn2 hα t]
        have hnn : (0 : ℝ) ≤ 2 * α / ((n : ℝ) * ((n : ℝ) - 1)) := by
          have h1 : (0 : ℝ) < (n : ℝ) - 1 := by
            have := M_pos hn2; simp only [M] at this; linarith
          have h2 : (0 : ℝ) < (n : ℝ) := by linarith
          positivity
        nlinarith [mul_nonneg (mul_nonneg hnn ht0) (by linarith : (0 : ℝ) ≤ 1 - t)]
      exact le_trans hstep (ih hmn)
    · have : m = n + 1 := by omega
      subst this
      exact le_rfl

end Sendov
