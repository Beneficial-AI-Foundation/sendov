/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Pack
import Sendov.FiniteRange.Recurrence

/-!
# Computing the recurrence by a single exponentiation

`Sendov.rev_qrow` says that `qrow` computes the coefficients of `(g₀ + g₁t + g₂t²) ^ k`.
Evaluating that identity at *integer* points turns it into a statement about packed values,
and the packing is nothing but the same Horner evaluation read in `ℤ` instead of `ℝ`.  So the
forward direction needs no new theory at all: `Sendov.pevZ_rowZ_qrow` follows from
`rev_qrow` by casting.

Two bases are involved:

* `β` packs a coefficient polynomial in `α` into one integer (`Sendov.pevZ`);
* `τ` packs the resulting row, a polynomial in `t`, into one integer.

Together they are the two-dimensional Kronecker substitution, and the whole recurrence
becomes `G ^ k` for the single integer `G = pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ²`.
`Sendov.unpackZ_pevZ` then reads the row back off, given the overflow bounds — which is where
the numerical parameters `β` and `τ` have to be chosen, one per degree.

## Main statements

* `Sendov.pev_intCast`, `Sendov.rev_intCast`: evaluation over `ℝ` at an integer point agrees
  with the packed evaluation over `ℤ`;
* `Sendov.pevZ_rowZ_qrow`: the recurrence as one integer exponentiation.
-/

namespace Sendov

/-- The row with each coefficient polynomial packed at the base `β`. -/
def rowZ (r : List (List ℤ)) (β : ℤ) : List ℤ := r.map (fun p => pevZ p β)

@[simp] lemma rowZ_nil (β : ℤ) : rowZ [] β = [] := rfl

@[simp] lemma rowZ_cons (p : List ℤ) (r : List (List ℤ)) (β : ℤ) :
    rowZ (p :: r) β = pevZ p β :: rowZ r β := rfl

@[simp] lemma rowZ_length (r : List (List ℤ)) (β : ℤ) : (rowZ r β).length = r.length := by
  simp [rowZ]

/-- Evaluating a coefficient polynomial over `ℝ` at an integer point is the packed
evaluation over `ℤ`. -/
lemma pev_intCast (p : List ℤ) (b : ℤ) : pev p (b : ℝ) = (pevZ p b : ℝ) := by
  induction p with
  | nil => simp [pev]
  | cons a p ih =>
    simp only [pev, pevZ_cons, ih]
    push_cast
    ring

/-- Evaluating a row over `ℝ` at integer points is the packed evaluation over `ℤ`. -/
lemma rev_intCast (r : List (List ℤ)) (β τ : ℤ) :
    rev r (β : ℝ) (τ : ℝ) = (pevZ (rowZ r β) τ : ℝ) := by
  induction r with
  | nil => simp [rev]
  | cons p r ih =>
    simp only [rev_cons, rowZ_cons, pevZ_cons, ih, pev_intCast]
    push_cast
    ring

/-- **The recurrence as one exponentiation.**  The two-dimensionally packed row is the `k`-th
power of a single integer.  In the kernel this replaces `Θ(k³)` interpreted list steps by one
GMP-backed exponentiation; measured at `k = 46`, hours become about half a second. -/
theorem pevZ_rowZ_qrow (g₀ g₁ g₂ : List ℤ) (k : ℕ) (β τ : ℤ) :
    pevZ (rowZ (qrow g₀ g₁ g₂ k) β) τ
      = (pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k := by
  have h := rev_qrow g₀ g₁ g₂ k (β : ℝ) (τ : ℝ)
  rw [rev_intCast, pev_intCast, pev_intCast, pev_intCast] at h
  exact_mod_cast h

/-- Reading the packed row back, given the overflow bound on the packed coefficients.  The
bound is a hypothesis: it is discharged per degree from explicit numerical parameters. -/
theorem rowZ_qrow_eq (g₀ g₁ g₂ : List ℤ) (k : ℕ) (β τ : ℤ) (hτ : 0 < τ)
    (hbound : ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ) :
    unpackZ τ (qrow g₀ g₁ g₂ k).length
        ((pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k)
      = rowZ (qrow g₀ g₁ g₂ k) β := by
  rw [← pevZ_rowZ_qrow, ← rowZ_length (qrow g₀ g₁ g₂ k) β]
  exact unpackZ_pevZ τ hτ _ hbound

/-! ### The moment as a single integer polynomial

`Sendov.irow` has rational weights `1/(j+4)`.  Scaling by a common multiple `L` of the
denominators clears them, turning the moment into one `ℤ`-polynomial in `α`. -/

/-- `∑ⱼ (L/(i+j+4)) • rⱼ`: the moment numerator, scaled by `L` to clear denominators. -/
def wsum (L : ℤ) : ℕ → List (List ℤ) → List ℤ
  | _, [] => []
  | i, p :: r => padd (p.map (fun c => (L / ((i : ℤ) + 4)) * c)) (wsum L (i + 1) r)

@[simp] lemma wsum_nil (L : ℤ) (i : ℕ) : wsum L i [] = [] := rfl

@[simp] lemma wsum_cons (L : ℤ) (i : ℕ) (p : List ℤ) (r : List (List ℤ)) :
    wsum L i (p :: r)
      = padd (p.map (fun c => (L / ((i : ℤ) + 4)) * c)) (wsum L (i + 1) r) := rfl

/-- **The scaled moment is an integer polynomial.**  Given that `L` clears every denominator
`i+j+4` occurring, `wsum` computes `L` times `Sendov.irow`. -/
theorem pev_wsum (L : ℤ) : ∀ (r : List (List ℤ)) (i : ℕ) (α : ℝ),
    (∀ j, j < r.length → ((i : ℤ) + j + 4) ∣ L) →
    pev (wsum L i r) α = (L : ℝ) * irow r i α := by
  intro r
  induction r with
  | nil => intro i α _; simp [irow]
  | cons p r ih =>
    intro i α hdvd
    have h0 : ((i : ℤ) + 4) ∣ L := by
      have := hdvd 0 (by simp)
      simpa using this
    obtain ⟨m, hm⟩ := h0
    have hine : ((i : ℤ) + 4) ≠ 0 := by positivity
    have hw : L / ((i : ℤ) + 4) = m := by rw [hm, Int.mul_ediv_cancel_left _ hine]
    have hcast : ((m : ℤ) : ℝ) * ((i : ℝ) + 4) = (L : ℝ) := by
      rw [hm]; push_cast; ring
    have hi4 : ((i : ℝ) + 4) ≠ 0 := by positivity
    have hrest : ∀ j, j < r.length → (((i + 1 : ℕ) : ℤ) + j + 4) ∣ L := by
      intro j hj
      have := hdvd (j + 1) (by simpa using Nat.succ_lt_succ hj)
      push_cast at this ⊢
      convert this using 2
      ring
    rw [wsum_cons, pev_padd, pev_map_mul, hw, ih (i + 1) α hrest]
    simp only [irow]
    field_simp
    linear_combination (pev p α) * hcast

end Sendov
