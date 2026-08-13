/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic

/-!
# Sendov's conjecture and the Phelps–Rodriguez conjecture

This is the statement of record for the Palomar submission.  It states two theorems and
introduces no definitions of its own; every notion used is Mathlib's.

## The statements

Let `p` be a complex polynomial of degree at least `2` all of whose zeroes lie in the closed
unit disk, and let `a` be a zero of `p`.

**Sendov's conjecture** (`SendovConjecture.sendov`) asserts that `p'` has a zero `ζ` with
`‖ζ - a‖ ≤ 1`: every zero of `p` has a critical point of `p` within distance one.

**The Phelps–Rodriguez conjecture** (`SendovConjecture.phelps_rodriguez`) strengthens this to a
*strict* inequality together with a classification of the exceptions: either `p'` has a zero `ζ`
with `‖ζ - a‖ < 1`, or `a` lies on the unit circle and `p` is a nonzero scalar multiple of
`zⁿ - aⁿ`, where `n` is the degree of `p`.  The second alternative is genuinely attained: for
`p = zⁿ - 1` and `a = 1`, the only critical point is `0`, at distance exactly `1` from `a`.

Phelps–Rodriguez implies Sendov, since in the exceptional case `0` is a critical point and
`‖0 - a‖ = ‖a‖ = 1`.

## How the hypotheses are phrased

* "degree at least `2`" is `2 ≤ p.natDegree`.  This excludes `p = 0`, for which
  `Polynomial.natDegree` is `0`.  Degrees `0` and `1` are genuine exclusions rather than
  conveniences: a nonzero constant has no zeroes, and a linear polynomial has a nonvanishing
  constant derivative, so the conclusion fails vacuously in one case and outright in the other.
* "all zeroes in the closed unit disk" is `∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1`, quantified over
  all of `ℂ` rather than over `Polynomial.roots`.  The two agree here, but the form used avoids
  relying on the reader's knowledge that `Polynomial.roots` is a multiset that is empty by
  convention when `p = 0`.
* `a` is an arbitrary complex zero of `p`.  It is not assumed to be real, nonzero, simple, or
  of any particular modulus, and `‖a‖ ≤ 1` is not assumed — it follows from `hzeroes`.
* `Polynomial.derivative` is the formal derivative, and `‖·‖` is the usual absolute value on
  `ℂ`.

No hypothesis restricts the multiplicity of `a`, the number of distinct zeroes, or the
positions of the other zeroes beyond the closed unit disk.

## Provenance and status

These are the conjectures of Sendov and of Phelps–Rodriguez, in full generality.  Neither
statement is new, nothing here is claimed to be new, and no literature or formalization search
was performed.

Sendov's conjecture was proved, and formalized in Lean, before this work, and the informal
proof formalized here is a digestion of that proof; this is the second formalization of it.
See `formalization.yaml` and the repository README for the sources, the relationship to that
earlier work, and an account of how this formalization was produced.

The proofs are in the `Sendov` library of this repository and are compared against these
statements by Comparator.  They use `propext`, `Classical.choice` and `Quot.sound` only.
-/

namespace SendovConjecture

open Polynomial

/-- **Sendov's conjecture.**  If every zero of the complex polynomial `p` lies in the closed
unit disk and `p` has degree at least `2`, then every zero `a` of `p` has a zero of `p'` within
distance `1`. -/
theorem sendov {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 := by
  sorry

/-- **The Phelps–Rodriguez conjecture.**  Under the hypotheses of Sendov's conjecture, the
distance may be taken to be strictly less than `1`, unless `a` lies on the unit circle and `p`
is a nonzero scalar multiple of `zⁿ - aⁿ` with `n = deg p`. -/
theorem phelps_rodriguez {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧
          p = C c * (X ^ p.natDegree - C (a ^ p.natDegree))) := by
  sorry

end SendovConjecture
