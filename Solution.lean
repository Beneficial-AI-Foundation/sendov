/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Conjecture

/-!
# Solutions to the Challenge

The two declarations of `Challenge.lean`, proved.  Each is a thin bridge to the corresponding
theorem in `Sendov.Conjecture`; the two differences are bookkeeping only.

* The Challenge takes the degree hypothesis as `2 ≤ p.natDegree`, whereas the library carries
  the degree as a separate natural number `n` together with `p.natDegree = n`.  The bridge
  instantiates `n := p.natDegree` and discharges the second hypothesis by `rfl`.
* The Challenge quantifies the disk hypothesis over all of `ℂ`, whereas the library quantifies
  over `Polynomial.roots`.  Membership in `Polynomial.roots` yields `p.eval w = 0`, which is
  what the bridge uses; the converse direction is not needed.

Neither difference weakens the statement: the Challenge hypotheses are the weaker pair, so the
Challenge conclusions are the stronger claims.
-/

namespace SendovConjecture

open Polynomial

/-- **Sendov's conjecture**, proved in `Sendov.sendov`. -/
theorem sendov {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 :=
  Sendov.sendov (n := p.natDegree) hdeg rfl (fun w hw => hzeroes w (mem_roots'.1 hw).2) hpa

/-- **The Phelps–Rodriguez conjecture**, proved in `Sendov.phelps_rodriguez`. -/
theorem phelps_rodriguez {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧
          p = C c * (X ^ p.natDegree - C (a ^ p.natDegree))) :=
  Sendov.phelps_rodriguez (n := p.natDegree) hdeg rfl
    (fun w hw => hzeroes w (mem_roots'.1 hw).2) hpa

end SendovConjecture
