# The finite-range check

Reference material for the finite-range component of the proof: the Bernstein-certificate
verification of the numerical claim `stat` for degrees 5 to 100, and the analytic argument for
degrees 101 and above.  This is one component; for the proof as a whole, and for where this
component is used, see the [repository README](../README.md).

The two documents below are external hand-off material, and both have been superseded in
parts.  A reviewer should know which claims still stand.

| file | what it is | status |
|---|---|---|
| [`plan-finite-range.md`](plan-finite-range.md) | The original hand-off plan for formalizing the finite range, written before any code existed. | **External, superseded in parts.** See below. |
| [`proof-large-degree.md`](proof-large-degree.md) | An informal but formalization-ready proof that `stat` is impossible for `n > 100`, plus (in its §9) speculative strategies for lowering the finite cutoff. | **External. Formalized in outline, not in detail** — see below. Its §9 is explicitly labelled unproved by its author. |

The project's own design record, including the measurements behind the decisions recorded
here, is [`design.md`](design.md).

## Where the plan has been superseded

`plan-finite-range.md` is still the best statement of the *goal* and of the trust policy, but
several of its technical recommendations were overturned by measurement.  Recorded here so a
reader does not follow them by mistake:

- **§2.4, degree five.** The chord bound, the `H(B)` formula in half-integer powers of `B`,
  and the substitution `α = 3r²/(1-r²)` are all unnecessary.  A tunable tangent parameter
  `w = 1/3` folds degree five into the general odd-degree path.
- **§3, the infeasible/bound dichotomy.** No box ever needs an infeasibility certificate.
  Only `α ≤ (n-1)/2` is used, which follows from `A ≥ 0`.
- **§4, adaptive subdivision.** One Bernstein certificate covers the whole interval at every
  degree tested.  The generator never bisects.
- **§2.2, formula (M).** Correct, and proved as `Sendov.integral_moment`, but with `Θ(k²)`
  terms it cannot be expanded by `simp` beyond about `k = 20`.  The plan anticipates this
  ("if the closed multinomial formula is slow, prove a recurrence") — the recurrence is
  `Recurrence.lean`, and it too needed a change of *representation* to be usable.

What the plan gets right and should be kept: the trust policy (§7), the insistence that the
integral replacement be proved rather than assumed, and the acceptance criteria (§10).

## Where `proof-large-degree.md` has been superseded

Its §1–3 are formalized as written (`LargeDegree/Beta.lean`, `LargeDegree/Tail.lean`).  Its
§4–§7 are formalized in outline only, because using the sharp Beta constant
`6/((r+1)(r+2)(r+3)(r+4))` in place of the write-up's `6/r⁴` changes what needs proving:

- **§4.1 and its degree-8 certificate (17)–(18) are not needed.**  With the sharp constant the
  `n(n-2)` cancels and the first tail term is a rational function of `n`.
- **(16) is not true as stated.**  The first tail term does not decrease with `n` on its own —
  at `α = 17` it rises by 0.37% up to `n ≈ 108`.  It is the `c⁴` in the denominator that makes
  the product decrease.  `Monotone.lean` takes a flat 1% allowance instead and certifies it.
- **§4.2 is kept**, but with `√B ≤ 12/13` (a rational bound) so nothing irrational enters the
  step ratio, and with `B^((n-4)/2)` rewritten as the natural power `(√B)^(n-4)`.
- **§7's split of `[0,17]` at `α = 16` is unnecessary.**  One degree-58 Bernstein certificate
  covers the whole range, with all 59 coefficients positive.  The tight `T̃₂(17) = 0.55719`
  against `279/500` (0.15% of room) does not arise; the margin at `α = 17` is 7.7%.

See `design.md` §7 for the details.

## Note on §9 of `proof-large-degree.md`

That section proposes lowering the finite cutoff via monotonicity `R_{n+2} ≤ R_n`, or via a
four-chord majorant.  Both were investigated:

- The monotonicity is **true** (verified numerically over `53 ≤ n ≤ 95`) but has a minimum
  relative margin of 1.48%, against the ~15% a direct proof of `R_n < 1` is allowed.  It
  demands far more sharpness than the goal.
- The four-chord table in §9.3 **reproduces** to three decimals.  Eight chords give a
  comfortable margin (0.932 at `n = 53` against 0.989 for four).  But the majorant does not
  fix the cost problem, because `ring`'s cost is dominated by intermediate expansion rather
  than term count.

See `design.md` §6 for the measurements.
