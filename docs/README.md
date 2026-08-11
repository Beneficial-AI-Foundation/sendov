# Documents

Reference material for the Sendov finite-range formalization.  Provenance and status differ
between these files, and a reviewer should know which is which.

| file | what it is | status |
|---|---|---|
| [`design.md`](design.md) | This project's own design record: what is proved, what is open, why the architecture is what it is, and the measured costs behind each decision. | Maintained. Measurements reproducible; claims about the Lean development are checkable against the source. |
| [`plan-finite-range.md`](plan-finite-range.md) | The original hand-off plan for formalizing the finite range, written before any code existed. | **External, superseded in parts.** See below. |
| [`proof-large-degree.md`](proof-large-degree.md) | An informal but formalization-ready proof that `stat` is impossible for `n > 100`, plus (in its §9) speculative strategies for lowering the finite cutoff. | **External, not yet formalized.** Its §1–8 arithmetic has been checked; its §9 is explicitly labelled unproved by its author. |
| [`sendov-blog-post.tex`](sendov-blog-post.tex) | Source of the blog post the claim comes from. `stat` is the equation being formalized. | Draft, unpublished. |

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
