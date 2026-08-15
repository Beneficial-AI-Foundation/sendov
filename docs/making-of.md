# Making of

*How this formalization actually happened: a curated transcript of the conversation between
Terence Tao and Claude (Opus 5, running in Claude Code) that produced the Lean development in
this repository. Four days, 10–13 August 2026, in one long-running conversation that had to be
compacted several times, plus an earlier session that created the repository.*

**How to read this**

- Tao's messages appear in `>` blockquotes, verbatim, trimmed with `[…]` where long. Replies
  of the form "yes", "ok, continue", "resume" are folded into the narration — there were many.
- Claude's side is compressed into *italic* summaries of what actually changed.
- The stage headings follow the git history, which is the authoritative record; `git log
  --reverse` reads as a more granular version of this document.
- Dead ends and mistakes are kept in. They are the instructive part, and leaving them out
  would misrepresent how the work went.

A companion document, [`getting-started.md`](getting-started.md), describes how to set up to do
something like this.

---

## 0. Before the transcript

The repository was created from a fresh Lean project — `lake new`, following the
[leanprover-community project instructions](https://leanprover-community.github.io/install/project.html)
— with VS Code, the Lean 4 extension, and Claude Code already installed. Then the conversation
was launched, and everything below happened inside it.

The first four commits (10 August) set the target and proved the easiest cases:

- `Initial commit: state the finite-range numerical claim`
- `Milestone 1: prove the finite-range claim in degree six`
- `Milestone 2: prove the finite-range claim in degree seven`
- `Milestone 3: degree five, and a simplification of the remaining plan`

The goal at this point was narrow: **not** Sendov's conjecture, but the single numerical
inequality that a blog-post proof left to computation on a finite range of degrees. The
polynomial argument was deliberately kept outside the project — that scope, and the trust
policy below, come from an externally supplied hand-off plan written before any code existed:
[`plan-finite-range.md`](plan-finite-range.md). The blog post it refers to is
[*A digestion of the proof of Sendov's conjecture*](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/).

Two decisions made here shaped everything after. The first was a **trust policy**, fixed before
any real code: no `sorry`, no project-defined `axiom`, no `native_decide`, no `unsafe`, no
floating point in any statement or proof — with [`scripts/audit.sh`](../scripts/audit.sh)
written to enforce it and run every time. The second was that the Python certificate generators
would live **outside the trusted base**: they emit Lean source that Lean re-verifies from
scratch, so a bug in a generator causes a build failure rather than a false theorem. Where the
plan's technical recommendations were later overturned by measurement is recorded in
[`finite-range.md`](finite-range.md).

---

## 1. General machinery, and the first real degree

> ok, let's build the general degree machinery

*Generalized the per-degree proofs into a moment formula and a reduction that works at any
degree, then attempted degree 20.*

> ok, try n=20

*Degree 20 became the first certificate-backed degree. Also corrected a feasibility claim that
had been stated too strongly, which pulled the provable range back to `n ≤ 97`, and committed
the generator so the certificates were reproducible rather than magic constants.*

Then a request that turned out to matter:

> Can you summarize what steps (1)-(2) are again?

*This kind of question was load-bearing throughout. Restating the plan repeatedly caught drift
between what had been agreed and what was being built.*

---

## 2. The representation problem

The moment computation would not scale. The obvious fix — replace the closed formula by a
recurrence — was tried and did not work either.

> ok lets measure 46

*Measured it. The recurrence was correct and provable, but far too slow: `List (List ℤ)`
arithmetic at `k = 46` ran for hours. Commit: `Moments by a verified recurrence`, immediately
followed by the realization that the recurrence was unusable as represented.*

The fix was **Kronecker packing** — encode the whole coefficient array in the digits of a
single natural number, so the recurrence becomes one big-integer exponentiation:

| representation | k=24 | k=32 | k=46 |
|---|---|---|---|
| `List (List ℤ)` | 120 s | >20 min | hours |
| 2-D packed, single `Nat` | — | — | ~0.5 s |

*Commit: `Kronecker packing: the fix is representation, not algorithm`. This is the single
largest speedup in the project, and it came from changing the data structure, not the
algorithm. The measurements are in [`design.md`](design.md) §4; the Lean is
[`Pack.lean`](../Sendov/FiniteRange/Pack.lean) and
[`PackBridge.lean`](../Sendov/FiniteRange/PackBridge.lean).*

Degrees 53 and 97 then went through:

> Let's do n=53

> ok let's do n=97

---

## 3. Batching, from a suggestion

> if there is enough slack it still might be possible to batch together adjacent values of n by
> a cheap interval arithmetic type method: for say n = 66, 67, 68 upper bound each term of the
> desired expression by the worst case choice of n in this range (which could be 66 in some
> terms and 68 in others).

*This worked, and paid better than expected — one certificate covering twenty degrees at once.
Overall the dominant cost fell about 5.5×, and on the hardest range `n ∈ [62,97]` about 12.5×.*

| range | individually | batched | saving |
|---|---|---|---|
| `n ∈ [6,40]` | 14.2 min | 3.5 min | 4× |
| `n ∈ [42,60]` | 28.3 min | 10.2 min | 2.8× |
| `n ∈ [62,97]` | 69.8 min | 5.6 min | **12.5×** |

*Machinery in [`Batch.lean`](../Sendov/FiniteRange/Batch.lean); measurements in
[`design.md`](design.md) §3.*

---

## 4. Widening the target

> GPT has supplied some possible approaches to handle the 50 < n < 100 range, as well as an
> analytic argument that can handle n > 100; the original blog post handles n > 200. So one
> might be able to broaden the goal to handle all n >= 5, not just 5 <= n <= 100 (which is
> towards my long term goal to completely formalize the proof of Sendov). In any event one can
> compare the options provided here with the ones you are empirically testing.

*The analytic argument for large degrees went in — the Beta integral replacing a cruder Gamma
tail bound, the tail estimate, the degree monotonicity — and met the certificates at the seam
`100/101`. Commit: `The claim, for every degree`. The finite-range goal was now closed on both
sides, with no range left open. The supplied analytic argument is
[`proof-large-degree.md`](proof-large-degree.md); the Lean is
[`LargeDegree/`](../Sendov/LargeDegree/), and [`finite-range.md`](finite-range.md) records the
several points at which the write-up had to be departed from.*

Then a check on whether the certificates were doing any work at all:

*Wrote [`scripts/mutation_test.sh`](../scripts/mutation_test.sh), which perturbs a certificate
and confirms the build fails.
Its first run found that part of what it was testing did not bite — recorded in the commit
message rather than quietly fixed.*

---

## 5. The reduction chain

> Fantastic! Now I'd like to be a bit more ambitious. I've revised the reference blog post
> […] We've now shown that {stat} is infeasible for any alpha \leq 17 and n \geq 5. But {stat}
> can ultimately be deduced from {1Q} and {origin-exact}, and these inequalities also imply
> alpha \leq 17, so this shows that {1Q} and {origin-exact} are not simultaneously satisfiable
> for n \geq 5. I'd like this to be the next formalization target. As per the blog post, this
> splits up into several separate subgoals […] Can you check all of these implications and
> propose a plan to formalize them? You are encouraged to re-use lemmas that can be placed in
> the Common directory.

*Checked each implication first, then built them in order. The crux was a sharp bound
`log(sinh h / h) ≤ √(h²+9) - 3`, needed to three orders at `h = 0`. The textbook route is an
infinite series, which is painful in Lean; instead a family of functions closed under
differentiation reduced the whole thing to one `ring` identity, eight monotonicity steps, and
a polynomial with all coefficients positive — [`Common/Sinh.lean`](../Sendov/Common/Sinh.lean).
Commits: `The sinh lemma, without the series` through `The chain closes: {1Q} and
{origin-exact} are incompatible`; the chain itself is [`Reduction/`](../Sendov/Reduction/).*

---

## 6. From a counterexample to the inequalities

> Great! I'm now interested in formalizing Conjecture \ref{interior} in the blog post. This
> requires combining polar_origin_incompatible with a derivation of Lemma \ref{identities} from
> the existence of a counterexample to Conjecture \ref{interior}, and then a derivation of the
> polar and origin inequalities from those identities. Can you plan a path towards doing this?

*Planned, then built bottom-up. Two ingredients were missing from Mathlib and had to be proved
from scratch: **Maclaurin's inequality** (the standard route needs Newton's inequalities plus
real-rootedness and Rolle; an elementary multiset induction reducing to Bernoulli turned out to
be much shorter — [`Maclaurin.lean`](../Sendov/Analytic/Maclaurin.lean)) and the **defect
lemma** (the write-up's proof goes through `sinh` and a limiting argument; a direct induction
avoided both — [`Defect.lean`](../Sendov/Analytic/Defect.lean)).*

Mid-stream, an instruction that changed the architecture of everything downstream:

> One should use multisets throughout including for Maclaurin (one can use multiset induction
> for this)

*This paid off twice: multiset AM–GM came free from the same Bernoulli step, and a large amount
of index bookkeeping simply never arose.*

> The later components are "[…]sendov-low-degrees-lean-plan.md" and
> "[…]sendov-boundary-rubinstein-lean-plan.md". You can read them to see if it affects the
> current plan, and then go for the defect lemma

*Those two are now [`plan-low-degrees.md`](plan-low-degrees.md) and
[`plan-boundary-rubinstein.md`](plan-boundary-rubinstein.md); they were followed closely, and
became §7 below.*

*Two mistakes belong here. Twice, drafting a file, Claude wrote `sorry` placeholders intending
to fill them in — a direct violation of the project's own trust policy. Both were removed
before any commit, and both were reported rather than quietly deleted. The policy is only worth
anything if breaking it gets said out loud.*

Then the identities, the polar branch point, and the origin channel, over several sessions:

> ok let's do the identities

> OK, let's get to 1Q

> ok let's do origin-exact!

*The origin channel was the largest single piece: the pointwise error bound via Maclaurin,
Cauchy–Schwarz and the quadratic mean; the derivative of `F(t) = ∏(1 - a t qⱼ)`; the triangle
inequality by FTC; the defect estimate for `J ∑ 1/zⱼ`; and finally `(origin-exact)` itself,
landing exactly on the hypothesis the reduction chain wanted:
[`Origin.lean`](../Sendov/Analytic/Origin.lean),
[`Jsum.lean`](../Sendov/Analytic/Jsum.lean),
[`OriginExact.lean`](../Sendov/Analytic/OriginExact.lean).*

A recurring theme in this stretch: everything was kept **division-free**. The blog post's
convention of "removing singularities" when some `zⱼ` vanishes was made *unnecessary* rather
than formalized, by clearing denominators in the statements themselves.

---

## 7. All degrees, and the remaining cases

> Lets extend the interior conjecture to n >= 2!

*The high-degree argument genuinely fails below `n = 5` — the discriminant `(3n-1)² - 4(n-1)³`
turns positive. But the low degrees do not need it: bounding each factor of the branch point by
a scalar already contradicts itself for `n ≤ 5` —
[`LowDegree.lean`](../Sendov/Analytic/LowDegree.lean), following
[`plan-low-degrees.md`](plan-low-degrees.md). Degree 5 is now proved twice, by independent
routes.*

> Let's do the a=1 Rubinstein theorem and the a=0 case next

*`a = 0` turned out to be three lines of consequence from a lemma that was already there. The
boundary case `|a| = 1` needed a genuinely different argument, since the polar identity
degenerates there, and it is where the Phelps–Rodriguez equality classification comes from —
[`Boundary.lean`](../Sendov/Boundary.lean), following
[`plan-boundary-rubinstein.md`](plan-boundary-rubinstein.md).*

> Let's formalize the full Sendov and Phelps-Rodriguez conjecture!

*Only a rotation was left — [`Conjecture.lean`](../Sendov/Conjecture.lean). Both conjectures,
in full generality, on `propext`, `Classical.choice` and `Quot.sound` alone.*

---

## 8. Registration, and a correction

> I would like to prepare this repository for registration at the Palomar registry
> https://palomar-registry.org/ . What would need to be done to do this?

*Read the registry's own policy repository rather than guessing, and found the repository had
**no `LICENSE` file** — while all 76 Lean files claimed one. Added the
[`Challenge.lean`](../Challenge.lean)/[`Solution.lean`](../Solution.lean) pair,
[`comparator.json`](../comparator.json) and [`formalization.yaml`](../formalization.yaml), and
validated the metadata by running the registry's own validator locally.*

Registration succeeded, with one reviewer comment:

> The Palomar registry succeeded with the following comment: The narrow novelty claims about the
> Rubinstein boundary proof and the formalization are unsupported by a documented literature
> search. […] I can disclaim any novelty claim on the Rubinstein result, and stress more heavily
> that this is the second formalizaton of the Sendov conjecture result (though the first of the
> Phelps-Rodriguez version).

*The comment was fair, and checking it against the published blog post turned up something
worse: the post is a digestion **of** the earlier proof, not an independent argument — it says
so, and cites specific inequalities as extracted from it. So the submitted metadata's claim of
independence from the earlier Lean formalization was simply wrong, and was corrected to
`builds-on`. Every novelty claim in the repository is now qualified as unknown, with an explicit
statement that no literature search was performed — see
[Provenance and novelty](../README.md#provenance-and-novelty).*

*A postscript, and a vindication of the reviewer's point. The boundary argument of §7 — the one
the documentation had called "a new proof of Rubinstein's theorem" — turned out not to be new.
Its two ingredients are equation (5.1) and Remark 5.1 of a 2025 preprint of Tang and Zhang,
[arXiv:2508.10341](https://arxiv.org/abs/2508.10341), which combines them to give the `a = 1`
case of Sendov's conjecture; the reciprocal identity and the half-plane bound are both there.
It was reached here independently, from the blog post, but a literature search would have found
it, which is exactly what the reviewer said. The documentation now says so.*

---

## What the process actually looked like

Some observations that are not visible in the final source.

**Memory, not time, was the binding constraint.** Building 31 certificate files in parallel
produced `0xC0000409` crashes and "failed to read … olean" errors on *toolchain* files — which
look exactly like disk corruption and are actually out-of-memory. The fix was
[`scripts/staged_build.sh`](../scripts/staged_build.sh). At one point the VS Code Lean server
holding 7.4 GB had to be restarted.

**Numerical claims were checked before being proved.** Maclaurin's inequality was verified
numerically over 200,000 cases before any Lean was written; the cheap AM–GM alternative was
measured and found to lose a factor of `e`, which would have broken a later step. Several hours
were saved by finding that out first.

**The design record was maintained continuously.** [`design.md`](design.md) accumulated not
just what
was proved but the measurements behind each decision and a running list of Lean traps — `set`
introducing a definition that `linarith` zeta-reduces, `field_simp` distributing across an
integral atom, `rw [h]` where `h : p = …` also rewriting the `p` inside `p.leadingCoeff`. That
list stopped several repeat mistakes.

**Verification beat assertion, repeatedly.** Where a claim could be checked mechanically it was:
link targets in the README resolved against the files, the audit script mutation-tested to
confirm it bites, the registry metadata run through the registry's own code, the Challenge and
Solution types compared under `pp.all` rather than by eye.

---

*Part of [teorth/sendov](https://github.com/teorth/sendov).*
