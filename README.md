# Sendov's conjecture in Lean

A formalization of **Sendov's conjecture** and the **Phelps–Rodriguez conjecture**, in full
generality.

```lean
/-- Sendov's conjecture. -/
theorem Sendov.sendov {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1

/-- The Phelps–Rodriguez conjecture. -/
theorem Sendov.phelps_rodriguez {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧ p = C c * (X ^ n - C (a ^ n)))
```

If every zero of a complex polynomial of degree `n ≥ 2` lies in the closed unit disk, then
every zero `a` has a critical point within distance `1` — and within distance *strictly* less
than `1`, unless `a` is on the unit circle and `p` is a scalar multiple of `zⁿ - aⁿ`.

The informal proof being formalized is
[*A digestion of the proof of Sendov's conjecture*](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/).

Both are in [`Sendov/Conjecture.lean`](Sendov/Conjecture.lean#L83), and both depend on
`propext`, `Classical.choice` and `Quot.sound` only.

[`Challenge.lean`](Challenge.lean) is the statement of record: 84 lines, importing only
Mathlib, declaring no definitions of its own. A reader who wants to check *what* has been
proved should read that file and need not read anything else.

## Roadmap

The proof is by contradiction throughout. Suppose `p` has degree `n ≥ 2`, all zeroes in the
closed unit disk, `p(a) = 0`, and *no* critical point within distance `1` of `a`.

### 0. Normalize, and split into two multisets

A rotation `p(ωz)` moves `a` to the real point `‖a‖`, so `a` may be assumed real and in
`[0,1]` — [`Sendov.rotate`](Sendov/Conjecture.lean#L43). The counterexample is then
repackaged as two multisets of `n-1` points of the closed unit disk:

| | |
|---|---|
| the other zeroes `zⱼ` | [`exists_root_multiset`](Sendov/Counterexample/Factor.lean#L46) |
| the critical points, as `qⱼ = 1/(a - wⱼ)` | [`exists_crit_multiset`](Sendov/Counterexample/Factor.lean#L74) |

The hypothesis "no critical point within distance 1" is exactly `‖qⱼ‖ ≤ 1`.

### 1. Four identities linking zeroes to critical points

All in [`Sendov/Counterexample/Identities.lean`](Sendov/Counterexample/Identities.lean), all
division-free, so that no `p'(a) ≠ 0` side condition is ever needed:

| identity | meaning | |
|---|---|---|
| [`centroid_identity`](Sendov/Counterexample/Identities.lean#L60) | centroid of zeroes = centroid of critical points | |
| [`prod_sub_mul_prod`](Sendov/Counterexample/Identities.lean#L322) | `p'(a)` two ways: `(∏qⱼ)(∏(a-zⱼ)) = n` | |
| [`polar_identity`](Sendov/Counterexample/Identities.lean#L355) | `∏(1-azⱼ)/(a-zⱼ)` as an integral | |
| [`first_origin_identity`](Sendov/Counterexample/Identities.lean#L241) | `∫₀¹F` in terms of `∏zⱼ` | `F(t) = ∏(1 - a t qⱼ)` |
| [`second_origin_identity`](Sendov/Counterexample/Identities.lean#L165) | `F(1)` in terms of `∏zⱼ` and `∑1/zⱼ` | |

### 2. The branch point `(⋆)`

The polar identity together with `p'(a)` two ways gives

> [`one_le_integral_prod_norm`](Sendov/Analytic/Polar.lean#L115) : `1 ≤ ∫₀¹ ∏ⱼ ‖a + t(1-a²)qⱼ‖ dt`

This is where the argument forks. The Möbius estimate `|1-az|/|a-z| ≥ 1` is the one step that
needs `a` real.

### 3a. Low degrees, `2 ≤ n ≤ 5`

Bounding each factor of `(⋆)` by the *scalar* `X(t) = a + (1-a²)t` already contradicts itself:
`1 ≤ Jₘ(a) = ∫₀¹X(t)ᵐ dt` with `m = n-1`, while `Jₘ(a) < 1` for `0 < a < 1` and `m ≤ 4`. The
computation is done once, at `m = 4`, where `1 - J₄(a) = ((1-a)³(1+a)/5)(a⁴-3a³+3a+4)`.

> [`low_degree_contradiction`](Sendov/Analytic/LowDegree.lean#L210), from
> [`one_le_lowJ`](Sendov/Analytic/LowDegree.lean#L93) and
> [`lowJ_lt_one`](Sendov/Analytic/LowDegree.lean#L185)

No origin channel, no `Real.rpow`, no certificates.

### 3b. High degrees, `n ≥ 5`: two channels that cannot both hold

Write `x + iy = (∑ⱼqⱼ)/(n-1)` and `α = (n-1)(1-a²)/2`.

**The polar channel.** AM–GM relaxes `(⋆)` to a scalar inequality in `x` alone:

> [`one_le_integral_Ppolar`](Sendov/Analytic/Polar.lean#L274) — the raw polar inequality `(1Q)`

**The origin channel.** Differentiating `F(t) = ∏ⱼ(1 - a t qⱼ)` and integrating against the
fundamental theorem of calculus:

| step | |
|---|---|
| `∑ⱼ∏_{k≠j}‖1-atq_k‖ ≤ (n-1)β(t)^{(n-2)/2}` | [`sumEraseProdMap_norm_le`](Sendov/Analytic/Origin.lean#L158) |
| `‖F'(t) + (n-1)a(x+iy)F(t)‖ ≤ …` | [`norm_deriv_add_le`](Sendov/Analytic/Origin.lean#L329) |
| integrate, using `F(0) = 1` | [`one_le_tri`](Sendov/Analytic/Origin.lean#L388) |
| estimate `J∑1/zⱼ`, paying the defect `1-\|J\|²` | [`Jsum_estimate`](Sendov/Analytic/Jsum.lean#L122) |
| `‖W‖ ≥ 2an/(n-1)`, collapsing `\|J\|` to `1` | [`grow`](Sendov/Analytic/OriginExact.lean#L92) |
| | [`origin_exact`](Sendov/Analytic/OriginExact.lean#L179) |

`grow` reduces to `(n-1)²a² - (3n-1)a + (n-1) > 0`, whose discriminant `(3n-1)² - 4(n-1)³` is
negative exactly from `n ≥ 5`. **This is the only place `n ≥ 5` is used.**

**The contradiction.** The two inequalities force `α ≤ 17` and then contradict each other:

> [`polar_origin_incompatible`](Sendov/Reduction/Main.lean#L60)

by way of the chain `(1Q) ⟹ (lt)` ([`polar_exp`](Sendov/Reduction/Polar.lean#L74)),
`(lt) ⟹ (beta-bound)` ([`beta_le`](Sendov/Reduction/BetaBound.lean#L108)),
[`alpha_le_seventeen`](Sendov/Reduction/Alpha17.lean#L106), and a numerical claim `stat`:

> [`stat_lt_one`](Sendov/Main.lean#L40), from
> [`finite_range_le_100`](Sendov/FiniteRange/Cover.lean#L58) (degrees 5–100, by Bernstein
> certificates) and [`large_degree`](Sendov/LargeDegree/Endgame.lean#L251) (degrees ≥ 101,
> analytically)

See [`docs/finite-range.md`](docs/finite-range.md) for that component on its own.

### 3c. The boundary, `‖a‖ = 1`

The polar identity degenerates at the boundary — the reflected point `1/a` coincides with `a`
and `1-a² = 0` — so it is replaced by one identity from `p''(1)/p'(1)`:

> `∑ⱼqⱼ = 2∑ⱼ1/(1-zⱼ)` — [`boundary_reciprocal`](Sendov/Boundary.lean#L151)

Both sides are then pinned: `Re qⱼ ≤ ‖qⱼ‖ ≤ 1` caps the left at `n-1`, while
`Re 1/(1-z) - 1/2 = (1-‖z‖²)/(2‖1-z‖²) ≥ 0` floors the right at `n-1`. Equality term by term
forces `qⱼ = 1`, so every critical point is `0` and `p = c(zⁿ-1)`.

> [`all_q_eq_one`](Sendov/Boundary.lean#L168) → [`rubinstein_one`](Sendov/Boundary.lean#L210)

This is a new proof of Rubinstein's theorem, and it is where the Phelps–Rodriguez equality
case comes from.

### 3d. The centre, `a = 0`

`p'(a)` two ways is already enough: `(∏qⱼ)(∏zⱼ) = n` with both factors of norm at most one
forces `n ≤ 1`.

> [`sendov_center`](Sendov/Interior.lean#L125)

### 4. Assembling

> [`sendov_interior`](Sendov/Interior.lean#L53) (real `0 < a < 1`) →
> [`sendov_interior_real`](Sendov/Interior.lean#L162) (with `a = 0`) →
> [`phelps_rodriguez`](Sendov/Conjecture.lean#L83) (rotation, and the boundary) →
> [`sendov`](Sendov/Conjecture.lean#L158)

## Two ingredients absent from Mathlib

* **Maclaurin's inequality**, top case — [`Multiset.esymm_card_pred_le`](Sendov/Analytic/Maclaurin.lean#L166),
  by multiset induction reducing to Bernoulli. The same induction gives multiset AM–GM,
  [`Multiset.prod_le_mean_pow`](Sendov/Analytic/Maclaurin.lean#L107).
* **The defect lemma** — [`defect`](Sendov/Analytic/Defect.lean#L93):
  `∏|wⱼ| · ∑ⱼ|1/wⱼ - conj wⱼ| ≤ 1 - ∏|wⱼ|²` on the closed unit disk.

A third piece worth naming is [`log_sinh_div_le`](Sendov/Common/Sinh.lean#L245),
`log(sinh h / h) ≤ √(h²+9) - 3`, which is sharp to three orders at `h = 0` and is the crux of
the `(beta-bound)` step.

## Trust

* no `sorry` and no project-defined `axiom`, with one deliberate exception: `Challenge.lean`
  *states* the two theorems without proving them, which is what makes it the statement of
  record for Comparator to check `Solution.lean` against. `scripts/audit.sh` requires exactly
  those two holes and no others, and forbids `sorry` everywhere else including `Solution.lean`;
* no `native_decide`, no `unsafe`, no floating point in any statement or proof;
* `maxHeartbeats` / `maxRecDepth` appear only as deliberate resource knobs, each with an
  explanatory comment.

`scripts/audit.sh` checks all of this and prints the axiom dependencies of the top-level
results; `scripts/mutation_test.sh` checks that the numerical certificates are actually
load-bearing.

## Building

```
lake exe cache get
lake build
bash scripts/audit.sh
```

Memory, not time, is the binding constraint on a full build; `scripts/staged_build.sh` builds
the certificate files in batches.

## Documents

| | |
|---|---|
| [`docs/design.md`](docs/design.md) | design record: status table, the measurements behind each decision, and the traps encountered |
| [`docs/finite-range.md`](docs/finite-range.md) | the finite-range check on its own |
| [`docs/proof-large-degree.md`](docs/proof-large-degree.md) | informal proof for degrees ≥ 101 |
| [`docs/plan-*.md`](docs/) | the staged hand-off plans, with notes on where they were superseded |
| [the blog post](https://terrytao.wordpress.com/2026/08/12/a-digestion-of-the-proof-of-sendovs-conjecture/) | the informal proof being formalized |

## Provenance

**Nothing here is claimed to be new.** Sendov's conjecture had already been proved, and
already formalized in Lean — independently, and before this work — by Lech Mazur, at
[ProofAtlas](https://www.proofatlas.ai/formalizations/sendov-conjecture/). Priority for the
first machine-checked proof belongs to that work. This development shares no code with it and
was written instead from a later, much shorter informal argument; it additionally proves the
Phelps–Rodriguez equality classification, which that formalization does not state.

The informal proof formalized here is a digestion of the argument, which also yields the new
proof of Rubinstein's boundary theorem in §3c. `formalization.yaml` records the full source
list and relationships.

## How this was produced

Essentially all of the Lean source in this repository was written by **Claude Opus 5**
(Anthropic), working interactively in Claude Code under the direction and review of the
author: choosing the Lean formulations, finding and repairing proofs, and designing the
certificate machinery. The author set the targets, supplied the informal proof and the staged
plans in `docs/`, made the mathematical decisions, and reviewed the output as it was produced.
No external or independent review has been performed.

The Bernstein certificates in `Sendov/FiniteRange/` are emitted by the Python scripts in
`scripts/`. Those scripts are outside the trusted base: they write Lean source that Lean
re-verifies from scratch, so a bug in them causes a build failure, not an unsound theorem.

## Licence

Apache-2.0; see [`LICENSE`](LICENSE).
