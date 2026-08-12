# Sendov's conjecture in Lean

A formalization of **Sendov's conjecture** and the **Phelps–Rodriguez conjecture**, following
the digestion of the proof at `blog/2026/sendov.tex`.

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

Both are in [`Sendov/Conjecture.lean`](Sendov/Conjecture.lean), and both depend on
`propext`, `Classical.choice` and `Quot.sound` only.

[`Challenge.lean`](Challenge.lean) is the statement of record: 84 lines, importing only
Mathlib, declaring no definitions of its own, and stating exactly these two theorems.
[`Solution.lean`](Solution.lean) proves them. A reader who wants to check *what* has been
proved should read `Challenge.lean` and need not read anything else.

## Trust

* no `sorry` and no project-defined `axiom`, with one deliberate exception: `Challenge.lean`
  *states* the two theorems without proving them, which is what makes it the statement of
  record for Comparator to check `Solution.lean` against. `scripts/audit.sh` requires exactly
  those two holes and no others, and forbids `sorry` everywhere else including `Solution.lean`;
* no `native_decide`, no `unsafe`, no floating point in any statement or proof;
* `maxHeartbeats` / `maxRecDepth` appear only as deliberate resource knobs, each with an
  explanatory comment.

`scripts/audit.sh` checks all of this and prints the axiom dependencies of the top-level
results; `scripts/mutation_test.sh` checks that the numerical certificates are actually load-
bearing.

## Layout

The argument splits on the position of the distinguished zero `a`, after a rotation
normalizes it to be real and nonnegative.

| case | route | files |
| --- | --- | --- |
| `a = 0` | `p'(a)` two ways forces `n ≤ 1` | `Interior.lean` |
| `0 < a < 1`, `n ≤ 5` | branch at `(⋆)`, scalar chord | `Analytic/LowDegree.lean` |
| `0 < a < 1`, `n ≥ 5` | polar and origin channels are incompatible | `Analytic/*`, `Reduction/*` |
| `\|a\| = 1` | Rubinstein, via `p''(1)/p'(1)` | `Boundary.lean` |
| rotation back | | `Conjecture.lean` |

The `n ≥ 5` route is the substance. A counterexample would satisfy two inequalities:

* the **polar** inequality `(1Q)`, from the polar identity and `p'(a)` two ways
  (`Counterexample/Identities.lean`, `Analytic/Polar.lean`);
* the **origin** inequality `(origin-exact)`, from the centroid identity, the two origin
  identities and the defect lemma (`Analytic/{Origin,Jsum,OriginExact}.lean`).

`Reduction/Main.lean` shows the two cannot hold together, by way of `α ≤ 17` and a numerical
claim `stat` that is verified for `5 ≤ n ≤ 100` by Bernstein certificates
(`FiniteRange/`) and for `n ≥ 101` analytically (`LargeDegree/`).

Two ingredients absent from Mathlib are proved here: **Maclaurin's inequality** in the top case
(`Analytic/Maclaurin.lean`, by multiset induction reducing to Bernoulli) and the **defect
lemma** (`Analytic/Defect.lean`).

See [`docs/design.md`](docs/design.md) for the design record, including a status table and the
list of traps encountered.

## Building

```
lake exe cache get
lake build
bash scripts/audit.sh
```

Memory, not time, is the binding constraint on a full build; `scripts/staged_build.sh` builds
the certificate files in batches.

## Provenance

**Nothing here is claimed to be new.** Sendov's conjecture had already been proved, and
already formalized in Lean — independently, and before this work — by Lech Mazur, at
[ProofAtlas](https://www.proofatlas.ai/formalizations/sendov-conjecture/). Priority for the
first machine-checked proof belongs to that work. This development shares no code with it and
was written instead from a later, much shorter informal argument; it additionally proves the
Phelps–Rodriguez equality classification, which that formalization does not state.

The informal proof formalized here is a digestion of the argument, which also yields a new
proof of Rubinstein's boundary theorem. `docs/design.md` records the design decisions, and
`formalization.yaml` records the full source list and relationships.

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
