# Lean plan for Rubinstein's boundary theorem and its equality case

## Goal

Formalize the following boundary form of Sendov's conjecture, assuming that the
factorization and normalization machinery developed for the blog-post proof is
already available.

> **Boundary theorem.** Let \(p\in\mathbb C[z]\) have degree \(n\geq2\), with
> all roots in the closed unit disk, and let \(a\) be a root with \(|a|=1\).
> Then \(p'\) has a root \(w\) satisfying \(|w-a|\leq1\). Moreover, there is
> a root with \(|w-a|<1\), unless
> \[
> p(z)=c(z^n-a^n)
> \]
> for some nonzero scalar \(c\).

This is Rubinstein's theorem, including the equality classification. The proof
below is not a transcription of Rubinstein's original argument. It is a short
boundary specialization of the zero--critical-point communication principle in
the blog post.

The exact polar identity itself should **not** be used at the boundary. When
\(a=1\), the reflected point \(1/a\) coincides with \(a\), while
\(1-a^2=0\), and the polar identity degenerates to a tautology. Instead, add
one elementary identity obtained from \(p''(a)/p'(a)\).

## 1. Normalize the distinguished root

Use the existing rotation normalization to reduce to
\[
a=1.
\]
Multiplication of the polynomial by a nonzero scalar does not affect its roots
or critical points, so it is also convenient to make \(p\) monic.

The final rotation should be undone only after proving the normalized equality
case \(p(z)=z^n-1\).

If the existing `ClosedObstruction` type includes the hypothesis \(a<1\), do
not force the boundary case into that type. Either work directly with the
polynomial factorization or introduce a very small boundary-obstruction
structure containing only:

- the non-distinguished roots \(z_j\);
- the critical points \(w_j\), or their reciprocal coordinates \(q_j\);
- \(|z_j|\leq1\);
- \(|1-w_j|\geq1\);
- the two factorizations of \(p\) and \(p'\).

## 2. Remove the repeated-root case

If \(1\) is a multiple root of \(p\), then
\[
p'(1)=0,
\]
so the strict conclusion holds immediately. Thus, under the hypothesis that no
critical point lies in the open disk \(D(1,1)\), one may assume
\[
p'(1)\ne0.
\]
In particular, \(1\) is simple, and all remaining roots \(z_j\) satisfy
\(z_j\ne1\).

Schematic Lean split:

```lean
by_cases hcrit : p.derivative.eval 1 = 0
· exact strict_witness_at_distinguished_root hcrit
· -- Continue under hp1 : p.derivative.eval 1 ≠ 0.
```

Prefer whatever root API is already used by the blog formalization. The code
above is only schematic.

## 3. Reciprocal coordinates for the critical points

List the critical points with multiplicity as
\[
w_1,\ldots,w_{n-1}.
\]
Under the contradiction hypothesis
\[
|1-w_j|\geq1,
\]
define
\[
q_j:=\frac1{1-w_j}.
\]
Then
\[
|q_j|\leq1.                                                  \tag{1}
\]

This is the same reciprocal coordinate as in the blog post with \(a=1\):
\(w_j=1-1/q_j\). No appeal to Gauss--Lucas is needed.

Suggested helper:

```lean
lemma norm_q_le_one
    (hsep : 1 ≤ ‖(1 : ℂ) - w‖) :
    ‖((1 : ℂ) - w)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  exact inv_le_one₀ (by positivity) hsep
```

Adjust the inverse-order lemma to the version available in the project. First
record that \((1:\mathbb C)-w\ne0\), which follows from `hsep`.

## 4. The boundary reciprocal identity

Write
\[
p(z)=(z-1)Q(z),
\qquad
Q(z)=\prod_{j=1}^{n-1}(z-z_j),
\]
after monic normalization. Then
\[
p'(1)=Q(1),\qquad p''(1)=2Q'(1),
\]
and hence
\[
\frac{p''(1)}{p'(1)}
=2\frac{Q'(1)}{Q(1)}
=2\sum_{j=1}^{n-1}\frac1{1-z_j}.                            \tag{2}
\]

On the other hand, from
\[
p'(z)=n\prod_{j=1}^{n-1}(z-w_j)
\]
one gets
\[
\frac{p''(1)}{p'(1)}
=\sum_{j=1}^{n-1}\frac1{1-w_j}
=\sum_{j=1}^{n-1}q_j.                                      \tag{3}
\]
Comparing (2) and (3) gives
\[
\boxed{
\sum_{j=1}^{n-1}q_j
=2\sum_{j=1}^{n-1}\frac1{1-z_j}.}
\tag{BR}
\]

This is the only new zero--critical-point identity needed for the boundary
case. It is also the \(k=\nu=1\) specialization of the reciprocal identities
of Meir and Sharma.

### Recommended Lean formulation

Keep the lemma independent of the subsequent inequalities:

```lean
lemma boundary_reciprocal_identity
    (hp1 : p.derivative.eval 1 ≠ 0)
    (hzfac : p = (X - 1) * ∏ j, (X - C (z j)))
    (hwfac : p.derivative = C n * ∏ j, (X - C (w j)))
    (hq : ∀ j, q j = ((1 : ℂ) - w j)⁻¹) :
    ∑ j, q j = 2 * ∑ j, ((1 : ℂ) - z j)⁻¹ := by
  ...
```

The actual factorization syntax should follow the repository. There are two
reasonable implementations:

1. evaluate the logarithmic derivatives at \(1\), using the project's existing
   product-differentiation lemma;
2. differentiate the two finite products explicitly, evaluate at \(1\), and
   cancel the common nonzero factor \(p'(1)\).

The first route is shorter if a logarithmic-derivative lemma already exists.
The second route avoids division until the final cancellation and may be more
robust in Lean.

Do not confuse (BR) with the centroid identity. The centroid identity compares
first ordinary moments of the roots and critical points. Identity (BR) compares
first **reciprocal** moments centered at the distinguished root.

## 5. The elementary disk inequality

For every \(z\in\overline{D(0,1)}\) with \(z\ne1\),
\[
\Re\frac1{1-z}-\frac12
=\frac{1-|z|^2}{2|1-z|^2}\geq0.                             \tag{4}
\]
Therefore
\[
\Re\frac1{1-z}\geq\frac12.                                \tag{5}
\]

Package this as a standalone complex-number lemma. It is probably the only
part of the proof for which a little low-level complex algebra is needed.

```lean
lemma half_le_re_inv_one_sub
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    (1 / ((1 : ℂ) - z)).re ≥ (1 : ℝ) / 2 := by
  ...
```

A robust proof strategy is:

1. set \(d=|1-z|^2>0\);
2. use
   \[
   \Re(1-z)^{-1}=\frac{1-\Re z}{|1-z|^2};
   \]
3. after multiplying by the positive denominator, reduce the desired
   inequality to
   \[
   2(1-\Re z)-|1-z|^2=1-|z|^2\geq0.
   \]

In Lean, use the repository's preferred lemmas for `Complex.normSq`, inverse
real parts, and `Complex.sq_norm`. Once the denominator is known positive,
`field_simp` followed by `ring`/`nlinarith` should finish. Avoid introducing
square roots: work with squared norms throughout.

The equality case in (4) is \(|z|=1\), but it is not needed for the final
classification; equality on the critical-point side already determines the
polynomial.

## 6. Sandwich the real part of the reciprocal sum

From \(|q_j|\leq1\),
\[
\Re q_j\leq |q_j|\leq1.
\]
Hence
\[
\Re\sum_{j=1}^{n-1}q_j\leq n-1.                            \tag{6}
\]

From (BR) and (5),
\[
\Re\sum_{j=1}^{n-1}q_j
=2\sum_{j=1}^{n-1}\Re\frac1{1-z_j}
\geq n-1.                                                   \tag{7}
\]
Therefore equality holds:
\[
\Re\sum_{j=1}^{n-1}q_j=n-1.                                \tag{8}
\]

Suggested lemma:

```lean
lemma re_sum_q_eq_card
    (hqnorm : ∀ j, ‖q j‖ ≤ 1)
    (hzunit : ∀ j, ‖z j‖ ≤ 1)
    (hzne : ∀ j, z j ≠ 1)
    (hrecip : ∑ j, q j = 2 * ∑ j, ((1 : ℂ) - z j)⁻¹) :
    (∑ j, q j).re = Fintype.card ι := by
  have hupper : (∑ j, q j).re ≤ Fintype.card ι := by
    rw [map_sum]
    -- Sum `(q j).re ≤ ‖q j‖ ≤ 1`.
    ...
  have hlower : (Fintype.card ι : ℝ) ≤ (∑ j, q j).re := by
    rw [hrecip]
    -- Apply `half_le_re_inv_one_sub` term by term.
    ...
  linarith
```

The return type on the right should of course be coerced to `ℝ`; the displayed
signature is schematic.

## 7. Extract equality term by term

Each number \(1-\Re q_j\) is nonnegative, and (8) says
\[
\sum_{j=1}^{n-1}(1-\Re q_j)=0.
\]
Consequently
\[
\Re q_j=1
\]
for every \(j\). Together with \(|q_j|\leq1\), this forces
\[
q_j=1.                                                       \tag{9}
\]

It is useful to separate the scalar complex equality lemma from the finite-sum
argument:

```lean
lemma eq_one_of_re_eq_one_of_norm_le_one
    {q : ℂ} (hre : q.re = 1) (hq : ‖q‖ ≤ 1) :
    q = 1 := by
  apply Complex.ext
  · simpa [hre]
  · -- From `‖q‖² = q.re² + q.im² ≤ 1`, infer `q.im = 0`.
    have himsq : q.im ^ 2 ≤ 0 := by
      ...
    have : q.im = 0 := by nlinarith [sq_nonneg q.im]
    simpa [this]
```

Then:

```lean
lemma all_q_eq_one
    (hqnorm : ∀ j, ‖q j‖ ≤ 1)
    (hsum : (∑ j, q j).re = Fintype.card ι) :
    ∀ j, q j = 1 := by
  have hnonneg : ∀ j, 0 ≤ 1 - (q j).re := by
    intro j
    exact sub_nonneg.mpr ((q j).re.le_trans (hqnorm j))
  have hzerosum : ∑ j, (1 - (q j).re) = 0 := by
    -- Rewrite using `hsum` and `map_sum`.
    ...
  have hterm : ∀ j, 1 - (q j).re = 0 := by
    -- Use the finite-sum theorem saying a sum of nonnegative terms is zero
    -- iff every term is zero.
    ...
  intro j
  apply eq_one_of_re_eq_one_of_norm_le_one
  · linarith [hterm j]
  · exact hqnorm j
```

There may already be an equality lemma for `Complex.re z ≤ ‖z‖`; if its
equality case is convenient, it can replace the explicit real/imaginary-part
calculation.

## 8. Recover all critical points and classify the polynomial

Since
\[
q_j=(1-w_j)^{-1}=1,
\]
one has
\[
w_j=0                                                        \tag{10}
\]
for every \(j\). Thus all \(n-1\) critical points, counted with multiplicity,
are zero. In the monic normalization,
\[
p'(z)=n z^{n-1}.                                             \tag{11}
\]
It follows that \(p(z)-z^n\) is constant. Since \(p(1)=0\),
\[
p(z)=z^n-1.                                                  \tag{12}
\]

Suggested split:

```lean
lemma all_critical_points_zero
    (hqdef : ∀ j, q j = ((1 : ℂ) - w j)⁻¹)
    (hqone : ∀ j, q j = 1) :
    ∀ j, w j = 0 := by
  intro j
  have := congrArg (fun u : ℂ => u * ((1 : ℂ) - w j)) (hqone j)
  -- Or use `inv_eq_one.mp` after proving the denominator nonzero.
  ...
```

Then reuse the already-formalized factorization of \(p'\):

```lean
lemma monic_eq_X_pow_sub_one_of_all_critical_zero
    (hpmonic : p.Monic)
    (hpdeg : p.natDegree = n)
    (hp1 : p.eval 1 = 0)
    (hwzero : ∀ j, w j = 0)
    (hderivfac : ... ) :
    p = X ^ n - 1 := by
  have hderiv : p.derivative = C n * X ^ (n - 1) := by
    -- Rewrite the critical-point factorization using `hwzero`.
    ...
  have hzero_deriv : (p - X ^ n).derivative = 0 := by
    -- `derivative (X^n) = C n * X^(n-1)`.
    ...
  have hconst : (p - X ^ n).degree ≤ 0 :=
    derivative_eq_zero_iff.mp hzero_deriv
  -- A polynomial with zero derivative is constant in characteristic zero.
  -- Evaluate at 1 to identify the constant as -1.
  ...
```

Use the exact characteristic-zero lemma available in mathlib rather than the
schematic `degree ≤ 0` line if possible. A coefficient-extensionality proof is
also acceptable and may be easier if the repository already controls every
coefficient through the derivative identity.

For a nonmonic polynomial, the same argument gives
\[
p(z)=c(z^n-1),
\]
where \(c\) is its leading coefficient. It is cleaner to divide by the leading
coefficient at the start and restore it at the end.

Undoing the rotation that sent the original boundary root \(a\) to \(1\)
gives
\[
p(z)=c(z^n-a^n).                                             \tag{13}
\]

Be careful with the scalar introduced by polynomial composition under
rotation. The theorem only asserts existence of some nonzero \(c\), so there
is no need to simplify that scalar aggressively.

## 9. Logical form of the final theorem

The cleanest primary statement is the strict-or-extremal alternative:

```lean
theorem boundary_sendov_strict_or_extremal
    (hpdeg : 2 ≤ p.natDegree)
    (hroots : ∀ z, IsRoot p z → ‖z‖ ≤ 1)
    (ha : IsRoot p a)
    (haunit : ‖a‖ = 1) :
    (∃ w, IsRoot p.derivative w ∧ ‖w - a‖ < 1) ∨
      (∃ c : ℂ, c ≠ 0 ∧
        p = C c * (X ^ p.natDegree - C (a ^ p.natDegree))) := by
  ...
```

Derive the ordinary closed-disk Sendov statement as a corollary:

- in the strict branch, replace `< 1` by `≤ 1`;
- in the extremal branch, use the critical point \(w=0\), for which
  \(|0-a|=1\).

Also derive the equality classification in the form most useful elsewhere:

```lean
theorem boundary_no_strict_critical_iff_extremal ... :
    (¬ ∃ w, IsRoot p.derivative w ∧ ‖w - a‖ < 1) ↔
      ∃ c : ℂ, c ≠ 0 ∧
        p = C c * (X ^ p.natDegree - C (a ^ p.natDegree)) := by
  ...
```

For the reverse implication, calculate the derivative of
\(c(z^n-a^n)\): its only critical point is zero, at distance exactly one from
the unit-modulus zero \(a\).

## 10. Minimal dependency graph

```text
existing rotation and monic normalization
                 |
                 v
     repeated-root case split
                 |
                 v
factorizations of p and p' at the root 1
                 |
                 v
boundary_reciprocal_identity (BR)
                 |
                 +------------------------------+
                 |                              |
                 v                              v
half_le_re_inv_one_sub                 norm_q_le_one
                 |                              |
                 +---------------+--------------+
                                 |
                                 v
                      re_sum_q_eq_card
                                 |
                                 v
                         all_q_eq_one
                                 |
                                 v
                  all critical points are zero
                                 |
                                 v
                         p(z) = z^n - 1
                                 |
                                 v
             strict boundary Sendov or extremal form
```

No polar integral estimate, origin identity, defect lemma, interval
arithmetic, numerical certificate, or Gauss--Lucas theorem is required.

## 11. Audit checklist

1. The proof treats the repeated-root case before dividing by \(p'(1)\).
2. Every non-distinguished root \(z_j\) is known to differ from \(1\) before
   forming \((1-z_j)^{-1}\).
3. The critical points and the non-distinguished roots are listed with
   multiplicity, each in a family of cardinality \(n-1\).
4. The separation hypothesis has the correct strictness: the negation of
   existence of a critical point at distance `< 1` is distance `≥ 1` for every
   critical point.
5. Identity (BR) has the factor \(2\). It comes from
   \(p''(1)=2Q'(1)\).
6. The disk inequality is used in the direction
   \(\Re(1-z)^{-1}\geq1/2\).
7. Equality is extracted term by term from a finite sum of nonnegative real
   quantities; it is not inferred merely from an equality of sums without
   checking the individual upper bounds.
8. The polynomial classification uses characteristic zero when concluding
   that a polynomial with zero derivative is constant.
9. Rotation back from \(1\) to \(a\) produces \(z^n-a^n\), not
   \(z^n-a\).
10. `#print axioms` on the final theorem contains neither `sorryAx` nor a
    project-defined axiom.

## 12. Historical citation

The original result is:

- Z. Rubinstein, *On a problem of Ilyeff*, Pacific J. Math. **26** (1968),
  159--161, especially Theorem 1.

The reciprocal identity used here appears as a special case of the more
general identities in:

- A. Meir and A. Sharma, *On Ilyeff's conjecture*, Pacific J. Math. **31**
  (1969), 459--467, equations (3.1)--(3.3).

