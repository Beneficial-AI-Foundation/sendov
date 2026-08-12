# Lean plan for the low-degree cases of Sendov's conjecture

## Scope

This note sketches a Lean proof of Sendov's conjecture in degrees
\(n=2,3,4\), assuming that the normalization and polar-identity machinery of
the blog-post proof has already been formalized.

The proposed proof does **not** formalize the classical arguments of Brannan
or Rubinstein. It branches from the blog proof immediately after the exact
polar identity and uses only elementary real inequalities and the integrals of
polynomials of degree at most four.

In fact, exactly the same argument proves the slightly stronger range
\(2\leq n\leq5\). It is worth stating and formalizing it in that form, since
this also removes degree five from the finite-certificate machinery.

The notation below is mathematical rather than tied to the exact names in the
existing Lean repository. The coding agent should reuse the repository's
existing definitions of a normalized/closed obstruction and its exact polar
identity rather than duplicating them.

## 1. Input supplied by the existing blog formalization

Suppose a normalized obstruction of degree \(n=m+1\) exists. Thus:

- \(m\geq1\);
- \(0<a<1\);
- \(q_1,\ldots,q_m\in\overline{D(0,1)}\), so \(|q_j|\leq1\);
- the exact polar identity holds:
  \[
  \prod_{j=1}^m\frac{1-a z_j}{a-z_j}
  =
  \int_0^1\prod_{j=1}^m
       \bigl(a+t(1-a^2)q_j\bigr)\,dt.
  \tag{P}
  \]

The disk-Mobius estimate already used in the blog proof gives
\[
 \left|\frac{1-a z_j}{a-z_j}\right|\geq1.
\]
Taking absolute values in (P), using the integral triangle inequality, and
then using \(|q_j|\leq1\), gives
\[
\begin{aligned}
1
&\leq
\left|\int_0^1\prod_{j=1}^m
       \bigl(a+t(1-a^2)q_j\bigr)\,dt\right| \\
&\leq
\int_0^1\prod_{j=1}^m
       \left|a+t(1-a^2)q_j\right|\,dt \\
&\leq
\int_0^1\bigl(a+(1-a^2)t\bigr)^m\,dt.
\end{aligned}
\tag{1}
\]
Here the last inequality follows pointwise from
\[
\left|a+t(1-a^2)q_j\right|
\leq a+t(1-a^2)|q_j|
\leq a+t(1-a^2),
\]
because \(a,t,1-a^2\geq0\).

Define
\[
 X_a(t):=a+(1-a^2)t,
 \qquad
 J_m(a):=\int_0^1X_a(t)^m\,dt.
\]
The only consequence of all the polynomial/obstruction machinery needed in
the low-degree proof is therefore
\[
1\leq J_m(a).
\tag{2}
\]

### Suggested wrapper lemma

Use the actual obstruction type and finite indexing type in the repository.
Schematically:

```lean
def lowX (a t : ℝ) : ℝ := a + (1 - a ^ 2) * t

def lowJ (m : ℕ) (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, lowX a t ^ m

lemma one_le_lowJ_of_obstruction
    (D : ClosedObstruction m) :
    1 ≤ lowJ m D.a := by
  -- Exact polar identity.
  -- Lower-bound the norm of its left side by 1.
  -- Apply norm_integral_le_integral_norm.
  -- Compare every factor using ‖D.q j‖ ≤ 1.
  ...
```

If the existing polar-channel lemma already concludes
\[
1\leq\int_0^1 c(t)^m\,dt
\quad\text{with}\quad
0\leq c(t)\leq a+(1-a^2)t,
\]
reuse it and integrate the pointwise comparison instead. That will be even
shorter.

Important: retain the **exact** polar integral here. Do not pass through the
quadratic-mean bound involving \(x\), or through the exponential polar
inequality. Those relaxations are useful in high degree but obscure this
low-degree argument.

## 2. The scalar quartic estimate

The key scalar fact is
\[
J_4(a)<1 \qquad (0<a<1).
\tag{3}
\]
Direct integration and factorization give
\[
1-J_4(a)
=
\frac{(1-a)^3(1+a)}5
\left(a^4-3a^3+3a+4\right).
\tag{4}
\]
The final factor is positive, since
\[
a^4-3a^3+3a+4
=
2+3a+(1-a)\bigl(2+2a+a^2(2-a)\bigr)>0.
\tag{5}
\]
Every factor on the right of (4) is therefore positive when \(0<a<1\).

### Suggested Lean lemmas

```lean
lemma lowJ_four_identity (a : ℝ) :
    1 - lowJ 4 a =
      ((1 - a) ^ 3 * (1 + a) / 5) *
        (a ^ 4 - 3 * a ^ 3 + 3 * a + 4) := by
  ...

lemma quartic_aux_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < a ^ 4 - 3 * a ^ 3 + 3 * a + 4 := by
  have hfactor :
      a ^ 4 - 3 * a ^ 3 + 3 * a + 4 =
        2 + 3 * a + (1 - a) * (2 + 2 * a + a ^ 2 * (2 - a)) := by
    ring
  rw [hfactor]
  positivity

lemma lowJ_four_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    lowJ 4 a < 1 := by
  have haux := quartic_aux_pos ha0 ha1
  have hfac :
      0 < ((1 - a) ^ 3 * (1 + a) / 5) *
        (a ^ 4 - 3 * a ^ 3 + 3 * a + 4) := by
    positivity
  rw [← sub_pos]
  rw [lowJ_four_identity]
  exact hfac
```

The precise proof of `lowJ_four_identity` depends on the integration API
already present in the repository. Two reasonable implementations are:

1. Expand
   \[
   (a+(1-a^2)t)^4
   =a^4+4a^3(1-a^2)t+6a^2(1-a^2)^2t^2
     +4a(1-a^2)^3t^3+(1-a^2)^4t^4,
   \]
   integrate the five monomials, and finish with `ring`.

2. Reuse the repository's already-formalized moment evaluation code, if it can
   evaluate this fixed fourth moment cheaply.

Route 1 is probably simpler and more auditable. This calculation is fixed
degree and should not encounter the expression-size problem that occurred in
the medium-degree certificate code.

Avoid proving (4) by first dividing by \(1-a^2\). The expanded-polynomial proof
has no denominators depending on \(a\) and hence creates fewer side conditions.

## 3. Dominate exponents one through four by the quartic

For every \(X\geq0\) and every integer \(1\leq m\leq4\),
\[
X^m\leq1-\frac m4+\frac m4X^4.
\tag{6}
\]
This is weighted AM-GM, but in Lean it is easiest to split the four possible
values of \(m\). The nontrivial cases reduce to the identities
\[
\begin{aligned}
X^4-4X+3
  &=(X-1)^2(X^2+2X+3), &&m=1,\\
X^4-2X^2+1
  &=(X^2-1)^2, &&m=2,\\
3X^4-4X^3+1
  &=(X-1)^2(3X^2+2X+1), &&m=3.
\end{aligned}
\tag{7}
\]
The case \(m=4\) is equality.

### Suggested Lean lemma

```lean
lemma pow_le_quartic_average
    {x : ℝ} (hx : 0 ≤ x) {m : ℕ}
    (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    x ^ m ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * x ^ 4 := by
  interval_cases m
  · omega -- impossible m = 0
  · have hsq : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
    have hpos : 0 ≤ x ^ 2 + 2 * x + 3 := by positivity
    nlinarith [mul_nonneg hsq hpos]
  · nlinarith [sq_nonneg (x ^ 2 - 1)]
  · have hsq : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
    have hpos : 0 ≤ 3 * x ^ 2 + 2 * x + 1 := by positivity
    nlinarith [mul_nonneg hsq hpos]
  · ring_nf
```

The exact behavior of `interval_cases` depends on whether the bounds have
already been added to the local arithmetic context. If it is awkward, prove
four separate scalar lemmas and dispatch with `omega` plus a short `rcases` or
finite enumeration. Do not build a general weighted-AM-GM library solely for
this step.

Since \(0<a<1\) and \(0\leq t\leq1\), one has \(X_a(t)\geq0\). Apply (6)
pointwise and integrate:
\[
\begin{aligned}
J_m(a)
&\leq
\int_0^1\left(1-\frac m4+\frac m4X_a(t)^4\right)dt\\
&=1-\frac m4+\frac m4J_4(a).
\end{aligned}
\tag{8}
\]
Since \(m>0\) and \(J_4(a)<1\), this implies
\[
J_m(a)<1.
\tag{9}
\]

### Suggested integrated lemma

```lean
lemma lowJ_lt_one
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    lowJ m a < 1 := by
  have hX : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lowX a t := by
    intro t ht
    dsimp [lowX]
    have hdelta : 0 ≤ 1 - a ^ 2 := by nlinarith
    positivity

  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      lowX a t ^ m ≤
        1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowX a t ^ 4 := by
    intro t ht
    exact pow_le_quartic_average (hX t ht) hm0 hm4

  have h_integral :
      lowJ m a ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowJ 4 a := by
    -- Apply intervalIntegral.integral_mono_on to hpoint.
    -- Establish integrability automatically: all functions are polynomials.
    -- Evaluate the integral of the constant term over [0,1].
    ...

  have h4 : lowJ 4 a < 1 := lowJ_four_lt_one ha0 ha1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm0
  nlinarith
```

Depending on the repository conventions, the pointwise integral comparison
may ask for \(t\in [0,1]\) or for a statement valid almost everywhere. Since
these are continuous polynomial functions, the integrability obligations
should be discharged by `Continuous.intervalIntegrable` (or the corresponding
existing helper).

An alternative is to bypass (8) and calculate \(J_1,J_2,J_3\) directly. That
works, but the common quartic majorant is more modular and avoids three
separate positivity factorizations.

## 4. Contradiction for a normalized obstruction

Combine (2) and (9):
\[
1\leq J_m(a)<1,
\]
a contradiction.

```lean
lemma no_obstruction_of_m_le_four
    (D : ClosedObstruction m)
    (hm0 : 1 ≤ m) (hm4 : m ≤ 4) : False := by
  have hlo : 1 ≤ lowJ m D.a := one_le_lowJ_of_obstruction D
  have hhi : lowJ m D.a < 1 :=
    lowJ_lt_one D.a_pos D.a_lt_one hm0 hm4
  linarith
```

Here `m` is the number of non-distinguished zeros, so the polynomial degree is
\(n=m+1\). Therefore:

- \(n=2\) corresponds to \(m=1\);
- \(n=3\) corresponds to \(m=2\);
- \(n=4\) corresponds to \(m=3\);
- the same proof also includes \(n=5\), corresponding to \(m=4\).

This off-by-one point is worth recording explicitly in the code comments.

## 5. Hooking this into the polynomial theorem

The existing normalization layer should already reduce a failed interior
Sendov conclusion to a normalized obstruction. Reuse its handling of:

- rotation and scaling of the distinguished zero;
- a repeated distinguished zero, for which \(p'(a)=0\);
- the case \(a=0\);
- the boundary case \(|a|=1\), if the global theorem includes it;
- the passage from polynomial degree \(n\) to obstruction size \(m=n-1\).

The only new branch needed should be schematic code of the following form:

```lean
theorem sendov_degree_le_five
    (hpdeg : 2 ≤ p.natDegree)
    (hpdeg5 : p.natDegree ≤ 5)
    (hzeros : ... )
    (ha : IsRoot p a) :
    ∃ w, IsRoot (derivative p) w ∧ dist w a ≤ 1 := by
  by_contra hsendov
  obtain ⟨m, D, hm_degree, ...⟩ :=
    normalizedObstruction_of_sendov_failure hsendov
  have hm0 : 1 ≤ m := by omega
  have hm4 : m ≤ 4 := by omega
  exact no_obstruction_of_m_le_four D hm0 hm4
```

Do not rely on the origin inequality in this branch. Its proof in the blog
uses the discriminant estimate valid from \(n\geq5\), and the later simplified
origin estimate contains the exponent \((n-4)/2\). Neither feature is needed
for low degree once the exact polar identity is retained.

## 6. Likely Lean friction points

### Complex versus real integrals

The exact polar identity is complex-valued. The required chain is
\[
1\leq |\text{left side}|
=\left|\int f\right|
\leq\int|f|
\leq J_m(a).
\]
Be careful not to rewrite the norm of an integral as the integral of the norm;
only the inequality is available. Reuse whatever Bochner/interval-integral
triangle lemma the blog formalization already employs.

### Products indexed by a finite type

The last pointwise comparison can be shown either factor by factor with
`Finset.prod_le_prod`, or by reusing an existing lemma bounding the polar
integrand. For `prod_le_prod`, first establish nonnegativity of all norms and
of `lowX a t`.

### Strictness

The polar side only gives \(1\leq J_m(a)\). All strictness comes from
\(0<a<1\), which implies \(J_4(a)<1\). Consequently, do not weaken the
normalization hypotheses to \(a\leq1\) at this stage. At \(a=1\), one has
\(J_m(1)=1\), as expected from the regular-polygon equality examples.

### Natural-number casts

In (6)--(8), the expression \(m/4\) is a real quotient. Write `(m : ℝ) / 4`
explicitly. Establish `(0 : ℝ) < m` by `exact_mod_cast` from `1 ≤ m` before
the final `nlinarith` call.

### Avoid `Real.rpow`

All powers in this branch are natural powers. Keeping them as `Nat` powers
will allow `ring`, `nlinarith`, and polynomial integration to work directly.
Do not reuse a high-degree lemma that has converted \(m/2\) into a real
exponent.

## 7. Minimal dependency graph

The recommended proof architecture is:

```text
existing exact polar identity
        |
        v
one_le_lowJ_of_obstruction

fixed fourth-moment calculation ---> lowJ_four_lt_one
                                          |
scalar case split m=1,2,3,4 -------------+
        |                                 |
        v                                 v
pow_le_quartic_average -------------> lowJ_lt_one
                                          |
                                          v
                              no_obstruction_of_m_le_four
                                          |
                                          v
                              Sendov for degrees 2--5
```

No interval arithmetic, Bernstein certificates, origin-channel estimates,
asymptotic estimates, or degree-specific root formulas are required.

## 8. Audit checklist

Before treating this branch as complete, check:

1. `#print axioms` for the final low-degree theorem contains neither
   `sorryAx` nor a project-defined numerical axiom.
2. The polar lower bound really starts from the exact complex identity and
   uses the correct direction of the integral triangle inequality.
3. The theorem's degree variable \(n\) and the obstruction-size variable
   \(m=n-1\) have not been conflated.
4. The strict inequality uses `a < 1`, not merely `a ≤ 1`.
5. The cases \(a=0\), repeated distinguished roots, and boundary
   distinguished roots are discharged by the pre-existing normalization
   layer rather than silently omitted.
6. If degree five remains in the separate certificate suite, verify that the
   two proofs agree; after that, the certificate proof for degree five can be
   retained as a redundancy check or removed from the trusted proof path.

## References for the classical low-degree result

The proposed proof is new-method-specific and does not use these papers, but
the original low-degree attribution is:

- D. A. Brannan, *On a conjecture of Ilieff*, Proc. Cambridge Philos. Soc.
  **64** (1968), 83--85. This treats the cubic case.
- Z. Rubinstein, *On a problem of Ilyeff*, Pacific J. Math. **26** (1968),
  159--161. Theorem 2 treats degrees three and four together.
- A. Meir and A. Sharma, *On Ilyeff's conjecture*, Pacific J. Math. **31**
  (1969), 459--467. This extends the result to degree five.

