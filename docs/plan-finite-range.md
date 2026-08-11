# Lean verification plan for the finite Sendov range

## 1. Objective and scope

The goal is to formalize only the finite-dimensional numerical implication left open in the blog post. The full polynomial argument should remain outside this project initially.

Write

\[
M=n-1,\qquad
A=1-\frac{2\alpha}{M},\qquad
B=\frac{\alpha}{3+\alpha},
\]

\[
c=1-\frac{\alpha}{M}-\frac{\alpha}{2(3+\alpha)},
\qquad
Q(t)=1-2ct+At^2.
\]

The domain to be certified is

\[
5\le n\le 200,\qquad 0\le\alpha\le17,
\qquad c^2\le A.
\tag{D}
\]

The last condition is the feasibility condition occurring in the blog post. The target is to prove that, on this domain,

\[
\begin{split}
R_n(\alpha):={}&\frac16+\frac1{4(3+\alpha)}
+\frac1{2M}+\frac1{4M(3+\alpha)}\\
&+\frac{A^2nM(n-2)}{4(3+\alpha)}
 \int_0^1 t^3Q(t)^{(n-4)/2}\,dt
<1.
\end{split}
\tag{F}
\]

This contradicts equation `stat` of the blog post, which asserts \(1\le R_n(\alpha)\). Here \(A=a^2\), so the factor \(A^2\) in (F) is the blog post's \(a^4\).

A useful final interface is therefore something like:

```lean
theorem finite_range_contradiction
    (n : ℕ) (α : ℝ)
    (hn_lo : 5 ≤ n) (hn_hi : n ≤ 200)
    (hα_lo : 0 ≤ α) (hα_hi : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α)
    (hstat : 1 ≤ finiteRangeRHS n α) : False
```

The original argument has \(\alpha>0\), because an earlier inequality was divided by \(\alpha\). It is harmless and convenient for the numerical lemma to include \(\alpha=0\), since the upper bound in (F) extends continuously there and is still strictly below one.

## 2. Eliminate numerical integration first

It is preferable not to certify a quadrature routine. The integral in (F) admits an exact algebraic treatment in even degrees and a simple algebraic upper bound in odd degrees.

### 2.1 Basic bounds on the quadratic

The feasibility condition gives

\[
Q(t)=(1-ct)^2+(A-c^2)t^2\ge0.
\]

Moreover, \(Q\) is convex, \(Q(0)=1\), and \(Q(1)=B<1\). Hence

\[
0\le Q(t)\le1\qquad(0\le t\le1).
\tag{Q}
\]

The identity \(Q(1)=B\) should be checked in Lean directly from the definitions. Positivity of every denominator should be recorded explicitly; in particular, \(M>0\) and \(3+\alpha>0\).

### 2.2 Exact polynomial moments

For an integer \(k\ge0\), define

\[
I_k(n,\alpha)=\int_0^1t^3Q(t)^k\,dt.
\]

The multinomial theorem gives the exact finite sum

\[
I_k=
\sum_{\substack{i,j\ge0\\i+j\le k}}
\frac{k!}{i!j!(k-i-j)!}
\frac{(-2c)^iA^j}{4+i+2j}.
\tag{M}
\]

This follows by expanding

\[
(1+(-2c)t+At^2)^k
\]

and integrating each monomial. It can instead be implemented recursively if the triple sum causes performance problems. Either representation is exact and rational in \(\alpha\).

For even \(n\), put \(k=(n-4)/2\). The integral in (F) is exactly \(I_k\).

### 2.3 Odd degrees at least seven

If \(n\ge7\) is odd, put \(k=(n-5)/2\). By (Q) and

\[
2\sqrt u\le1+u\qquad(0\le u\le1),
\]

one has

\[
Q(t)^{k+1/2}
\le \frac{Q(t)^k+Q(t)^{k+1}}2.
\]

Consequently,

\[
\int_0^1t^3Q(t)^{(n-4)/2}\,dt
\le\frac{I_k+I_{k+1}}2.
\tag{O}
\]

This removes every square root and reduces the problem to a rational inequality in \(\alpha\).

### 2.4 The special case \(n=5\)

The bound (O) is a little too wasteful in degree five. Use convexity of \(Q\) instead:

\[
Q(t)\le(1-t)Q(0)+tQ(1)=1-(1-B)t.
\]

Thus

\[
\int_0^1t^3\sqrt{Q(t)}\,dt\le H(B),
\]

where

\[
H(B)=\frac{1}{(1-B)^4}
\left[
\frac{32}{315}
-\left(
\frac23B^{3/2}-\frac65B^{5/2}
+\frac67B^{7/2}-\frac29B^{9/2}
\right)
\right].
\tag{H}
\]

Introduce \(r=\sqrt B\) only inside the degree-five module. Then

\[
B=r^2,qquad
\alpha=\frac{3r^2}{1-r^2},
\]

and the right side of (H), as well as the degree-five instance of (F), becomes rational in \(r\). Since \(\alpha\le17\), it is enough to work with \(0\le r<1\); one may choose a convenient rational outer endpoint and exclude its extraneous portion by the transformed constraints. For example, \(r\le19/20\) contains the entire range implied by \(B\le17/20\).

An alternative is to use several rational affine upper bounds for \(\sqrt u\) and keep \(\alpha\) as the sole variable. The substitution above is probably simpler.

## 3. Reduce each degree to polynomial positivity

Define `upperRHS n α` by replacing the integral in (F) as follows:

- if \(n\) is even, use (M) exactly;
- if \(n\ge7\) is odd, use (O);
- if \(n=5\), use (H).

The desired statement is

\[
1-\operatorname{upperRHS}_n(\alpha)>0.
\]

For \(n\ge6\), this is a rational function of \(\alpha\). Clear a known-positive denominator and write it as

\[
1-\operatorname{upperRHS}_n(\alpha)
=\frac{P_n(\alpha)}{D_n(\alpha)},
\qquad D_n(\alpha)>0.
\]

The certificate only has to prove \(P_n(\alpha)>0\). It is fine for \(D_n\) to be larger than the least common denominator; a uniform, easily verified positive denominator is preferable to a minimal one.

The feasibility constraint can likewise be written, after clearing a positive denominator, as a polynomial inequality

\[
G_n(\alpha)\ge0,
\]

where \(G_n\) represents \(A-c^2\). Thus a box may be closed in either of two ways:

1. prove \(G_n<0\) throughout the box, so the box contains no feasible point; or
2. prove \(P_n>0\) throughout the box.

This avoids finding the exact endpoint imposed by \(c^2\le A\). Simply cover all of \([0,17]\) and let each interval certificate establish either infeasibility or the desired upper bound.

For \(n=5\), do the same after the substitution \(\alpha=3r^2/(1-r^2)\).

## 4. Recommended certificate: rational Bernstein bounds

Use exact rational Bernstein certificates on rational subintervals.

If \(p\in\mathbb Q[X]\) and \([\ell,u]\) is a rational interval, transform

\[
p(\ell+(u-\ell)s)
=\sum_{j=0}^d b_j {d\choose j}s^j(1-s)^{d-j}.
\]

For \(0\le s\le1\), every Bernstein basis function is nonnegative and their sum is one. Therefore

\[
\min_j b_j>0\quad\Longrightarrow\quad
p(x)>0\quad(\ell\le x\le u).
\tag{B}
\]

Bernstein bounds are preferable here to a naive interval evaluation of a fully expanded polynomial: they substantially reduce dependency and wrapping losses.

The untrusted generator may adaptively subdivide intervals. Lean must verify all of the following using exact rational arithmetic:

- the boxes are ordered and cover the entire outer interval;
- every endpoint is the exact endpoint claimed in the data;
- a box labeled `infeasible` has a Bernstein certificate for \(-G_n>0\);
- a box labeled `bound` has a Bernstein certificate for \(P_n>0\);
- every strict certificate has a positive rational lower margin, not merely a nonnegative one.

The safest design is for the certificate data to contain only rational endpoints and a box label, with Lean recomputing the Bernstein coefficients. If this is too slow, the generator may also emit coefficients, but Lean must then verify the exact polynomial identity relating them to \(P_n\) or \(-G_n\).

## 5. Suggested Lean project structure

```text
SendovFinite/
  Basic.lean
  Moments.lean
  OddBound.lean
  DegreeFive.lean
  Bernstein.lean
  CertificateData.lean
  Verify.lean
```

### `Basic.lean`

- Define `M`, `A`, `B`, `c`, and `Q` using exact real expressions.
- Define the finite-range feasibility predicate.
- Prove denominator positivity.
- Prove `Q_nonneg`, `Q_le_one`, and `Q_one` from (D).
- Keep casts between `ℕ`, `ℚ`, and `ℝ` explicit and localized.

### `Moments.lean`

- Define the rational moment expression in (M).
- Prove it equals the interval integral of \(t^3Q(t)^k\).
- Isolate all finite-sum and integration library work here.
- If the closed multinomial formula is slow, prove a recurrence for the coefficient vector of \(Q^k\) and integrate that vector termwise.

### `OddBound.lean`

- Prove `two_mul_sqrt_le_add` in the precise form needed for \(0\le u\).
- Deduce (O) from `Q_nonneg` and `Q_le_one`.
- Avoid carrying `Real.sqrt` past this module.

### `DegreeFive.lean`

- Prove the convex chord bound for `Q`.
- Prove (H), either by a direct antiderivative or by the substitution used above.
- Introduce \(r\) locally and reduce the resulting statement to rational polynomial positivity.

### `Bernstein.lean`

- Define the Bernstein basis over `ℚ` and its evaluation in `ℝ`.
- Prove nonnegativity on \([0,1]\), the partition-of-unity identity, and theorem (B).
- Define a small verified checker for a polynomial and rational box.
- Prove the checker's soundness once; certificate data should not contain proofs.

### `CertificateData.lean`

- Store generated rational subdivision data.
- It is reasonable to generate one definition per degree to reduce elaboration pressure.
- Keep all numerical constants rational or dyadic. Do not use floating-point literals.

### `Verify.lean`

- Dispatch the finite range of `n`, perhaps with `interval_cases n`.
- For each degree, invoke the corresponding checked certificate.
- Combine the integral upper-bound theorem with polynomial positivity.
- Export `finite_range_contradiction`.

If a single `interval_cases` call produces an unwieldy term, generate 196 small degree-specific theorems and combine them with a balanced decision tree.

## 6. External certificate generator

The generator can be written in Python, Sage, Julia, or another convenient language. It is not part of the trusted computing base because Lean rechecks its output exactly.

High-level pseudocode:

```text
for n in 5..200:
    construct the exact rational upper bound
    construct the cleared numerator P_n
    construct the cleared feasibility polynomial G_n
    queue := [outer interval]

    while queue is nonempty:
        box := pop(queue)

        if Bernstein(-G_n, box) has all coefficients > 0:
            emit (box, infeasible)
        else if Bernstein(P_n, box) has all coefficients > 0:
            emit (box, bound)
        else:
            bisect box at a rational midpoint
```

Use exact rational arithmetic when generating the final certificate. Floating point is useful only for choosing initial splits and diagnosing hard boxes.

For degree five, run the same algorithm in \(r\), with the transformed feasibility and bound polynomials.

## 7. Trusted-computing-base policy

The formalization should be deliberately conservative because the purpose is to rule out a numerical or formalization loophole.

Recommended:

- `ring`, `ring_nf`, `field_simp`, `norm_num`, and `positivity`;
- a proved-in-Lean Bernstein checker;
- kernel-checked reduction via `decide` only if performance is acceptable;
- a pinned Lean toolchain and pinned mathlib commit.

Avoid:

- `sorry`, `admit`, or new `axiom` declarations;
- `unsafe` definitions in the proof path;
- `native_decide` or any mechanism whose correctness depends on trusting generated native code;
- custom metaprogramming that manufactures proof terms without a small proved soundness theorem;
- floating-point comparisons in the theorem or certificate checker;
- an FFI or external oracle whose answer is accepted without an exact Lean-side check.

The last stage of CI should include:

```lean
#print axioms finite_range_contradiction
```

and a source audit such as

```text
rg -n '\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b' SendovFinite
```

Any standard axioms imported by mathlib, such as classical choice or propositional extensionality, should be reported explicitly. There should be no project-specific axioms.

## 8. Development milestones

1. **Degree 6:** verify one even degree using the exact moment formula.
2. **Degree 7:** verify one odd degree using the averaged-moment bound (O).
3. **Degree 5:** verify the chord bound and the \(r\)-substitution.
4. **Checker:** prove the Bernstein checker's soundness and test it on hand-written low-degree polynomials.
5. **Generator:** generate and check certificates for all degrees.
6. **Composition:** prove the single theorem `finite_range_contradiction`.
7. **Audit:** run the axiom printout, forbidden-token audit, and a clean rebuild from the pinned lockfile.

Do not begin by generating all 196 certificates. The three prototype degrees above expose the parity, square-root, integration, denominator, and certificate issues with much shorter compile cycles.

## 9. Numerical diagnostics, not proof inputs

Previous floating-point exploration suggests generous slack:

- for \(6\le n\le200\), the conservative odd-degree rationalization above gave a largest upper RHS of approximately `0.8554015065`, observed at \(n=53,\alpha=17\);
- for \(n=5\), the chord bound gave a largest upper RHS of approximately `0.9037698413`, observed at \(\alpha=0\).

These figures should be reproduced independently by the generator, but they must not appear as assumptions in Lean. They indicate that coarse rational subdivisions ought to suffice; the expected difficulty is expression size and proof-engineering performance, not a tiny mathematical margin.

## 10. Acceptance criteria

The handoff is complete only when all of the following hold:

- `lake build` succeeds from a clean checkout with pinned versions;
- the exported theorem has exactly the finite-range hypotheses (D), plus `hstat`, and concludes `False`;
- the integral replacement is proved in Lean, not silently built into the theorem statement;
- every external certificate is checked using exact arithmetic by a proved sound checker;
- all 196 degrees are covered, including the separate \(n=5\) argument;
- `#print axioms` reveals no project-specific axioms;
- no prohibited escape hatch occurs in the dependency path of the final theorem;
- deleting or corrupting a certificate box causes verification to fail.

Once this standalone theorem is stable, it can be imported into a larger formalization and applied directly to the blog post's `stat` inequality. Keeping the numerical certificate independent of the polynomial material makes both the audit and any future correction much easier.
