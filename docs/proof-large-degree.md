# A formalization-ready proof that `stat` is impossible for \(n>100\), \(0\le\alpha\le17\)

## 1. Statement

Let \(n\) be a natural number with \(n>100\), and let \(0\le\alpha\le17\). Set

\[
A_n:=a^2=1-\frac{2\alpha}{n-1},\qquad
B:=\frac{\alpha}{3+\alpha},
\]

\[
c_n:=1-\frac{\alpha}{n-1}-\frac{\alpha}{2(3+\alpha)},
\qquad
Q_n(t):=1-2c_nt+A_nt^2.
\]

Assume the feasibility condition

\[
c_n^2\le A_n.
\tag{1}
\]

Equation `stat` in the blog post is

\[
\begin{split}
1\le{}&\frac16+\frac1{4(3+\alpha)}
+\frac1{2(n-1)}+\frac1{4(n-1)(3+\alpha)}\\
&+\frac{A_n^2n(n-1)(n-2)}{4(3+\alpha)}
 \int_0^1t^3Q_n(t)^{(n-4)/2}\,dt.
\end{split}
\tag{stat}
\]

The exponent in this formula is a real exponent, not natural-number division. We prove that the right-hand side is strictly less than one.

The proof has four steps:

1. replace the integral by the exponential-tail estimate already used in the blog post;
2. prove discretely that the resulting upper bound decreases with \(n\) for \(n\ge101\);
3. at \(n=101\), replace the half-integral power by an integral power;
4. split \(0\le\alpha\le17\) into \([0,16]\) and \([16,17]\), and use exact rational endpoint estimates.

## 2. Preliminary bounds

For \(n\ge101\) and \(0\le\alpha\le17\),

\[
A_n\ge1-\frac{34}{100}=\frac{33}{50}>0,
\tag{2}
\]

and

\[
c_n\ge1-\frac{17}{100}-\frac{17}{40}
=\frac{81}{200}>0.
\tag{3}
\]

Also

\[
0\le B\le\frac{17}{20}<1.
\tag{4}
\]

Condition (1) gives

\[
Q_n(t)=(1-c_nt)^2+(A_n-c_n^2)t^2\ge0.
\tag{5}
\]

Finally, direct simplification gives

\[
Q_n(1)=1-2c_n+A_n=B.
\tag{6}
\]

## 3. The integral upper bound

Put \(r=(n-4)/2\), so \(r>0\). The quadratic \(Q_n\) has its vertex at

\[
t_0=\frac{c_n}{A_n}.
\]

If \(0\le t\le t_0\), then \(A_nt^2\le c_nt\), and hence

\[
Q_n(t)\le1-c_nt\le e^{-c_nt}.
\]

Here \(1-c_nt\ge0\): indeed, (1) and \(t\le c_n/A_n\) give
\(c_nt\le c_n^2/A_n\le1\). Thus all real powers used below are applied to
nonnegative quantities.

Using (5), raising to the positive power \(r\) gives

\[
Q_n(t)^r\le e^{-rc_nt}.
\tag{7}
\]

If \(t_0\le1\), then \(Q_n\) is increasing on \([t_0,1]\), so by (6)

\[
Q_n(t)\le Q_n(1)=B\qquad(t_0\le t\le1).
\tag{8}
\]

If \(t_0>1\), this second interval is empty. Extending both resulting nonnegative integrals gives, in either case,

\[
\begin{split}
\int_0^1t^3Q_n(t)^r\,dt
&\le \int_0^\infty t^3e^{-rc_nt}\,dt
  +\int_0^1t^3B^r\,dt\\
&=\frac{6}{r^4c_n^4}+\frac14B^r\\
&=\frac{96}{(n-4)^4c_n^4}+\frac14B^{(n-4)/2}.
\end{split}
\tag{9}
\]

Consequently, `stat` implies

\[
1\le U_n(\alpha),
\tag{10}
\]

where

\[
\begin{split}
U_n(\alpha):={}&\frac16+\frac1{4(3+\alpha)}
+\frac1{2(n-1)}+\frac1{4(n-1)(3+\alpha)}\\
&+T_{1,n}(\alpha)+T_{2,n}(\alpha),
\end{split}
\tag{11}
\]

with

\[
T_{1,n}(\alpha):=
\frac{24A_n^2n(n-1)(n-2)}
{(3+\alpha)(n-4)^4c_n^4},
\tag{12}
\]

\[
T_{2,n}(\alpha):=
\frac{A_n^2n(n-1)(n-2)}{16(3+\alpha)}
B^{(n-4)/2}.
\tag{13}
\]

Everything after this point is an elementary inequality.

## 4. Discrete monotonicity in \(n\)

We prove

\[
U_{n+1}(\alpha)\le U_n(\alpha)
\qquad(n\ge101).
\tag{14}
\]

The first four terms in (11) plainly decrease with \(n\). It remains to treat (12) and (13).

### 4.1 The first tail term

One has

\[
A_{n+1}-A_n=\frac{2\alpha}{n(n-1)}
\]

and, by (2),

\[
\frac{A_{n+1}}{A_n}
=1+\frac{2\alpha}{n(n-1)A_n}
\le1+\frac{1700}{33n(n-1)}.
\tag{15}
\]

Also \(c_{n+1}\ge c_n\). Therefore

\[
\frac{T_{1,n+1}}{T_{1,n}}
\le
\left(1+\frac{1700}{33n(n-1)}\right)^2
\frac{n+1}{n-2}
\left(\frac{n-4}{n-3}\right)^4.
\tag{16}
\]

The right-hand side is strictly less than one for every \(n\ge101\). This can be checked without analysis. After multiplying by the positive denominator

\[
33^2n^2(n-1)^2(n-2)(n-3)^4,
\]

the desired inequality is

\[
\begin{split}
&33^2n^2(n-1)^2(n-2)(n-3)^4\\
&\qquad-\bigl(33n(n-1)+1700\bigr)^2(n+1)(n-4)^4>0.
\end{split}
\tag{17}
\]

Writing \(k=n-101\ge0\), the left side of (17) expands exactly as

\[
\begin{split}
{}&1011812007899760000\\
&+171120966977415200k\\
&+9227125609237658k^2\\
&+250975969057803k^3\\
&+3989097576248k^4\\
&+38904262097k^5\\
&+230383461k^6\\
&+763356k^7+1089k^8.
\end{split}
\tag{18}
\]

Every coefficient is positive. This proves that \(T_{1,n}\) decreases with \(n\).

### 4.2 The second tail term

If \(\alpha=0\), then \(B=0\) and \(T_{2,n}=0\), so there is nothing to prove. Suppose \(\alpha>0\). Then

\[
\frac{T_{2,n+1}}{T_{2,n}}
=\left(\frac{A_{n+1}}{A_n}\right)^2
 \frac{n+1}{n-2}\sqrt B.
\tag{19}
\]

For \(n\ge101\), (15) and (4) give

\[
\frac{T_{2,n+1}}{T_{2,n}}
\le
\left(\frac{3350}{3333}\right)^2
\frac{34}{33}\sqrt{\frac{17}{20}}<1.
\tag{20}
\]

The last inequality is an exact rational check after squaring the nonnegative quantities:

\[
\frac{17}{20}
\left(\frac{3350}{3333}\right)^4
\left(\frac{34}{33}\right)^2
=\frac{123753071841250000}{134390674732795569}<1.
\tag{21}
\]

Thus \(T_{2,n}\) also decreases with \(n\). This proves (14), and hence

\[
U_n(\alpha)\le U_{101}(\alpha)
\qquad(n\ge101).
\tag{22}
\]

This discrete argument is recommended for Lean: it avoids differentiating with respect to the degree.

## 5. Reduction at \(n=101\)

At \(n=101\), the exponent in (13) is \(97/2\). Since \(0\le B\le1\),

\[
B^{97/2}=B^{48}\sqrt B\le B^{48}.
\tag{23}
\]

Define

\[
\widetilde T_2(\alpha):=
\frac{A_{101}^2\,101\cdot100\cdot99}{16(3+\alpha)}B^{48}.
\tag{24}
\]

It is enough to prove that

\[
\begin{split}
\widetilde U(\alpha):={}&\frac16+\frac1{4(3+\alpha)}
+\frac1{200}+\frac1{400(3+\alpha)}\\
&+T_{1,101}(\alpha)+\widetilde T_2(\alpha)<1.
\end{split}
\tag{25}
\]

All powers in (25) are now natural powers, so (25) is a rational inequality in \(\alpha\).

## 6. Monotonicity in \(\alpha\) at \(n=101\)

The first four terms of (25) decrease with \(\alpha\). Both tail terms increase with \(\alpha\) on \([0,17]\).

Indeed,

\[
A_{101}=1-\frac{\alpha}{50}=\frac{50-\alpha}{50},
\]

\[
c_{101}
=1-\frac{\alpha}{100}-\frac{\alpha}{2(3+\alpha)}
=\frac{300+47\alpha-\alpha^2}{100(3+\alpha)}.
\tag{26}
\]

After differentiating \(T_{1,101}\) and clearing positive factors, the sign of the derivative is the sign of

\[
p_1(\alpha):=15000-2368\alpha+185\alpha^2-3\alpha^3.
\tag{27}
\]

For \(0\le\alpha\le17\),

\[
p_1(\alpha)
\ge15000-2368\alpha+134\alpha^2>0.
\tag{28}
\]

The first inequality uses \(-3\alpha^3\ge-51\alpha^2\). The second follows from the exact identity

\[
134\bigl(15000-2368\alpha+134\alpha^2\bigr)
=(134\alpha-1184)^2+608144>0.
\tag{29}
\]

Thus \(T_{1,101}\) is increasing.

For \(\alpha>0\), differentiating \(\widetilde T_2\) and clearing positive factors reduces the sign to

\[
p_2(\alpha):=7200-200\alpha-\alpha^2.
\tag{30}
\]

On \([0,17]\),

\[
p_2(\alpha)\ge7200-3400-289=3511>0.
\tag{31}
\]

Continuity handles \(\alpha=0\), so \(\widetilde T_2\) is increasing on the closed interval.

For Lean, one can either use the standard theorem that a nonnegative derivative implies monotonicity on an interval, or prove the two endpoint-domination lemmas directly after rewriting the tail terms as rational functions. The derivative route produces only the cubic and quadratic polynomials above.

## 7. Exact rational endpoint estimates

Split into two intervals.

### 7.1 The interval \(0\le\alpha\le16\)

The elementary part of (25) is decreasing, while both tail terms are increasing. Hence

\[
\begin{split}
\widetilde U(\alpha)
\le{}&\left(\frac16+\frac1{12}+\frac1{200}+\frac1{1200}\right)
+T_{1,101}(16)+\widetilde T_2(16).
\end{split}
\tag{32}
\]

At \(\alpha=16\),

\[
A_{101}=\frac{17}{25},\qquad
c_{101}=\frac{199}{475},\qquad
B=\frac{16}{19}.
\]

Direct rational arithmetic gives

\[
\frac16+\frac1{12}+\frac1{200}+\frac1{1200}
=\frac{307}{1200}<\frac{32}{125},
\tag{33}
\]

\[
T_{1,101}(16)
=
\frac{24(17/25)^2\,101\cdot100\cdot99}
{19\cdot97^4(199/475)^4}
<\frac{43}{200},
\tag{34}
\]

and

\[
\widetilde T_2(16)
=\frac{(17/25)^2\,101\cdot100\cdot99}{16\cdot19}
 \left(\frac{16}{19}\right)^{48}
<\frac{199}{500}.
\tag{35}
\]

The right side of (32) is therefore less than

\[
\frac{32}{125}+\frac{43}{200}+\frac{199}{500}
=\frac{869}{1000}<1.
\tag{36}
\]

### 7.2 The interval \(16\le\alpha\le17\)

Now use \(\alpha=16\) for the decreasing elementary part and \(\alpha=17\) for the increasing tail terms:

\[
\begin{split}
\widetilde U(\alpha)
\le{}&\left(\frac16+\frac1{76}+\frac1{200}+\frac1{7600}\right)
+T_{1,101}(17)+\widetilde T_2(17).
\end{split}
\tag{37}
\]

At \(\alpha=17\),

\[
A_{101}=\frac{33}{50},\qquad
c_{101}=\frac{81}{200},\qquad
B=\frac{17}{20}.
\]

Exact rational arithmetic gives

\[
\frac16+\frac1{76}+\frac1{200}+\frac1{7600}
<\frac{37}{200},
\tag{38}
\]

\[
T_{1,101}(17)
=\frac{24(33/50)^2\,101\cdot100\cdot99}
{20\cdot97^4(81/200)^4}
<\frac{11}{50},
\tag{39}
\]

and

\[
\widetilde T_2(17)
=\frac{(33/50)^2\,101\cdot100\cdot99}{16\cdot20}
 \left(\frac{17}{20}\right)^{48}
<\frac{279}{500}.
\tag{40}
\]

It follows that

\[
\widetilde U(\alpha)
<\frac{37}{200}+\frac{11}{50}+\frac{279}{500}
=\frac{963}{1000}<1.
\tag{41}
\]

Combining (36) and (41) proves

\[
\widetilde U(\alpha)<1
\qquad(0\le\alpha\le17).
\tag{42}
\]

By (22), (23), and (25), this implies \(U_n(\alpha)<1\) for every \(n>100\). This contradicts (10), completing the proof.

## 8. Suggested Lean decomposition

A convenient formalization order is:

```lean
-- Definitions
def A (n : ℕ) (α : ℝ) : ℝ := 1 - 2 * α / (n - 1)
def B (α : ℝ) : ℝ := α / (3 + α)
def c (n : ℕ) (α : ℝ) : ℝ :=
  1 - α / (n - 1) - α / (2 * (3 + α))

-- Mathematical reduction
lemma integral_tail_bound ... :
  integralTerm n α ≤
    96 / ((n - 4)^4 * c n α ^ 4) +
    (1 / 4) * (B α) ^ ((n - 4 : ℝ) / 2)

-- Discrete monotonicity
lemma T1_antitone_nat ... : T1 (n + 1) α < T1 n α
lemma T2_antitone_nat ... : T2 (n + 1) α < T2 n α
lemma U_le_U101 ... : U n α ≤ U 101 α

-- Degree 101
lemma T1_mono_alpha_101 :
  MonotoneOn (T1 101) (Set.Icc 0 17)
lemma T2star_mono_alpha_101 :
  MonotoneOn T2star (Set.Icc 0 17)

-- Exact endpoint checks
lemma low_alpha_bound ... : α ∈ Set.Icc 0 16 → Ustar α < 869 / 1000
lemma high_alpha_bound ... : α ∈ Set.Icc 16 17 → Ustar α < 963 / 1000

theorem stat_unsatisfiable_of_gt_100 ...
    (hstat : 1 ≤ statRHS n α) : False
```

In actual Lean definitions, cast `n` to `ℝ` before subtracting; the schematic definitions above should not be copied literally because natural-number subtraction would otherwise occur first. For example, use `((n : ℝ) - 1)`.

The endpoint inequalities (33)--(35) and (38)--(40) should close with `norm_num` after unfolding definitions. The polynomial identities (18), (29), and the derivative reductions should close with `ring`. No floating-point value is part of the proof.

For the real powers in Sections 3--5, it may be simplest to use `Real.rpow`. Keep the facts \(0\le B\le1\) available as named lemmas. In particular, isolate the identities

\[
B^{(n-3)/2}=B^{(n-4)/2}\sqrt B
\]

and

\[
B^{97/2}=B^{48}\sqrt B
\]

behind small lemmas, since the exact mathlib rewriting API for `Real.rpow` can otherwise obscure the elementary argument.

Finally, run

```lean
#print axioms stat_unsatisfiable_of_gt_100
```

and ensure that the result depends on no project-specific axioms, `sorry`, `native_decide`, or external numerical oracle.

## 9. Optional hybrid strategy for lowering the finite certification cutoff

This section describes a possible replacement for the division of labor

\[
5\le n\le100\quad\hbox{(one certificate for every degree)},
\qquad n\ge101\quad\hbox{(the analytic argument above)}.
\]

It is **not part of the proved argument in Sections 1--8**.  The principal
monotonicity assertion below has substantial numerical support but still needs
an analytic proof.  The purpose of this section is to give a coding agent exact
targets to investigate without building the degree-97 moment expansion first.

### 9.1 The exact right-hand side

Retain the definitions (A_n,c_n,Q_n,B) from Section 1, and define locally

\[
I_n(\alpha):=\int_0^1t^3Q_n(t)^{(n-4)/2}\,dt,
\]

\[
P_n(\alpha):=
\frac{A_n^2n(n-1)(n-2)}{4(3+\alpha)}.
\]

Thus the exact right-hand side of `stat` is

\[
R_n(\alpha):=
\frac16+\frac1{4(3+\alpha)}
+\frac1{2(n-1)}+\frac1{4(n-1)(3+\alpha)}
+P_n(\alpha)I_n(\alpha).
\tag{43}
\]

This (R_n) is the exact expression, not the cruder (U_n) from (11).

The key calculation is

\[
A_{n+1}-A_n=\frac{2\alpha}{n(n-1)},
\qquad
c_{n+1}-c_n=\frac{\alpha}{n(n-1)},
\]

and hence

\[
\boxed{
Q_{n+1}(t)=Q_n(t)-\frac{2\alpha}{n(n-1)}t(1-t).
}
\tag{44}
\]

In particular,

\[
Q_{n+1}(t)\le Q_n(t)
\qquad(0\le t\le1).
\tag{45}
\]

The two-step version is

\[
\boxed{
Q_{n+2}(t)=Q_n(t)
-\frac{4\alpha}{(n-1)(n+1)}t(1-t).
}
\tag{46}
\]

These identities should be proved in Lean before introducing integrals.  They
are just `field_simp`/`ring` identities once positivity of the natural-number
denominators has been recorded.

The feasibility hypothesis gives

\[
Q_n(t)=(1-c_nt)^2+(A_n-c_n^2)t^2\ge0.
\tag{47}
\]

There is also a useful upper bound, valid on \(0\le t\le1\):

\[
Q_n(t)\le (1-t)Q_n(0)+tQ_n(1)
=1-(1-B)t\le1.
\tag{48}
\]

Here the first inequality is simply convexity of the quadratic \(Q_n\), and
\(Q_n(0)=1,\ Q_n(1)=B\).  Thus all bases in (44)--(48) lie in \([0,1]\).

Feasibility propagates in the direction in which it is needed.  Indeed, put

\[
b:=\frac{\alpha}{2(3+\alpha)},\qquad s_n:=\frac{\alpha}{n-1}.
\]

Then

\[
A_n-c_n^2=2b-b^2-s_n^2-2bs_n.
\tag{48a}
\]

For \(\alpha\ge0\), both \(b\ge0\) and \(s_{n+1}\le s_n\).  The right-hand
side of (48a) therefore increases with \(n\).  Consequently

\[
c_n^2\le A_n\quad\Longrightarrow\quad
c_{n+1}^2\le A_{n+1}.
\tag{48b}
\]

This lemma should be available when comparing the exact moments at different
degrees.

### 9.2 The strongest proposed hybrid

Floating-point reconnaissance suggests

\[
R_{n+1}(\alpha)\le R_n(\alpha)
\qquad
(n\ge53, 0\le\alpha\le17, c_n^2\le A_n).
\tag{49?}
\]

Some observed maxima of the exact expression are

\[
\begin{array}{c|c}
n&\max R_n(\alpha)\\ \hline
50&0.84015\\
51&0.84802\\
52&0.85255\\
53&0.85285\\
54&0.84943\\
55&0.84278\\
60&0.77633\\
70&0.59148\\
97&0.29175.
\end{array}
\]

These decimals are motivation only and must not enter the formal proof.

If (49?) can be proved, the existing degree-53 Bernstein certificate proves
(R_{53}<1), and no degree above 53 needs a separate certificate.  The odd
degree tangent bound used in the certificate need not itself be monotone: use
it only to prove (R_{53}<1), while applying (49?) to the exact real-power
expression (43).

The following parity-preserving assertion is a slightly weaker but probably
cleaner target:

\[
R_{n+2}(\alpha)\le R_n(\alpha)
\qquad(n\ge53).
\tag{50?}
\]

It would require endpoint certificates at (n=53) and (n=54), but (46) has
the advantage that the exponent rises by exactly one:

\[
\frac{n+2-4}{2}=\frac{n-4}{2}+1.
\]

The elementary part of (43) already decreases with (n).  Consequently it is
enough to prove

\[
P_{n+2}I_{n+2}\le P_nI_n.
\tag{51?}
\]

Writing (r=(n-4)/2) and

\[
\varepsilon_n:=\frac{4\alpha}{(n-1)(n+1)},
\]

the exact integral inequality to be proved is

\[
\int_0^1t^3
 \bigl(Q_n(t)-\varepsilon_nt(1-t)\bigr)^{r+1}\,dt
\le
\left(\frac{A_n}{A_{n+2}}\right)^2
\frac{(n-1)(n-2)}{(n+1)(n+2)}
\int_0^1t^3Q_n(t)^r\,dt.
\tag{52?}
\]

Equation (52?) retains the decrement in (46).  Merely replacing
(Q_{n+2}) by (Q_n) loses too much near (alpha=17), so the decrement
should not be discarded at the start of the proof.  A plausible analytic
route is to apply a logarithmic or Bernoulli estimate to

\[
\left(1-\frac{\varepsilon_nt(1-t)}{Q_n(t)}\right)^{r+1}
\]

on regions where (Q_n>0), treating a zero of (Q_n), if present, by
continuity.  Splitting into a small-(alpha) and a large-(alpha) range is
acceptable if a uniform proof of (52?) proves awkward.

The Lean target should initially be stated directly, rather than hidden behind
a general theory of parameter-dependent moments:

```lean
lemma Q_succ_sub
    (hn : 2 ≤ n) :
    Q (n + 1) α t =
      Q n α t - (2 * α / ((n : ℝ) * ((n : ℝ) - 1))) * t * (1 - t) := by
  field_simp
  ring

lemma Q_add_two_sub
    (hn : 2 ≤ n) :
    Q (n + 2) α t =
      Q n α t -
        (4 * α / (((n : ℝ) - 1) * ((n : ℝ) + 1))) * t * (1 - t) := by
  field_simp
  ring

lemma Q_nonneg
    (hfeas : c n α ^ 2 ≤ A n α) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Q n α t := by
  -- Rewrite as (1-c*t)^2 + (A-c^2)*t^2.
  ...

lemma Q_le_one
    (hA : 0 ≤ A n α) (hB : B α ≤ 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Q n α t ≤ 1 := by
  -- Use Q(t) ≤ (1-t)Q(0)+tQ(1).
  ...

lemma feasibility_mono_succ
    (hn : 2 ≤ n) (hα0 : 0 ≤ α)
    (hfeas : c n α ^ 2 ≤ A n α) :
    c (n + 1) α ^ 2 ≤ A (n + 1) α := by
  -- Use (48a) and α/(n : ℝ) ≤ α/((n : ℝ)-1).
  ...

lemma exact_tail_antitone_add_two
    (hn : 53 ≤ n) (hα0 : 0 ≤ α) (hα17 : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) :
    P (n + 2) α * I (n + 2) α ≤ P n α * I n α := by
  -- This is the genuinely new analytic lemma, equivalent to (52?).
  ...

lemma exact_stat_antitone_add_two ... :
    exactStatRHS (n + 2) α ≤ exactStatRHS n α := by
  ...
```

Do not put a `sorry`-backed version of `exact_tail_antitone_add_two` on the
dependency path of the final theorem.  It is useful first as an isolated
experimental target.

### 9.3 A Lean-friendly algebraic chord majorant

If exact monotonicity is resistant, the following intermediate majorant may be
more useful than the exponential secants suggested initially.  It involves
only natural powers and polynomial integration.

Divide ([0,1]) into the four intervals

\[
\left[0,\frac14\right],\quad
\left[\frac14,\frac12\right],\quad
\left[\frac12,\frac34\right],\quad
\left[\frac34,1\right].
\]

For (j=0,1,2,3), let (L_{j,n}) be the affine chord joining the values of
(Q_n) at (j/4) and ((j+1)/4).  Convexity and (47)--(48) give

\[
0\le Q_n(t)\le L_{j,n}(t)\le1
\qquad\left(\frac j4\le t\le\frac{j+1}4\right).
\tag{53}
\]

Put

\[
k_n:=\left\lfloor\frac{n-4}{2}\right\rfloor
=\frac{n-4}{2}\quad\hbox{using natural-number division}.
\]

Since the bases lie in ([0,1]),

\[
Q_n(t)^{(n-4)/2}\le L_{j,n}(t)^{k_n}.
\tag{54}
\]

For even (n) this only uses (Q_n\le L_{j,n}); for odd (n), it also uses
(x^{k+1/2}\le x^k) on (0\le x\le1).  Therefore

\[
I_n(\alpha)\le
\sum_{j=0}^3
\int_{j/4}^{(j+1)/4}t^3L_{j,n}(t)^{k_n}\,dt.
\tag{55}
\]

This is useful computationally because (L_{j,n}) is affine.  If
(L(t)=u+vt), one may expand

\[
\int_a^bt^3(u+vt)^k\,dt
=\sum_{\ell=0}^k {k\choose\ell}u^{k-\ell}v^\ell
 \frac{b^{\ell+4}-a^{\ell+4}}{\ell+4}.
\tag{56}
\]

Thus a generated expression has (O(k)), rather than (O(k^2)), summands.
This directly avoids the 676-term quadratic-moment expansion that exhausted
the heartbeat limit at (n=53).  A constant-size endpoint-power formula is
also available after substituting (y=u+vt), but it divides by (v^4) and
therefore requires a separate (v=0) case; (56) is safer initially.

Floating-point tests, restricted to the feasibility region (c_n^2\le A_n),
give the following maxima for the right-hand side obtained from (55):

\[
\begin{array}{c|c}
n&\hbox{maximum of the four-chord upper bound}\\ \hline
6&0.652\\
7&0.885\\
20&0.607\\
40&0.804\\
50&0.901\\
51&0.975\\
52&0.920\\
53&0.989\\
54&0.924\\
55&0.987\\
60&0.864\\
70&0.674\\
97&0.340.
\end{array}
\]

Again, these values are non-rigorous diagnostics.  They suggest that the
four-chord bound may already prove `stat` impossible for every (n\ge6);
degree (5) loses too much in (54) and should retain the existing tunable
tangent argument.

There are two ways to exploit (55):

1. **Engineering-only improvement.**  Generate a Bernstein certificate for
   the four-chord upper bound at each remaining degree.  This does not lower
   the formal cutoff by itself, but it replaces the problematic quadratic
   moment expansion by four linear-power expansions.  The already successful
   Bernstein and `ring` layers can remain unchanged.
2. **Genuine hybrid.**  Prove that the four-chord upper bound is
   parity-wise decreasing after (n=53), and certify only (n=53,54).
   Formula (46) implies that every chord (L_{j,n+2}) is pointwise no larger
   than (L_{j,n}), while (k_{n+2}=k_n+1).  The only remaining difficulty is
   to show that the resulting decay beats the increase in (P_n).  This is a
   simpler algebraic problem than (52?), because all four integrals have the
   explicit form (56).

A reasonable Lean decomposition is:

```lean
def node (j : ℕ) : ℝ := (j : ℝ) / 4

def chordQ (n j : ℕ) (α t : ℝ) : ℝ :=
  (node (j + 1) - t) * 4 * Q n α (node j) +
  (t - node j) * 4 * Q n α (node (j + 1))

lemma Q_le_chordQ
    (hj : j < 4) (ht : t ∈ Set.Icc (node j) (node (j + 1)))
    (hA : 0 ≤ A n α) :
    Q n α t ≤ chordQ n j α t := by
  -- For a quadratic, chordQ - Q is an explicit nonnegative multiple
  -- of (t-node j)*(node (j+1)-t).
  ...

lemma chordQ_mem_Icc ... :
    chordQ n j α t ∈ Set.Icc (0 : ℝ) 1 := by
  ...

lemma rpow_le_chord_natPow ... :
    Real.rpow (Q n α t) (((n : ℝ) - 4) / 2) ≤
      chordQ n j α t ^ ((n - 4) / 2) := by
  -- In actual code, parenthesize the Real.rpow exponent explicitly;
  -- the displayed syntax here is schematic.
  ...

lemma integral_affine_pow ... :
    ∫ t in a..b, t^3 * (u + v*t)^k =
      ∑ ℓ in Finset.range (k + 1),
        (Nat.choose k ℓ : ℝ) * u^(k-ℓ) * v^ℓ *
          (b^(ℓ+4) - a^(ℓ+4)) / (ℓ+4) := by
  ...

lemma exact_moment_le_four_chords ... :
    I n α ≤ chordMomentBound n α := by
  ...
```

Be careful not to write `Q n α t ^ ((n : ℝ) - 4) / 2` when the intention is
`Real.rpow (Q n α t) (((n : ℝ) - 4) / 2)`: ordinary `^` and `/` would parse
differently.  Keeping the exact moment and the natural-power chord moment as
different definitions will prevent this class of error.

### 9.4 Exponential-secant fallback

A second fallback starts from

\[
Q_n(t)^{(n-4)/2}
\le
\exp\left(\frac{n-4}{2}\bigl(-2c_nt+A_nt^2\bigr)\right),
\tag{57}
\]

using (log x\le x-1).  Majorize the convex quadratic exponent by affine
secants and integrate (t^3e^{ut+v}) explicitly.  Floating-point tests suggest
cutoffs near

\[
\begin{array}{c|c}
\hbox{equal secant intervals}&\hbox{approximate cutoff}\\ \hline
2&n\ge84\\
4&n\ge71\\
8&n\ge67.
\end{array}
\]

This would reduce the largest finite Bernstein degree from about (96) to
about (68) with four intervals.  Nevertheless, (55) is probably preferable
in Lean because it avoids `Real.exp` and transcendental endpoint estimates.

## 10. Recommended implementation order

1. Keep the proved (n>100) theorem from Sections 1--8 intact as the fallback.
2. Prove (44), (46), (47), and (48) in a small file.  These are reusable and
   should be inexpensive.
3. Spend a bounded amount of time on the exact two-step lemma (52?).  If it
   succeeds, combine it with the existing (n=53,54) certificates and stop.
4. If (52?) stalls, formalize the generic four-chord majorant (53)--(56).
   First regenerate (n=53) and (n=54) using this majorant and verify the
   numerical generator against direct quadrature at several rational values
   of (alpha).
5. Attempt parity-wise monotonicity of the four-chord bound.  If this also
   stalls, use the chord bound merely to generate the degrees (54,ldots,100):
   it removes the present `mom` expansion bottleneck even though it does not
   lower the analytic cutoff.
6. Only then consider the exponential-secant route.
7. For every generated degree, independently compare the generated rational
   function with direct high-precision evaluation before committing the Lean
   file.  This is a diagnostic against generator errors, not part of the proof.
8. Finish with `#print axioms` on the theorem that combines the finite and
   analytic ranges.  It should contain no `sorryAx`, project-defined axiom,
   `native_decide`, or unverified external certificate oracle.
