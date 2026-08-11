# Sendov finite-range formalization — design notes

A standing record of what this project is, what is proved, what is open, and why the
architecture is what it is.  Written to be read cold, including by a reviewer who has not
seen the code.  Numbers here were measured on this project's actual shapes, not estimated;
several of them overturned a design that looked obviously right on paper.

Machine: Windows 11, Lean 4.34.0-rc1, mathlib pinned in `lake-manifest.json`.  Timings
include Lean startup (~1.5–2 s) unless stated otherwise.

---

## 1. The claim

From the blog post *A digestion of the proof of Sendov's conjecture*.  After the polynomial
argument, one inequality — equation `stat` — remains unproved on a finite range.  Writing
`M = n-1`, `A = a² = 1 - 2α/M`, `c = 1 - α/M - α/(2(3+α))`, `Q(t) = 1 - 2ct + At²`,
`B = α/(3+α)`, the claim is that

```
R n α = 1/6 + 1/(4(3+α)) + 1/(2M) + 1/(4M(3+α))
          + A² n M (n-2)/(4(3+α)) · ∫₀¹ t³ Q(t)^((n-4)/2) dt
```

satisfies `R n α < 1` on `5 ≤ n ≤ 97`, `0 ≤ α ≤ 17`, subject to the feasibility constraint
`c² ≤ A`.  (`n ≥ 98` is handled by a separate analytic argument; see §6.)  The exponent is a
*real* exponent — half-integral for odd `n` — so `Real.rpow` is involved.

`Sendov/Statement.lean` states exactly this with one `sorry`, and derives the `False` form in
which it is applied.  That file is the audit surface: everything else exists to discharge it.

**Numerically**, `R` attains max `0.8529` at `n = 53, α = 17`.  So a bound may lose ~15% and
still succeed — a fact that matters repeatedly below.

---

## 2. Status

| component | file | state |
|---|---|---|
| Claim statement | `Statement.lean` | 1 `sorry` (the goal) |
| Basic properties | `FiniteRange/Basic.lean` | proved |
| Moment formula (M) | `FiniteRange/Moments.lean` | proved |
| Odd-degree bound | `FiniteRange/OddBound.lean` | proved |
| Per-degree reduction | `FiniteRange/Reduce.lean` | proved |
| Degrees 5, 6, 7, 8, 20 | `FiniteRange/Degree*.lean` | proved, no `sorryAx` |
| Moment recurrence | `FiniteRange/Recurrence.lean` | proved; too slow to use (§4) |
| Kronecker packing core | `FiniteRange/Pack.lean` | proved |
| Beta integral (n ≥ 98) | `LargeDegree/Beta.lean` | proved |
| Certificate generator | `scripts/gen_degree.py` | untrusted, self-checking |

Open: the packing bridge (§7), degrees 9–97, and the analytic `n ≥ 98` argument beyond its
Beta core.

---

## 3. The reduction chain

Each degree reduces to polynomial positivity in `α` alone:

1. **`R_le_of_integral_le`** — the coefficient of the integral in `R` is nonnegative, so any
   upper bound `J` for the integral bounds `R`.
2. **Even `n`** — `integral_eq_mom`: the integral *equals* the moment `mom n α k`, `k=(n-4)/2`.
   No hypotheses at all; it is a polynomial identity.
   **Odd `n`** — `integral_rpow_le`: `√q ≤ q/(2w) + w/2` (the tangent to `√·` at `q = w²`)
   turns `Q^(k+1/2)` into a combination of `mom n α k` and `mom n α (k+1)`, for any `w > 0`.
3. **`alpha_le_half_M`** — feasibility gives `α ≤ (n-1)/2`, the only numerical input needed.
4. Clear denominators: `1 - R n α = P n (α) / D n (α)` with `D > 0`, `deg P = n - 2`.
5. **Bernstein certificate** — `U^d · P(α) = Σⱼ Γⱼ αʲ (U-α)^(d-j)` with all `Γⱼ > 0`, whence
   `P > 0` on `[0, U]`.

### Simplifications found along the way

- **The tangent parameter `w` unifies degree 5.** The plan gave `n = 5` its own apparatus
  (chord bound, `H(B)` in half-integer powers of `B`, the substitution `α = 3r²/(1-r²)`)
  because bound (O) is too wasteful there. True — (O) gives `1.0625` at `α = 0`, proving
  nothing — but the cause is narrow: (O) is the tangent taken at `q = 1`, and in degree 5 the
  relevant `Q` values are small. Taking `w = 1/3` instead gives `0.737` against the exact
  `0.716`. All odd degrees now share one code path and no square roots survive.
- **No subdivision.** One Bernstein certificate on the whole interval has all coefficients
  positive at every degree tested (20, 53, 97). The plan's adaptive bisection is unnecessary.
- **No infeasibility branch.** Only the numerical step needs feasibility, and only as
  `α ≤ (n-1)/2`. The exact feasible region (cut out by a quartic) is never required. This is
  *not* the claim that `A ≥ 0` replaces feasibility: the odd-degree bound needs `0 ≤ Q` on
  `[0,1]`, which is `Q_nonneg` and uses the full `c² ≤ A`.
- **Beta, not Gamma.** For `n ≥ 98` the write-up bounds the tail by `Q ≤ exp(-ct)` and the
  Gamma integral. Keeping the chord as a *power* instead gives
  `∫₀¹ t³(1-t)ˢ dt = 6/((s+1)(s+2)(s+3)(s+4))` — no improper integral, no `Real.exp`, and
  strictly sharper, so every constant downstream survives unchanged.

---

## 4. Computing the moment: representation, not algorithm

`∫₀¹ t³ Qᵏ dt` is the bottleneck. The multinomial formula (M) has `Θ(k²)` terms and its
`simp` expansion dies around `k = 20` — at `n = 53` the 676-term expansion exhausts 2 M
heartbeats. `Recurrence.lean` replaces it with the coefficient recurrence
`R(k+1,j) = g₀R(k,j) + g₁R(k,j-1) + g₂R(k,j-2)`, where `D·Q = g₀ + g₁t + g₂t²` with
`D = 2(n-1)(3+α)` and the `gᵢ` integer polynomials in `α`. That is correct but still slow:

| representation | k=24 | k=32 | k=46 |
|---|---|---|---|
| `List (List ℤ)` (`Recurrence.lean`) | 120 s | >20 min | hours |
| 1-D packed, `List ℤ` | — | — | 158 s |
| 2-D packed, single `Nat` (`Pack.lean`) | — | — | ~0.5 s |

Kernel `Nat` arithmetic is GMP-backed — a 4000-digit multiplication and a 50th power are
milliseconds — while list recursion is interpreted at roughly 240 µs per coefficient
operation. `qrow` was never the wrong *algorithm*; it was the wrong *representation*. Under
Kronecker packing (evaluate at a base exceeding every coefficient) polynomial multiplication
becomes `Nat` multiplication and the whole recurrence becomes `base ^ k`, one exponentiation.

Measured end to end through the verified `unpackN`: one exponentiation to a 3,042,311-bit
number plus extraction of all 93 coefficients, **7 s**.

### Numerical parameters

Two bases are needed per degree: `β` packs a coefficient polynomial in `α`, `τ` packs the
resulting row in `t`.  With `L1 = 30(n-1) - 16` (the sum of `|coefficients|` of `g₀,g₁,g₂`,
which bounds every coefficient of the `k`-th power) and `L = lcm(4 .. 2k+4)` (clearing the
`1/(j+4)` weights):

```
β > 2 · (2k+1) · (L/4) · L1^k        -- fits the moment numerator's coefficients
τ > 2 · L1^k · (β^(2k+1) - 1)/(β-1)  -- fits the α-packed row entries
```

| n | k | L1 | L | β | τ | `G^k` |
|---|---|---|---|---|---|---|
| 20 | 8 | 554 | 28 b | 104 b | 1,735 b | 0.003 MB |
| 53 | 24 | 1544 | 72 b | 331 b | 16,107 b | 0.09 MB |
| 97 | 47 | 2864 | 136 b | 681 b | 64,554 b | 0.72 MB |

Verified at `n = 53` with the real `g` coefficients: the `τ` bound holds, and the kernel
computes `G^24` (788,991 bits) and extracts all 49 α-packed row entries in **9 s** including
Lean startup.

### The packing bound is essentially free

`unpackN_pow` requires `(npev p 1)ᵏ < b`, the sum of coefficients to the `k`-th power.
Against the true maximum coefficient:

| n | k | true max | bound `L1ᵏ` | slack | packed size |
|---|---|---|---|---|---|
| 53 | 24 | 249 b | 255 b | 6 b | 0.07 MB |
| 97 | 46 | 522 b | 529 b | 7 b | 0.54 MB |

5–7 bits, under 1.5% of block size. Take `B = bitlength(L1ᵏ) + 1` with `L1 = 30(n-1) - 16`;
no per-degree tuning, packed objects under 0.6 MB.

---

## 5. `ring` costs, and the build budget

| task | time | peak memory |
|---|---|---|
| Bernstein identity, degree 18 (n=20) | ~12 s | small |
| Bernstein identity, degree 52 (n=53) | ~99 s | — |
| Bernstein identity, degree 96 (n=97) | 129 s | ~4 GB |
| 8-chord moment identity, degree 48 (n=53) | never finished | >10 GB, killed |

`ring` handles the Bernstein identity at every degree needed, so the certificate layer needs
no packing. Two consequences: roughly **3 hours** for 93 degrees, and **4 GB peaks**, so
high-degree files must not compile in parallel.

The last row is why the moment is not expanded symbolically: Bernstein terms are
`Γⱼ αʲ (U-α)^(d-j)`, one binomial expansion each, whereas chord terms are products of two
different high-degree powers. Same degree, entirely different cost.

---

## 6. Approaches measured and rejected

- **Interval arithmetic in `α`.** Needs ~200 α-boxes at `n = 53` (`p=8,N=60` still gives
  1.0999); the `m`-th power amplifies interval loss.
- **Extending the analytic `n ≥ 98` argument downward.** Its bound bottoms out at exactly
  `n = 98`; the Beta improvement lowers `U₅₄` from 2.10 to 1.88, nowhere near 1.
- **Monotonicity `R_{n+2} ≤ R_n`.** True — verified over `53 ≤ n ≤ 95`, and `R_{n+1} ≤ R_n`
  too — but the minimum relative margin is **1.48%** at `(53, 17)`, while proving `R_n < 1`
  directly allows ~15%. Monotonicity demands ten times the sharpness of the actual goal, and
  a chord-based sufficient condition loses 10%. Rejected on those grounds, not on difficulty.
- **Endpoint-power chord integrals.** ~8× algorithmically, but introduces `v⁴` denominators,
  `v = 0` case splits *inside* the feasible region, and raises `deg P` from ~96 to ~164.
  Superseded by packing, which is faster and touches nothing.

---

## 7. Open work

1. **Packing bridge.** Signed coefficients: *done* — `unpackZ_pevZ` recovers a `ℤ`-polynomial
   from its packed value by balanced-digit extraction, under `2|c| < b`.  Still to do:
   connect the packed computation to `qrow`/`rev` so `integral_moment_of` applies unchanged,
   and assemble the moment `Σⱼ R(k,j)/(j+4)`.
2. **Degrees 9–97**, generated and checked; validate each new path against an
   already-proved degree before bulk generation.
3. **Composition** of 93 degrees into `finite_range` — a balanced dispatch tree, not one
   `interval_cases`.
4. **Analytic `n ≥ 98`**: the tail assembly, discrete monotonicity in `n`, the reduction at
   `n = 101`, `α`-monotonicity, and the endpoint estimates. Its arithmetic has been verified
   externally (the degree-8 expansion, the SOS identity, all six endpoint estimates); the
   tightest is `T̃₂(17) = 0.55719` against `279/500`, 0.15% of room, so that step must use the
   exact rational.
5. **Audit**: `#print axioms`, forbidden-token grep, clean rebuild from the pinned toolchain,
   and a mutation test — corrupt one certificate coefficient and confirm the build fails.

---

## 8. Trust policy

No `sorry` (outside the stated goal), no `axiom`, no `native_decide`, no `unsafe`, no
floating point in any statement or proof. `maxHeartbeats` / `maxRecDepth` are raised in
generated files; these are resource knobs, not escape hatches, and are recorded here
deliberately.

`scripts/gen_degree.py` is untrusted: Lean re-derives `P n` and checks the Bernstein identity
with `ring`, so a corrupted coefficient fails the build. Its `--check` mode compares against
numerical quadrature, and that check has already caught a real bug — a dropped `2ˡ` in
`(-2c)ˡ` produced a `P` wrong by sign and scale which nevertheless admitted a Bernstein
representation, with every coefficient negative. **Positivity of a certificate is not
evidence that `P` is right**; only agreement with an independent evaluation is. Two
generators written in this project were silently wrong and caught only this way.
