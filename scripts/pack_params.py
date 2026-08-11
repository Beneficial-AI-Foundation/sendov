#!/usr/bin/env python3
"""Numerical parameters for the packed moment computation, one set per degree.

Emits the two Kronecker bases used by Sendov/FiniteRange/PackBridge.lean:
  beta -- packs a coefficient polynomial in alpha into one integer
  tau  -- packs the resulting row, a polynomial in t, into one integer
together with L = lcm(4 .. 2k+4), which clears the 1/(j+4) weights of irow.

These are the values that discharge the overflow hypotheses of unpackZ_pevZ.
"""
from math import lcm
# Numerical parameters for the packed moment computation, per degree.
#   L1  = sum of |coefficients| of g0,g1,g2  (bounds every coefficient of the k-th power)
#   L   = lcm(4 .. 2k+4)                     (clears the 1/(j+4) weights)
#   beta > 2 * max|moment-numerator coefficient|  <= 2 * (2k+1) * (L/4) * L1^k
#   tau  > 2 * max|alpha-packed row entry|        <= 2 * L1^k * (beta^(2k+1)-1)/(beta-1)
def params(n, k):
    M = n - 1
    L1 = 8*M + (12*M + abs(12-2*M) + 4) + (6*M + abs(2*M-12) + 4)      # = 30M - 16
    L  = lcm(*range(4, 2*k+5))
    coefmax = L1**k
    nmommax = (2*k+1) * (L//4 + 1) * coefmax
    beta = 2*nmommax + 1
    packmax = coefmax * ((beta**(2*k+1) - 1)//(beta-1) + 1)
    tau = 2*packmax + 1
    G_bits = (tau**2).bit_length() + max(x.bit_length() for x in [L1])
    return L1, L, beta, tau, G_bits, k
print(f"{'n':>4} {'k':>3} {'L1':>6} {'L bits':>7} {'beta bits':>10} {'tau bits':>10} {'G^k bits':>10} {'G^k MB':>8}")
for n, k in [(20,8),(53,24),(53,25),(97,46),(97,47)]:
    L1, L, beta, tau, Gb, k = params(n, k)
    Gk = Gb * k
    print(f"{n:>4} {k:>3} {L1:>6} {L.bit_length():>7} {beta.bit_length():>10} "
          f"{tau.bit_length():>10} {Gk:>10} {Gk/8/1024/1024:>8.2f}")
print()
print("sanity: bound vs truth at n=53,k=24 (true max coeff measured earlier: 249 bits)")
L1,L,beta,tau,_,_ = params(53,24)
print(f"  L1^k = {(L1**24).bit_length()} bits (bound on any coefficient)")
print(f"  L = lcm(4..52) = {L.bit_length()} bits")
print(f"  beta = {beta.bit_length()} bits, tau = {tau.bit_length()} bits")
