import sympy as sp

j, a, k = sp.symbols('j a k', nonnegative=True)

def bern(expr, var, U, other):
    p = sp.Poly(sp.expand(expr), var); d = p.degree()
    cf = [p.coeff_monomial(var**i) for i in range(d+1)]
    G = [sp.expand(sum(cf[i]*sp.binomial(d-i, m-i)*U**i for i in range(m+1))) for m in range(d+1)]
    # identity check
    lhs = sp.expand(U**d*expr)
    rhs = sp.expand(sum(G[m]*var**m*(U-var)**(d-m) for m in range(d+1)))
    assert sp.expand(lhs-rhs) == 0, "Bernstein identity FAILED"
    return d, G

def show(name, expr, var, U, other):
    d, G = bern(expr, var, U, other)
    print(f"--- {name}: {U}^{d} * expr = sum_m G_m {var}^m ({U}-{var})^({d}-m) ---")
    for m, g in enumerate(G):
        gp = sp.Poly(g, other)
        neg = [c for c in gp.all_coeffs() if c < 0]
        print(f"  G[{m}] = {sp.expand(g)}")
        print(f"         {'all coefficients nonneg' if not neg else 'HAS NEGATIVE COEFFICIENTS'}")
    return G

N = 100 + j
Q = sp.expand(101*(100-2*a)**2*N*(N+3)*(N+5) - 100*100*103*105*(N-2*a)**2)
GQ = show("Q", Q, a, 17, j)
# the one bad coefficient: check its quadratic part is positive definite
g2 = sp.Poly(GQ[2]/12, j)
c3, c2, c1, c0 = g2.all_coeffs()
print(f"  G[2]/12 = {c3} j^3 + {c2} j^2 + {c1} j + {c0}")
print(f"  discriminant of the quadratic part = {c1**2 - 4*c2*c0}  (negative => positive definite)")
print(f"  4*{c2}*(that quadratic) = ({2*c2} j + {c1})^2 + {4*c2*c0 - c1**2}")

print()
n = 101 + k
S = sp.expand(13*(n-1-2*a)**2*(n-2)*n**2 - 12*(n-2*a)**2*(n+1)*(n-1)**2)
GS = show("S", S, a, 17, k)
