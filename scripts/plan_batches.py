import numpy as np, sympy as sp
X,W = np.polynomial.legendre.leggauss(800); T=0.5*(X+1); W=0.5*W
def base(n, al):
    M=n-1.0; return 1/6+1/(4*(3+al))+1/(2*M)+1/(4*M*(3+al))
def pref(n, al):
    M=n-1.0; A=1-2*al/M; return A**2*n*M*(n-2)/(4*(3+al))
def I(n, al):
    M=n-1.0; A=1-2*al/M; c=1-al/M-al/(2*(3+al))
    return np.sum(W*T**3*np.maximum(1-2*c*T+A*T*T,0.0)**((n-4)/2))
def batch_max(n0, n1):
    amax = min(17.0, (n1-1)/2); best = 0.0
    for al in np.linspace(0, amax, 400):
        if 1-2*al/(n0-1.0) < 0: continue
        best = max(best, base(n0, al) + pref(n1, al)*I(n0, al))
    return best
a = sp.symbols('alpha')
def bern_ok(n0, n1):
    M0=sp.Integer(n0-1); M1=sp.Integer(n1-1); k0=(n0-4)//2
    A0=1-2*a/M0; c0=sp.cancel(1-a/M0-a/(2*(3+a))); A1=1-2*a/M1
    mom = sum(sp.binomial(k0,i)*sp.binomial(i,l)*(-2*c0)**l*A0**(i-l)/sp.Integer(2*i-l+4)
              for i in range(k0+1) for l in range(i+1))
    R = (sp.Rational(1,6)+1/(4*(3+a))+1/(2*M0)+1/(4*M0*(3+a))
         + A1**2*n1*M1*(n1-2)/(4*(3+a))*mom)
    num, _ = sp.fraction(sp.cancel(sp.together(1-R)))
    P = sp.Poly(sp.expand(num), a); d = P.degree()
    cf = [sp.Integer(x) for x in P.all_coeffs()][::-1]
    U = sp.Rational(17) if sp.Rational(17) <= sp.Rational(n1-1,2) else sp.Rational(n1-1,2)
    p_,q_ = U.p, U.q
    G = [sum(cf[i]*q_**(j-i)*sp.binomial(d-i,j-i)*p_**i for i in range(j+1)) for j in range(d+1)]
    return d, all(g>0 for g in G), sum(1 for g in G if g<=0)
def plan(th):
    n0=6; out=[]
    while n0 <= 97:
        n1=n0
        while n1+1 <= 97 and batch_max(n0,n1+1) < th: n1 += 1
        out.append((n0,n1,batch_max(n0,n1))); n0=n1+1
        if n0 % 2 == 1: n0 += 1
    return out
p = plan(0.95); p.sort(key=lambda x:-x[2])
print("tightest batches in the 0.95 plan (Bernstein checked):")
for n0,n1,b in p[:6]:
    d, ok, neg = bern_ok(n0,n1)
    print(f"  [{n0},{n1}] bound={b:.4f} degP={d} certificate={ok}" + (f" ({neg} bad)" if not ok else ""))
