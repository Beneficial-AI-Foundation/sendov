"""Generate a Lean file proving R n a < 1 for a batch n0 <= n <= n1  (n0 even)."""
import sys, io, sympy as sp
from math import lcm, comb
sys.set_int_max_str_digits(50000000)

def build(n0, n1):
    assert n0 % 2 == 0, "n0 must be even so the moment has an integer exponent"
    k = (n0-4)//2; M0, M1 = n0-1, n1-1; a = sp.symbols('alpha')
    # ---- packed moment data at n0 ----
    g0=[6*M0,2*M0]; g1=[-12*M0,12-2*M0,4]; g2=[6*M0,2*M0-12,-4]
    L1n = sum(abs(x) for x in g0+g1+g2); L = lcm(*range(4,2*k+5)); mlen = 1+3*k
    beta = 2*(L*L1n**k)+1; tau = 2*(L1n**k * beta**mlen)+1
    def padd(p,q):
        r=[0]*max(len(p),len(q))
        for i,x in enumerate(p): r[i]+=x
        for i,x in enumerate(q): r[i]+=x
        return r
    def pmul(p,q):
        if not p or not q: return []
        r=[0]*(len(p)+len(q)-1)
        for i,x in enumerate(p):
            if x:
                for j,y in enumerate(q): r[i+j]+=x*y
        return r
    row=[[1]]
    for _ in range(k):
        new=[[] for _ in range(len(row)+2)]
        for i,e in enumerate(row):
            for s,g in enumerate((g0,g1,g2)): new[i+s]=padd(new[i+s],pmul(g,e))
        row=new
    Nmom=[]
    for j,e in enumerate(row): Nmom=padd(Nmom,[(L//(j+4))*x for x in e])
    def pevZ(p,b):
        s=0
        for x in reversed(p): s=x+b*s
        return s
    Gv = pevZ(g0,beta)+pevZ(g1,beta)*tau+pevZ(g2,beta)*tau**2
    X = Gv**k
    blocks=[]; y=X
    for _ in range(2*k+1):
        r=y%tau; d=r if 2*r<tau else r-tau; blocks.append(d); y=(y-d)//tau
    assert sum((L//(j+4))*b for j,b in enumerate(blocks)) == pevZ(Nmom,beta)
    assert 2*max(abs(b) for b in blocks)<tau and 2*max(abs(x) for x in Nmom)<beta
    assert len(Nmom) <= mlen
    # ---- quadrature cross-check of the moment ----
    import numpy as np
    Xg,Wg = np.polynomial.legendre.leggauss(700); T=0.5*(Xg+1); Wg=0.5*Wg
    def pv(p,x):
        s=0.0
        for c in reversed(p): s=c+x*s
        return s
    for al in [0.0, 9.0, 17.0]:
        Mf=float(M0); A=1-2*al/Mf; c=1-al/Mf-al/(2*(3+al)); Qv=np.maximum(1-2*c*T+A*T*T,0)
        quad=np.sum(Wg*T**3*Qv**k)
        mine=pv([float(x) for x in Nmom],al)/(float(L)*(2*Mf*(3+al))**k)
        assert abs(mine-quad) < 1e-8*abs(quad), f"quadrature mismatch at alpha={al}"
    # ---- the batch bound, exactly ----
    Nm = sum(sp.Integer(x)*a**i for i,x in enumerate(Nmom))
    I0 = Nm/(sp.Integer(L)*(sp.Integer(2*M0)*(3+a))**k)
    bound = (sp.Rational(1,6) + sp.Rational(1,4)/(3+a) + sp.Rational(1,2*M0)
             + sp.Rational(1,4*M0)/(3+a)
             + (1-sp.Rational(2,M1)*a)**2*sp.Integer(n1*M1*(n1-2))*sp.Rational(1,4)/(3+a)*I0)
    num, den = sp.fraction(sp.cancel(sp.together(1-bound)))
    nums = sp.Poly(sp.expand(num), a); dens = sp.Poly(sp.expand(den), a)
    assert all(c.is_Rational for c in nums.all_coeffs()+dens.all_coeffs())
    scale = sp.ilcm(*[sp.Rational(c).q for c in nums.all_coeffs()+dens.all_coeffs()])
    nums = sp.Poly(sp.expand(num*scale), a); dens = sp.Poly(sp.expand(den*scale), a)
    cf = [sp.Integer(c) for c in nums.all_coeffs()][::-1]
    p = dens.degree(); const = sp.Integer(dens.all_coeffs()[0])
    assert sp.expand(dens.as_expr() - const*(3+a)**p) == 0
    d = nums.degree()
    G = [sum(cf[i]*comb(d-i,j-i)*17**i for i in range(j+1)) for j in range(d+1)]
    assert all(g>0 for g in G), "Bernstein certificate not all-positive"
    def ev(cs,x):
        s=sp.Integer(0)
        for c in reversed(cs): s=c+x*s
        return s
    for v in [sp.Rational(1,2), sp.Integer(7), sp.Integer(17)]:
        assert sp.simplify((1-bound).subs(a,v) - ev(cf,v)/(const*(3+v)**p)) == 0
    # ---- feasibility quartic at n0 ----
    c0s = 1 - a/M0 - a/(2*(3+a)); A0s = 1 - 2*a/M0
    feas = sp.Poly(sp.expand(sp.cancel((A0s - c0s**2)*(2*M0*(3+a))**2)), a)
    cnum = sp.Poly(sp.expand(sp.cancel(c0s*(2*M0*(3+a)))), a)
    print(f"[{n0},{n1}] k={k} degP={d} pole={p} Nmom={len(Nmom)} beta={beta.bit_length()}b "
          f"tau={tau.bit_length()}b G^k={X.bit_length()}b  ALL CHECKS PASS")
    return dict(n0=n0,n1=n1,k=k,M0=M0,M1=M1,L=L,beta=beta,tau=tau,Nmom=Nmom,mlen=mlen,
                cf=cf,G=G,d=d,const=const,p=p,feas=feas.all_coeffs()[::-1],
                cnum=cnum.all_coeffs()[::-1])
if __name__ == "__main__":
    import pickle
    r = build(int(sys.argv[1]), int(sys.argv[2]))
    pickle.dump(r, open(f"batch_{sys.argv[1]}_{sys.argv[2]}.pkl","wb"))
