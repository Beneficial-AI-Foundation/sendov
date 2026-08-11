import sys, io
from math import lcm
sys.set_int_max_str_digits(20000000)
def build(n, k):
    M = n-1; G = 3
    g0 = [6*M, 2*M]; g1 = [-12*M, 12-2*M, 4]; g2 = [6*M, 2*M-12, -4]
    L1 = sum(abs(c) for c in g0+g1+g2)
    L  = lcm(*range(4, 2*k+5))
    mlen = 1 + G*k
    beta = 2*(L * L1**k) + 1
    tau  = 2*(L1**k * beta**mlen) + 1
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
            for s,g in enumerate((g0,g1,g2)): new[i+s]=padd(new[i+s], pmul(g,e))
        row=new
    Nmom=[]
    for j,e in enumerate(row): Nmom = padd(Nmom, [(L//(j+4))*c for c in e])
    def pevZ(p,b):
        s=0
        for c in reversed(p): s=c+b*s
        return s
    Gv = pevZ(g0,beta) + pevZ(g1,beta)*tau + pevZ(g2,beta)*tau**2
    X = Gv**k
    blocks=[]; y=X
    for _ in range(2*k+1):
        r=y%tau; d=r if 2*r<tau else r-tau; blocks.append(d); y=(y-d)//tau
    ok_pack = sum((L//(j+4))*b for j,b in enumerate(blocks)) == pevZ(Nmom, beta)
    ok_bounds = (2*max(abs(b) for b in blocks) < tau and 2*max(abs(c) for c in Nmom) < beta
                 and len(Nmom) <= mlen)
    import numpy as np
    Xg,Wg = np.polynomial.legendre.leggauss(700); T=0.5*(Xg+1); Wg=0.5*Wg
    def pv(p,x):
        s=0.0
        for c in reversed(p): s=c+x*s
        return s
    ok_quad=True
    for al in [0.0, 9.0, 17.0]:
        Mf=float(M); A=1-2*al/Mf; c=1-al/Mf-al/(2*(3+al)); Q=np.maximum(1-2*c*T+A*T*T,0)
        quad=np.sum(Wg*T**3*Q**k)
        mine=pv([float(x) for x in Nmom],al)/(float(L)*(2*Mf*(3+al))**k)
        ok_quad &= abs(mine-quad) < 1e-8*abs(quad)
    print(f"  n={n} k={k}: pack={ok_pack} bounds={ok_bounds} quad={ok_quad} "
          f"| beta {beta.bit_length()}b tau {tau.bit_length()}b G^k {X.bit_length()}b "
          f"({X.bit_length()/8/1024/1024:.2f} MB) Nmom len {len(Nmom)}")
    assert ok_pack and ok_bounds and ok_quad
    return L, beta, tau, Nmom, mlen
out = {}
for k in (46, 47):
    out[k] = build(97, k)
io.open("n97_data.txt","w").write(repr({k: (str(v[0]), str(v[1]), str(v[2]), v[3], v[4]) for k,v in out.items()}))
print("saved")
