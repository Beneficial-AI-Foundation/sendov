import sys, io
from math import lcm
sys.set_int_max_str_digits(4000000)
n, k = 53, 24; M = n-1; G = 3
g0 = [6*M, 2*M]; g1 = [-12*M, 12-2*M, 4]; g2 = [6*M, 2*M-12, -4]
L1 = sum(abs(c) for c in g0+g1+g2)
L  = lcm(*range(4, 2*k+5))
mlen = 1 + G*k                                  # provable entry-length bound
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
lhs = sum((L//(j+4))*b for j,b in enumerate(blocks))
print("L1 =", L1, " mlen =", mlen, " Nmom len =", len(Nmom))
print("packed check :", lhs == pevZ(Nmom, beta))
print("beta bits    :", beta.bit_length(), " tau bits:", tau.bit_length(), " G^k bits:", X.bit_length())
print("bounds hold  : tau", 2*max(abs(b) for b in blocks) < tau,
      "| beta", 2*max(abs(c) for c in Nmom) < beta,
      "| lenN", len(Nmom) <= mlen)
# validate the moment against quadrature
import numpy as np
Xg,Wg = np.polynomial.legendre.leggauss(600); T=0.5*(Xg+1); Wg=0.5*Wg
def pv(p,x):
    s=0.0
    for c in reversed(p): s=c+x*s
    return s
ok=True
for al in [0.0, 7.0, 17.0]:
    Mf=float(M); A=1-2*al/Mf; c=1-al/Mf-al/(2*(3+al)); Q=np.maximum(1-2*c*T+A*T*T,0)
    quad=np.sum(Wg*T**3*Q**k)
    mine=pv([float(x) for x in Nmom],al)/(float(L)*(2*Mf*(3+al))**k)
    ok &= abs(mine-quad) < 1e-9*abs(quad)
    print(f"  a={al:5.1f} packed={mine:.10e} quad={quad:.10e}")
print("quadrature agrees:", ok)
io.open("n53_data.txt","w").write(f"{L}\n{beta}\n{tau}\n{Nmom}\n{mlen}\n")
