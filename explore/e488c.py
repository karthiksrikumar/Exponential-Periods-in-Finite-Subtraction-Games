# Exhaustive: all primitive A with max(A)<=n0 (A subset [2,n0]), all n in [maxA, n0], m up to Mmax.
# Check sharp form (n+1) f(m) <= 2 m f(n).
import numpy as np, sys
n0=int(sys.argv[1]); Mmax=int(sys.argv[2])
divs=[[d for d in range(2,k) if k%d==0] for k in range(n0+1)]
worst=[]
cnt=0
def rec(start, A):
    global cnt
    if A:
        cnt+=1
        mark=np.zeros(Mmax+1,dtype=np.int32)
        for a in A: mark[a::a]=1
        f=np.cumsum(mark); m=np.arange(Mmax+1)
        D=np.zeros(Mmax+1); D[1:]=f[1:]/m[1:]
        suf=np.maximum.accumulate(D[::-1])[::-1]
        mx=max(A)
        ns=np.arange(mx,n0+1)
        r=suf[ns+1]*(ns+1)/(2*f[ns])
        k=int(np.argmax(r))
        worst.append((float(r[k]),tuple(A),int(ns[k])))
    for x in range(start,n0+1):
        if any(x%a==0 for a in A): continue
        rec(x+1,A+[x])
rec(2,[])
worst.sort(reverse=True)
print('sets',cnt)
for w in worst[:10]: print(w)
print('non-singleton:')
for w in [w for w in worst if len(w[1])>1][:10]: print(w)
