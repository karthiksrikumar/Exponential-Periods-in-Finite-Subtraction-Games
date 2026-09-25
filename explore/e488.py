# Quick search for counterexamples to Erdos 488: f(m)/m >= 2 f(n)/n with m>n>=max(A)
import itertools, random, numpy as np
from fractions import Fraction
def best_ratio(A, M):
    mark = np.zeros(M+1, dtype=np.int64)
    for a in A: mark[a::a] = 1
    f = np.cumsum(mark)  # f[x] = |B cap [1,x]|
    x = np.arange(M+1); 
    D = np.zeros(M+1); D[1:] = f[1:]/x[1:]
    a0 = max(A)
    # for each n>=a0 need max_{m>n} D[m]; suffix max
    suf = np.maximum.accumulate(D[::-1])[::-1]
    best=0; arg=None
    for n in range(a0, M):
        r = suf[n+1]/D[n]
        if r>best: best=r; arg=n
    return best,arg
random.seed(1)
top=[]
N=40
for size in range(1,4):
    for A in itertools.combinations(range(2,N+1), size):
        r,n = best_ratio(A, 4*max(A)+50)
        top.append((r,A,n))
top.sort(reverse=True)
for t in top[:15]: print(t)
print('--- size>=2')
for t in [t for t in top if len(t[1])>=2][:15]: print(t)
