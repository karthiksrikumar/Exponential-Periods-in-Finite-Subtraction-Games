import itertools, numpy as np, random
def worst(A, M):
    mark = np.zeros(M+1, dtype=np.int64)
    for a in A: mark[a::a] = 1
    f = np.cumsum(mark); x=np.arange(M+1)
    D = np.zeros(M+1); D[1:] = f[1:]/x[1:]
    suf = np.maximum.accumulate(D[::-1])[::-1]
    a0=max(A); best=0; arg=None
    for n in range(a0, M):
        r = suf[n+1]*(n+1)/(2*f[n])   # test D(m) <= 2 f(n)/(n+1)
        if r>best: best=r; arg=(n, f[n])
    return best,arg
res=[]
for size in range(1,5):
    for A in itertools.combinations(range(2,26), size):
        r,arg=worst(A, 6*max(A)+30); res.append((r,A,arg))
res.sort(reverse=True)
for t in res[:12]: print(t)
random.seed(2)
for _ in range(20000):
    k=random.randint(2,8); A=tuple(sorted(random.sample(range(2,120),k)))
    r,arg=worst(A,4*max(A)+30); res.append((r,A,arg))
res.sort(reverse=True)
print('random'); 
for t in res[:8]: print(t)
print('size>=2 best')
for t in [t for t in res if len(t[1])>=2][:10]: print(t)
