import random, io, contextlib, collections
from lay import *
def sidon_increasing(n, rng, spread):
    Y=[0]; D=set()
    while len(Y)<n:
        c=Y[-1]+1
        while True:
            nd=[c-y for y in Y]
            if all(d not in D for d in nd) and len(set(nd))==len(nd): break
            c+=1+rng.randrange(0,spread)
        for d in nd: D.add(d); D.add(-d)
        Y.append(c)
    return Y
rng=random.Random(2); cnt=collections.Counter(); ex=[]
for trial in range(2000):
    G=rng.randint(3,14); ncl=rng.randint(1,4)
    eps=sorted(rng.sample(range(1,G),min(ncl,G-1)))
    Y=sidon_increasing(len(WIRES),rng,rng.randint(1,5))
    Bp=2*max(Y)+1+rng.randint(0,12); B=G*Bp
    res={w:G*y for w,y in zip(WIRES,Y)}; clk=rng.choice(eps)
    f=io.StringIO()
    with contextlib.redirect_stdout(f): out=check(res,eps,clk,B,verbose=True)
    m=f.getvalue().strip(); k=m.split()[0] if m else 'OK'; cnt[k]+=1
    if k=='uncovered' and len(ex)<6: ex.append((G,eps,clk,Y,B,m))
print(cnt)
for e in ex: print(e)
