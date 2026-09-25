import random, io, contextlib, collections
from lay import *
from design8 import sidon_increasing
rng=random.Random(4); cnt=collections.Counter(); ex=[]
for trial in range(1500):
    G=rng.randint(3,16); ncl=rng.randint(1,5)
    eps=sorted(rng.sample(range(1,G),min(ncl,G-1)))
    Y=sidon_increasing(len(WIRES),rng,rng.randint(1,5))
    Bp=2*max(Y)+1+rng.randint(0,12); B=G*Bp
    res={w:G*y for w,y in zip(WIRES,Y)}; clk=rng.choice(eps)
    f=io.StringIO()
    with contextlib.redirect_stdout(f): out=check2(res,eps,clk,B,verbose=True)
    m=f.getvalue().strip(); k=m.split()[0] if m else ('OK' if out else 'other'); cnt[k]+=1
    if len(ex)<8 and k in('uncovered','hits'): ex.append((G,eps,clk,Y,B,m))
print(cnt)
for e in ex: print(e)
