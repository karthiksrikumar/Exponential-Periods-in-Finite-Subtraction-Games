import random, sys, json, itertools
from design3 import check
from design2 import CIRCUIT, WIRES
def sidon_increasing(n, rng, spread, start=0):
    Y=[start]; D=set()
    while len(Y)<n:
        c=Y[-1]+1
        while True:
            c+=rng.randrange(0,spread)
            nd=[c-y for y in Y]
            if all(d not in D for d in nd) and all(-d not in D for d in nd) and len(set(nd))==len(nd): break
            c+=1
        for d in nd: D.add(d); D.add(-d)
        Y.append(c)
    return Y
rng=random.Random(int(sys.argv[1])); best=None
for trial in range(int(sys.argv[2])):
    G=rng.randint(4,14); ncl=rng.randint(1,4)
    eps=sorted(rng.sample(range(1,G),min(ncl,G-1)))
    Y=sidon_increasing(len(WIRES),rng,rng.randint(1,6))
    Bp=2*max(Y)+1+rng.randint(0,10); B=G*Bp
    res={w:G*y for w,y in zip(WIRES,Y)}
    out=check(res,eps,B)
    if out:
        intended,cover=out; ncov=len(set(cover.values())); tot=len(intended)+ncov
        if best is None or tot<best[0]:
            best=(tot,B,G,eps,res,cover); print('OK |S|=%d B=%d G=%d eps=%s Y=%s'%(tot,B,G,eps,Y),flush=True)
if best:
    tot,B,G,eps,res,cover=best
    json.dump({'B':B,'res':res,'clocks':eps,'cover':{str(k):v for k,v in cover.items()}},open('best_layout.json','w'))
