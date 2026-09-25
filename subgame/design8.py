import random, sys, json
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
if __name__=='__main__':
    rng=random.Random(int(sys.argv[1])); best=None; nok=0
    for trial in range(int(sys.argv[2])):
        G=rng.randint(3,16); ncl=rng.randint(1,5)
        eps=sorted(rng.sample(range(1,G),min(ncl,G-1)))
        Y=sidon_increasing(len(WIRES),rng,rng.randint(1,5))
        Bp=2*max(Y)+1+rng.randint(0,12); B=G*Bp
        res={w:G*y for w,y in zip(WIRES,Y)}; clk=rng.choice(eps)
        out=check2(res,eps,clk,B)
        if out:
            nok+=1; intended,cover=out
            S=build_S2(res,clk,B,cover,5); tot=len(S)
            if best is None or tot<best[0]:
                best=(tot,B,G,eps,clk,res,cover); print('OK |S|=%d B=%d G=%d eps=%s clk=%d Y=%s'%(tot,B,G,eps,clk,Y),flush=True)
    print('nok',nok)
    if best:
        tot,B,G,eps,clk,res,cover=best
        json.dump({'B':B,'res':res,'clocks':eps,'clk':clk,'cover':{str(k):v for k,v in cover.items()}},open('best_layout.json','w'))
