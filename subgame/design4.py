import random, sys, json
from design3 import check
from design2 import CIRCUIT, WIRES
def greedy_positions(t, rng, spread):
    # clocks 0..t-1; place wires greedily so that differences wire-x (x in X so far) are all new
    X=list(range(t)); diffs=set()
    for a in X:
        for b in X:
            if a!=b: diffs.add(a-b)
    pos=[]; cur=t-1
    for w in WIRES:
        cand=cur+1
        while True:
            cand+=rng.randrange(1,spread)
            nd=[cand-x for x in X]+[x-cand for x in X]
            if all(d not in diffs for d in nd) and len(set(nd))==len(nd):
                break
        for d in nd: diffs.add(d)
        X.append(cand); pos.append(cand); cur=cand
    return pos
if __name__=='__main__':
    rng=random.Random(int(sys.argv[1])); found=[]
    for trial in range(int(sys.argv[2])):
        t=rng.randint(1,6); spread=rng.randint(2,12)
        pos=greedy_positions(t,rng,spread)
        res=dict(zip(WIRES,pos)); clocks=list(range(t))
        for margin in range(t+1, 2*max(pos)):
            B=max(pos)+margin
            out=check(res,clocks,B)
            if out:
                intended,cover=out; ncov=len(set(cover.values()))
                found.append((B,len(intended)+ncov,t,res,cover))
                print('OK B=%d t=%d |S|=%d res=%s'%(B,t,len(intended)+ncov,res),flush=True)
                break
    found.sort(key=lambda x:(x[1],x[0]))
    if found:
        B,sz,t,res,cover=found[0]
        json.dump({'B':B,'res':res,'clocks':list(range(t)),'cover':{str(k):v for k,v in cover.items()}},open('best_layout.json','w'))
        print('BEST',found[0][:3])
