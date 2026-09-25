import random, sys, json
# Compact bit-serial counter. Inputs: (src, J) with J in {0,1,'K'}. 'CLK' = clock residue 0 (constant 1).
CIRCUIT = [
 ('boot',  [('CLK',1)]),
 ('nm',    [('boot',0),('marker','K')]),
 ('marker',[('nm',0)]),
 ('ncin',  [('carry',1),('marker',0)]),
 ('nb',    [('u','K')]),
 ('g1',    [('u','K'),('carry',1),('marker',0)]),
 ('carry', [('nb',0),('ncin',0)]),
 ('u',     [('g1',0),('carry',0)]),
]
WIRES=[w for w,_ in CIRCUIT]
def check(res, clocks, B):
    X=set(res.values())|set(clocks)
    if len(X)!=len(res)+len(clocks): return None
    intended={}
    for w,ins in CIRCUIT:
        for src,J in ins:
            sr = 0 if src=='CLK' else res[src]
            if J==0 and sr>=res[w]: return None
            d=(res[w]-sr)%B
            if d in intended: return None
            intended[d]=(w,src)
    Xl=sorted(X)
    for d,(w,src) in intended.items():
        hits=[e for e in Xl if (e-d)%B in X]
        if hits!=[res[w]]: return None
    bad=set((e-x)%B for e in Xl for x in Xl)   # all differences incl 0
    cover={}
    for r in range(B):
        if r in X: continue
        ok=None
        for c in sorted(clocks):
            if c>=r: break
            d=r-c
            if d in bad or d in intended: continue
            ok=d;break
        if ok is None: return None
        cover[r]=ok
    return intended,cover
def search(B,nclk,rng,tries):
    best=None
    for t in range(tries):
        clocks=[0]+sorted(rng.sample(range(1,B),nclk-1)) if nclk>1 else [0]
        free=[r for r in range(1,B) if r not in clocks]
        pos=sorted(rng.sample(free,len(WIRES)))
        # respect topological order: assign in given order (list already topological)
        res=dict(zip(WIRES,pos))
        out=check(res,clocks,B)
        if out:
            intended,cover=out
            ncov=len(set(cover.values()))
            if best is None or ncov<best[0]: best=(ncov,res,clocks,intended,cover); print('found B',B,'clocks',clocks,'res',res,'#covertaps',ncov,flush=True)
    return best
if __name__=='__main__':
    B=int(sys.argv[1]); nclk=int(sys.argv[2]); rng=random.Random(int(sys.argv[3])); tries=int(sys.argv[4])
    best=search(B,nclk,rng,tries)
    if best:
        ncov,res,clocks,intended,cover=best
        json.dump({'B':B,'res':res,'clocks':clocks,'cover':{str(k):v for k,v in cover.items()}},open('lay_%d_%d.json'%(B,nclk),'w'))
