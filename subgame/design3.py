import random, sys, json
from design2 import CIRCUIT, WIRES
def check(res, clocks, B, verbose=False):
    X=set(res.values())|set(clocks)
    if len(X)!=len(res)+len(clocks): return None
    intended={}
    for w,ins in CIRCUIT:
        for src,J in ins:
            sr = 0 if src=='CLK' else res[src]
            if J==0 and sr>=res[w]: return None
            d=(res[w]-sr)%B
            if d in intended:
                if verbose: print('dup intended',d)
                return None
            intended[d]=(w,src)
    Xl=sorted(X)
    for d,(w,src) in intended.items():
        hits=[e for e in Xl if (e-d)%B in X]
        if hits!=[res[w]]:
            if verbose: print('intended',d,w,src,'hits',hits)
            return None
    bad=set((e-x)%B for e in Xl for x in Xl)
    cover={}
    for r in range(B):
        if r in X: continue
        ok=None
        for c in sorted(clocks,reverse=True):
            if c>=r: continue
            d=r-c
            if d in bad or d in intended: continue
            ok=d;break
        if ok is None:
            if verbose: print('uncovered',r)
            return None
        cover[r]=ok
    return intended,cover
def attempt(t,G,Gspread,margin,rng):
    clocks=list(range(t))
    pos=[]; cur=t-1
    for i in range(len(WIRES)):
        cur+=G+rng.randrange(Gspread); pos.append(cur)
    B=cur+margin
    res=dict(zip(WIRES,pos))
    return check(res,clocks,B),res,clocks,B
if __name__=='__main__':
    rng=random.Random(int(sys.argv[1]))
    found=0
    for trial in range(int(sys.argv[2])):
        t=rng.randint(2,8); G=rng.randint(t+1,3*t+6); Gs=rng.randint(1,20); margin=rng.randint(t+2,60)
        out,res,clocks,B=attempt(t,G,Gs,margin,rng)
        if out:
            intended,cover=out
            ncov=len(set(cover.values()))
            print('OK B=%d t=%d res=%s #cover=%d'%(B,t,res,ncov),flush=True); found+=1
            json.dump({'B':B,'res':res,'clocks':clocks,'cover':{str(k):v for k,v in cover.items()}},open('lay3_%d.json'%trial,'w'))
            if found>=5: break
    print('done found',found)
