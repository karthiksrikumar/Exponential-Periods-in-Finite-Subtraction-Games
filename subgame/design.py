# Design a subtraction set S_k whose outcome sequence simulates a bit-serial binary counter.
import random, itertools, sys
# Logical circuit: wire -> list of (source_wire, block_delay J). 'K' means delay k (long tap).
CIRCUIT = [
 ('one',   []),
 ('boot',  [('one',1)]),
 ('nm',    [('boot',0),('marker','K')]),
 ('marker',[('nm',0)]),
 ('ncin',  [('carry',1),('marker',0)]),
 ('cin',   [('ncin',0)]),
 ('nb',    [('u','K')]),
 ('g1',    [('u','K'),('cin',0)]),
 ('g2',    [('u','K'),('g1',0)]),
 ('g3',    [('cin',0),('g1',0)]),
 ('xnor',  [('g2',0),('g3',0)]),
 ('u',     [('xnor',0)]),
 ('carry', [('nb',0),('ncin',0)]),
]
WIRES=[w for w,_ in CIRCUIT]
CONST1={'one'}  # wires with no inputs are constant 1 -> usable as clocks for covering
def try_layout(B, rng, tries=20000):
    for _ in range(tries):
        # residues: increasing order to respect same-block topological order
        pos=sorted(rng.sample(range(1,B),len(WIRES)-1))
        res={'one':0}  # 'one' at residue 0 (position 0 is always P)
        for w,p in zip(WIRES[1:],pos): res[w]=p
        X=set(res.values())
        # intended tap residues
        intended={}  # delta -> (target,source)
        ok=True
        for w,ins in CIRCUIT:
            for (src,J) in ins:
                d=(res[w]-res[src])%B
                if J==0 and res[src]>=res[w]: ok=False;break
                if d in intended and intended[d]!=(w,src): ok=False;break
                intended[d]=(w,src)
            if not ok: break
        if not ok: continue
        # uniqueness: for each intended delta, only (target) residue e in X has e-d in X
        for d,(w,src) in intended.items():
            hits=[e for e in X if (e-d)%B in X]
            if hits!=[res[w]]: ok=False;break
        if not ok: continue
        # covering: zero residues r need clock c<r (c in residues of CONST1 wires) with delta=r-c, delta not hitting X from X
        clocks=[res[w] for w in CONST1]
        cover={}
        for r in range(B):
            if r in X: continue
            found=None
            for c in sorted(clocks):
                if c>=r: continue
                d=r-c
                if d in intended: continue
                if any((e-d)%B in X for e in X): continue
                found=d;break
            if found is None: ok=False;break
            cover[r]=found
        if not ok: continue
        return res,intended,cover
    return None
def build_S(res,intended,cover,B,k):
    S=set()
    for w,ins in CIRCUIT:
        for (src,J) in ins:
            JJ = k if J=='K' else J
            s=JJ*B+res[w]-res[src]
            assert s>0
            S.add(s)
    for r,d in cover.items(): S.add(d)
    return sorted(S)
if __name__=='__main__':
    rng=random.Random(int(sys.argv[2]) if len(sys.argv)>2 else 1)
    B=int(sys.argv[1])
    out=try_layout(B,rng)
    if out is None: print('no layout for B=',B); sys.exit()
    res,intended,cover=out
    print('B=',B,'res=',res)
    print('distinct covering taps=',len(set(cover.values())),'intended taps=',len(intended))
    for k in [3,4,5]:
        S=build_S(res,intended,cover,B,k); print('k=',k,'|S|=',len(S),'maxS=',max(S))
    import json; json.dump({'B':B,'res':res,'cover':cover},open('layout_B%d.json'%B,'w'))
