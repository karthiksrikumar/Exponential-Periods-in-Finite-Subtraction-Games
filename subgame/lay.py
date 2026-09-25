# Layout checker + S builder + direct simulator for counter-embedding designs.
import itertools
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
def taps(res, clk, B, circuit=CIRCUIT):
    """intended taps as list of (target, src, J, delta_mod_B)."""
    out=[]
    for w,ins in circuit:
        for src,J in ins:
            sr = clk if src=='CLK' else res[src]
            out.append((w,src,J,(res[w]-sr)%B))
    return out
def check(res, clocks, clk, B, circuit=CIRCUIT, verbose=False):
    X=set(res.values())|set(clocks)
    if len(X)!=len(res)+len(clocks) or 0 not in X: return None
    T=taps(res,clk,B,circuit); intended={}
    for (w,src,J,d) in T:
        sr = clk if src=='CLK' else res[src]
        if J==0 and sr>=res[w]:
            if verbose: print('order',w,src)
            return None
        if d==0 or d in intended:
            if verbose: print('dup',d)
            return None
        intended[d]=(w,src)
    Xl=sorted(X)
    for d,(w,src) in intended.items():
        hits=[e for e in Xl if (e-d)%B in X]
        if hits!=[res[w]]:
            if verbose: print('hits',d,w,src,hits)
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
def build_S(res, clk, B, cover, k, circuit=CIRCUIT):
    S=set()
    for (w,src,J,d) in taps(res,clk,B,circuit):
        sr = clk if src=='CLK' else res[src]
        JJ = k if J=='K' else J
        s=JJ*B+res[w]-sr; assert s>0,(w,src,s); S.add(s)
    for r,d in cover.items(): S.add(d)
    return sorted(S)
def simulate(S, N):
    Sset=sorted(S); w=bytearray(N)
    for n in range(N):
        v=1
        for s in Sset:
            if s>n: break
            if w[n-s]: v=0;break
        w[n]=v
    return w
def logical(k, nblocks):
    """simulate the intended circuit: returns dict wire -> list per block"""
    vals={w:[0]*nblocks for w in WIRES}; vals['CLK']=[1]*nblocks
    def get(src,tau,J):
        JJ=k if J=='K' else J
        t=tau-JJ
        return vals[src][t] if t>=0 else 0
    for tau in range(nblocks):
        for w,ins in CIRCUIT:
            vals[w][tau]= 0 if any(get(src,tau,J) for src,J in ins) else 1
    return vals

def block0_values(k=5):
    v=logical(k,1); return {w:v[w][0] for w in WIRES}
def check2(res, clocks, clk, B, circuit=CIRCUIT, verbose=False):
    """covering: blocks>=1 via any clock (same or previous block); block 0 via any X element with value 1 at tau=0 below r."""
    X=set(res.values())|set(clocks)
    if len(X)!=len(res)+len(clocks) or 0 not in X: return None
    T=taps(res,clk,B,circuit); intended={}
    for (w,src,J,d) in T:
        sr = clk if src=='CLK' else res[src]
        if J==0 and sr>=res[w]: return None
        if d==0 or d in intended: return None
        intended[d]=(w,src)
    Xl=sorted(X)
    for d,(w,src) in intended.items():
        hits=[e for e in Xl if (e-d)%B in X]
        if hits!=[res[w]]:
            if verbose: print('hits',d,w,src,hits)
            return None
    bad=set((e-x)%B for e in Xl for x in Xl)|set(intended)
    v0=block0_values(); ones0=set(clocks)|{res[w] for w in WIRES if v0[w]}
    cover={}  # r -> list of taps s
    for r in range(B):
        if r in X: continue
        tapsr=[]
        # (a) clock same block below
        sa=None
        for c in sorted(clocks,reverse=True):
            if c<r and (r-c) not in bad: sa=r-c;break
        if sa is not None: tapsr=[sa]
        else:
            # (a') clock in previous block + (b) block-0 cover
            sp=None
            for c in sorted(clocks):
                if c>r and ((r-c)%B) not in bad: sp=r-c+B;break
            sb=None
            for x in sorted(ones0,reverse=True):
                if x<r and (r-x) not in bad: sb=r-x;break
            if sp is None or sb is None:
                if verbose: print('uncovered',r,sp,sb)
                return None
            tapsr=[sp,sb]
        cover[r]=tapsr
    return intended,cover
def build_S2(res, clk, B, cover, k, circuit=CIRCUIT):
    S=set()
    for (w,src,J,d) in taps(res,clk,B,circuit):
        sr = clk if src=='CLK' else res[src]
        JJ = k if J=='K' else J
        s=JJ*B+res[w]-sr; assert s>0,(w,src,s); S.add(s)
    for r,ts in cover.items():
        for s in ts: S.add(s)
    return sorted(S)
