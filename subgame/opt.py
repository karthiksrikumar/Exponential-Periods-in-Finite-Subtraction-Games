import random, sys, json, time
from lay import CIRCUIT, WIRES, logical
from lay2 import verify_design, verify_X, eff, taps_to_S
V0=logical(8,1)
def intended_taps(B,res,clk):
    T=set()
    for w,ins in CIRCUIT:
        for src,J in ins:
            sr = clk if src=='CLK' else res[src]
            s0=res[w]-sr
            if J=='K':
                q=-1 if s0<0 else 0; T.add((('k',q), s0-q*B))
            else:
                s=J*B+s0
                if s<=0: return None
                T.add((s//B, s%B))
    return T
def safe_cover_tap(t,B,role):
    # tap must not land from any X element onto an X element
    q,d=t
    for e in role:
        l,J=eff(e,q,d,B)
        if l in role: return False
    return True
def design_cost(B,res,clocks,clk,want_S=False):
    role={c:('C',None) for c in clocks}
    for w,r in res.items():
        if r in role: return None
        role[r]=('W',w)
    if 0 not in role: return None
    T=intended_taps(B,res,clk)
    if T is None: return None
    if not verify_X(B,res,clocks,sorted(T,key=str)):
        return None
    ones0=set(clocks)|{res[w] for w in WIRES if V0[w][0]}
    zeros=[r for r in range(B) if r not in role]
    # candidate covering taps: (q,d) with q in {0,1}, d in 0..B-1, safe
    cand={}
    for q in (0,1):
        for d in range(B):
            if q==0 and d==0: continue
            t=(q,d)
            if not safe_cover_tap(t,B,role): continue
            covA=set(); covB=set()
            for r in zeros:
                l,J=eff(r,q,d,B)
                if l in role and role[l][0]=='C' and J in (0,1): covA.add(r)
                if J==0 and l in ones0: covB.add(r)
            if covA or covB: cand[t]=(covA,covB)
    # intended taps may also cover
    for t in T:
        covA=set(); covB=set()
        for r in zeros:
            q,d=t
            l,J=eff(r,q,d,B)
            if l in role and role[l][0]=='C' and J in (0,1): covA.add(r)
            if J==0 and l in ones0: covB.add(r)
        cand[t]=(covA,covB)
    needA=set(zeros); needB=set(zeros)
    for t in T:
        needA-=cand[t][0]; needB-=cand[t][1]
    chosen=[]
    while needA or needB:
        best=None;bv=0
        for t,(a,b) in cand.items():
            if t in T: continue
            v=len(a&needA)+len(b&needB)
            if v>bv: bv=v;best=t
        if best is None: return None
        chosen.append(best); needA-=cand[best][0]; needB-=cand[best][1]
    taps=sorted(T,key=str)+chosen
    if not verify_design(B,res,clocks,taps): return None
    return len(set(map(str,taps))),taps
def intended_ok(B,res,clocks,T,role):
    return False
def sidon_inc(n,rng,spread):
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
    rng=random.Random(int(sys.argv[1])); tlim=float(sys.argv[2]); best=None; t0=time.time(); n=0
    while time.time()-t0<tlim:
        n+=1
        G=rng.randint(2,16)
        Y=sidon_inc(len(WIRES),rng,rng.randint(1,4))
        Bp=max(Y)+1+rng.randint(0,max(Y)+8); B=G*Bp
        if B>400: continue
        res={w:G*y for w,y in zip(WIRES,Y)}
        ncls=rng.randint(1,3); cls=rng.sample(range(1,G),min(ncls,G-1)) if G>1 else []
        dens=rng.random()
        clocks=set()
        for e in cls:
            for z in range(Bp):
                if z==0 or rng.random()<dens: clocks.add(e+G*z)
        clocks=sorted(clocks)
        if not clocks: continue
        clk=rng.choice(clocks[:3])
        out=design_cost(B,res,clocks,clk)
        if out:
            cost,taps=out
            if best is None or cost<best[0]:
                best=(cost,B,res,clocks,clk,taps); print('iter',n,'|S|=',cost,'B=',B,'G=',G,'#clocks',len(clocks),flush=True)
                json.dump({'B':B,'res':res,'clocks':clocks,'clk':clk,'taps':[[list(q) if isinstance(q,tuple) else q,d] for q,d in taps]},open('opt_best_%s.json'%sys.argv[1],'w'))
    print('done iters',n,'best',best[0] if best else None)
