import json, sys, random, math, time
from opt import design_cost
from lay import CIRCUIT, WIRES
def valid_order(res):
    for w,ins in CIRCUIT:
        for src,J in ins:
            if J==0 and src!='CLK' and res[src]>=res[w]: return False
    return True
def evalL(B,res,clocks,clk):
    if not valid_order(res) or clk not in clocks: return None
    if len(set(res.values())|set(clocks))!=len(res)+len(clocks): return None
    if any(v>=B or v<0 for v in res.values()) or any(c>=B or c<0 for c in clocks): return None
    return design_cost(B,res,sorted(clocks),clk)
LAM=float(sys.argv[5]) if len(sys.argv)>5 else 0.0
L=json.load(open(sys.argv[1])); rng=random.Random(int(sys.argv[2])); tlim=float(sys.argv[3]); tag=sys.argv[4]
B=L['B']; res=dict(L['res']); clocks=set(L['clocks']); clk=L['clk']
cur=evalL(B,res,clocks,clk); cost=cur[0]+LAM*B; best=(cost,B,dict(res),set(clocks),clk,cur[1]); T=3.0; t0=time.time(); it=0
while time.time()-t0<tlim:
    it+=1
    nB,nres,ncl,nclk=B,dict(res),set(clocks),clk
    mv=rng.random()
    if mv<0.35:
        w=rng.choice(WIRES); nres[w]=(nres[w]+rng.choice([-3,-2,-1,1,2,3]))
    elif mv<0.5:
        ncl.add(rng.randrange(nB))
    elif mv<0.65 and len(ncl)>1:
        c=rng.choice(sorted(ncl)); 
        if c!=nclk: ncl.discard(c)
    elif mv<0.8:
        c=rng.choice(sorted(ncl)); ncl.discard(c); c2=(c+rng.choice([-2,-1,1,2]))%nB; ncl.add(c2)
        if c==nclk: nclk=c2
    elif mv<0.9:
        nB=B+rng.choice([-4,-3,-2,-1,1,2,3,4])
    else:
        nclk=rng.choice(sorted(ncl))
    out=evalL(nB,nres,ncl,nclk)
    if out is None: continue
    c=out[0]+LAM*nB
    if c<=cost or rng.random()<math.exp((cost-c)/T):
        B,res,clocks,clk,cost=nB,nres,ncl,nclk,c
        if c<best[0]:
            best=(c,B,dict(res),set(clocks),clk,out[1]); print('it',it,'best |S|=',c,'B=',B,'#clocks',len(clocks),flush=True)
            json.dump({'B':B,'res':res,'clocks':sorted(clocks),'clk':clk,'taps':[[list(q) if isinstance(q,tuple) else q,d] for q,d in out[1]]},open('ann_best_%s.json'%tag,'w'))
    T=max(0.3,T*0.9995)
print('done',it,'best',best[0])
