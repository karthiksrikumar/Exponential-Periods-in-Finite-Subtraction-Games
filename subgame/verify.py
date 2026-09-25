import json, sys, subprocess, numpy as np
from lay import *
L=json.load(open('best_layout.json')); B=L['B']; res=L['res']; clocks=L['clocks']; clk=L['clk']
cover={int(k):v for k,v in L['cover'].items()}
X=set(res.values())|set(clocks)
for k in [int(x) for x in sys.argv[1:]]:
    S=build_S2(res,clk,B,cover,k)
    open('S_k.txt','w').write('\n'.join(map(str,S)))
    per_expected=k*(2**k)*B
    N=3*per_expected+5*k*B
    subprocess.run(['./sim.exe','S_k.txt',str(N),'w.bin'],check=True)
    w=np.fromfile('w.bin',dtype=np.uint8)
    nb=N//B
    lg=logical(k,nb)
    ok=True
    for tau in range(nb):
        blk=w[tau*B:(tau+1)*B]
        for r in range(B):
            if r in clocks: exp=1
            elif r in X:
                wire=[x for x,v in res.items() if v==r][0]; exp=lg[wire][tau]
            else: exp=0
            if blk[r]!=exp:
                ok=False; print('MISMATCH k=%d tau=%d r=%d got=%d exp=%d'%(k,tau,r,blk[r],exp)); break
        if not ok: break
    # period check
    def is_period(p,start):
        return np.array_equal(w[start:start+per_expected], w[start+p:start+p+per_expected])
    st=5*k*B
    per_ok=is_period(per_expected,st)
    # minimality: check proper divisors of expected period of form per/q for primes q
    minimal=True
    pe=per_expected; q=2; divs=set()
    t=pe
    while q*q<=t:
        while t%q==0: divs.add(q); t//=q
        q+=1
    if t>1: divs.add(t)
    for q in divs:
        if is_period(pe//q,st): minimal=False; print('  smaller period',pe//q)
    print('k=%d |S|=%d maxS=%d  sim-matches-counter=%s  period %d? %s minimal=%s'%(k,len(S),max(S),ok,pe,per_ok,minimal),flush=True)
