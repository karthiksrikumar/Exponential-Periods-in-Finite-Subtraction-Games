import json, sys, subprocess, numpy as np
from lay import WIRES, logical
from lay2 import taps_to_S
L=json.load(open(sys.argv[1])); B=L['B']; res=L['res']; clocks=set(L['clocks'])
taps=[(tuple(q) if isinstance(q,list) else q, d) for q,d in L['taps']]
X=set(res.values())|clocks
inv={v:w for w,v in res.items()}
for k in [int(x) for x in sys.argv[2:]]:
    S=taps_to_S(B,taps,k); open('S_k.txt','w').write('\n'.join(map(str,S)))
    pe=k*(2**k)*B; N=3*pe+5*k*B
    subprocess.run(['./sim.exe','S_k.txt',str(N),'w.bin'],check=True)
    w=np.fromfile('w.bin',dtype=np.uint8); nb=N//B; lg=logical(k,nb)
    exp=np.zeros(nb*B,dtype=np.uint8)
    for r in range(B):
        if r in clocks: exp[r::B]=1
        elif r in inv: exp[r:nb*B:B]=np.array(lg[inv[r]][:nb],dtype=np.uint8)
    ok=np.array_equal(w[:nb*B],exp)
    st=5*k*B
    isp=lambda p: np.array_equal(w[st:st+pe], w[st+p:st+p+pe])
    t=pe; q=2; divs=set()
    while q*q<=t:
        while t%q==0: divs.add(q); t//=q
        q+=1
    if t>1: divs.add(t)
    minimal=all(not isp(pe//q) for q in divs)
    print('k=%d |S|=%d maxS=%d match=%s period=%d ok=%s minimal=%s'%(k,len(S),max(S),ok,pe,isp(pe),minimal),flush=True)
