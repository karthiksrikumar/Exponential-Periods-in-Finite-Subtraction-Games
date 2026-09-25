# convert existing layout_G13 to symbolic taps and verify with new checker
import json
from lay import *
from lay2 import verify_design, taps_to_S
L=json.load(open('layout_G13.json')); B=L['B']; res=L['res']; clocks=L['clocks']; clk=L['clk']
cover={int(k):v for k,v in L['cover'].items()}
taps=set()
for (w,src,J,d) in taps(res,clk,B) if False else []: pass
from lay import taps as tp
T=set()
for (w,src,J,d) in tp(res,clk,B):
    sr = clk if src=='CLK' else res[src]
    s0=res[w]-sr  # may be negative
    JJ=('k',0) if J=='K' else J
    # s = JJ*B + s0 ; normalize to (q, delta) with 0<=delta<B
    if isinstance(JJ,int):
        s=JJ*B+s0; T.add((s//B, s%B))
    else:
        q=-1 if s0<0 else 0; d=s0-q*B
        T.add((('k',q), d))
for r,ts in cover.items():
    for s in ts: T.add((s//B,s%B))
print('taps',len(T))
print('verify:',verify_design(B,res,clocks,sorted(T,key=str),verbose=True))
