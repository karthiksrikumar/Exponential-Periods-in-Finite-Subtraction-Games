import random, io, contextlib, collections
from design3 import check
from design4 import greedy_positions
from design2 import WIRES
rng=random.Random(11); cnt=collections.Counter(); exs=[]
for trial in range(30):
    t=rng.randint(1,8); spread=rng.randint(2,25)
    pos=greedy_positions(t,rng,spread); res=dict(zip(WIRES,pos)); clocks=list(range(t)); mx=max(pos)
    for B in range(2*mx+2, 3*mx):
        f=io.StringIO()
        with contextlib.redirect_stdout(f): out=check(res,clocks,B,verbose=True)
        m=f.getvalue().strip(); k=m.split()[0] if m else 'OK'; cnt[k]+=1
        if k=='uncovered' and len(exs)<5 and B==2*mx+2: exs.append((t,pos,B,m))
print(cnt)
for e in exs: print(e)
