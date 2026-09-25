import random, io, contextlib, collections
from design3 import check
from design4 import greedy_positions
from design2 import WIRES
rng=random.Random(3); cnt=collections.Counter(); ex=None
for trial in range(50):
    t=rng.randint(1,6); spread=rng.randint(2,12)
    pos=greedy_positions(t,rng,spread); res=dict(zip(WIRES,pos)); clocks=list(range(t))
    for margin in range(t+1, 2*max(pos)):
        B=max(pos)+margin
        f=io.StringIO()
        with contextlib.redirect_stdout(f): out=check(res,clocks,B,verbose=True)
        m=f.getvalue().strip()
        cnt[m.split()[0] if m else 'OK']+=1
        if m.startswith('uncovered') and ex is None: ex=(t,res,B,m)
print(cnt); print(ex)
