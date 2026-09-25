import random, collections
from design3 import check
from design2 import CIRCUIT, WIRES
import design3
rng=random.Random(5)
cnt=collections.Counter()
import io,contextlib
for trial in range(3000):
    t=rng.randint(2,8); G=rng.randint(t+1,3*t+6); Gs=rng.randint(1,20); margin=rng.randint(t+2,60)
    clocks=list(range(t)); pos=[]; cur=t-1
    for i in range(len(WIRES)): cur+=G+rng.randrange(Gs); pos.append(cur)
    B=cur+margin; res=dict(zip(WIRES,pos))
    f=io.StringIO()
    with contextlib.redirect_stdout(f): out=check(res,clocks,B,verbose=True)
    msg=f.getvalue().split()
    cnt[msg[0] if msg else 'OK']+=1
print(cnt)
