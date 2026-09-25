import random, sys, json, itertools, io, contextlib, collections
from lay import *
from design8 import sidon_increasing
rng=random.Random(int(sys.argv[1])); best=None; nok=0; cnt=collections.Counter()
for G in range(5,21):
    for m in (2,3):
        for E in itertools.combinations(range(1,G),m):
            for clk in E:
                for trial in range(3):
                    Y=sidon_increasing(len(WIRES),rng,rng.randint(1,4))
                    Bp=2*max(Y)+1+rng.randint(0,6); B=G*Bp
                    res={w:G*y for w,y in zip(WIRES,Y)}
                    f=io.StringIO()
                    with contextlib.redirect_stdout(f): out=check2(res,list(E),clk,B,verbose=True)
                    msg=f.getvalue().strip(); cnt[msg.split()[0] if msg else 'OK']+=1
                    if out:
                        nok+=1; intended,cover=out
                        S=build_S2(res,clk,B,cover,5); tot=len(S)
                        if best is None or tot<best[0]:
                            best=(tot,B,G,E,clk,res,cover,Y); print('OK |S|=%d B=%d G=%d E=%s clk=%d Y=%s'%(tot,B,G,E,clk,Y),flush=True)
print('nok',nok,cnt)
if best:
    tot,B,G,E,clk,res,cover,Y=best
    json.dump({'B':B,'res':res,'clocks':list(E),'clk':clk,'cover':{str(k):v for k,v in cover.items()}},open('best_layout.json','w'))
