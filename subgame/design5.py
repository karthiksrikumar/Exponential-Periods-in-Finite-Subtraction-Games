import random, sys, json
from design3 import check
from design4 import greedy_positions
from design2 import CIRCUIT, WIRES
rng=random.Random(int(sys.argv[1])); found=[]
for trial in range(int(sys.argv[2])):
    t=rng.randint(1,8); spread=rng.randint(2,25)
    pos=greedy_positions(t,rng,spread); res=dict(zip(WIRES,pos)); clocks=list(range(t))
    mx=max(pos)
    for B in range(2*mx+2, 4*mx):
        out=check(res,clocks,B)
        if out:
            intended,cover=out; ncov=len(set(cover.values()))
            found.append((len(intended)+ncov,B,t,res,cover))
            print('OK |S|=%d B=%d t=%d res=%s'%(len(intended)+ncov,B,t,res),flush=True)
            break
found.sort(key=lambda x:(x[0],x[1]))
if found:
    sz,B,t,res,cover=found[0]
    json.dump({'B':B,'res':res,'clocks':list(range(t)),'cover':{str(k):v for k,v in cover.items()}},open('best_layout.json','w'))
    print('BEST |S|=%d B=%d t=%d'%(sz,B,t))
