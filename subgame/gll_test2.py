import random, sys
from gll import build, choose_cover, verify, random_circuit
def random_sidon(n, rng):
    Y=[0]; D=set()
    while len(Y)<n:
        c=Y[-1]+rng.randint(2,6)
        while True:
            nd=[c-y for y in Y]
            if c!=1 and all(d not in D for d in nd) and len(set(nd))==len(nd): break
            c+=1
        for d in nd: D.add(d)
        Y.append(c)
    return Y
rng=random.Random(int(sys.argv[1])); fails=0; tot=0
for trial in range(int(sys.argv[2])):
    W=rng.randint(3,int(sys.argv[3]))
    circ=random_circuit(W,rng,maxfan=4)
    Y=random_sidon(W,rng); Bp=3*max(Y)+3+rng.randint(0,50)
    try: names,res,clocks,B,taps,want,X=build(circ,Y=Y,Bp=Bp)
    except ValueError: continue
    cov,bad=choose_cover(B,res,clocks,taps,X,{'boot':1}); tot+=1
    if cov is None: fails+=1; print('cover fail',W,bad,Y); continue
    msg=verify(names,res,clocks,B,taps|cov,want,X)
    if msg: fails+=1; print('FAIL',W,msg,Y)
print('tested',tot,'fails',fails)
