# General layout lemma experiments: build a design for an ARBITRARY circuit and check validity exactly.
# circuit: list of (name, [(src, (a,b))...]) with src = wire name or 'CLK'; delay a*K+b; wire 0 must be 'boot' with input CLK delay (0,1).
import random, sys
def eff(e, q, d, B):
    # q=(a,b) symbolic ; returns landing residue, delay (a, b + wrap)
    a,b=q
    if e>=d: return (e-d,(a,b))
    return (e-d+B,(a,b+1))
def sidon_ET(n):
    # Erdos-Turan: for prime p>n: y_j = 2 p j + (j^2 mod p)
    p=n+1
    while any(p%q==0 for q in range(2,int(p**0.5)+1)): p+=1
    return [2*p*j + (j*j)%p for j in range(n)], p
def build(circuit, G=13, E=(1,5,12), clk=5, Y=None, Bp=None):
    names=[w for w,_ in circuit]; W=len(names)
    if Y is None: Y,_=sidon_ET(W)
    # ensure y_0=0 and y_1>=2 : ET gives y0=0, y1=2p+1 ok
    if Bp is None: Bp=3*max(Y)+3
    B=G*Bp
    res={w:G*y for w,y in zip(names,Y)}
    clocks=list(E)
    X=set(res.values())|set(clocks)
    taps=set(); want={w:set() for w in names}
    for w,ins in circuit:
        for src,(a,b) in ins:
            sr = clk if src=='CLK' else res[src]
            d0=res[w]-sr
            if d0>0: q=(a,b); d=d0
            else:
                if a==0 and b==0: raise ValueError('same-block edge must go forward')
                # s = (a K + b) B + d0 = (aK + b - 1) B + (B + d0)
                if b>=1: q=(a,b-1)
                else: raise ValueError('need b>=1 for backward edge')
                d=B+d0
            taps.add((q,d)); want[w].add((src,(a,b)))
    return names,res,clocks,B,taps,want,X
def choose_cover(B,res,clocks,taps,X,v0):
    role=set(X)
    bad=set((e-x)%B for e in X for x in X)
    ones0=set(clocks)|{res[w] for w in v0 if v0[w]}
    cov=set()
    for r in range(B):
        if r in role: continue
        # A: clock same block below, else previous block ; B: block0 cover same block
        A=None
        for c in sorted(clocks,reverse=True):
            if c<r and (r-c) not in bad: A=((0,0),r-c); break
        Bc=None
        if A is None:
            for c in sorted(clocks):
                if c>r and ((r-c)%B) not in bad: A=((0,1),r-c+B) ; break
            for x in sorted(ones0,reverse=True):
                if x<r and (r-x) not in bad: Bc=((0,0),r-x); break
            if A is None or Bc is None: return None,r
            cov.add(A); cov.add(Bc)
        else: cov.add(A)
    return cov,None
def verify(names,res,clocks,B,taps,want,X):
    role={c:('C',None) for c in clocks}
    for w,r in res.items(): role[r]=('W',w)
    got={w:set() for w in names}
    for e,(kind,name) in role.items():
        for (q,d) in taps:
            l,J=eff(e,q,d,B)
            if l not in role: continue
            lk,ln=role[l]
            if kind=='C': return 'clock %d reads %d via %s'%(e,l,(q,d))
            key=('CLK',J) if lk=='C' else (ln,J)
            if key not in want[name]: return 'wire %s unintended %s'%(name,key)
            got[name].add(key)
    for w in names:
        if got[w]!=want[w]: return 'missing %s %s'%(w,want[w]-got[w])
    return None
def random_circuit(W, rng, maxfan=3):
    circ=[('boot',[('CLK',(0,1))])]
    names=['boot']
    for j in range(1,W):
        nm='w%d'%j; ins=set()
        for _ in range(rng.randint(1,maxfan)):
            src=rng.choice(names)  # no self-loops (a move that is a multiple of B reads every residue itself)
            kind=rng.random()
            if src==nm or kind<0.4:
                dl=rng.choice([(0,1),(0,2),(1,0),(1,1),(1,2)])
            else: dl=(0,0) if src!=nm else (0,1)
            if src==nm and dl==(0,0): dl=(0,1)
            if rng.random()<0.05: src='CLK'; dl=rng.choice([(0,1),(1,1)])
            ins.add((src,dl))
        circ.append((nm,sorted(ins)))
        names.append(nm)
    return circ
if __name__=='__main__':
    rng=random.Random(1); fails=0; tot=0
    for trial in range(int(sys.argv[1])):
        W=rng.randint(3,int(sys.argv[2]))
        circ=random_circuit(W,rng)
        try: names,res,clocks,B,taps,want,X=build(circ)
        except ValueError as e: continue
        v0={'boot':1}  # conservative: only boot known 1 at block 0
        cov,bad=choose_cover(B,res,clocks,taps,X,v0)
        tot+=1
        if cov is None: fails+=1; print('cover fail W',W,'r',bad); continue
        msg=verify(names,res,clocks,B,taps|cov,want,X)
        if msg: fails+=1; print('W',W,'FAIL',msg)
    print('tested',tot,'fails',fails)
