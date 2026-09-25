# Logic-level validation of the PSPACE reduction's bit-serial CA (Theorem pspace).
# TM: LSB-first binary counter on tape  |- b1..bN -|  ; increments until overflow, then accepts.
import itertools, random
L_, R_ = 'L', 'R'
SYMS=['_','0','1',L_,R_]          # '_' = blank (zero code)
STATES=['inc','back','acc']
def delta(q,a):
    if q=='inc':
        if a=='1': return ('inc','0',+1)
        if a=='0': return ('back','1',-1)
        if a==R_:  return ('acc',R_,0)
    if q=='back':
        if a in '01': return ('back',a,-1)
        if a==L_:    return ('inc',L_,+1)
    if q=='acc': return ('acc',a,0)
    raise ValueError((q,a))
ZERO=('_',None,0)
def F(l,c,r):
    """CA rule on cells (sym, head, flag). zero cell maps to zero cell."""
    sym,head,flag=c
    nsym=sym; nhead=None
    if head is not None:
        q2,a2,d=delta(head,sym); nsym=a2
        if d==0: nhead=q2
    if l[1] is not None:
        q2,a2,d=delta(l[1],l[0])
        if d==+1: nhead=q2
    if r[1] is not None:
        q2,a2,d=delta(r[1],r[0])
        if d==-1: nhead=q2
    nflag=int(l[2] or c[2] or r[2] or nhead=='acc')
    return (nsym,nhead,nflag)
assert F(ZERO,ZERO,ZERO)==ZERO
def tm_run(x, tmax):
    tape=[L_]+list(x)+[R_]; pos=1; q='inc'; t=0; acc_time=None
    confs=[]
    for t in range(tmax):
        confs.append((list(tape),pos,q))
        if q=='acc' and acc_time is None: acc_time=t
        q2,a2,d=delta(q,tape[pos]); tape[pos]=a2; pos+=d; q=q2
    return confs,acc_time
def serial_ca(x, tmax):
    Lc=len(x)+2
    init=[(L_,None,0)]+[(b,'inc' if i==0 else None,0) for i,b in enumerate(x)]+[(R_,None,0)]
    N=tmax*Lc
    cells=[None]*N
    get=lambda t: cells[t] if t>=0 else ZERO
    for tau in range(N):
        v=F(get(tau-Lc-1),get(tau-Lc),get(tau-Lc+1))
        if tau<Lc:
            assert v==ZERO           # first word: all reads negative -> zero code
            v=init[tau]              # OR with init taps loads the initial configuration
        cells[tau]=v
    return cells,Lc
rng=random.Random(0); bad=0; tests=0
for N in range(1,8):
    for x in itertools.product('01',repeat=N):
        x=''.join(x); tests+=1
        tmax=(2**N+2)*(2*N+4)+N+4
        confs,acc=tm_run(x,tmax)
        cells,Lc=serial_ca(x,tmax)
        for t,(tape,pos,q) in enumerate(confs):
            for i in range(Lc):
                c=cells[t*Lc+i]
                exp_head = q if i==pos else None
                if c[0]!=tape[i] or c[1]!=exp_head:
                    bad+=1; print('MISMATCH',x,t,i,c,(tape[i],exp_head)); break
            else: continue
            break
        # flag at cell 1 at final time == accepted
        tstar=tmax-1
        if cells[tstar*Lc+1][2]!=(1 if acc is not None and acc+Lc<=tstar else 0):
            bad+=1; print('FLAG MISMATCH',x,acc,cells[tstar*Lc+1])
print('inputs tested',tests,'mismatches',bad)
