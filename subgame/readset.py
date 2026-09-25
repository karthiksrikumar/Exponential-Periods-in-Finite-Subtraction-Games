# "don't-care" relaxation: only residues READ by clocks/wires need guaranteed values.
import json, sys
from lay import CIRCUIT, WIRES, logical
from lay2 import eff
from opt import intended_taps
V0=logical(8,1)
def closure(B,res,clocks,clk,max_iter=400):
    X=set(res.values())|set(clocks); role={c:('C',None) for c in clocks}
    for w,r in res.items(): role[r]=('W',w)
    ones0=set(clocks)|{res[w] for w in WIRES if V0[w][0]}
    T=set(intended_taps(B,res,clk))
    bad=set((e-x)%B for e in X for x in X)   # moves whose residue is a difference of X would create X->X reads
    def reads(T):
        R=set()
        for e in X:
            for (q,d) in T:
                l,J=eff(e,q,d,B)
                if l not in X: R.add(l)
        return R
    covered=set()
    for it in range(max_iter):
        R=reads(T)
        unc=[r for r in sorted(R) if r not in covered]
        # a residue r is covered if some tap lands on a clock with delay<=1 AND (block-0) some tap with delay 0 lands on a 1-valued element
        def is_cov(r,T):
            okA=okB=False
            for (q,d) in T:
                l,J=eff(r,q,d,B)
                if l in role and role[l][0]=='C' and J in (0,1): okA=True
                if J==0 and l in ones0: okB=True
            return okA and okB
        unc=[r for r in unc if not is_cov(r,T)]
        if not unc: return T,R
        r=unc[0]
        # choose a new safe tap covering r (same-block clock below), prefer one covering most other uncovered residues
        best=None;bs=-1
        cands=[]
        for c in clocks:
            if c<r and (r-c) not in bad: cands.append((0,r-c))
            if c>r and ((r-c)%B) not in bad: cands.append((1,r-c+B))  # prev block (needs block-0 cover too)
        for x in ones0:
            if x<r and (r-x) not in bad: cands.append((0,r-x))
        if not cands: return None,('stuck',r)
        for (qq,d) in cands:
            t=((qq//1 if isinstance(qq,int) else qq),d)
            q=0; dd=d
            T2=T|{(0,dd)} if dd<B else T
            s=sum(1 for u in unc if is_cov(u,T2))
            if s>bs: bs=s; best=(0,dd)
        T=T|{best}
    return None,'maxiter'
if __name__=='__main__':
    for f in sys.argv[1:]:
        L=json.load(open(f)); B=L['B']; res=L['res']; clocks=L['clocks']; clk=L['clk']
        T,R=closure(B,res,clocks,clk)
        print(f,'B',B,'|intended|',len(intended_taps(B,res,clk)),'->',('|S|=%d |R|=%d'%(len(T),len(R))) if T else R)
