# Generalized exact layout checker. A design = (B, role map, tap list S (actual integers), k-dependence).
# We represent taps symbolically: s = q*B + delta with q in {0,1,...} or q = 'k' (long) / 'k-1'.
# Verification is done by the exact local rule for a symbolic k (k >= kmin), plus block-0 conditions.
from lay import CIRCUIT, WIRES, logical
def eff(e, qs, delta, B):
    """landing (residue, block delay) when tap (qs,delta) applied at residue e. qs is int or ('k',c) meaning k+c."""
    if e>=delta: return (e-delta, qs)
    return (e-delta+B, add1(qs))
def add1(qs):
    return qs+1 if isinstance(qs,int) else ('k',qs[1]+1)
def verify_design(B, res, clocks, taps, circuit=CIRCUIT, verbose=False):
    """taps: list of (qs, delta). Checks all local conditions for the counter circuit (symbolic k).
       Returns True/False."""
    role={}
    for c in clocks: role[c]=('C',None)
    for w,r in res.items():
        if r in role: return False
        role[r]=('W',w)
    if 0 not in role: 
        if verbose: print('0 not in X'); 
        return False
    want={w:set() for w in WIRES}
    for w,ins in circuit:
        for src,J in ins:
            srcres = None if src=='CLK' else res[src]
            want[w].add((src, J if J!='K' else ('k',0)))
    # CLK source: any clock residue allowed? we require the tap to land on a clock; treat 'CLK' as 'any clock'
    got={w:set() for w in WIRES}
    for e,(kind,name) in role.items():
        for (qs,d) in taps:
            l,J=eff(e,qs,d,B)
            if l not in role: continue  # lands on zero residue: harmless
            lk,ln=role[l]
            if kind=='C':
                if verbose: print('clock',e,'reads',l,'via',(qs,d)); 
                return False
            # e is wire
            if lk=='C':
                # allowed only if this is the intended CLK input of this wire
                if ('CLK',J) in want[name]: got[name].add(('CLK',J)); continue
                if verbose: print('wire',name,'reads clock',l,'J',J); 
                return False
            key=(ln,J)
            if key not in want[name]:
                if verbose: print('wire',name,'unintended input',key,'via',(qs,d)); 
                return False
            got[name].add(key)
    for w in WIRES:
        if got[w]!=want[w]:
            if verbose: print('wire',w,'missing',want[w]-got[w]); 
            return False
    # covering zero residues: blocks>=1: need tap landing on clock (any J) ; block 0: need landing on a 1-valued X elem in same block (J=0)
    v0=logical(8,1)
    ones0=set(clocks)|{res[w] for w in WIRES if v0[w][0]}
    for r in range(B):
        if r in role: continue
        okA=False; okB=False
        for (qs,d) in taps:
            l,J=eff(r,qs,d,B)
            if l in role and role[l][0]=='C' and (J in (0,1)) : okA=True
            if J==0 and l in ones0: okB=True
        # note: J=1 landing on clock works for blocks>=1; J=0 landing on clock works for all blocks incl 0
        if not okA or not okB:
            # okA with J=0 clock implies okB
            if verbose: print('zero residue',r,'uncovered',okA,okB)
            return False
    return True
def taps_to_S(B,taps,k):
    S=set()
    for qs,d in taps:
        q = qs if isinstance(qs,int) else k+qs[1]
        s=q*B+d
        if s<=0: return None
        S.add(s)
    return sorted(S)

def verify_X(B, res, clocks, taps, circuit=CIRCUIT):
    """wire/clock conditions only (no covering)."""
    role={}
    for c in clocks: role[c]=('C',None)
    for w,r in res.items():
        if r in role: return False
        role[r]=('W',w)
    want={w:set() for w in WIRES}
    for w,ins in circuit:
        for src,J in ins:
            want[w].add((src, J if J!='K' else ('k',0)))
    got={w:set() for w in WIRES}
    for e,(kind,name) in role.items():
        for (qs,d) in taps:
            l,J=eff(e,qs,d,B)
            if l not in role: continue
            lk,ln=role[l]
            if kind=='C': return False
            if lk=='C':
                if ('CLK',J) in want[name]: got[name].add(('CLK',J)); continue
                return False
            if (ln,J) not in want[name]: return False
            got[name].add((ln,J))
    return all(got[w]==want[w] for w in WIRES)
