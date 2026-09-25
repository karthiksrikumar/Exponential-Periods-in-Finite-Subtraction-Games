# Bit-serial ring cellular automaton embedded in a subtraction game.
# Rule R (elementary CA, radius 1) on a ring of k cells with initial configuration x (length k).
# Block tau = t*k + i  <->  cell i at time t.  New cell (t,i) reads (t-1,i-1),(t-1,i),(t-1,i+1)
# = blocks tau-k-1, tau-k, tau-k+1, EXCEPT at the ring seam (i=0 left nbr is (t-1,k-1)=tau-1 ; i=k-1 right nbr is (t-1,0)=tau-2k+1).
# We handle the seam with the marker wire (marker = [k | tau]) and 'last' = marker delayed by (k-1) i.e. [tau = -1 mod k].
# Circuit (NOR only), with sum-of-products for rule R.
import itertools
def ca_circuit(rule):
    """returns circuit list (name, [(src,(a,b))]) with long delay K+c where k=K+1 ; K = k-1.
       long delays: k-1=(1,0), k=(1,1), k+1=(1,2), 2k-1 = 2K+1 = (2,1)."""
    C=[]
    C.append(('boot',[('CLK',(0,1))]))
    # marker = [k | tau] : nm = NOR(boot, marker[-k]) ; marker = NOR(nm)
    C.append(('nm',[('boot',(0,0)),('marker',(1,1))]))
    C.append(('marker',[('nm',(0,0))]))
    # last(tau) = [tau = k-1 mod k] = marker(tau-(k-1)) for tau>=k-1 ; need also tau=k-1 in first word: marker(0)=1 -> ok since tau-(k-1)=0
    # last = NOR(nlast) ; nlast = NOR(marker[-(k-1)])
    C.append(('nlast',[('marker',(1,0))]))
    C.append(('last',[('nlast',(0,0))]))
    # neighbour values (as positive literals) via double negation:
    # L = u at tau-k-1 normally, at tau-1 if marker ; C = u at tau-k ; R = u at tau-k+1 normally, at tau-2k+1 if last
    # nL = NOR( AND(u[-k-1], nm) , AND(u[-1], marker) ) = NOR(p1,p2) with p1 = NOR(nu[-k-1]? ...)
    # simpler: define 'nu' = NOR(u) (same block) so that u[-d] negations are available as nu[-d].
    C.append(('nu_placeholder',[]))  # replaced below after u defined (order matters)
    return C
