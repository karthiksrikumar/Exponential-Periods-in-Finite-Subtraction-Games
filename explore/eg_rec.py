from functools import lru_cache
# N(k): max n s.t. K_n r-coloured with alpha(G_i) <= k_i. Upper bound via vertex recursion.
@lru_cache(None)
def N(k):
    k=tuple(sorted(k)); r=len(k)
    if r==1: return k[0]  # single colour = complete graph: alpha=1 always <= k if k>=1 (any n) -> infinite; handle separately
    if k[0]==0: return 0
    if k[0]==1:
        # colour with alpha<=1 must be complete on vertex set -> all edges that colour; other colours empty => n <= min other k
        return min(k[1:])
    s=0
    for i in range(r):
        kk=list(k); kk[i]-=1; s+=N(tuple(kk))
    return 1 + s//(r-1)
for r in range(2,7):
    print(r, N(tuple([r]*r)), 'target r^2 =', r*r)
