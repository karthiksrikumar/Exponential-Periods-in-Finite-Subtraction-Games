# Erdos-Gyarfas (Erdos #617): r-colour E(K_n) so every (r+1)-set sees all r colours.
import itertools, sys
def gen(n, r, path, symbreak=True):
    V=range(n); E=list(itertools.combinations(V,2)); eid={e:i for i,e in enumerate(E)}
    var=lambda e,c: eid[e]*r+c+1
    cls=[]
    for e in E:
        for c1,c2 in itertools.combinations(range(r),2): cls.append([-var(e,c1),-var(e,c2)])
        cls.append([var(e,c) for c in range(r)])
    for S in itertools.combinations(V,r+1):
        es=list(itertools.combinations(S,2))
        for c in range(r): cls.append([var(e,c) for e in es])
    if symbreak:
        # colour symmetry: edge (0,1) gets colour 0
        cls.append([var((0,1),0)])
    with open(path,'w') as f:
        f.write(f"p cnf {len(E)*r} {len(cls)}\n")
        for c in cls: f.write(' '.join(map(str,c))+' 0\n')
    return len(E)*r, len(cls)
if __name__=='__main__':
    n,r=int(sys.argv[1]),int(sys.argv[2])
    print(gen(n,r,f'eg_{n}_{r}.cnf'))
