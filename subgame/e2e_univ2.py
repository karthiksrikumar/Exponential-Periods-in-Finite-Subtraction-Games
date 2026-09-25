# End-to-end: two-ring universal circuit -> layout lemma design (numeric delays) -> game -> compare with CA.
import sys, subprocess, itertools, random, numpy as np
from univ2 import build, ca_run2
from gll import build as gbuild, choose_cover, verify
def numeric(C, L1, L2):
    return [(w, [(s, (0, a1*L1 + a2*L2 + c)) for s, (a1, a2, c) in ins]) for w, ins in C.wires]
seed = int(sys.argv[1]); L2 = int(sys.argv[2]); m = int(sys.argv[3]); runs = int(sys.argv[4])
L1 = m * L2
rng = random.Random(seed); b = 1
table = {pat: tuple(rng.randint(0,1) for _ in range(b)) for pat in itertools.product([0,1], repeat=3*b)}
rule = lambda l,c,r: table[tuple(l)+tuple(c)+tuple(r)]
itab = {k: tuple(rng.randint(0,1) for _ in range(b)) for k in itertools.product([0,1], repeat=3)}
init = lambda v,f,l: itab[(v,f,l)]
bnd = tuple(rng.randint(0,1) for _ in range(b))
C = build(b, rule, init, bnd)
circ = numeric(C, L1, L2)
names, res, clocks, B, taps, want, X = gbuild(circ)
cov, bad = choose_cover(B, res, clocks, taps, X, {'boot': 1}); assert cov is not None
msg = verify(names, res, clocks, B, taps | cov, want, X); assert msg is None, msg
S = sorted(set(bb * B + d for (a, bb), d in taps | cov)); assert min(S) > 0
print(f'rule table={table} wires={len(names)} B={B} |S|={len(S)} maxS={max(S)} L1={L1} L2={L2}')
R = 2 ** L2; nblocks = runs * R * L1 + 1; N = nblocks * B
open('S_u2.txt','w').write('\n'.join(map(str,S)))
subprocess.run(['./simwin.exe','S_u2.txt',str(N),'w_u2.bin'],check=True)
w = np.fromfile('w_u2.bin', dtype=np.uint8)
badc = 0
for j in range(runs):
    Xv = (j + 1) % R
    hist = ca_run2(rule, init, bnd, L1, Xv, R - 1, b, L2)
    for T in range(R):
        for i in range(L1):
            n = ((j*R + T)*L1 + i)*B + res['s0']
            if w[n] != hist[T][i][0]: badc += 1
print(f'game vs direct CA: {runs} runs x {R} steps x {L1} cells, mismatches {badc}')
