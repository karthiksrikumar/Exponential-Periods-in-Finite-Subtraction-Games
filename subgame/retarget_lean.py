# Retarget the design-specific Lean files to a new design JSON:
#   Design.lean (regenerated), Main.lean, Grundy.lean, Tests.lean, Exact.lean (constants replaced).
# Usage: python retarget_lean.py <design.json> <oldB> <oldN> <oldTop> <oldShortMax> <oldK*>
# (the "old" values are the ones currently hard-coded in the Lean files).
import json, re, subprocess, sys
from math import comb

J = sys.argv[1]
oldB, oldN, oldTop, oldShort, oldKs = map(int, sys.argv[2:7])
L = json.load(open(J))
B = L['B']
taps = []
for q, d in L['taps']:
    if isinstance(q, list): taps.append((1, 1 + q[1], d))
    else: taps.append((0, q, d))
n = len(set(taps))
longs = [t for t in taps if t[0] == 1]
assert all(t[1] == 0 for t in longs), 'long taps must be (1,0,delta)'
top = max(t[2] for t in longs)
short = max(t[1] * B + t[2] for t in taps if t[0] == 0)
assert short <= B + top, 'short moves must stay below the largest long move for K >= 1'
assert len({t[2] for t in taps}) == len(taps), 'residues must be distinct'
off = B - top
deg = comb(n, 2)
k = 2
while not (B * k * 2 ** k > (B * k - off) ** deg): k += 1
Ks, mS = k - 1, B * k - off
oldOff = oldB - oldTop
oldDeg = comb(oldN, 2)
oldmS = oldB * (oldKs + 1) - oldOff
print(f'B={B} n={n} top={top} off={off} short={short} crossover k={k} maxS={mS} deg={deg}')

subprocess.run([sys.executable, 'gen_lean.py', J, '../lean/Sts/Design.lean'], check=True)

def rep(path, pairs):
    s = open(path, encoding='utf8').read()
    for a, b in pairs:
        s = re.sub(a, b, s)
    open(path, 'w', encoding='utf8').write(s)

common = [(r'\b%d\b' % oldB, str(B))]
rep('../lean/Sts/Grundy.lean', common)
rep('../lean/Sts/Main.lean', common + [(r'\b%d\b' % oldN, str(n))])
rep('../lean/Sts/Tests.lean', common + [(r'\b%d\b' % oldN, str(n))])
rep('../lean/Sts/Exact.lean', [
    (r'\b%d\b' % oldmS, str(mS)), (r'\b%d\b' % oldKs, str(Ks)), (r'\b%d\b' % (oldKs + 1), str(k)),
    (r'\b%d\b' % oldDeg, str(deg)), (r'\b%d\b' % oldShort, str(short)),
    (r'\b%d\b' % (oldTop + 1), str(top + 1)), (r'\b%d\b' % oldTop, str(top)),
    (r'\b%d\b' % oldB, str(B)), (r'\b%d\b' % oldN, str(n)), (r'\b%d\b' % oldOff, str(off)),
])
print('retargeted; new constants: B', B, 'n', n, 'top', top, 'short', short, "K*", Ks)
