# One-ring universal circuit U_F exactly as formalised in Lean (lean/Sts/Univ*.lean).
# Ring length L = K + 2; delays (a,b) mean a*K+b: L-1 = (1,1), L = (1,2), L+1 = (1,3).
# Wire set is uniform in F: for every state bit q the wires nc,nl,nlm,lm,nlmm,nr,nrm,rm,nrmm,t2,ns,s
# and 8 init terms; one minterm wire per pattern p in ({0,1}^b)^3.  Only input LISTS depend on F.
import itertools
from univ import Circ

def build1(b, rule, init, bnd):
    C = Circ(); add = C.add
    add('boot', [('CLK', (0, 1))])
    add('nm', [('boot', (0, 0)), ('mk', (1, 2))])
    add('mk', [('nm', (0, 0))])
    add('nlc', [('mk', (1, 1))])
    add('lc', [('nlc', (0, 0))])
    add('tncin', [('tcarry', (0, 1)), ('mk', (0, 0))])
    add('tnb', [('tu', (1, 2))])
    add('tg1', [('tu', (1, 2)), ('tcarry', (0, 1)), ('mk', (0, 0))])
    add('tcarry', [('tnb', (0, 0)), ('tncin', (0, 0))])
    add('tu', [('tg1', (0, 0)), ('tcarry', (0, 0))])
    add('novf', [('boot', (0, 0)), ('tcarry', (0, 1))])
    add('inj', [('nm', (0, 0)), ('novf', (0, 0))])
    add('hold', [('mk', (0, 0)), ('nrs', (0, 1))])
    add('nrs', [('inj', (0, 0)), ('hold', (0, 0))])
    add('rs', [('nrs', (0, 0))])
    add('xnc', [('xcarry', (0, 1))])
    add('xc2', [('mk', (0, 0)), ('xnc', (0, 0))])
    add('xncin', [('inj', (0, 0)), ('xc2', (0, 0))])
    add('xnb', [('xu', (1, 2))])
    add('xg1', [('xu', (1, 2)), ('inj', (0, 0)), ('xc2', (0, 0))])
    add('xcarry', [('xnb', (0, 0)), ('xncin', (0, 0))])
    add('xu', [('xg1', (0, 0)), ('xcarry', (0, 0))])
    add('nxu', [('xu', (0, 0))])
    for q in range(b):
        s = f's{q}'
        add(f'nc{q}', [(s, (1, 2))])
        add(f'nl{q}', [(s, (1, 3))])
        add(f'nlm{q}', [(s, (1, 3)), ('mk', (0, 0))])
        add(f'lm{q}', [(f'nlm{q}', (0, 0))] if bnd[q] else [(f'nl{q}', (0, 0)), ('mk', (0, 0))])
        add(f'nlmm{q}', [(f'lm{q}', (0, 0))])
        add(f'nr{q}', [(s, (1, 1))])
        add(f'nrm{q}', [(s, (1, 1)), ('lc', (0, 0))])
        add(f'rm{q}', [(f'nrm{q}', (0, 0))] if bnd[q] else [(f'nr{q}', (0, 0)), ('lc', (0, 0))])
        add(f'nrmm{q}', [(f'rm{q}', (0, 0))])
    pats = list(itertools.product([0, 1], repeat=3 * b))
    for pat in pats:
        l, c, r = pat[:b], pat[b:2 * b], pat[2 * b:]
        lits = []
        for q in range(b): lits.append((f'nlmm{q}', (0, 0)) if l[q] else (f'lm{q}', (0, 0)))
        for q in range(b): lits.append((f'nc{q}', (0, 0)) if c[q] else (f's{q}', (1, 2)))
        for q in range(b): lits.append((f'nrmm{q}', (0, 0)) if r[q] else (f'rm{q}', (0, 0)))
        add('m' + ''.join(map(str, pat)), lits)
    for q in range(b):
        ms = [('m' + ''.join(map(str, pat)), (0, 0)) for pat in pats
              if rule(pat[:b], pat[b:2 * b], pat[2 * b:])[q]]
        add(f'nF{q}', ms)
    for q in range(b):
        add(f't2_{q}', [('rs', (0, 0)), (f'nF{q}', (0, 0))])
        for v, f, l in itertools.product([0, 1], repeat=3):
            add(f'it{q}_{v}{f}{l}', [('nrs', (0, 0)), ('nxu' if v else 'xu', (0, 0)),
                                     ('nm' if f else 'mk', (0, 0)), ('nlc' if l else 'lc', (0, 0))])
        terms = [(f'it{q}_{v}{f}{l}', (0, 0)) for v, f, l in itertools.product([0, 1], repeat=3)
                 if init(v, f, l)[q]]
        add(f'ns{q}', [(f't2_{q}', (0, 0))] + terms)
        add(f's{q}', [(f'ns{q}', (0, 0))])
    C.check_order()
    return C

def run1(rule, init, bnd, L, X, T, b):
    conf = [tuple(init((X >> i) & 1, int(i == 0), int(i == L - 1))) for i in range(L)]
    hist = [conf]
    for t in range(T):
        conf = [tuple(rule(conf[i - 1] if i > 0 else bnd, conf[i], conf[i + 1] if i < L - 1 else bnd))
                for i in range(L)]
        hist.append(conf)
    return hist

def validate1(C, b, rule, init, bnd, L, runs):
    K = L - 2; R = 2 ** L
    V = C.simulate(K, runs * R * L)
    bad = 0
    for j in range(runs):
        hist = run1(rule, init, bnd, L, j + 1, R - 1, b)
        for T in range(R):
            for i in range(L):
                tau = (j * R + T) * L + i
                if tuple(V[f's{q}'][tau] for q in range(b)) != hist[T][i]: bad += 1
    return bad

if __name__ == '__main__':
    import random
    rng = random.Random(1); tot = 0; n = 0
    for num in range(256):
        rule = lambda l, c, r, num=num: ((num >> (l[0] * 4 + c[0] * 2 + r[0])) & 1,)
        itab = {k: (rng.randint(0, 1),) for k in itertools.product([0, 1], repeat=3)}
        init = lambda v, f, l, itab=itab: itab[(v, f, l)]
        bnd = (rng.randint(0, 1),)
        C = build1(1, rule, init, bnd)
        for L in (3, 4, 5):
            tot += validate1(C, 1, rule, init, bnd, L, 4); n += 1
    for trial in range(6):
        b = 2
        tab = {p: tuple(rng.randint(0, 1) for _ in range(b)) for p in itertools.product([0, 1], repeat=3 * b)}
        rule = lambda l, c, r, tab=tab: tab[tuple(l) + tuple(c) + tuple(r)]
        itab = {k: tuple(rng.randint(0, 1) for _ in range(b)) for k in itertools.product([0, 1], repeat=3)}
        init = lambda v, f, l, itab=itab: itab[(v, f, l)]
        bnd = tuple(rng.randint(0, 1) for _ in range(b))
        C = build1(b, rule, init, bnd)
        for L in (3, 4, 5):
            tot += validate1(C, b, rule, init, bnd, L, 4); n += 1
    print('one-ring circuit: configurations', n, 'wires(b=1)=', len(build1(1, rule=lambda l, c, r: (0,), init=lambda v, f, l: (0,), bnd=(0,)).wires),
          'TOTAL mismatches', tot)
