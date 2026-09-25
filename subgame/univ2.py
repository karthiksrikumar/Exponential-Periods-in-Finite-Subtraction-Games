# Two-ring universal circuit (for EXPTIME-hardness with a bounded number of moves, S in binary).
# Control ring of length L2 (timer T and input counter X, one bit per block), tape ring of length
# L1 = m*L2 (the CA, one cell per block).  A run lasts 2^L2 tape rounds; at the start of a run the
# tape is initialised from X (cells i < L2 get bit i of X, the other cells get init(0)).
# Delays are arbitrary numbers here (functions of L1, L2); the layout lemma only needs residues.
import itertools, sys
from univ import Circ, ca_run, elementary

def build(b, rule, init, bnd):
    C = Circ()
    def D(L1=0, L2=0, c=0): return (L1, L2, c)
    add = C.add
    add('boot', [('CLK', D(c=1))])
    add('nm1', [('boot', D()), ('mk1', D(L1=1))])
    add('mk1', [('nm1', D())])
    add('nlc1', [('mk1', D(L1=1, c=-1))])
    add('lc1', [('nlc1', D())])
    add('nm2', [('boot', D()), ('mk2', D(L2=1))])
    add('mk2', [('nm2', D())])
    add('nlc2', [('mk2', D(L2=1, c=-1))])
    add('fwh', [('mk2', D()), ('nfw', D(c=1))])
    add('nfw', [('mk1', D()), ('fwh', D())])
    # timer
    add('tnc', [('tcarry', D(c=1))])
    add('tc2', [('mk2', D()), ('tnc', D())])
    add('tncin', [('mk1', D()), ('tc2', D())])
    add('tnb', [('tu', D(L2=1))])
    add('tg1', [('tu', D(L2=1)), ('mk1', D()), ('tc2', D())])
    add('tcarry', [('tnb', D()), ('tncin', D())])
    add('tu', [('tg1', D()), ('tcarry', D())])
    add('ntcy', [('tcarry', D())])
    add('ovfnow', [('nlc2', D()), ('ntcy', D()), ('nfw', D())])     # lc2 & tcarry & fw
    # pending overflow: pend = boot | ovfnow | (pend[-1] & ~mk1) ... cleared when the new round starts
    # run start at mk1 if pend[-1] (or boot at tau=0):  rsinj = mk1 & (boot | pend[-1])
    add('npb', [('boot', D()), ('pend', D(c=1))])                    # ~(boot | pend[-1])
    add('rsinj', [('nm1', D()), ('npb', D())])                      # mk1 & (boot|pend[-1])
    add('ph', [('mk1', D()), ('npend', D(c=1))])                    # ~mk1 & pend[-1]
    add('npend', [('ovfnow', D()), ('ph', D())])
    add('pend', [('npend', D())])
    # run-start round flag rs: rs = rsinj | (~mk1 & rs[-1])
    add('rh', [('mk1', D()), ('nrs', D(c=1))])
    add('nrs', [('rsinj', D()), ('rh', D())])
    add('rs', [('nrs', D())])
    # input counter X on the control ring: +1 at the first control word of a run-start round
    add('xnc', [('xcarry', D(c=1))])
    add('xc2', [('mk2', D()), ('xnc', D())])
    add('xncin', [('rsinj', D()), ('xc2', D())])
    add('xnb', [('xu', D(L2=1))])
    add('xg1', [('xu', D(L2=1)), ('rsinj', D()), ('xc2', D())])
    add('xcarry', [('xnb', D()), ('xncin', D())])
    add('xu', [('xg1', D()), ('xcarry', D())])
    add('nxu', [('xu', D())])
    # input value for this tape cell: v = fw & xu  (cells i >= L2 get 0)
    add('v', [('nfw', D()), ('nxu', D())])
    add('nv', [('v', D())])
    add('fwp', [('nfw', D())])                                       # fw
    # CA track on the tape ring
    P = {}; N = {}
    L0, Lm1, Lp1 = D(L1=1), D(L1=1, c=-1), D(L1=1, c=1)
    for q in range(b):
        s = f's{q}'
        add(f'nc{q}', [(s, L0)])
        P[('c', q)] = (s, L0); N[('c', q)] = (f'nc{q}', D())
        add(f'nl{q}', [(s, Lp1)])
        if bnd[q] == 0: add(f'lm{q}', [(f'nl{q}', D()), ('mk1', D())])
        else:
            add(f'nlm_{q}', [(s, Lp1), ('mk1', D())]); add(f'lm{q}', [(f'nlm_{q}', D())])
        add(f'nlmm{q}', [(f'lm{q}', D())])
        P[('l', q)] = (f'lm{q}', D()); N[('l', q)] = (f'nlmm{q}', D())
        add(f'nr{q}', [(s, Lm1)])
        if bnd[q] == 0: add(f'rm{q}', [(f'nr{q}', D()), ('lc1', D())])
        else:
            add(f'nrm_{q}', [(s, Lm1), ('lc1', D())]); add(f'rm{q}', [(f'nrm_{q}', D())])
        add(f'nrmm{q}', [(f'rm{q}', D())])
        P[('r', q)] = (f'rm{q}', D()); N[('r', q)] = (f'nrmm{q}', D())
    minterms = {}
    for pat in itertools.product([0, 1], repeat=3 * b):
        l, c, r = pat[:b], pat[b:2 * b], pat[2 * b:]
        out = rule(l, c, r)
        if not any(out): continue
        lits = []
        for p, bits in (('l', l), ('c', c), ('r', r)):
            for q in range(b):
                lits.append(N[(p, q)] if bits[q] else P[(p, q)])
        nm_ = 'm' + ''.join(map(str, pat)); add(nm_, lits); minterms[pat] = (nm_, out)
    for q in range(b):
        add(f'nF{q}', [(nm_, D()) for pat, (nm_, out) in minterms.items() if out[q]])
    # init(v, first=mk1, last=lc1): OR over true entries of rs & [v=..] & [mk1=..] & [lc1=..]
    litv = {1: ('nv', D()), 0: ('v', D())}
    litf = {1: ('nm1', D()), 0: ('mk1', D())}
    litl = {1: ('nlc1', D()), 0: ('lc1', D())}
    for q in range(b):
        add(f't2_{q}', [('rs', D()), (f'nF{q}', D())])
        terms = []
        for vv, ff, ll in itertools.product([0, 1], repeat=3):
            if init(vv, ff, ll)[q]:
                nmt = f'i{q}_{vv}{ff}{ll}'
                add(nmt, [('nrs', D()), litv[vv], litf[ff], litl[ll]])
                terms.append((nmt, D()))
        add(f'ns{q}', [(f't2_{q}', D())] + terms)
        add(f's{q}', [(f'ns{q}', D())])
    return C

def simulate2(C, L1, L2, nblocks):
    W = len(C.wires)
    vals = [bytearray(nblocks) for _ in range(W)]
    order = [(j, [(C.idx[s] if s != 'CLK' else -1, a1 * L1 + a2 * L2 + c) for s, (a1, a2, c) in ins])
             for j, (w, ins) in enumerate(C.wires)]
    for j, ins in order:
        for i, d in ins:
            assert d >= 0
            if d == 0: assert i < j, (C.wires[j][0], i)
    for t in range(nblocks):
        for j, ins in order:
            v = 1
            for i, d in ins:
                if d > t: continue
                if i < 0 or vals[i][t - d]: v = 0; break
            vals[j][t] = v
    return {w: vals[j] for j, (w, _) in enumerate(C.wires)}

def ca_run2(rule, init, bnd, L, X, T, b, L2):
    conf = [init(((X >> i) & 1) if i < L2 else 0, int(i == 0), int(i == L - 1)) for i in range(L)]
    hist = [conf]
    for t in range(T):
        new = []
        for i in range(L):
            l = conf[i - 1] if i > 0 else bnd
            r = conf[i + 1] if i < L - 1 else bnd
            new.append(tuple(rule(l, conf[i], r)))
        conf = new; hist.append(conf)
    return hist

def validate2(C, b, rule, init, bnd, L1, L2, runs):
    R = 2 ** L2
    nblocks = runs * R * L1 + 1
    V = simulate2(C, L1, L2, nblocks)
    bad = 0
    for j in range(runs):
        X = (j + 1) % R
        hist = ca_run2(rule, init, bnd, L1, X, R - 1, b, L2)
        for T in range(R):
            for i in range(L1):
                tau = (j * R + T) * L1 + i
                got = tuple(V[f's{q}'][tau] for q in range(b))
                if got != tuple(hist[T][i]):
                    bad += 1
                    if bad < 5: print('mismatch run', j, 'X', X, 'T', T, 'cell', i, got, hist[T][i])
    return bad

if __name__ == '__main__':
    import random
    rng = random.Random(7)
    tot = 0
    for trial in range(12):
        b = 1 if trial < 8 else 2
        table = {}
        for pat in itertools.product([0, 1], repeat=3 * b):
            table[pat] = tuple(rng.randint(0, 1) for _ in range(b))
        rule = lambda l, c, r, table=table: table[tuple(l) + tuple(c) + tuple(r)]
        itab = {k: tuple(rng.randint(0, 1) for _ in range(b)) for k in itertools.product([0, 1], repeat=3)}
        init = lambda v, f, l, itab=itab: itab[(v, f, l)]
        bnd = tuple(rng.randint(0, 1) for _ in range(b))
        C = build(b, rule, init, bnd)
        for (L2, m) in [(2, 2), (3, 2), (3, 3), (4, 2)]:
            L1 = m * L2
            runs = min(2 ** L2, 5)
            bad = validate2(C, b, rule, init, bnd, L1, L2, runs)
            tot += bad
            print(f'trial {trial} b={b} L2={L2} L1={L1} wires={len(C.wires)} runs={runs} mismatches={bad}', flush=True)
    print('TOTAL', tot)
