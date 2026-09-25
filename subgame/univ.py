# Universal enumerating circuit: a FIXED NOR circuit with delays a*K+b that, for ring length L = K+2,
# runs a radius-1 cellular automaton F (b-bit states, null boundary) on EVERY initial configuration
# X = 1, 2, 3, ... (bits of X, one per cell), each run lasting 2^L rounds (one round = L blocks).
# Validated at the logic level against a direct CA simulation.
import itertools, sys

class Circ:
    def __init__(self):
        self.wires = []          # list of (name, [(src, (a,b))])
        self.idx = {}
    def add(self, name, ins):
        assert name not in self.idx, name
        self.idx[name] = len(self.wires)
        self.wires.append((name, list(ins)))
        return name
    def set_inputs(self, name, ins):
        self.wires[self.idx[name]] = (name, list(ins))
    def check_order(self):
        """GLL conditions: boot first with CLK[-1]; delay-0 inputs from earlier wires;
        backward inputs need b>=1; no self-loops"""
        assert self.wires[0] == ('boot', [('CLK', (0, 1))]), self.wires[0]
        for j, (w, ins) in enumerate(self.wires):
            for src, (a, b) in ins:
                if src == 'CLK': continue
                i = self.idx[src]
                assert i != j, ('self loop', w)
                if (a, b) == (0, 0): assert i < j, ('delay0 forward only', w, src)
                if i > j: assert b >= 1, ('backward needs b>=1', w, src, (a, b))
        return True
    def simulate(self, K, nblocks):
        W = len(self.wires)
        vals = [bytearray(nblocks) for _ in range(W)]
        order = [(j, [(self.idx[s] if s != 'CLK' else -1, a * K + b) for s, (a, b) in ins])
                 for j, (w, ins) in enumerate(self.wires)]
        for t in range(nblocks):
            for j, ins in order:
                v = 1
                for i, d in ins:
                    if d > t: continue
                    if i < 0 or vals[i][t - d]:
                        v = 0; break
                vals[j][t] = v
        return {w: vals[j] for j, (w, _) in enumerate(self.wires)}

def build_universal(b, rule, init, bnd, name='U'):
    """rule: function (l,c,r) tuples of b bits -> tuple of b bits; init: bit -> tuple of b bits;
    bnd: boundary state (tuple).  Ring length L = K+2: delays L-1=(1,1), L=(1,2), L+1=(1,3)."""
    C = Circ()
    Lm1, L0, Lp1 = (1, 1), (1, 2), (1, 3)
    C.add('boot', [('CLK', (0, 1))])
    C.add('nm', [('boot', (0, 0)), ('marker', L0)])
    C.add('marker', [('nm', (0, 0))])
    C.add('nlc', [('marker', Lm1)])
    C.add('lc', [('nlc', (0, 0))])
    # timer: bit-serial counter, +1 every round
    C.add('tncin', [('tcarry', (0, 1)), ('marker', (0, 0))])
    C.add('tnb', [('tu', L0)])
    C.add('tg1', [('tu', L0), ('tcarry', (0, 1)), ('marker', (0, 0))])
    C.add('tcarry', [('tnb', (0, 0)), ('tncin', (0, 0))])
    C.add('tu', [('tg1', (0, 0)), ('tcarry', (0, 0))])
    # run start: rs = (marker & ovf) | (~marker & rs[-1]),  ovf = boot | tcarry[-1]
    C.add('novf', [('boot', (0, 0)), ('tcarry', (0, 1))])
    C.add('inj', [('nm', (0, 0)), ('novf', (0, 0))])              # marker & ovf
    C.add('hold', [('marker', (0, 0)), ('nrs', (0, 1))])          # ~marker & rs[-1]
    C.add('nrs', [('inj', (0, 0)), ('hold', (0, 0))])
    C.add('rs', [('nrs', (0, 0))])
    # input counter X: +1 at cell 0 of every run-start round
    C.add('xnc', [('xcarry', (0, 1))])                            # ~xcarry[-1]
    C.add('xc2', [('marker', (0, 0)), ('xnc', (0, 0))])           # ~marker & xcarry[-1]
    C.add('xncin', [('inj', (0, 0)), ('xc2', (0, 0))])            # ~cin
    C.add('xnb', [('xu', L0)])
    C.add('xg1', [('xu', L0), ('inj', (0, 0)), ('xc2', (0, 0))])  # ~(bit | cin)
    C.add('xcarry', [('xnb', (0, 0)), ('xncin', (0, 0))])         # bit & cin
    C.add('xu', [('xg1', (0, 0)), ('xcarry', (0, 0))])            # bit ^ cin
    C.add('nxu', [('xu', (0, 0))])
    # CA track: state bits s0..s{b-1} (positive), read with delays L+1 (left), L (centre), L-1 (right)
    # literals: for each neighbour position p in {l,c,r} and bit q: positive literal P[p][q], negative N[p][q]
    # masked left: l' = marker ? bnd : l ; masked right: r' = lc ? bnd : r
    P = {}; N = {}
    for q in range(b):
        s = f's{q}'
        # centre: positive literal = s[-L] (direct input), negative = wire nc_q
        C.add(f'nc{q}', [(s, L0)])
        P[('c', q)] = (s, L0); N[('c', q)] = (f'nc{q}', (0, 0))
        # left
        C.add(f'nl{q}', [(s, Lp1)])                                  # ~l
        if bnd[q] == 0:
            C.add(f'lm{q}', [(f'nl{q}', (0, 0)), ('marker', (0, 0))])   # l & ~marker
        else:
            C.add(f'nlm_{q}', [(s, Lp1), ('marker', (0, 0))])           # ~(l | marker)
            C.add(f'lm{q}', [(f'nlm_{q}', (0, 0))])                     # l | marker
        C.add(f'nlmm{q}', [(f'lm{q}', (0, 0))])
        P[('l', q)] = (f'lm{q}', (0, 0)); N[('l', q)] = (f'nlmm{q}', (0, 0))
        # right
        C.add(f'nr{q}', [(s, Lm1)])
        if bnd[q] == 0:
            C.add(f'rm{q}', [(f'nr{q}', (0, 0)), ('lc', (0, 0))])
        else:
            C.add(f'nrm_{q}', [(s, Lm1), ('lc', (0, 0))])
            C.add(f'rm{q}', [(f'nrm_{q}', (0, 0))])
        C.add(f'nrmm{q}', [(f'rm{q}', (0, 0))])
        P[('r', q)] = (f'rm{q}', (0, 0)); N[('r', q)] = (f'nrmm{q}', (0, 0))
    # minterms: AND of literals = NOR of complements
    minterms = {}
    for pat in itertools.product([0, 1], repeat=3 * b):
        l, c, r = pat[:b], pat[b:2 * b], pat[2 * b:]
        out = rule(l, c, r)
        if not any(out): continue
        lits = []
        for p, bits in (('l', l), ('c', c), ('r', r)):
            for q in range(b):
                lits.append(N[(p, q)] if bits[q] else P[(p, q)])
        nm_ = 'm' + ''.join(map(str, pat))
        C.add(nm_, lits)
        minterms[pat] = (nm_, out)
    for q in range(b):
        ms = [(nm_, (0, 0)) for pat, (nm_, out) in minterms.items() if out[q]]
        C.add(f'nF{q}', ms)                                          # ~F_q
    # new state: s_q = (rs & init_q(xu)) | (~rs & F_q)
    for q in range(b):
        # init_q(v) is one of: 0, 1, v, ~v
        i0, i1 = init(0)[q], init(1)[q]
        ins = [('nrs', (0, 0)), ('nF' + str(q), (0, 0))]
        C.add(f't2_{q}', [('rs', (0, 0)), (f'nF{q}', (0, 0))])        # ~rs & F
        if (i0, i1) == (0, 0):
            C.add(f'ns{q}', [(f't2_{q}', (0, 0))])
        elif (i0, i1) == (1, 1):
            C.add(f'ns{q}', [(f't2_{q}', (0, 0)), ('rs', (0, 0))])
        elif (i0, i1) == (0, 1):
            C.add(f't1_{q}', [('nrs', (0, 0)), ('nxu', (0, 0))])     # rs & xu
            C.add(f'ns{q}', [(f't1_{q}', (0, 0)), (f't2_{q}', (0, 0))])
        else:
            C.add(f't1_{q}', [('nrs', (0, 0)), ('xu', (0, 0))])      # rs & ~xu
            C.add(f'ns{q}', [(f't1_{q}', (0, 0)), (f't2_{q}', (0, 0))])
        C.add(f's{q}', [(f'ns{q}', (0, 0))])
    C.check_order()
    return C

def ca_run(rule, init, bnd, L, X, T, b):
    """direct simulation: configuration from bits of X (cell i gets bit i), T steps"""
    conf = [init((X >> i) & 1) for i in range(L)]
    hist = [conf]
    for t in range(T):
        new = []
        for i in range(L):
            l = conf[i - 1] if i > 0 else bnd
            r = conf[i + 1] if i < L - 1 else bnd
            new.append(tuple(rule(l, conf[i], r)))
        conf = new; hist.append(conf)
    return hist

def elementary(num):
    def rule(l, c, r):
        return ((num >> (l[0] * 4 + c[0] * 2 + r[0])) & 1,)
    return rule

def validate(C, b, rule, init, bnd, L, runs):
    K = L - 2
    R = 2 ** L
    nblocks = runs * R * L
    V = C.simulate(K, nblocks)
    bad = 0
    for j in range(runs):
        X = (j + 1) % R
        hist = ca_run(rule, init, bnd, L, X, R - 1, b)
        for T in range(R):
            for i in range(L):
                tau = (j * R + T) * L + i
                got = tuple(V[f's{q}'][tau] for q in range(b))
                if got != tuple(hist[T][i]):
                    bad += 1
                    if bad < 5: print('mismatch run', j, 'X', X, 'T', T, 'cell', i, got, hist[T][i])
    return bad

if __name__ == '__main__':
    tot = 0
    for num in [30, 90, 110, 184, 54, 150]:
        rule = elementary(num)
        for bndv in (0, 1):
            for iv in [((0,), (1,)), ((1,), (0,))]:
                init = lambda v, iv=iv: iv[v]
                C = build_universal(1, rule, init, (bndv,))
                for L in (3, 4, 5, 6):
                    runs = min(2 ** L, 6)
                    bad = validate(C, 1, rule, init, (bndv,), L, runs)
                    tot += bad
                    print(f'rule {num} bnd {bndv} init {iv} L={L} wires={len(C.wires)} runs={runs} mismatches={bad}')
    # a 2-bit-state random rule
    import random
    rng = random.Random(5)
    table = {}
    def rule2(l, c, r):
        key = (l, c, r)
        if key not in table: table[key] = (rng.randint(0, 1), rng.randint(0, 1))
        return table[key]
    for pat in itertools.product([0, 1], repeat=6): rule2(pat[:2], pat[2:4], pat[4:])
    init2 = lambda v: (v, 1 - v)
    C = build_universal(2, rule2, init2, (1, 0))
    for L in (3, 4, 5):
        bad = validate(C, 2, rule2, init2, (1, 0), L, min(2 ** L, 5))
        tot += bad
        print(f'2-bit random rule L={L} wires={len(C.wires)} mismatches={bad}')
    print('TOTAL mismatches', tot)
