# CP-SAT model: given block length B and FIXED wire residues for the counter circuit,
# choose clocks and covering taps minimising the total number of taps (= moves for large k).
# Conditions are exactly (A)-(E) of the simulation theorem (see lay2.verify_design).
import json, sys, time
from ortools.sat.python import cp_model
from lay import CIRCUIT, WIRES, logical
from lay2 import verify_design

def want_sets(circuit=CIRCUIT):
    want = {w: set() for w, _ in circuit}
    for w, ins in circuit:
        for src, J in ins:
            want[w].add((src, J))
    return want

def eff_type(e, typ, d, B):
    """landing residue and effective delay ('K' for k) of tap type typ with offset d at residue e"""
    wrap = 1 if e < d else 0
    l = (e - d) % B
    if typ == 's': J = wrap
    elif typ == 'p': J = 1 + wrap
    elif typ == 'L0': J = 'K' if wrap else 'K-1'
    elif typ == 'L1': J = 'K+1' if wrap else 'K'
    return l, J

def solve(B, res, circuit=CIRCUIT, time_limit=600, hint=None, workers=12, max_clocks=None,
          verbose=True, forbid=None):
    want = want_sets(circuit)
    wires = [w for w, _ in circuit]
    pos = {w: res[w] for w in wires}
    inv = {v: w for w, v in pos.items()}
    assert len(inv) == len(wires)
    v0 = logical(8, 1)
    one0w = {pos[w] for w in wires if v0[w][0]}
    m = cp_model.CpModel()
    c = [m.NewBoolVar(f'c{e}') if e not in inv else None for e in range(B)]
    def isC(l):
        return c[l]
    T = {}
    for typ in ('s', 'p'):
        for d in range(1, B):
            T[(typ, d)] = m.NewBoolVar(f'{typ}{d}')
    # intended taps (determined by wire positions); boot's clock input is chosen by the model
    fixed = set()
    for w, ins in circuit:
        e = pos[w]
        for src, J in ins:
            if src == 'CLK':
                continue
            es = pos[src]
            if J == 0:
                if es >= e: return None, 'order'
                fixed.add(('s', e - es))
            elif J == 1:
                if es > e: fixed.add(('s', e - es + B))
                else: fixed.add(('p', e - es))
            elif J == 'K':
                if es > e: fixed.add(('L0', e - es + B))
                else: fixed.add(('L1', e - es))
    for t in fixed:
        if t in T: m.Add(T[t] == 1)
        else: T[t] = True   # long taps are constants
    def tv(t):
        return T[t]
    allT = list(T.keys())
    # (B) wires see only intended inputs
    for w in wires:
        e = pos[w]
        for t in allT:
            typ, d = t
            l, J = eff_type(e, typ, d, B)
            if l in inv:
                ok = (inv[l], J) in want[w]
                if not ok:
                    if T[t] is True: return None, f'unintended {w}<-{inv[l]} via {t}'
                    m.Add(T[t] == 0)
            else:
                ok = ('CLK', J) in want[w]
                if not ok:
                    if T[t] is True: m.Add(c[l] == 0)
                    else: m.AddBoolOr([T[t].Not(), c[l].Not()])
    # boot's clock input must be realised: exists tap landing on a clock with delay 1
    bw = [w for w, ins in circuit if ('CLK', 1) in [(s, J) for s, J in ins]]
    for w in bw:
        e = pos[w]; opts = []
        for t in allT:
            typ, d = t
            if typ not in ('s', 'p'): continue
            l, J = eff_type(e, typ, d, B)
            if J == 1 and l not in inv:
                y = m.NewBoolVar('')
                m.AddImplication(y, T[t]); m.AddImplication(y, c[l]); opts.append(y)
        m.AddBoolOr(opts)
    # (A) clocks see only zero residues
    for e in range(B):
        if e in inv: continue
        for t in allT:
            typ, d = t
            l, J = eff_type(e, typ, d, B)
            if l in inv:
                if T[t] is True: m.Add(c[e] == 0)
                else: m.AddBoolOr([c[e].Not(), T[t].Not()])
            else:
                if l == e:
                    if T[t] is True: m.Add(c[e] == 0)
                    else: m.AddBoolOr([c[e].Not(), T[t].Not()])
                    continue
                if T[t] is True: m.AddBoolOr([c[e].Not(), c[l].Not()])
                else: m.AddBoolOr([c[e].Not(), T[t].Not(), c[l].Not()])
    # (D) + (E) covering of zero residues
    for e in range(B):
        if e in inv: continue
        optsD = []; optsE = []
        for t in allT:
            typ, d = t
            if typ not in ('s', 'p'): continue
            l, J = eff_type(e, typ, d, B)
            if J not in (0, 1): continue
            if l not in inv:
                y = m.NewBoolVar('')
                m.AddImplication(y, T[t]); m.AddImplication(y, c[l])
                optsD.append(y)
                if J == 0: optsE.append(y)
            elif J == 0 and l in one0w:
                optsE.append(T[t])
        m.AddBoolOr([c[e]] + optsD)
        m.AddBoolOr([c[e]] + optsE)
    if max_clocks is not None:
        m.Add(sum(x for x in c if x is not None) <= max_clocks)
    nlong = sum(1 for t in T if T[t] is True)
    obj = sum(T[t] for t in T if T[t] is not True)
    m.Minimize(obj)
    if hint is not None:
        hc, ht = hint
        for e in range(B):
            if c[e] is not None: m.AddHint(c[e], 1 if e in hc else 0)
        for t in T:
            if T[t] is not True: m.AddHint(T[t], 1 if t in ht else 0)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = time_limit
    s.parameters.num_workers = workers
    s.parameters.log_search_progress = False
    st = s.Solve(m)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None, s.StatusName(st)
    clocks = [e for e in range(B) if c[e] is not None and s.Value(c[e])]
    taps = [t for t in T if (T[t] is True) or s.Value(T[t])]
    return dict(clocks=clocks, taps=taps, ntaps=len(taps), bound=s.BestObjectiveBound() + nlong,
                status=s.StatusName(st)), None

def to_json(B, res, sol):
    out = []
    for typ, d in sol['taps']:
        if typ == 's': out.append([0, d])
        elif typ == 'p': out.append([1, d])
        elif typ == 'L0': out.append([['k', -1], d])
        elif typ == 'L1': out.append([['k', 0], d])
    return dict(B=B, res=res, clocks=sol['clocks'], taps=out)

def check_json(L):
    taps = [(tuple(q) if isinstance(q, list) else q, d) for q, d in L['taps']]
    return verify_design(L['B'], L['res'], set(L['clocks']), taps, verbose=True)

if __name__ == '__main__':
    L = json.load(open(sys.argv[1])); tl = float(sys.argv[2]) if len(sys.argv) > 2 else 300
    B = L['B']; res = L['res']
    hint_t = set()
    for q, d in L['taps']:
        if isinstance(q, list): hint_t.add(('L0' if q[1] == -1 else 'L1', d))
        else: hint_t.add(('s' if q == 0 else 'p', d))
    t0 = time.time()
    sol, err = solve(B, res, time_limit=tl, hint=(set(L['clocks']), hint_t))
    print('time', time.time() - t0, err)
    if sol:
        print('ntaps', sol['ntaps'], 'bound', sol['bound'], sol['status'], 'clocks', len(sol['clocks']))
        J = to_json(B, res, sol)
        print('verify', check_json(J))
        if len(sys.argv) > 3: json.dump(J, open(sys.argv[3], 'w'))
