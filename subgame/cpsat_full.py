# CP-SAT with wire positions free inside windows around a start design (large-neighbourhood search).
# Minimises the number of taps (moves) subject to the exact conditions (A)-(E).
import json, sys, time, random
from ortools.sat.python import cp_model
from lay import CIRCUIT, WIRES, logical
from cpsat_layout import want_sets, eff_type, to_json, check_json

def solve_window(B, res0, win, circuit=CIRCUIT, time_limit=300, hint=None, workers=4, seed=0,
                 fix=()):
    want = want_sets(circuit)
    wires = [w for w, _ in circuit]
    v0 = logical(8, 1)
    ones0 = [w for w in wires if v0[w][0]]
    m = cp_model.CpModel()
    AUX = []   # (y, a, b): y <-> a & b  (only y -> a, y -> b enforced)
    cand = {}
    for w in wires:
        if w in fix or win == 0:
            cand[w] = [res0[w]]
        else:
            cand[w] = sorted({(res0[w] + dd) % B for dd in range(-win, win + 1)})
    W = {(w, e): m.NewBoolVar(f'w_{w}_{e}') for w in wires for e in cand[w]}
    for w in wires:
        m.AddExactlyOne([W[(w, e)] for e in cand[w]])
    occ = {}
    for (w, e), v in W.items():
        occ.setdefault(e, []).append(v)
    c = [m.NewBoolVar(f'c{e}') for e in range(B)]
    for e in range(B):
        m.Add(c[e] + sum(occ.get(e, [])) <= 1)
    types = ('s', 'p', 'L0', 'L1')
    T = {(typ, d): m.NewBoolVar(f'{typ}{d}') for typ in types for d in range(1, B)}
    # (1) intended edges
    for w, ins in circuit:
        for src, J in ins:
            if src == 'CLK':
                # boot: exists tap with delay J landing on a clock (for each position of w)
                for e in cand[w]:
                    opts = []
                    for typ in ('s', 'p'):
                        for d in range(1, B):
                            l, JJ = eff_type(e, typ, d, B)
                            if JJ == J:
                                y = m.NewBoolVar('')
                                m.AddImplication(y, T[(typ, d)]); m.AddImplication(y, c[l])
                                AUX.append((y, ('T', (typ, d)), ('c', l)))
                                opts.append(y)
                    m.AddBoolOr(opts).OnlyEnforceIf(W[(w, e)])
                continue
            for ej in cand[w]:
                for ei in cand[src]:
                    if ej == ei: continue
                    d = (ej - ei) % B
                    ok = None
                    for typ in types:
                        l, JJ = eff_type(ej, typ, d, B)
                        if JJ == J: ok = typ
                    if ok is None:
                        m.AddBoolOr([W[(w, ej)].Not(), W[(src, ei)].Not()])
                    else:
                        m.AddBoolOr([W[(w, ej)].Not(), W[(src, ei)].Not(), T[(ok, d)]])
    # (2) unintended wire-wire landings
    for w in wires:
        for i in wires:
            if i == w: continue
            for ej in cand[w]:
                for ei in cand[i]:
                    if ej == ei:
                        m.AddBoolOr([W[(w, ej)].Not(), W[(i, ei)].Not()]); continue
                    d = (ej - ei) % B
                    for typ in types:
                        l, JJ = eff_type(ej, typ, d, B)
                        if (i, JJ) not in want[w]:
                            m.AddBoolOr([W[(w, ej)].Not(), W[(i, ei)].Not(), T[(typ, d)].Not()])
    # (3) wire sees clock (only boot's CLK input allowed, with the right delay)
    for w in wires:
        for e in cand[w]:
            for (typ, d), tv in T.items():
                l, JJ = eff_type(e, typ, d, B)
                if ('CLK', JJ) in want[w]: continue
                m.AddBoolOr([W[(w, e)].Not(), tv.Not(), c[l].Not()])
    # (4) clock sees clock, (5) clock sees wire
    for e in range(B):
        for (typ, d), tv in T.items():
            l, JJ = eff_type(e, typ, d, B)
            m.AddBoolOr([c[e].Not(), tv.Not(), c[l].Not()])
            for i in wires:
                if (i, l) in W:
                    m.AddBoolOr([c[e].Not(), tv.Not(), W[(i, l)].Not()])
    # (6) covering (D) and (E)
    for e in range(B):
        optsD = []; optsE = []
        for typ in ('s', 'p'):
            for d in range(1, B):
                l, JJ = eff_type(e, typ, d, B)
                if JJ not in (0, 1): continue
                y = m.NewBoolVar('')
                m.AddImplication(y, T[(typ, d)]); m.AddImplication(y, c[l])
                AUX.append((y, ('T', (typ, d)), ('c', l)))
                optsD.append(y)
                if JJ == 0:
                    optsE.append(y)
                    for i in ones0:
                        if (i, l) in W:
                            z = m.NewBoolVar('')
                            m.AddImplication(z, T[(typ, d)]); m.AddImplication(z, W[(i, l)])
                            AUX.append((z, ('T', (typ, d)), ('W', (i, l))))
                            optsE.append(z)
        m.AddBoolOr([c[e]] + occ.get(e, []) + optsD)
        m.AddBoolOr([c[e]] + occ.get(e, []) + optsE)
    m.Minimize(sum(T.values()))
    if hint is not None:
        hc, ht, hres = hint
        for e in range(B): m.AddHint(c[e], 1 if e in hc else 0)
        for k, tv in T.items(): m.AddHint(tv, 1 if k in ht else 0)
        for (w, e), v in W.items(): m.AddHint(v, 1 if hres[w] == e else 0)
        def hv(x):
            kind, key = x
            if kind == 'T': return 1 if key in ht else 0
            if kind == 'c': return 1 if key in hc else 0
            w, e = key; return 1 if hres[w] == e else 0
        for y, a, b in AUX: m.AddHint(y, hv(a) & hv(b))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = time_limit
    s.parameters.num_workers = workers
    s.parameters.random_seed = seed
    s.parameters.log_search_progress = False
    st = s.Solve(m)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None, s.StatusName(st)
    res = {w: [e for e in cand[w] if s.Value(W[(w, e)])][0] for w in wires}
    clocks = [e for e in range(B) if s.Value(c[e])]
    taps = [k for k, tv in T.items() if s.Value(tv)]
    return dict(res=res, clocks=clocks, taps=taps, ntaps=len(taps), bound=s.BestObjectiveBound(),
                status=s.StatusName(st)), None

def load_hint(L):
    ht = set()
    for q, d in L['taps']:
        if isinstance(q, list): ht.add(('L0' if q[1] == -1 else 'L1', d))
        else: ht.add(('s' if q == 0 else 'p', d))
    return set(L['clocks']), ht, L['res']

if __name__ == '__main__':
    L = json.load(open(sys.argv[1])); win = int(sys.argv[2]); tl = float(sys.argv[3]); out = sys.argv[4]
    rounds = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    best = L
    for r in range(rounds):
        B = best['B']
        t0 = time.time()
        sol, err = solve_window(B, best['res'], win, time_limit=tl, hint=load_hint(best), seed=r)
        if sol is None:
            print('round', r, 'fail', err, flush=True); continue
        J = to_json(B, sol['res'], sol)
        ok = check_json(J)
        print('round', r, 'ntaps', sol['ntaps'], 'bound', sol['bound'], sol['status'], 'verify', ok,
              'time %.0f' % (time.time() - t0), 'res', sol['res'], flush=True)
        if ok and sol['ntaps'] <= len(best['taps']):
            best = J; json.dump(J, open(out, 'w'))
