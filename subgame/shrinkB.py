# Try shorter blocks: keep the wire residues of best29.json, re-solve clocks + covering taps with CP-SAT
# for smaller block lengths B.  A smaller B gives a faster exponential rate 2^(max S / B).
import json, sys, time
from cpsat_layout import solve, to_json, check_json

L = json.load(open('best29.json'))
res = L['res']
Bs = [int(x) for x in sys.argv[1].split(',')]
tl = float(sys.argv[2])
for B in Bs:
    hc = set(c for c in L['clocks'] if c < B)
    ht = set()
    for q, d in L['taps']:
        if isinstance(q, int) and d < B: ht.add(('s' if q == 0 else 'p', d))
    t0 = time.time()
    sol, err = solve(B, res, time_limit=tl, hint=(hc, ht), workers=4)
    if sol is None:
        print('B', B, 'no solution:', err, 'time %.0f' % (time.time() - t0), flush=True)
        continue
    J = to_json(B, res, sol)
    ok = check_json(J)
    print('B', B, 'ntaps', sol['ntaps'], 'bound', sol['bound'], sol['status'], 'clocks', len(sol['clocks']),
          'verify', ok, 'time %.0f' % (time.time() - t0), flush=True)
    if ok:
        json.dump(J, open('shrink_B%d.json' % B, 'w'))
