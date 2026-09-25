# Iterative block shrinking with wire-position LNS: from a valid design at block length B, try
# smaller block lengths, letting every wire move within a window.  Also tries to reduce the number of
# moves at the current B.  Results: shrinklns_B<B>.json.
import json, sys, time
from cpsat_full import solve_window, load_hint
from cpsat_layout import to_json, check_json

start = json.load(open(sys.argv[1]))
Bs = [int(x) for x in sys.argv[2].split(',')]
win = int(sys.argv[3]); tl = float(sys.argv[4])
best = start
for B in Bs:
    hc, ht, hres = load_hint(best)
    hc = {c for c in hc if c < B}
    ht = {(t, d) for (t, d) in ht if d < B}
    t0 = time.time()
    sol, err = solve_window(B, best['res'], win, time_limit=tl, hint=(hc, ht, hres), workers=4)
    if sol is None:
        print('B', B, 'fail', err, 'time %.0f' % (time.time() - t0), flush=True)
        continue
    J = to_json(B, sol['res'], sol)
    ok = check_json(J)
    print('B', B, 'ntaps', sol['ntaps'], 'bound', sol['bound'], sol['status'], 'verify', ok,
          'time %.0f' % (time.time() - t0), 'res', sol['res'], flush=True)
    if ok:
        json.dump(J, open('shrinklns_B%d.json' % B, 'w'))
        best = J
