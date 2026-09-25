# End-to-end check of the constant-move universality construction:
# universal enumerating circuit (univ.py) -> General Layout Lemma design (gll.py) -> subtraction game S_L
# -> simulate the actual game -> compare every block with the circuit AND with a direct CA simulation.
import sys, subprocess, numpy as np
from univ import build_universal, elementary, ca_run
from gll import build, choose_cover, verify

def game_moves(C, K):
    names, res, clocks, B, taps, want, X = build(C.wires)
    cov, bad = choose_cover(B, res, clocks, taps, X, {'boot': 1})
    assert cov is not None, bad
    msg = verify(names, res, clocks, B, taps | cov, want, X)
    assert msg is None, msg
    alltaps = taps | cov
    S = sorted(set((a * K + b) * B + d for (a, b), d in alltaps))
    assert all(s > 0 for s in S)
    return S, names, res, clocks, B, len(alltaps)

if __name__ == '__main__':
    num = int(sys.argv[1]) if len(sys.argv) > 1 else 110
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    runs = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    rule = elementary(num); init = lambda v: (v,); bnd = (0,)
    C = build_universal(1, rule, init, bnd)
    K = L - 2
    S, names, res, clocks, B, ntaps = game_moves(C, K)
    # the SAME tap list for every L: number of moves is independent of L
    S2 = game_moves(C, K + 5)[0]
    print(f'wires={len(C.wires)} B={B} taps={ntaps} |S_L|={len(S)} |S_(L+5)|={len(S2)} maxS={max(S)}')
    R = 2 ** L
    nblocks = runs * R * L
    N = nblocks * B
    open('S_univ.txt', 'w').write('\n'.join(map(str, S)))
    subprocess.run(['./simwin.exe', 'S_univ.txt', str(N), 'w_univ.bin'], check=True)
    w = np.fromfile('w_univ.bin', dtype=np.uint8)
    V = C.simulate(K, nblocks)
    Wres = {res[n]: n for n in names}
    exp = np.zeros(N, dtype=np.uint8)
    for r in range(B):
        if r in clocks: exp[r::B] = 1
        elif r in Wres: exp[r::B] = np.frombuffer(bytes(V[Wres[r]]), dtype=np.uint8)
    mism = int(np.count_nonzero(w != exp))
    print('game vs circuit: positions', N, 'mismatches', mism)
    # read the CA state straight from the game and compare with direct CA simulation
    bad = 0
    for j in range(runs):
        X = (j + 1) % R
        hist = ca_run(rule, init, bnd, L, X, R - 1, 1)
        for T in range(R):
            for i in range(L):
                n = ((j * R + T) * L + i) * B + res['s0']
                if w[n] != hist[T][i][0]: bad += 1
    print(f'game vs direct CA (rule {num}, L={L}, {runs} runs x {R} steps x {L} cells): mismatches {bad}')
