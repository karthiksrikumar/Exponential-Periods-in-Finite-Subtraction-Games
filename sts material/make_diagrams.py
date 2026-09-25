"""Generate every diagram in `diagrams/` from scratch (python make_diagrams.py).

Only needs numpy + matplotlib.  Every picture of a game is computed from the actual game (the 26-move
game is simulated position by position); diagram 05 is a small hand-made illustration of the idea.
"""
import json, math, os
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Circle, Rectangle
from matplotlib.colors import ListedColormap

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'diagrams')
os.makedirs(OUT, exist_ok=True)

# colour-blind-safe palette (Okabe-Ito)
LOSE = '#D55E00'     # losing pile for the player to move (P-position)
WIN = '#9ecae1'      # winning pile (N-position)
BLUE, ORANGE, GREEN, SKY, PURPLE, YELLOW, GREY = '#0072B2', '#E69F00', '#009E73', '#56B4E9', '#CC79A7', '#F0E442', '#999999'
plt.rcParams.update({'font.size': 12, 'font.family': 'DejaVu Sans'})


def save(fig, name):
    fig.savefig(os.path.join(OUT, name), dpi=170, bbox_inches='tight', facecolor='white')
    plt.close(fig)
    print('wrote', name)


def outcomes(S, N):
    """w[n] = 1 if heap n is a losing position for the player to move (P-position)"""
    S = sorted(S)
    w = [0] * N
    for n in range(N):
        w[n] = 0 if any(s <= n and w[n - s] for s in S) else 1
    return w


def period(S, start=None, N=None):
    m = max(S)
    N = N or 20 * m + 200
    w = outcomes(S, N)
    for p in range(1, N // 3):
        a = N // 3
        if w[a:a + p * 2] == w[a + p:a + p * 3]:
            if all(w[i] == w[i + p] for i in range(a, N - p)):
                return p
    return None


def box(ax, x, y, w, h, text, fc='white', ec='black', fs=12, lw=1.5, round_=0.05, color='black', weight='normal'):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle='round,pad=0,rounding_size=%g' % round_, fc=fc, ec=ec, lw=lw))
    ax.text(x + w / 2, y + h / 2, text, ha='center', va='center', fontsize=fs, color=color, weight=weight, wrap=True)


def arrow(ax, p, q, text=None, color='black', lw=1.6, style='-|>', rad=0.0, fs=10, toff=(0, 0.12), ls='-'):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle=style, mutation_scale=16, color=color, lw=lw,
                                 connectionstyle='arc3,rad=%g' % rad, linestyle=ls))
    if text:
        ax.text((p[0] + q[0]) / 2 + toff[0], (p[1] + q[1]) / 2 + toff[1], text, ha='center', va='bottom',
                fontsize=fs, color=color)


# --------------------------------------------------------------------------------------------------




# 5. blocks idea (toy)
def fig_blocks():
    B, R = 18, 12
    rng = np.random.default_rng(5)
    grid = np.zeros((R, B))
    kind = ['z'] * B
    for c in (0, 7, 13): kind[c] = 'c'
    for c in (3, 10, 16): kind[c] = 'w'
    for r in range(R):
        for c in range(B):
            if kind[c] == 'c': grid[r, c] = 1
            elif kind[c] == 'w': grid[r, c] = rng.integers(0, 2)
    fig, ax = plt.subplots(figsize=(11, 6))
    ax.imshow(grid, cmap=ListedColormap(['white', 'black']), aspect='auto', extent=(-0.5, B - 0.5, R - 0.5, -0.5))
    for c in range(B + 1): ax.axvline(c - 0.5, color='#dddddd', lw=0.6)
    for r in range(R + 1): ax.axhline(r - 0.5, color='#dddddd', lw=0.6)
    for c in range(B):
        col = {'c': 'black', 'w': BLUE, 'z': GREY}[kind[c]]
        lab = {'c': 'clock', 'w': 'wire', 'z': ''}[kind[c]]
        if lab: ax.text(c, -1.1, lab, ha='center', fontsize=11, color=col, weight='bold', rotation=0)
        if kind[c] == 'w': ax.add_patch(Rectangle((c - 0.5, -0.5), 1, R, fill=False, ec=BLUE, lw=2.2))
    ax.set_xticks(range(B)); ax.set_yticks(range(R))
    ax.set_xlabel('column = position inside the block (residue r)'); ax.set_ylabel('row = block number (time)')
    ax.set_title('Cut the pile sizes into rows of equal length B:  n = (row) x B + (column)\n'
                 'black = losing pile.  Every column gets a job.', fontsize=13, pad=30)
    ax.text(B + 0.2, 1, 'CLOCK columns:\nalways losing\n(always 1)', fontsize=11, va='top')
    ax.text(B + 0.2, 4.6, 'WIRE columns:\ncarry one bit\nof information\nper row', fontsize=11, va='top', color=BLUE)
    ax.text(B + 0.2, 8.8, 'all other columns:\nalways winning\n(always 0)', fontsize=11, va='top', color='#555555')
    save(fig, '05_columns_have_jobs.png')


def design_S(k):
    L = json.load(open(os.path.join(HERE, 'data', 'design_26_moves.json')))
    B = L['B']
    S = set()
    for q, d in L['taps']:
        qq = (k + q[1]) if isinstance(q, list) else q
        S.add(qq * B + d)
    return sorted(S), L





# 9. growth
def fig_growth():
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(14, 5.2))
    rec = [tuple(map(int, l.split(','))) for l in open(os.path.join(HERE, 'data', 'five_move_records.csv')).readlines()[1:]]
    ms = [r[0] for r in rec]; ps = [r[1] for r in rec]
    a1.semilogy(ms, ps, 'o', ms=4, color=GREY, label='computer records, 5 moves (no proof)')
    ks = np.arange(2, 30)
    a1.semilogy(260 * ks - 16, 260 * ks * 2.0 ** ks, '-', color=LOSE, lw=2.5, label='our 26-move family (proved)')
    mm = np.linspace(10, 7500, 200)
    for d, ls in ((2, ':'), (3, '--')):
        a1.semilogy(mm, mm ** d, ls, color=BLUE, label='polynomial m^%d' % d)
    a1.set_xlabel('largest move m'); a1.set_ylabel('period (log scale)'); a1.set_xlim(0, 7500); a1.set_ylim(1, 1e13)
    a1.legend(fontsize=9.5, loc='upper left'); a1.grid(alpha=0.3)
    a1.set_title('Exponential growth beats every polynomial', fontsize=12.5)
    # Guy crossing (log2 scale)
    K = np.arange(100, 12001, 50)
    lp = np.log2(260 * K) + K
    lb = 325 * np.log2(260 * K - 16)
    a2.plot(K, lp, color=LOSE, lw=2.5, label='log2(period of our game)')
    a2.plot(K, lb, color=BLUE, lw=2.5, ls='--', label="log2(Guy's bound  m^325)")
    a2.axvline(6719, color='k', lw=1, ls=':')
    a2.text(6800, 2500, 'crossing at k = 6719\n(largest move 1,746,924)', fontsize=10.5)
    a2.set_xlabel('k (the counter has k bits)'); a2.set_ylabel('number of binary digits')
    a2.legend(fontsize=10, loc='upper left'); a2.grid(alpha=0.3)
    a2.set_title("Guy's conjectured bound for 26 moves is broken", fontsize=12.5)
    save(fig, '09_growth.png')


# 10. benchmarks
def fig_bench():
    stages = [('first working\nlayout', 1061), ('greedy\ncover', 169), ('annealing', 67), ('annealing', 56),
              ('annealing', 54), ('exact solver\n(clocks)', 48), ('exact solver\n(longer run)', 38),
              ('solver moves\nthe wires', 29), ('shorter\nblocks', 26)]
    fig, ax = plt.subplots(figsize=(12.5, 5))
    xs = np.arange(len(stages))
    cols = [GREY] * 5 + [BLUE] * 3 + [LOSE]
    ax.bar(xs, [s[1] for s in stages], color=cols, edgecolor='k')
    ax.set_yscale('log'); ax.set_ylim(10, 3000)
    for x, (lab, v) in zip(xs, stages):
        ax.text(x, v * 1.12, str(v), ha='center', fontsize=12, weight='bold')
    ax.set_xticks(xs); ax.set_xticklabels([s[0] for s in stages], fontsize=9.5)
    ax.set_ylabel('number of moves (log scale)')
    ax.set_title('Benchmark: moves needed for a proved exponential period, stage by stage\n'
                 '(grey: heuristic search, blue: exact constraint solving, orange: final formally verified game)',
                 fontsize=12)
    save(fig, '10_benchmark_moves.png')


# 11. universality pipeline
def fig_pipeline():
    fig, ax = plt.subplots(figsize=(14, 4.3))
    ax.set_xlim(0, 14); ax.set_ylim(0, 4); ax.axis('off')
    ax.text(7, 3.65, 'Universality: any bounded-memory computation fits inside a subtraction game with a FIXED number of moves',
            ha='center', fontsize=13.5, weight='bold')
    B = [(0.2, 'Any program\n(Turing machine with a\nbounded tape)', '#e8f1fa'),
         (3.7, 'A row of cells with a\nlocal update rule\n(cellular automaton)', '#e8f5ee'),
         (7.2, 'A fixed logic circuit\nwith delay lines\n(NOR gates)', '#fdf1e2'),
         (10.7, 'A subtraction game\nwhose moves depend only\non the memory size', '#fbe3d7')]
    for x, t, c in B:
        box(ax, x, 1.1, 3.0, 1.7, t, fc=c, fs=11.5)
    labs = ['TM.tm_universal', 'Univ.universal', 'GLL.simulate']
    for i in range(3):
        x0 = B[i][0] + 3.0; x1 = B[i + 1][0]
        arrow(ax, (x0 + 0.02, 1.95), (x1 - 0.02, 1.95), None)
        ax.text((x0 + x1) / 2, 0.7, labs[i], ha='center', fontsize=9.5, color=GREEN, weight='bold')
    ax.text(7, 0.15, 'green = name of the formally verified Lean theorem for that step', ha='center', fontsize=10, color=GREEN)
    save(fig, '11_universality_pipeline.png')




# 14. ELI5 light bulbs
def fig_lights():
    fig, ax = plt.subplots(figsize=(13, 3.8))
    ax.set_xlim(-0.5, 16); ax.set_ylim(-1.8, 2.2); ax.axis('off')
    w = outcomes([1, 2], 16)
    ax.text(7.7, 1.85, 'Explain like I\'m 5: a row of light bulbs', ha='center', fontsize=15, weight='bold')
    ax.text(7.7, 1.25, 'Rule: a new bulb turns ON only if the bulbs 1 and 2 places before it are both OFF.',
            ha='center', fontsize=12)
    for i in range(16):
        on = w[i]
        ax.add_patch(Circle((i, 0), 0.36, fc=YELLOW if on else '#dddddd', ec='k', lw=1.5))
        if on:
            for a in np.linspace(0, 2 * np.pi, 9)[:-1]:
                ax.plot([i + 0.45 * np.cos(a), i + 0.6 * np.cos(a)], [0.45 * np.sin(a), 0.6 * np.sin(a)],
                        color=ORANGE, lw=1.3)
        ax.text(i, -0.7, str(i), ha='center', fontsize=10)
    ax.text(7.7, -1.5, 'ON, off, off, ON, off, off, ...  The pattern repeats.  With a longer rule (26 look-back distances)\n'
            'the bulbs can be made to count in binary, and then the pattern takes astronomically long to repeat.',
            ha='center', fontsize=11)
    save(fig, '14_eli5_light_bulbs.png')



# --------------------------------------------------------------------------------------------------
def edge_point(b, t):
    """point where the line from the centre of box b=(x,y,w,h) towards point t leaves the box"""
    x, y, w, h = b
    cx, cy = x + w / 2, y + h / 2
    dx, dy = t[0] - cx, t[1] - cy
    if dx == 0 and dy == 0:
        return cx, cy
    sx = (w / 2) / abs(dx) if dx else float('inf')
    sy = (h / 2) / abs(dy) if dy else float('inf')
    s = min(sx, sy)
    return cx + dx * s, cy + dy * s


def centre(b):
    return b[0] + b[2] / 2, b[1] + b[3] / 2


def connect(ax, a, b, text=None, color='black', rad=0.0, fs=9.5, lw=1.6, tpos=0.5, toff=(0, 0), pa=None, pb=None):
    p = pa or edge_point(a, centre(b))
    q = pb or edge_point(b, centre(a))
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle='-|>', mutation_scale=16, color=color, lw=lw,
                                 connectionstyle='arc3,rad=%g' % rad, shrinkA=2, shrinkB=2))
    if text:
        mx = p[0] + (q[0] - p[0]) * tpos + toff[0]
        my = p[1] + (q[1] - p[1]) * tpos + toff[1]
        ax.text(mx, my, text, ha='center', va='center', fontsize=fs, color=color,
                bbox=dict(fc='white', ec='none', pad=1.2))


def draw_box(ax, b, text, fc='white', fs=11, weight='normal'):
    box(ax, b[0], b[1], b[2], b[3], text, fc=fc, fs=fs, weight=weight)


# 1. the game
def fig_game():
    fig, ax = plt.subplots(figsize=(12, 4.8))
    ax.set_xlim(-0.6, 13); ax.set_ylim(-2.5, 3.2); ax.axis('off')
    ax.text(6.25, 2.9, 'A subtraction game: a pile of tokens, a rule card, two players taking turns',
            ha='center', fontsize=15, weight='bold')
    for i in range(7):
        ax.add_patch(Circle((0.5 + 0.42 * (i % 3) + 0.2 * (i // 3), 1.05 + 0.36 * (i // 3)), 0.19, fc=YELLOW, ec='k'))
    ax.text(1.0, 0.45, 'pile of 7 tokens', ha='center', fontsize=11)
    box(ax, 2.3, 0.8, 2.3, 1.15, 'Rule card:\nyou may take\n1 or 2 tokens', fc='#fff7d6', fs=12)
    ax.text(5.1, 1.75, 'Players alternate.  The player who cannot move LOSES.', ha='left', fontsize=12)
    ax.text(5.1, 1.15, 'Question: from a pile of n tokens, can the player to move\nforce a win (if both play perfectly)?',
            ha='left', fontsize=12, va='center')
    w = outcomes([1, 2], 13)
    for n in range(13):
        c = LOSE if w[n] else WIN
        ax.add_patch(Rectangle((n, -1.2), 0.92, 0.92, fc=c, ec='k'))
        ax.text(n + 0.46, -0.74, str(n), ha='center', va='center', fontsize=13, weight='bold',
                color='white' if w[n] else 'black')
        ax.text(n + 0.46, -1.55, 'LOSE' if w[n] else 'win', ha='center', fontsize=8.5,
                color=LOSE if w[n] else '#3a6f96', weight='bold' if w[n] else 'normal')
    ax.text(-0.5, -0.74, 'n =', ha='right', va='center', fontsize=12)
    for t in (4, 3):
        ax.add_patch(FancyArrowPatch((5.46, -0.26), (t + 0.46, -0.26), arrowstyle='-|>', mutation_scale=14,
                                     color='k', lw=1.4, connectionstyle='arc3,rad=0.55'))
    ax.text(4.9, 0.42, 'from 5 you can move to 4 or 3', ha='center', fontsize=9.5)
    ax.text(6.3, -2.3, 'Losing piles (orange) are 0, 3, 6, 9, 12, ...: from them every move reaches a winning pile.  '
            'The pattern repeats every 3.', ha='center', fontsize=11)
    save(fig, '01_the_game.png')


# 2. patterns repeat
def fig_patterns():
    cards = [([1, 2], 'take 1 or 2'), ([1, 3, 4], 'take 1, 3 or 4'), ([2, 5, 7], 'take 2, 5 or 7'),
             ([3, 5, 11, 16, 19], 'take 3, 5, 11, 16 or 19')]
    N = 90
    fig, axes = plt.subplots(len(cards), 1, figsize=(13, 6.8))
    for ax, (S, name) in zip(axes, cards):
        w = outcomes(S, N)
        p = period(S)
        ax.imshow(np.array([w]), cmap=ListedColormap([WIN, LOSE]), aspect='auto', extent=(-0.5, N - 0.5, 0, 1))
        ax.set_yticks([]); ax.set_xticks(range(0, N, 10))
        for x in range(0, N, p):
            ax.axvline(x - 0.5, color='black', lw=1.6, ls='--')
        ax.set_title('Rule card "%s":  the pattern repeats every %d piles (dashed lines)' % (name, p),
                     fontsize=12, loc='left', pad=6)
    axes[-1].set_xlabel('pile size n   (orange = losing for the player to move, blue = winning)')
    fig.suptitle('Every rule card gives a pattern that eventually repeats.  How long can the repeat be?', fontsize=14,
                 weight='bold')
    fig.tight_layout()
    save(fig, '02_patterns_repeat.png')


# 3. the NOR rule
def fig_nor():
    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(13.5, 4.6), gridspec_kw={'width_ratios': [2.2, 1]})
    S = [1, 3, 4]
    w = outcomes(S, 12)
    ax.set_xlim(-0.6, 11); ax.set_ylim(-1.9, 3.0); ax.axis('off')
    for n in range(11):
        c = LOSE if w[n] else WIN
        ax.add_patch(Rectangle((n, 0), 0.9, 0.9, fc=c, ec='k'))
        ax.text(n + 0.45, 0.45, str(n), ha='center', va='center', fontsize=13, weight='bold',
                color='white' if w[n] else 'black')
    n = 9
    for s, rad, dy in ((1, 0.9, 0.55), (3, 0.55, 1.05), (4, 0.5, 1.45)):
        ax.add_patch(FancyArrowPatch((n + 0.45, 0.92), (n - s + 0.45, 0.92), arrowstyle='-|>', mutation_scale=14,
                                     color='k', lw=1.4, connectionstyle='arc3,rad=%g' % rad))
        ax.text(n - s / 2 + 0.45, 0.92 + dy, 'take %d' % s, ha='center', fontsize=10,
                bbox=dict(fc='white', ec='none', pad=0.5))
    ax.text(5, -0.8, 'Rule card {1, 3, 4}.  From pile 9 every move (to 8, 6 or 5) reaches a WINNING pile (blue),\n'
            'so 9 is LOSING.  A pile is losing exactly when none of the piles it can move to is losing.',
            ha='center', fontsize=11)
    ax.text(5, 2.85, 'The rule that decides every pile', ha='center', fontsize=14, weight='bold')
    ax2.axis('off'); ax2.set_xlim(0, 3); ax2.set_ylim(-0.6, 5)
    ax2.text(1.5, 4.7, 'This is a NOR gate', ha='center', fontsize=14, weight='bold')
    rows = [('input A', 'input B', 'A NOR B'), ('off', 'off', 'ON'), ('off', 'on', 'off'), ('on', 'off', 'off'),
            ('on', 'on', 'off')]
    for i, r in enumerate(rows):
        for j, t in enumerate(r):
            fc = '#eeeeee' if i == 0 else ('#ffe0cc' if t == 'ON' else 'white')
            ax2.add_patch(Rectangle((j, 3.8 - 0.75 * i), 1, 0.7, fc=fc, ec='k'))
            ax2.text(j + 0.5, 3.8 - 0.75 * i + 0.35, t, ha='center', va='center', fontsize=11,
                     weight='bold' if i == 0 or t == 'ON' else 'normal')
    ax2.text(1.5, -0.45, 'ON (losing) only if ALL inputs are off.\nNOR gates alone can build any computer.',
             ha='center', fontsize=10.5)
    save(fig, '03_nor_rule.png')


# 4. shift register view
def fig_register():
    fig, ax = plt.subplots(figsize=(12.5, 3.9))
    ax.set_xlim(-1, 14.4); ax.set_ylim(-2.2, 1.9); ax.axis('off')
    S = [1, 3, 4]
    w = outcomes(S, 40)
    n0 = 20
    ax.text(6.7, 1.55, 'The game as a machine: a tape of past answers and one NOR gate', ha='center', fontsize=15,
            weight='bold')
    for i in range(12):
        nn = n0 - 11 + i
        c = LOSE if w[nn] else WIN
        ax.add_patch(Rectangle((i, 0), 0.9, 0.9, fc=c, ec='k'))
        ax.text(i + 0.45, 0.45, str(nn), ha='center', va='center', fontsize=10, color='white' if w[nn] else 'black')
    ax.add_patch(Rectangle((12.3, 0), 0.9, 0.9, fc='white', ec='k', lw=2, ls='--'))
    ax.text(12.75, 0.45, '%d\n?' % (n0 + 1), ha='center', va='center', fontsize=10)
    box(ax, 9.7, -1.95, 2.0, 0.9, 'NOR', fc='#ffe0cc', fs=14, weight='bold')
    for s in S:
        x = 12 - s + 0.45
        ax.add_patch(FancyArrowPatch((x, -0.02), (10.7, -1.02), arrowstyle='-|>', mutation_scale=14, color=BLUE, lw=1.5))
        ax.text(x - 0.35, -0.4, 'back %d' % s, ha='center', fontsize=9, color=BLUE,
                bbox=dict(fc='white', ec='none', pad=0.3))
    ax.add_patch(FancyArrowPatch((11.72, -1.5), (12.75, -0.04), arrowstyle='-|>', mutation_scale=14, color='k', lw=1.5))
    ax.text(13.3, -1.35, 'writes the\nnext answer', ha='left', fontsize=10)
    ax.text(4.3, -1.5, 'The rule card = the distances the machine looks back.\n'
            'The largest move m = the length of its memory.', ha='center', fontsize=11)
    save(fig, '04_game_as_machine.png')


# 6. the real game
def fig_real():
    k = 3
    S, L = design_S(k)
    B = L['B']
    rows = 2 * k * 2 ** k
    w = np.array(outcomes(S, rows * B), dtype=np.uint8).reshape(rows, B)
    fig = plt.figure(figsize=(13, 7.2))
    ax = fig.add_axes([0.07, 0.08, 0.9, 0.66])
    ax.imshow(w, cmap=ListedColormap(['white', 'black']), aspect='auto', interpolation='nearest')
    names = {'boot': 'start', 'nm': 'not-marker', 'marker': 'marker', 'ncin': 'no-carry-in', 'nb': 'not-bit',
             'g1': 'helper', 'carry': 'carry', 'u': 'u = the counter bit'}
    for nm, r in L['res'].items():
        ax.annotate(names[nm], (r, -0.6), (r + 2, -4.5), ha='left', va='bottom', fontsize=9.5, color=BLUE,
                    rotation=40, arrowprops=dict(arrowstyle='-', color=BLUE, lw=0.8), annotation_clip=False)
    ax.set_xlabel('position inside the block (block length B = %d)' % B)
    ax.set_ylabel('block number')
    fig.text(0.5, 0.955, 'The actual 26-move game (k = 3): black = losing piles', ha='center', fontsize=14,
             weight='bold')
    fig.text(0.5, 0.915, 'Solid columns = clocks.  Broken columns = the 8 wires of a tiny computer (labelled in blue).',
             ha='center', fontsize=11.5)
    save(fig, '06_the_real_game.png')


# 7. the counter circuit
def fig_circuit():
    fig, ax = plt.subplots(figsize=(13, 7.8))
    ax.set_xlim(-0.3, 13.2); ax.set_ylim(-0.4, 8); ax.axis('off')
    ax.text(6.3, 7.65, 'The tiny computer inside the game: a binary counter built from 8 NOR gates', ha='center',
            fontsize=15, weight='bold')
    W, H = 2.0, 0.95
    P = {'clock': (0.3, 5.7), 'boot': (2.9, 5.7), 'nm': (5.5, 5.7), 'marker': (8.1, 5.7),
         'nb': (0.6, 3.25), 'ncin': (3.6, 3.25), 'g1': (7.2, 3.25), 'carry': (2.2, 0.9), 'u': (6.2, 0.9)}
    B = {k: (x, y, W, H) for k, (x, y) in P.items()}
    lab = {'clock': 'clock\n(always 1)', 'boot': 'start', 'nm': 'not-marker', 'marker': 'marker\n(word start)',
           'ncin': 'no-carry-in', 'nb': 'not-bit', 'g1': 'helper', 'carry': 'carry', 'u': 'u = the bit\nbeing stored'}
    for k, b in B.items():
        draw_box(ax, b, lab[k], fc='#eeeeee' if k == 'clock' else ('#ffe0cc' if k == 'u' else 'white'), fs=10.5)
    X = lambda k, f: B[k][0] + W * f          # point along the width
    top = lambda k: B[k][1] + H
    bot = lambda k: B[k][1]
    # same-block wires (black)
    connect(ax, B['boot'], B['nm']); connect(ax, B['nm'], B['marker'])
    connect(ax, B['marker'], B['g1'], pa=(X('marker', 0.35), bot('marker')), pb=(X('g1', 0.6), top('g1')))
    connect(ax, B['marker'], B['ncin'], pa=(X('marker', 0.1), bot('marker')), pb=(X('ncin', 0.75), top('ncin')))
    connect(ax, B['ncin'], B['carry'], pa=(X('ncin', 0.3), bot('ncin')), pb=(X('carry', 0.75), top('carry')), rad=0.15)
    connect(ax, B['nb'], B['carry'], pa=(X('nb', 0.6), bot('nb')), pb=(X('carry', 0.25), top('carry')))
    connect(ax, B['g1'], B['u'], pa=(X('g1', 0.3), bot('g1')), pb=(X('u', 0.45), top('u')))
    connect(ax, B['carry'], B['u'])
    # delayed wires (orange)
    connect(ax, B['clock'], B['boot'], '1 block ago', color=ORANGE, toff=(0, 0.3))
    connect(ax, B['marker'], B['nm'], 'k blocks ago', color=ORANGE, rad=0.55,
            pa=(X('marker', 0.5), top('marker')), pb=(X('nm', 0.5), top('nm')), toff=(0, 0.72))
    connect(ax, B['carry'], B['ncin'], '1 block ago', color=ORANGE, rad=0.25,
            pa=(X('carry', 0.95), top('carry')), pb=(X('ncin', 0.55), bot('ncin')), tpos=0.5, toff=(0.75, -0.05))
    connect(ax, B['carry'], B['g1'], '1 block ago', color=ORANGE, rad=0.0,
            pa=(X('carry', 1.0), B['carry'][1] + 0.8), pb=(X('g1', 0.05), bot('g1')), tpos=0.62, toff=(-0.2, 0.25))
    connect(ax, B['u'], B['g1'], 'k blocks ago', color=ORANGE, rad=0.35,
            pa=(X('u', 0.9), top('u')), pb=(X('g1', 0.9), bot('g1')), toff=(0.9, 0))
    # u -> not-bit, routed around the bottom
    ux, uy = X('u', 0.5), bot('u')
    path_y = -0.2
    ax.plot([ux, ux, 0.05, 0.05], [uy, path_y, path_y, B['nb'][1] + H / 2], color=ORANGE, lw=1.6)
    ax.add_patch(FancyArrowPatch((0.05, B['nb'][1] + H / 2), (B['nb'][0] - 0.02, B['nb'][1] + H / 2),
                                 arrowstyle='-|>', mutation_scale=16, color=ORANGE, lw=1.6))
    ax.text(3.6, path_y - 0.02, 'k blocks ago', ha='center', va='center', fontsize=9.5, color=ORANGE,
            bbox=dict(fc='white', ec='none', pad=1.2))
    ax.text(10.4, 2.3, 'Every box = one NOR gate:\nit is ON only if every\narrow into it is OFF.\n\n'
            'Black arrow: read in the\nsame block.\nOrange arrow: read an\nearlier block (a delay).\n\n'
            'new bit = old bit XOR carry-in\ncarry-out = old bit AND carry-in',
            fontsize=10.5, va='center', bbox=dict(fc='#f7f7f7', ec='#cccccc'))
    save(fig, '07_counter_circuit.png')

# 8. it counts (read off the simulated game)
def fig_counts():
    k = 4
    S, L = design_S(k)
    B = L['B']
    words = 2 ** k + 2
    blocks = words * k
    w = outcomes(S, blocks * B)
    ru = L['res']['u']
    M = np.zeros((k, words))
    for word in range(words):
        for i in range(k):
            M[i, word] = w[(word * k + i) * B + ru]
            assert M[i, word] == (((word + 1) % 2 ** k) >> i) & 1   # the proved closed form
    fig, ax = plt.subplots(figsize=(12, 5.6))
    ax.imshow(M, cmap=ListedColormap(['white', 'black']), aspect='auto', extent=(-0.5, words - 0.5, k - 0.5, -0.5))
    for x in range(words + 1): ax.axvline(x - 0.5, color='#bbbbbb', lw=0.8)
    for y in range(k + 1): ax.axhline(y - 0.5, color='#bbbbbb', lw=0.8)
    ax.set_yticks(range(k)); ax.set_yticklabels(['bit 0 (1s)', 'bit 1 (2s)', 'bit 2 (4s)', 'bit 3 (8s)'])
    ax.set_xticks(range(words))
    ax.set_xticklabels([str((wd + 1) % 2 ** k) for wd in range(words)], fontsize=12, color=LOSE, weight='bold')
    ax.set_xlabel('number stored in each word (one word = k = 4 blocks of the game)')
    ax.set_title('Read straight off the 26-move game (k = 4): the counter column u spells 1, 2, 3, ..., 15, 0, 1, ...\n'
                 'in binary.  It needs 2^k words to return to the start, so the period is  B x k x 2^k  positions.',
                 fontsize=12.5)
    save(fig, '08_it_counts.png')

# 12. complexity map
def fig_complexity():
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(14.5, 5.8), gridspec_kw={'width_ratios': [1.5, 1]})
    a1.set_xlim(0, 10.6); a1.set_ylim(0, 6); a1.axis('off')
    a1.text(5.3, 5.65, 'How hard is it to predict who wins from a huge pile?', ha='center', fontsize=13.5,
            weight='bold')
    cols = [('One fixed game', 'Easy.\nCompute the repeating\npattern once, then\nlook up the answer.', '#e8f5ee'),
            ('Moves written out\n(unary), fixed\nnumber of moves', 'PSPACE-complete:\nas hard as any\nmemory-bounded\npuzzle.',
             '#fdf1e2'),
            ('Moves written in\nbinary, fixed\nnumber of moves', 'EXPTIME-complete:\nprovably NO fast\nalgorithm exists.',
             '#fbe3d7')]
    for i, (h, t, c) in enumerate(cols):
        box(a1, 0.15 + 3.5 * i, 3.45, 3.2, 1.55, h, fc='#f4f4f4', fs=10.5, weight='bold')
        box(a1, 0.15 + 3.5 * i, 0.95, 3.2, 2.25, t, fc=c, fs=10.5)
    a1.text(5.3, 0.35, 'The pile size n is always written in binary (it can be astronomically large).', ha='center',
            fontsize=10)
    a2.set_xlim(0, 10); a2.set_ylim(-1.6, 10.2); a2.axis('off')
    for r, lab, c in ((4.8, 'EXPTIME', '#fbe3d7'), (3.7, 'PSPACE', '#fdf1e2'), (2.5, 'NP', '#eef3f8'),
                      (1.3, 'P', '#e8f5ee')):
        a2.add_patch(Circle((5, 5), r, fc=c, ec='k'))
        a2.text(5, 5 + r - 0.55, lab, ha='center', fontsize=12, weight='bold')
    a2.text(5, 4.6, 'fast\nalgorithms', ha='center', va='center', fontsize=9.5)
    a2.text(5, -1.2, 'Known: P is strictly smaller than EXPTIME\n(time hierarchy theorem).', ha='center', fontsize=10)
    save(fig, '12_complexity_map.png')


# 13. proof map
def fig_proofmap():
    fig, ax = plt.subplots(figsize=(14, 7.6))
    ax.set_xlim(0, 14); ax.set_ylim(0, 8.2); ax.axis('off')
    ax.text(7, 7.85, 'What the proof assistant (Lean) checked: files and main theorems', ha='center', fontsize=14.5,
            weight='bold')
    W, H = 2.35, 1.1
    N = {'Basic': (0.2, 6.2, 'Basic\nthe game, P-positions'), 'Arith': (0.2, 4.7, 'Arith\nblock arithmetic'),
         'Simulation': (2.95, 5.45, 'Simulation\ncircuit -> game'),
         'Counter': (0.2, 3.0, 'Bits + Counter\nthe NOR counter'),
         'Design': (2.95, 3.0, 'Design\n26 moves; layout\nchecked by kernel'),
         'Period': (5.7, 3.0, 'Period\nexact least period'),
         'Main': (8.45, 3.75, 'Main + Exact\nmain_exact,\nguy_explicit'), 'Grundy': (8.45, 2.2, 'Grundy\nnim-values'),
         'Open': (11.3, 2.2, 'OpenProblem\nall n >= 26;\nOpenGap stated'),
         'Layout': (5.7, 6.2, 'Layout\ngeneral layout\nlemma'), 'Transport': (8.45, 6.2, 'Transport\nany wire names'),
         'Univ': (11.3, 6.2, 'UnivCore +\nUniversal'), 'TM': (11.3, 4.4, 'TuringSim\ntm_universal')}
    col = {'Basic': '#eeeeee', 'Arith': '#eeeeee', 'Simulation': '#eeeeee', 'Counter': '#fdf1e2',
           'Design': '#fbe3d7', 'Period': '#fdf1e2', 'Main': '#fbe3d7', 'Grundy': '#fdf1e2', 'Open': '#fbe3d7',
           'Layout': '#e8f1fa', 'Transport': '#e8f1fa', 'Univ': '#dbe9f6', 'TM': '#dbe9f6'}
    Bx = {k: (x, y, W, H) for k, (x, y, t) in N.items()}
    for k, (x, y, t) in N.items():
        draw_box(ax, Bx[k], t, fc=col[k], fs=9.8)
    for a, b in [('Basic', 'Simulation'), ('Arith', 'Simulation'), ('Simulation', 'Design'), ('Counter', 'Design'),
                 ('Design', 'Period'), ('Period', 'Main'), ('Period', 'Grundy'), ('Main', 'Open'),
                 ('Simulation', 'Layout'), ('Layout', 'Transport'), ('Transport', 'Univ'), ('Univ', 'TM')]:
        connect(ax, Bx[a], Bx[b], color='#555555', lw=1.3)
    ax.text(7, 0.75, 'About 3,800 lines.  No unproved steps ("sorry"); only Lean\'s three standard axioms.\n'
            'Orange: the exponential-period theorem and Guy\'s conjecture.   Blue: universality and Turing machines.',
            ha='center', fontsize=10.5)
    save(fig, '13_proof_map.png')


# 15. timeline
def fig_timeline():
    ev = [(1935, 'Sprague & Grundy:\nevery such game\nbehaves like Nim'),
          (1982, 'Winning Ways\n(Berlekamp,\nConway, Guy)'),
          (1995, 'Althöfer &\nBültermann:\ncubic periods'),
          (1997, 'Flammenkamp:\nexperiments suggest\nexponential periods'),
          (2019, "Guy's conjecture\nrestated in Unsolved\nProblems (Nowakowski)"),
          (2024, 'Miklós & Post\n(with a seed);\nLarsson & Saha'),
          (2026, 'Larsson & Manabe:\nstill open'),
          (2026, 'THIS PROJECT:\nexponential periods\nwith 26 moves')]
    fig, ax = plt.subplots(figsize=(14, 4.6))
    n = len(ev)
    ax.set_xlim(-0.6, n - 0.4); ax.set_ylim(-3.1, 3.1); ax.axis('off')
    ax.plot([-0.5, n - 0.5], [0, 0], color='k', lw=2)
    for i, (y, t) in enumerate(ev):
        up = 1 if i % 2 == 0 else -1
        mine = t.startswith('THIS')
        c = LOSE if mine else BLUE
        ax.plot([i, i], [0, 0.75 * up], color=c, lw=1.5)
        ax.plot(i, 0, 'o', color=c, ms=10)
        s = ('%d\n%s' % (y, t)) if up > 0 else ('%s\n%d' % (t, y))
        ax.text(i, 0.85 * up, s, ha='center', va='bottom' if up > 0 else 'top', fontsize=9.8,
                color=LOSE if mine else 'black', weight='bold' if mine else 'normal')
    ax.set_title('A 90-year-old family of games and a decades-old question (not to scale)', fontsize=14,
                 weight='bold')
    save(fig, '15_timeline.png')


if __name__ == '__main__':
    fig_game(); fig_patterns(); fig_nor(); fig_register(); fig_blocks(); fig_real(); fig_circuit(); fig_counts()
    fig_growth(); fig_bench(); fig_pipeline(); fig_complexity(); fig_proofmap(); fig_lights(); fig_timeline()
