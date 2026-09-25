"""Live demo for "Subtraction Games Can Count and Compute".

Plain Python 3, no packages needed.   Run:   python demo.py        (menu)
                                             python demo.py all    (parts 2-4, no typing needed)
"""
import sys

# --------------------------------------------------------------------------------------------------
# The ONLY rule the computer knows:  a pile is LOSING  <=>  no move reaches a losing pile.


def losing_piles(rule_card, how_many):
    """lose[n] is True when pile n is losing for the player to move"""
    lose = []
    for n in range(how_many):
        lose.append(not any(s <= n and lose[n - s] for s in rule_card))
    return lose


def strip(lose, a, b):
    return ''.join('#' if lose[n] else '.' for n in range(a, b))


def least_period(seq, start):
    """smallest p such that seq repeats with period p from `start` on (checked to the end)"""
    N = len(seq)
    for p in range(1, (N - start) // 2 + 1):
        if all(seq[i] == seq[i + p] for i in range(start, N - p)):
            return p
    return None


# The 26-move game (the formally verified one): 23 fixed moves + 3 moves that depend on k.
B = 260
FIXED = [9, 11, 13, 16, 51, 72, 75, 77, 84, 89, 104, 110, 112, 124, 135, 148, 156, 171, 176, 186, 209, 211, 249]
WIRES = {'start': 1, 'not-marker': 10, 'marker': 26, 'no-carry-in': 35, 'not-bit': 70, 'helper': 98,
         'carry': 147, 'u (counter bit)': 222}


def rule_card(k):
    return sorted(FIXED + [B * (k - 1) + 108, B * (k - 1) + 136, B * (k - 1) + 244])


# --------------------------------------------------------------------------------------------------
def part1():
    print('\nPART 1. Play "take 1 or 2 tokens" against the computer.  Whoever cannot move loses.')
    lose = losing_piles([1, 2], 200)
    try:
        n = int(input('Choose a starting pile size (for example 10): ') or '10')
    except ValueError:
        n = 10
    first = input('Do you want to move first? [y/n]: ').strip().lower() != 'n'
    turn = 'you' if first else 'computer'
    while True:
        print('  pile = %d' % n)
        if n == 0:
            print('  You cannot move: you LOSE.' if turn == 'you' else '  The computer cannot move: you WIN!')
            break
        if turn == 'you':
            s = 0
            while s not in (1, 2) or s > n:
                try:
                    s = int(input('  take 1 or 2: '))
                except ValueError:
                    s = 0
        else:
            good = [s for s in (1, 2) if s <= n and lose[n - s]]
            s = good[0] if good else 1
            print('  computer takes %d%s' % (s, '' if good else '  (it is in a losing position and hopes you slip)'))
        n -= s
        turn = 'computer' if turn == 'you' else 'you'
    print('Secret: piles that are multiples of 3 are losing for the player to move.')


def part2():
    print('\nPART 2. Losing piles (#) and winning piles (.) for several rule cards: the patterns repeat.')
    for card in ([1, 2], [1, 3, 4], [2, 5, 7], [3, 5, 11, 16, 19]):
        lose = losing_piles(card, 400)
        p = least_period(lose, 100)
        print('\n  rule card %-20s period %d' % (card, p))
        print('  ' + strip(lose, 0, 100))
        print('  ' + ''.join('|' if (n % p == 0) else ' ' for n in range(100)) + '   <- repeats every %d' % p)


def part3(k=4):
    print('\nPART 3. The 26-move game with k = %d.  The computer knows only the rule of the game.' % k)
    card = rule_card(k)
    print('  rule card (26 moves): %s' % card)
    words = 2 ** k + 2
    lose = losing_piles(card, words * k * B)
    print('\n  Wire columns inside each block of %d pile sizes (# = losing), first 3k blocks:' % B)
    for name, col in WIRES.items():
        print('   %-16s %s' % (name, ''.join('#' if lose[t * B + col] else '.' for t in range(3 * k))))
    print('\n  Now read the column "u" in groups of k = %d blocks, least significant bit first:' % k)
    col = WIRES['u (counter bit)']
    for w in range(words):
        bits = [1 if lose[(w * k + i) * B + col] else 0 for i in range(k)]
        value = sum(b << i for i, b in enumerate(bits))
        print('   word %2d: bits %s  ->  %2d' % (w, ''.join(map(str, reversed(bits))), value))
    print('\n  It counts 1, 2, 3, ..., %d, 0, 1, ...  The game is a binary counter!' % (2 ** k - 1))


def part4(k=3):
    print('\nPART 4. Measure the period of the 26-move game directly (k = %d).' % k)
    card = rule_card(k)
    predicted = B * k * 2 ** k
    lose = losing_piles(card, 3 * predicted + 1000)
    p = least_period(lose, 1000)
    print('  largest move       = %d   (formula 260k - 16 = %d)' % (max(card), 260 * k - 16))
    print('  measured period    = %d' % p)
    print('  predicted 260*k*2^k = %d   ->  %s' % (predicted, 'MATCH' if p == predicted else 'MISMATCH'))
    print('  For k = 6719 the period has 2029 digits and beats Guy\'s conjectured bound (max S)^325.')


def main():
    if len(sys.argv) > 1 and sys.argv[1] == 'all':
        part2(); part3(); part4(); return
    while True:
        print('\n=== Subtraction games can count ===')
        print(' 1. play "take 1 or 2" against the computer')
        print(' 2. see the repeating patterns')
        print(' 3. watch the 26-move game count in binary')
        print(' 4. measure the exponential period')
        print(' q. quit')
        c = input('choose: ').strip().lower()
        if c == '1': part1()
        elif c == '2': part2()
        elif c == '3': part3()
        elif c == '4': part4()
        elif c in ('q', 'quit', 'exit', ''): break


if __name__ == '__main__':
    try:
        main()
    except (EOFError, KeyboardInterrupt):
        print()
        print('bye')
