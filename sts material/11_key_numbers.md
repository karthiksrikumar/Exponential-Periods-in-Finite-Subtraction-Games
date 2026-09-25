# Key numbers (cheat sheet)

## The main theorem

| quantity | value |
|---|---|
| moves on the rule card | **26** (exactly, for every k) |
| fixed moves | 23: 9, 11, 13, 16, 51, 72, 75, 77, 84, 89, 104, 110, 112, 124, 135, 148, 156, 171, 176, 186, 209, 211, 249 |
| moves that depend on k | 3: 260(k−1)+108, 260(k−1)+136, 260(k−1)+244 |
| block length B | **260** |
| clock columns / wire columns | 29 / 8 |
| largest move | **260k − 16** |
| period | **260 · k · 2^k** = (max S + 16) · 2^((max S + 16)/260) |
| growth rate | period > 2^(max S / 260) |
| preperiod | at most 260 |

## Examples

| k | largest move | period |
|---|---|---|
| 2 | 504 | 2,080 |
| 3 | 764 | 6,240 |
| 4 | 1,024 | 16,640 |
| 6 | 1,544 | 99,840 |
| 20 | 5,184 | 5,452,595,200 |

## Guy's conjecture

| quantity | value |
|---|---|
| Guy's degree for n = 26 moves | 26·25/2 = **325** |
| first k beating (max S)^325 | **k = 6719** |
| largest move there | **1,746,924** |
| size of the period there | a 2,029-digit number |
| numbers of moves where Guy's bound provably fails | **every n ≥ 26** |
| numbers of moves still open | **3 to 25** |

## The search (moves needed)

1061 → 169 → 67 → 56 → 54 (heuristics) → 48 → 38 → 29 (exact solver) → **26** (shorter block)

Trade-off: 29 moves at B = 377, **26 at B = 260**, 28 at B = 240.

## Verification

| quantity | value |
|---|---|
| Lean code | about **3,800 lines**, 17 files |
| axioms used | 3 standard ones (propext, Classical.choice, Quot.sound) |
| `sorry` / `native_decide` | 0 / 0 |
| full Lean build | about 30–60 minutes on a laptop |
| simulated periods (k = 2…6) | 2080, 6240, 16640, 41600, 99840: all exact |
| universal game simulated | 123,181 moves, 24 million positions, 0 mismatches |
| cellular automaton rules checked | all 256 elementary rules |

## History

| year | event |
|---|---|
| 1902 | Bouton solves Nim |
| 1935/1939 | Sprague and Grundy theory |
| 1982 | *Winning Ways* (Berlekamp, Conway, Guy) |
| 1995 | Althöfer and Bültermann: cubic periods |
| 1997 | Flammenkamp: experiments suggest exponential periods (≈ 2^(0.3 m)) |
| 2019 | Guy's conjecture in *Unsolved Problems in Combinatorial Games* |
| 2024 | Miklós and Post (with a seed); Larsson and Saha survey |
| 2026 | Larsson and Manabe: still open. **This project: solved** |
