# Subtraction Games Can Count and Compute

**Exponentially long periods in subtraction games, a counterexample to Guy's conjecture, and universality with a bounded number of moves, with a Lean 4 formalization.**

## The results

In the subtraction game with move set `S`, a heap of `n` tokens is reduced by some `s ∈ S` per move; the player who cannot move loses. The win/loss (P/N) sequence is eventually periodic. Guy conjectured that for `|S| = n` the period is bounded by a polynomial of degree `n(n-1)/2` in `max S`. Flammenkamp conjectured the opposite from experiments. Whether super-polynomial periods exist at all was open (Miklós–Post 2024; Larsson–Saha 2024; Larsson–Manabe 2026).

**Theorem 1 (exponential periods).** For every `k ≥ 2` there is an explicit move set `S_k` with **exactly 26 moves** and `max S_k = 260k − 16`, whose outcome sequence has **least period exactly `260 · k · 2^k = (max S_k + 16) · 2^((max S_k + 16)/260)`**. In particular the period exceeds `2^(max S / 260)`. The nim-sequence period is a multiple of it. So **Guy's conjecture is false** and Flammenkamp's conjecture is true. The first `k` for which the period beats `(max S)^C(26,2) = (max S)^325` is `k = 6719`, where `max S = 1,746,924`.

```
S_k = {9 11 13 16 51 72 75 77 84 89 104 110 112 124 135 148 156 171 176 186 209 211 249}
      ∪ {260(k−1)+108, 260(k−1)+136, 260(k−1)+244}
```

What is assumed: the standard game (one heap, finite `S`, normal play, standard recursion from `n = 0`), with no seed, no modified start and no extra heaps. The number of moves is fixed, and "period" is the standard least eventual period. The growth is exponential in the largest move itself, not just in a parameter.

**Theorem 2 (universality with a bounded number of moves).** For every cellular automaton `F` there is a fixed list of move templates `(a, c, δ)` such that, for every ring length `L`, the game with moves `(a(L−2) + c)·B + δ` runs `F` on a ring of `L` cells, one initial configuration after another. **This theorem is formally verified** (`SubGame.Univ.universal`). So is its Turing-machine version: every deterministic Turing machine with a bounded tape is simulated on all inputs (`SubGame.TM.tm_universal`).

**Open problem (stated formally in Lean as `SubGame.OpenGap`).** Is there a number of moves `n` with `3 ≤ n ≤ 25` for which periods are not polynomially bounded? For `n ≤ 2` periods are at most `2 max S`; for every `n ≥ 26` the answer is yes (`superPoly_of_ge`).

**Theorem 3 (complexity).** Deciding whether `n` (in binary) is a P-position is:

- **PSPACE-complete** even for a bounded number of moves written in unary. In fact it is PSPACE-complete for one explicit one-parameter family `S_L`.
- **EXPTIME-complete** for a bounded number of moves written in binary. So no polynomial-time algorithm exists, unconditionally.

Idea: the outcome bit satisfies `w(n) = NOR(w(n−s) : s ∈ S)`, so the game is a shift register with NOR feedback. Split positions into blocks of length `B = 260`. Each residue is either a *clock* (always P), a *zero* residue (always N), or a *wire* carrying one logic bit per block. With a carefully found layout, every wire computes a NOR gate of prescribed inputs, and one long move gives a delay line of `k` blocks.

- For Theorem 1 the circuit is a bit-serial binary counter.
- For Theorem 2 it is a fixed circuit that enumerates inputs and runs a cellular automaton.

## Benchmarks: number of moves

`1061 → 169 → 67 → 56 → 54` came from Sidon layouts, greedy set cover and simulated annealing. `→ 48 → 38 → 29` came from exact CP-SAT optimization of the clocks and covering moves, followed by large-neighbourhood search over wire positions. `→ 26` came from also shortening the block (377 → 260). Every design was checked by an exact verifier and by simulating the game itself. For the final design the least periods are 2080, 6240, 16640, 41600 and 99840 for k = 2..6.

Shorter blocks trade moves for a faster exponential rate (each checked exactly and by simulation):

| block length `B` | moves | period | growth |
|---|---|---|---|
| 377 | 29 | `377 k 2^k` | `2^(max S / 377)` |
| 260 (formalised) | 26 | `260 k 2^k` | `2^(max S / 260)` |
| 240 | 28 | `240 k 2^k` | `2^(max S / 240)` |

(`subgame/best29.json`, `subgame/best26.json`, `subgame/shrinklns_B240.json`.)

## Repository layout

| path | contents |
|---|---|
| `lean/` | Lean 4 + Mathlib formalization (`lake build`) |
| `subgame/` | C and Python code: period computation, layout checker, CP-SAT/annealing search, simulation-based verification, universal circuits, figures |
| `paper/` | LaTeX paper (`paper.tex`, `paper.pdf`) and figures |
| `explore/` | exploration of other problems considered (Erdős #488, #617, …) |
| `sts material/` | explanations for any audience (explain-like-I'm-5, background, how it works, applications, open problems, judge Q&A, presentation kit), 15 diagrams, and a live demo (`python demo.py`) |

### Lean files (`lean/Sts/`)

| file | content |
|---|---|
| `Basic.lean` | `IsPSet`, uniqueness, computable `outcome` |
| `Arith.lean` | block arithmetic |
| `Simulation.lean` | designs, the five finite layout conditions, **simulation theorem** |
| `Bits.lean`, `Counter.lean` | binary carry / increment lemmas; the 8-wire NOR counter |
| `Design.lean` | the concrete 26-move design (generated by `subgame/gen_lean.py` from `subgame/best26.json`); all conditions by `decide +kernel` |
| `Period.lean` | least eventual period `260 k 2^k` |
| `Main.lean`, `Grundy.lean` | `exponential_period`, `not_polynomially_bounded`; nim-values |
| `Tests.lean`, `Exact.lean` | sanity checks; **`main_exact`**: exactly 26 moves, `max S = 260k − 16`, period `(max S + 16)·2^((max S + 16)/260)`, `2^(max S/260) < P`; **`guy_explicit`** for `k = 6719` |
| `Layout.lean` | **General Layout Lemma**: every NOR circuit is simulated by a subtraction game (`GLL.simulate`) |
| `Transport.lean` | the layout lemma for arbitrary finite wire types |
| `UnivCore.lean`, `Universal.lean` | cellular automata, the universal enumerating circuit, **`Univ.universal`** |
| `TuringSim.lean` | Turing machines with a bounded tape, their cellular automata; **`TM.tm_universal`**: every such machine is simulated, on all inputs, by one bounded-move family of subtraction games |
| `OpenProblem.lean` | Guy's bound for `n` moves: **`guy_false_of_ge`** (it fails for every `n ≥ 26`) and the formal statement **`OpenGap`** of the remaining open problem (`3 ≤ n ≤ 25`) |

`#print axioms` for the main theorems reports only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no `native_decide`.

Build: `cd lean && lake exe cache get && lake build`. `Design.lean` takes about 30 minutes because the finite checks run in the kernel.

### Reproducing the computations (`subgame/`)

```
python -m ziglang cc -O3 sim.c -o sim.exe                 # simulate a game
python -m ziglang cc -O3 simwin.c -o simwin.exe           # fast simulator for sparse P-sets
python verify2.py best26.json 2 3 4 5 6                   # simulate S_k, compare with the counter, exact least period
python cpsat_layout.py <design.json> <seconds> <out>      # exact clock/cover optimisation (fixed wires)
python cpsat_full.py <design.json> <window> <seconds> <out> <rounds>   # wire-position LNS
python univ1.py; python univ2.py                           # universal circuits vs direct CA simulation
python e2e_univ.py 110 4 3                                 # universal game, simulated end to end
python shrink_lns.py <design.json> 260,240 6 1200          # shorten the block (wires free in windows)
python retarget_lean.py best26.json 377 29 363 502 8771    # regenerate the design-specific Lean files
```
