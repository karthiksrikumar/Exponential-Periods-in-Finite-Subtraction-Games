# Presentation kit

Ready-to-adapt pitches, a slide outline, a poster plan and a live demo. Put everything in your own
words; memorised scripts sound memorised.

---

## The 30-second pitch

> "There's a simple game: a pile of tokens, and a card listing how many you may take; whoever can't
> move loses. For any card, the pattern of winning and losing pile sizes eventually repeats. Since
> the 1990s mathematicians have asked how long that repeat can be, and Richard Guy conjectured it's
> always polynomially short. I proved him wrong: with just 26 numbers on the card, the repeat can
> be exponentially long. The trick is that the game can be turned into a tiny computer that counts
> in binary. And every step of the proof is checked by a computer proof assistant."

## The 2-minute version (add these beats)

1. **Hook** (show `diagrams/01_the_game.png`): play "take 1 or 2" with a judge for three moves.
2. **The pattern repeats** (`02_patterns_repeat.png`): always, by the pigeonhole principle, but how
   long can it take?
3. **The conjecture:** Guy said polynomial. Flammenkamp's experiments hinted exponential. Open for
   about 30 years.
4. **The key insight** (`03_nor_rule.png`): the winning rule *is* a NOR gate, and NOR gates can
   build computers.
5. **The construction** (`06_the_real_game.png`, `08_it_counts.png`): blocks of 260, columns become
   wires, and the game counts in binary. Period = 260·k·2^k.
6. **Trust:** machine-checked in Lean, and the game simulated bit for bit.
7. **Bonus:** the game can simulate *any* program, so predicting the winner is provably hard.

## The 5-minute talk (slide outline)

| # | slide | diagram | say |
|---|---|---|---|
| 1 | Title + one-line result | `09_growth.png` | "Exponential periods with 26 moves; Guy's conjecture is false." |
| 2 | The game | `01_the_game.png` | Rules; losing piles for "take 1 or 2". |
| 3 | Patterns repeat | `02_patterns_repeat.png` | Pigeonhole: period ≤ 2^m. The question: how long? |
| 4 | History | `15_timeline.png` | Guy (polynomial), Flammenkamp (experiments), open until now. |
| 5 | Key insight | `03_nor_rule.png`, `04_game_as_machine.png` | NOR gate plus shift register means the game can compute. |
| 6 | Blocks, clocks, wires | `05_columns_have_jobs.png` | Time and place; three kinds of columns; moves = delayed wires. |
| 7 | The counter | `07_counter_circuit.png` | 8 NOR gates; a k-bit number increases by 1 every k blocks. |
| 8 | It really counts | `06_the_real_game.png`, `08_it_counts.png` | Read straight from the pile sizes. |
| 9 | The theorem | `09_growth.png` | Period 260·k·2^k; beats Guy's bound at k = 6719. |
| 10 | Finding 26 numbers | `10_benchmark_moves.png` | 1061 → 26 via annealing and exact solvers. |
| 11 | Proof checked by computer | `13_proof_map.png` | Lean, about 3,800 lines, standard axioms; plus simulation. |
| 12 | Universality and hardness | `11_universality_pipeline.png`, `12_complexity_map.png` | Any program fits inside; PSPACE/EXPTIME-complete. |
| 13 | What's next | text | The 3–25 gap (stated formally), growth rate, other games. |

## Poster layout (landscape, 4 columns)

```
+------------------+-------------------+-------------------+------------------+
| 1. THE QUESTION  | 3. THE KEY IDEA   | 5. THE THEOREM    | 7. UNIVERSALITY  |
| game picture     | NOR rule          | big formula:      | pipeline diagram |
| repeating        | blocks/clocks/    | P = 260 k 2^k     | complexity map   |
| patterns         | wires picture     | growth plot       |                  |
+------------------+-------------------+-------------------+------------------+
| 2. HISTORY       | 4. THE COUNTER    | 6. HOW WE KNOW    | 8. OPEN PROBLEMS |
| timeline         | circuit diagram   | proof map (Lean)  | 3-25 gap         |
| Guy vs.          | "it counts"       | simulation table  | growth rate      |
| Flammenkamp      | picture           | benchmark 1061→26 | QR code to repo  |
+------------------+-------------------+-------------------+------------------+
```

Poster tips: one big claim per panel, large pictures and little text; put the formula
**P = 260 · k · 2^k** in huge type, and make "Guy's conjecture is false" readable from 3 metres
away.

## Live demo

Run `python demo.py` on a laptop at the booth (plain Python 3, no installs):

* **Part 1:** play "take 1 or 2" against the computer, which always wins from a winning pile.
* **Part 2:** the repeating patterns for several rule cards, printed as coloured strips.
* **Part 3:** the 26-move game computed from scratch. The counter column is read off and printed
  as binary numbers 1, 2, 3, …. This is the most convincing moment: the computer computes only
  winning and losing piles, and a counter appears.

Suggested line: *"The computer only knows the rule of the game. It doesn't know about counters.
Watch this column…"*

## Handling nerves and hard questions

* If you don't know, say "I don't know, but here's how I'd find out." That is a strong answer.
* Keep the three-layer trust story ready: formal proof, simulation, written proof.
* Keep the honest limits ready: 26 is not known to be optimal; the complexity-class bookkeeping and
  the EXPTIME construction are on paper; novelty is based on the current literature.
* Have `08_judge_questions.md` nearly memorised, especially questions 6, 7, 13, 21 and 32.

## Integrity checklist before submitting

- [ ] Your forms describe accurately what you did and what tools did, including any AI assistance.
- [ ] You checked the current Regeneron STS rules on AI use and followed them.
- [ ] You can explain every diagram in this folder without notes.
- [ ] You can derive the period 260·k·2^k on a whiteboard.
- [ ] You can explain why the Lean check means the result is true.
