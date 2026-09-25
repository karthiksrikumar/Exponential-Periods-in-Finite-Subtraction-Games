# Open problems and what comes next

A good result answers one question and sharpens the next ones. Here is where things stand.

---

## Open Problem 1: the gap between 3 and 25 moves

> **Is there a number n with 3 ≤ n ≤ 25 such that the periods of n-move subtraction games are
> not bounded by any polynomial in the largest move?**

| number of moves | what is known |
|---|---|
| 1 | period = 2 · (the move): tiny |
| 2 | period at most 2 · max S (classical) |
| 3 | conjectured (Flammenkamp) to be linear or quadratic; unproved |
| 4 – 25 | **open** |
| 26 and more | **exponential periods exist** (this project, proved in Lean) |

Flammenkamp's experiments suggest the answer is **yes already for 5 moves**: his record 5-move
periods grow roughly like 2^(0.3 · max S). The question is stated formally in Lean as
`SubGame.OpenGap` (file `lean/Sts/OpenProblem.lean`), so any future solution can be checked
against exactly that statement.

**Two ways to attack it.**
* **Push the construction down.** Shave moves off the circuit method (26 → 20 → …). This needs
  cleverer circuits (fewer wires, gates that share moves) and better layouts. The exact solver
  proves much lower bounds are *not* ruled out.
* **Understand the chaos.** Explain Flammenkamp's 5-move records directly. That would need a new,
  more "organic" mechanism, perhaps signals moving and colliding like gliders in the Game of Life.

## Open Problem 2: the best growth rate

Our periods grow like 2^(max S / 260). The trivial upper bound is 2^(max S), and Flammenkamp's
experimental records grow like 2^(0.3 · max S).

> What is the largest c such that games with a bounded number of moves can have period at least
> 2^(c · max S)?

Our trade-off (29 moves at B = 377, 26 at B = 260, 28 at B = 240) suggests shorter blocks with
richer layouts. Packing several counter bits into each block is another route.

## Open Problem 3: the complexity threshold

> What is the least number of moves c for which deciding the winner is PSPACE-hard?

Two moves are easy. Our construction gives *some* constant c, but a large one (about 100,000 moves
for the general layout). Finding the true threshold would pin down exactly where these games become
computationally universal.

## Open Problem 4: formalise the rest

* The two-parameter (EXPTIME) construction is only checked by simulation. A Lean proof would follow
  the same pattern as the one-parameter version.
* The complexity-class statements ("PSPACE-complete") need a formal definition of polynomial-time
  reductions, which Lean's library does not have yet.

## Open Problem 5: other games

The blocks-clocks-wires method should apply to:
* **misère play** (the player who makes the last move *loses*),
* **octal games** and other take-away games (Kayles, Dawson's Kayles), whose periodicity is a famous
  mystery,
* **nim-values** instead of win/lose (Grundy values up to |S|),
* **partizan** subtraction games, where the two players have different rule cards.

---

## How someone could continue this project

Everything needed is in the repository:

| tool | what it does |
|---|---|
| `subgame/cpsat_layout.py` | exact optimisation of clocks and covering moves for fixed wire positions |
| `subgame/cpsat_full.py` | large-neighbourhood search that also moves the wires |
| `subgame/shrink_lns.py` | tries shorter block lengths |
| `subgame/verify2.py` | simulates a design and checks the exact period |
| `subgame/retarget_lean.py` | turns a new design into the Lean files, so a better design can be formally verified with one command |
| `subgame/univ1.py`, `univ2.py` | the universal circuits, for experiments with other automata |

A concrete first project for someone new: **find a 25-move design**. The solver runs on a laptop
(use at most 4 worker threads on an 8 GB machine). If it succeeds, `retarget_lean.py` produces a
formal proof for it automatically.
