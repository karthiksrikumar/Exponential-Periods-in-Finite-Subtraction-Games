# The results

Each result is given three ways: in plain words, exactly, and with its verification status.

Status labels used below:
* **[Lean]**: proved in the Lean proof assistant from the definition of the game. Only Lean's three
  standard axioms are used, with no gaps.
* **[paper]**: proved in the paper with a traditional written proof.
* **[simulated]**: additionally checked by running the actual games on a computer.

---

## Result 1. Exponentially long periods with 26 moves  [Lean] [simulated]

**Plain words.** There are rule cards with only 26 numbers whose win/lose pattern takes an
exponentially long time to repeat, compared with the largest number on the card.

**Exactly.** For every k ≥ 2 let

  S_k = {9, 11, 13, 16, 51, 72, 75, 77, 84, 89, 104, 110, 112, 124, 135, 148, 156, 171, 176, 186,
     209, 211, 249} ∪ {260(k−1) + 108, 260(k−1) + 136, 260(k−1) + 244}.

Then:
* |S_k| = **26** exactly, for every k;
* max S_k = **260k − 16**;
* the outcome sequence of the subtraction game S_k has **least period exactly 260 · k · 2^k**,
  which equals (max S_k + 16) · 2^((max S_k + 16)/260) > 2^(max S_k / 260);
* the nim-value sequence (Sprague–Grundy values) has a least period divisible by 260 · k · 2^k.

| k | largest move | period | checked by |
|---|---|---|---|
| 2 | 504 | 2,080 | Lean + simulation |
| 3 | 764 | 6,240 | Lean + simulation |
| 4 | 1,024 | 16,640 | Lean + simulation |
| 5 | 1,284 | 41,600 | Lean + simulation |
| 6 | 1,544 | 99,840 | Lean + simulation |
| 20 | 5,184 | 5,452,595,200 | Lean |
| 100 | 25,984 | about 3.3 × 10^34 | Lean |
| 6,719 | 1,746,924 | a 2,029-digit number | Lean |

Lean theorems: `SubGame.Concrete.main_exact`, `exponential_period`, `nim_period_dvd`.

## Result 2. Guy's conjecture is false  [Lean]

**Plain words.** Guy predicted that for n moves the period is at most a polynomial of degree
n(n−1)/2 in the largest move. With 26 moves that degree is 325, and the prediction fails.

**Exactly.**
* For every C and d there is a 26-move game whose period exceeds C · (max S)^d
  (`guy_fails`, `not_polynomially_bounded`).
* Explicitly, S_6719 has 26 moves, largest move 1,746,924, and period
  260 · 6719 · 2^6719 > (1,746,924)^325. k = 6719 is the first k where this happens
  (`guy_explicit`).
* The same holds for **every** number of moves n ≥ 26 (add harmless extra moves):
  `superPoly_of_ge` and `guy_false_of_ge`.

**What this confirms:** Flammenkamp's 1997 conjecture that exponential periods exist.

## Result 3. The game can simulate any circuit  [Lean] [simulated]

**Plain words.** Any digital circuit made of NOR gates with delays can be built inside a one-pile
subtraction game.

**Exactly (General Layout Lemma).** For every NOR circuit with delay lines (with a start wire and
no self-loops), placing wire j at column 13·y_j (y a Sidon set), clocks at columns 1, 5, 12, and
following a fixed covering table produces a subtraction game whose losing piles encode the
circuit's values exactly. Lean: `SubGame.GLL.simulate`, and `GLL.simulateA` for arbitrary wire
names.

## Result 4. Universality with a bounded number of moves  [Lean] [simulated]

**Plain words.** One family of games, whose moves depend only on a size parameter, runs a given
cellular automaton, and hence any Turing machine with bounded memory, on **every** input.

**Exactly.** For every b-bit cellular automaton F there are a block length B, residues ρ and a
fixed finite list of move templates such that, for every ring length L = K + 2, the game with moves
(aK + c)B + δ satisfies:

  position ((j·2^L + T)·L + i)·B + ρ_q is losing ⟺ bit q of cell i, after T < 2^L steps of F
  from the input j + 1, is 1.

The Turing-machine version: for every deterministic machine with a bounded tape, the losing piles
of one fixed-size family encode its complete configuration at every step, on every input.
Lean: `SubGame.Univ.universal`, `SubGame.TM.tm_universal`, `SubGame.TM.tm_state`.

Validation: the universal circuit was compared with direct simulation for all 256 elementary
cellular automaton rules, and a real universal game (123,181 moves) was simulated over
24 million positions with no mismatch.

## Result 5. Predicting the winner is provably hard  [paper, built on the Lean results]

**Plain words.** Given the rule card and a huge pile size, deciding who wins is as hard as any
problem solvable with a reasonable amount of memory. If the numbers are written in binary, no fast
algorithm can exist at all.

**Exactly.** SubGame = "given S and n (n in binary), is n a losing pile?" is
* **PSPACE-complete** when S is given in unary, even restricted to |S| ≤ c for a fixed c. In fact
  it is PSPACE-complete for **one explicit one-parameter family** S_L.
* **EXPTIME-complete** when S is given in binary, even with |S| ≤ c. Since P ≠ EXPTIME is a
  *theorem* (the time hierarchy theorem), no polynomial-time algorithm exists. This does not
  depend on any unproved conjecture.
* Computing the least period is **PSPACE-hard**.

What is formal: the simulation of Turing machines (Result 4). What is on paper: choosing a
machine for a PSPACE-complete language, the polynomial-time bookkeeping, and the two-ring circuit
used for EXPTIME (checked by simulation, not in Lean).

## Result 6. Trading moves for speed  [simulated, exact verifier]

| block length B | moves | period | growth |
|---|---|---|---|
| 377 | 29 | 377 k 2^k | 2^(max S / 377) |
| **260** | **26** | **260 k 2^k** | **2^(max S / 260)** (formalised) |
| 240 | 28 | 240 k 2^k | 2^(max S / 240) |

## The open problem that remains  [stated in Lean]

> **Is there a number of moves n with 3 ≤ n ≤ 25 for which periods are not polynomially bounded?**

For n ≤ 2 periods are at most 2 · max S (classical). For n ≥ 26 the answer is yes (Result 2). The
Lean file `OpenProblem.lean` states the question precisely as `SubGame.OpenGap`, next to the proofs
for n ≥ 26. See `07_open_problems_and_whats_next.md`.
