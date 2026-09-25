# Judge questions: 40 questions and strong answers

Judges probe for three things: **do you understand it, is it correct, and is it new?** Practise
answering these out loud. Short, precise answers are best, followed by an offer to go deeper.

---

## A. The problem and why it matters

**1. In one sentence, what did you prove?**
Subtraction games with a fixed number of moves (26) can have periods that grow exponentially in the
largest move, which refutes a conjecture of Richard Guy and settles a question open since the 1990s.

**2. What is a subtraction game?**
A pile of tokens and a list of allowed amounts. Players alternately remove an allowed amount, and
whoever cannot move loses. Example: "take 1 or 2", where the losing piles are the multiples of 3.

**3. Why does the win/lose pattern repeat at all?**
Each answer depends only on the previous m answers (m = largest move). There are finitely many
possible lists of m answers, so one must repeat, and from then on everything repeats. That bounds
the period by 2^m.

**4. What exactly did Guy conjecture?**
That for n moves the period is at most a polynomial of degree n(n−1)/2 in the largest move. It is
recorded in *Unsolved Problems in Combinatorial Games* (Nowakowski, Games of No Chance 5, 2019).

**5. Why is exponential versus polynomial such a big difference?**
A polynomial like m^325 eventually loses to any exponential like 2^(m/260). Our game overtakes
Guy's degree-325 bound at k = 6719, where both numbers have about 2,029 digits, and after that the
gap grows without limit.

**6. Is your period exponential in the largest move, or only in some parameter?**
In the largest move. The period is (m + 16) · 2^((m + 16)/260), where m is the largest move. So it
is at least 2^(m/260).

**7. Did you use a modified version of the game?**
No. It is the standard game: one pile, a finite rule card, normal play, and outcomes computed by
the usual rule from pile 0. There is no seed, no modified start and no extra piles. The number of
moves is fixed at 26, and "period" is the standard least eventual period. (Miklós and Post in 2024
needed a seed. We do not.)

**8. Why should anyone care about a game?**
Three reasons. It settles a well-known open problem. It shows that an extremely simple system can
compute anything, like Rule 110 or the Game of Life. And it gives an unconditional computational
lower bound, which is rare. See `06_applications_and_impact.md`.

## B. The construction

**9. What is the key idea?**
The rule "a pile is losing iff no move reaches a losing pile" is a NOR gate. If you cut pile sizes
into blocks of 260, each position inside a block can act as a wire, a constant 1 (clock) or a
constant 0, and the moves act as wires with time delays. So the game runs a circuit.

**10. What are clocks, zeros and wires?**
Clock columns are always losing. Zero columns are always winning, because some move from them
reaches a clock. Wire columns change from block to block and carry one bit each.

**11. How does a move become a wire?**
A move of size 260q + δ connects a column to the column δ places to the left, q or q + 1 blocks
earlier. A long move (about 260k) reaches k blocks back. That is a delay line that stores k bits.

**12. What circuit did you build?**
A bit-serial binary counter from 8 NOR gates: start, marker, not-marker, no-carry-in, not-bit,
helper, carry and u. Every k blocks the stored k-bit number increases by 1.

**13. Why is the period exactly 260 · k · 2^k?**
The counter takes 2^k increments to wrap around, each increment takes k blocks, and a block is 260
positions. To show nothing smaller works: clocks force multiples of 260, the marker forces
multiples of k blocks, and the counter forces multiples of 2^k words.

**14. Why 26 moves? What are they for?**
12 moves implement the 13 wire connections of the counter (one move serves two connections). The
other 14 ensure every zero column is covered by a clock. One of them also feeds the start wire.

**15. Why is it hard to find the numbers?**
Every move acts on every column, so a move intended for one connection creates connections between
every pair of columns at the same distance. You must place columns so that no unwanted connections
appear (a Sidon-set-like condition) while covering every zero column with few moves.

**16. How did you find them?**
Sidon-set constructions gave a first valid design with 1061 moves. Greedy set cover and simulated
annealing brought it to 54. Exact constraint programming (Google's CP-SAT solver) brought it to 38,
letting the solver move the wires brought it to 29, and shortening the block to 260 brought it to
26.

**17. Could you explain the counter's logic?**
Adding 1 bit by bit: new bit = old bit XOR carry-in, and carry-out = old bit AND carry-in, with
carry-in = 1 at the start of each word. In NOR gates: helper = NOR(old bit, carry-in),
carry = NOR(not-bit, no-carry-in), u = NOR(helper, carry).

**18. What does "universal" mean here?**
For any cellular automaton, and hence any Turing machine with a bounded tape, there is one family
of games with a fixed number of moves that simulates it on every input. The same layout method
turns any NOR circuit into a game.

## C. Correctness

**19. How do you know it is correct?**
Three independent ways: a machine-checked proof in Lean, direct simulation of the games, and a
written proof.

**20. What is Lean, and why trust it?**
A proof assistant. Every step is checked by a small trusted kernel. Our proofs use only the three
standard axioms (propext, Classical.choice, Quot.sound), with no `sorry` and no `native_decide`.

**21. Could the Lean statement be subtly different from the real claim?**
That is the right worry. The game is defined in Lean directly by its rule, with no mention of our
construction. Sanity checks confirm known cases ({1,2} gives multiples of 3; {1,3,4} gives n mod 7
∈ {0, 2}). The period is defined in the standard way, and we prove both that 260·k·2^k is a period
and that every period is a multiple of it.

**22. What part did the computer check by "brute force"?**
Only the finite layout conditions for the specific 26-move design (260 columns × 26 moves), checked
inside Lean's kernel. The statement for all k is proved symbolically.

**23. Did you actually run the game?**
Yes. A separate C program plays the game from the definition. For k = 2…6 every position matches
the prediction, and the least periods are exactly 2080, 6240, 16640, 41600 and 99840.

**24. What is not machine-checked?**
The complexity-class bookkeeping (Lean has no PSPACE) and the two-parameter EXPTIME construction.
The simulation of Turing machines by games *is* machine-checked.

**25. What would it take to break your result?**
A bug in Lean's kernel, or the simulation program and the Lean proof both being wrong in the same
way. The independent checks make either very unlikely.

**26. How long does verification take?**
The full Lean build takes about 30–60 minutes on a laptop, mostly the finite layout check. The
simulations take seconds to minutes.

## D. Novelty and literature

**27. How do you know nobody did this before?**
The standard references still list it as open: Nowakowski's 2019 unsolved-problems list, the 2024
survey by Larsson and Saha (Conjecture 1), Miklós and Post (2024), and Larsson and Manabe's March
2026 paper. Searches for exponential periods in subtraction games found no proof. We would still
welcome an expert's confirmation.

**28. What did Flammenkamp do?**
In his 1997 thesis he computed record periods of five-move games, found growth like 2^(0.3 m), and
conjectured exponential periods. He had evidence but no proof. We prove it, with more moves.

**29. What did Miklós and Post do?**
They got super-polynomial periods e^(Ω(√m)) for a *modified* game in which the first outcomes are
prescribed. The unmodified question stayed open.

**30. Was hardness known for these games?**
For several piles and for games on graphs, yes. For a single pile we know of no earlier hardness
result. We show PSPACE- and EXPTIME-completeness, even with a bounded number of moves.

**31. Is 26 optimal?**
Unknown. The answer is somewhere between 3 and 26. That is our Open Problem 1, stated formally in
Lean.

## E. Process, tools and your role

**32. What did you do, and what did the tools do?**
*Answer honestly and specifically.* One useful structure: what you chose (the problem, the
approach), what you understood and checked (the key ideas, the proofs, the simulations), and what
tools produced (search programs, the constraint solver, the proof assistant, and an AI assistant
used for code and formalisation). Judges respect clarity about tools. They do not respect
vagueness. Check the current Regeneron STS rules on AI assistance and disclose accordingly.

**33. Why did you use AI or computers? Isn't that cheating?**
Computers are standard research tools in mathematics: the Four Colour Theorem, the Kepler
conjecture and many combinatorics results rely on them. What matters is that every claim is
checked, and ours are checked by a proof assistant and independent simulation. Be ready to explain
any step yourself.

**34. What was the hardest part?**
Suggested honest options: the layout puzzle (every move acts everywhere), proving the period is
*exactly* 260·k·2^k and not a divisor, or getting the formal proof through Lean. Pick what was
hardest *for you*.

**35. What did you learn?**
Say it in your own words. For example: how a very simple rule can compute; why exponential beats
polynomial; how to turn a proof idea into a design problem; what a proof assistant guarantees.

**36. What dead ends did you hit?**
Five-move families behave chaotically, and every simple family we tried had erratic periods. That
is why we switched from *finding* long periods to *designing* them. We also examined several other
open problems (Erdős problems) before choosing this one.

## F. Beyond

**37. What would you do with more time?**
Push the move count down (26 → 25 → …), improve the growth rate, formalise the EXPTIME
construction, and try the method on misère play and octal games.

**38. Could this help cryptography?**
Indirectly. A subtraction game is a nonlinear feedback shift register, the kind used in stream
ciphers, and our tools compute periods exactly and embed computation. But our registers are
structured, not secure.

**39. What is the most surprising thing about the result?**
That a game you can play with coins on a table can simulate any computer program, so that simply
predicting who wins can be as hard as any computation.

**40. If you had to explain it to a 10-year-old?**
"The losing piles form a pattern that repeats. I found rules that make the game secretly count in
binary, and counting to a huge number takes forever, so the pattern takes forever to repeat."
