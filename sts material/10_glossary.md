# Glossary

**Axiom (Lean's standard axioms).** Basic assumptions everything else rests on. Our proofs use only
the three standard ones in Lean: `propext` (equivalent statements are equal), `Classical.choice`
(choosing an element from a non-empty set) and `Quot.sound` (quotients behave correctly).

**Binary counter.** A circuit that stores a number in binary (0s and 1s) and adds 1 to it
repeatedly. A k-bit counter returns to its start after 2^k steps.

**Bit-serial.** Processing a number one bit at a time instead of all bits at once. Our counter
handles one bit per block.

**Block (length B).** A group of B consecutive pile sizes. We write n = B·τ + r: τ is the block
(time) and r the position inside it (place). Our B is 260.

**Cellular automaton.** A row of cells, each in one of finitely many states, all updated together
by the same local rule that looks at neighbouring cells. Rule 110 and the Game of Life are famous
examples.

**Clock (column).** A position inside the block that is a losing pile in every block (always 1).

**Combinatorial game theory.** The mathematics of two-player games with perfect information and no
chance.

**Complexity class.** A family of problems grouped by the resources needed to solve them.
* **P:** solvable in polynomial time (fast).
* **NP:** solutions can be *checked* in polynomial time.
* **PSPACE:** solvable with a polynomial amount of memory (possibly very slowly).
* **EXPTIME:** solvable in exponential time.
* A problem is **complete** for a class if it is in the class and every other problem in the class
  reduces to it. It is then the "hardest" problem there.

**Conjecture.** A statement believed but not proved. *Guy's conjecture* (periods are polynomially
bounded) is now **refuted**; *Flammenkamp's conjecture* (exponential periods exist) is now **proved**.

**CP-SAT.** Google's constraint-programming solver (part of OR-Tools). You describe the rules a
solution must satisfy and what to minimise, and it searches, exactly, for the best solution.

**Delay line.** A memory in which information travels for a fixed time before being read back. In
our game, a long move of about 260k reads the value from k blocks earlier.

**Eventually periodic.** A sequence that, after some starting stretch (the *preperiod*), repeats
forever with some period p.

**Exponential vs polynomial.** A polynomial grows like m^d for a fixed d; an exponential grows like
c^m. Every exponential eventually overtakes every polynomial.

**Formal verification.** Checking a proof with a computer program that verifies every logical step.

**General Layout Lemma.** Our theorem that any NOR circuit with delays can be built inside a
subtraction game (proved in Lean).

**Grundy value (nim-value).** A number attached to each position of an impartial game. The position
is losing exactly when its Grundy value is 0.

**Guy, Richard K. (1916–2020).** Co-author of *Winning Ways*, collector of unsolved problems in
number theory and combinatorial games.

**Impartial game.** Both players have the same moves from every position (unlike chess).

**Kernel (Lean).** The small, trusted core of Lean that checks every proof step.

**Lean / Mathlib.** A proof assistant and programming language; Mathlib is its large library of
formalised mathematics.

**Losing pile (P-position).** A pile size from which the player about to move loses against perfect
play.

**Marker.** The wire of our counter that is 1 at the first block of every word.

**Move (rule-card number).** An allowed amount to remove. Our game has 26.

**Nim.** The classic game with several piles where you remove any number from one pile, solved by
Bouton in 1902.

**NOR gate.** A logic gate whose output is 1 exactly when all its inputs are 0. NOR gates alone can
build any digital circuit.

**Normal play.** The player who cannot move loses.

**Open problem.** A question nobody has answered. Ours: can 3 to 25 moves give super-polynomial
periods?

**Period (least eventual period).** The smallest p > 0 such that, from some point on, the win/lose
pattern repeats every p pile sizes.

**Pigeonhole principle.** If more than N objects go into N boxes, some box gets two. It is why every
subtraction game's pattern repeats.

**Proof assistant.** Software that checks mathematical proofs; Lean, Coq and Isabelle are examples.

**Shift register.** A memory of the last m bits that computes the next bit from some of them. With
NOR feedback, it is exactly a subtraction game.

**Sidon set.** A set of numbers whose pairwise differences are all different. We used Sidon sets to
place wires so that no move creates an unwanted connection.

**Simulated annealing.** A search method that makes random changes, accepts improvements, and
sometimes accepts small setbacks to escape dead ends.

**`sorry`.** In Lean, a placeholder that skips a proof. Our development contains none.

**Subtraction game.** One pile, a rule card S of allowed amounts, normal play.

**Time hierarchy theorem.** A theorem proving that more time lets you solve strictly more problems;
in particular P ≠ EXPTIME.

**Turing machine.** The standard mathematical model of a computer: a tape, a read/write head and a
finite set of states.

**Universal.** Able to simulate any computation (here: any bounded-memory computation).

**Wire (column).** A position inside the block whose value changes from block to block and carries
one bit of the circuit.

**Winning pile (N-position).** A pile size from which the player about to move can force a win.

**Word.** k consecutive blocks, which together store one k-bit number of the counter.

**Zero (column).** A position inside the block that is a winning pile in every block (always 0),
because some move from it reaches a clock.
