# Where everything is

This page maps the repository: the presentation materials, the paper source you edit, the diagrams, the data and the proofs. For the math itself, see [README.md](README.md).

## 1. Presentation materials: `sts material/`

Start with [`sts material/README.md`](sts%20material/README.md). It lists the files in a suggested reading order.

| file | what it is | use it for |
|---|---|---|
| `01_explain_like_im_5.md` | the whole project with no math | opening a talk, explaining it to non-mathematicians |
| `02_background.md` | subtraction games, periods, Guy's conjecture, history | the "why it matters" slides |
| `03_how_it_works.md` | blocks, clocks, wires, the NOR rule, the counter | the core explanation |
| `04_results.md` | the theorems in plain language | the results slide |
| `05_how_we_know_its_true.md` | the Lean proof, simulations, written proof | the trust and verification slide |
| `06_applications_and_impact.md` | computation, complexity, broader impact | the "so what" slide |
| `07_open_problems_and_whats_next.md` | the 3–25 move gap and other questions | the final slide |
| `08_judge_questions.md` | likely judge questions with answers | interview practice |
| **`09_presentation_kit.md`** | **30-second and 2-minute pitches, a 13-slide outline, a poster layout, the demo plan and an integrity checklist** | **building the slides and the poster** |
| `10_glossary.md` | every term defined | quick lookup |
| `11_key_numbers.md` | every number you might be asked for | a cheat sheet |
| `demo.py` | live demo in plain Python 3 | run `python demo.py` (menu) or `python demo.py all` |

## 2. The paper (LaTeX source you can edit)

| file | what it is |
|---|---|
| **`paper/paper.tex`** | **the full paper. Edit this file.** It is self-contained: all sections are inlined, and nothing is `\input`. |
| `paper/paper.pdf` | the compiled paper (15 pages) |
| `paper/figs/` | figures for the paper: `bitmap` and `wires` are included; `growth` is spare (each as `.pdf` and `.png`) |
| `paper/part_*.tex` | the section drafts the paper was assembled from. They are kept for reference only and are **not** used by `paper.tex`. |
| `paper/paper_v1.tex`, `paper_v1.pdf` | an earlier version, kept for comparison |

To rebuild the PDF after editing, run this from `paper/`:

```
pdflatex paper.tex
pdflatex paper.tex      # run it twice so cross-references resolve
```

Overleaf also works. Upload `paper.tex` and the `figs/` folder, keeping the folder structure.

## 3. All diagrams

| location | what | regenerate with |
|---|---|---|
| `sts material/diagrams/01_the_game.png` … `15_timeline.png` | 15 plain-language diagrams for slides and the poster | `python "sts material/make_diagrams.py"` (needs matplotlib) |
| `paper/figs/*.pdf`, `*.png` | 3 technical figures for the paper (`bitmap` and `wires` appear in it; `growth` is spare) | `cd subgame && python figs.py` |
| inside `paper/paper.tex` | the counter-circuit figure, drawn in TikZ | edit it directly in the `.tex` file |

The diagrams in `sts material/diagrams/`:

1. `01_the_game`: the game and its rules
2. `02_patterns_repeat`: patterns always repeat
3. `03_nor_rule`: the winning rule is a NOR gate
4. `04_game_as_machine`: the game as a shift register
5. `05_columns_have_jobs`: clocks, zeros and wires
6. `06_the_real_game`: the actual 26-move game, drawn as a picture
7. `07_counter_circuit`: the 8-gate counter
8. `08_it_counts`: the counter read off the game
9. `09_growth`: the period against Guy's bound
10. `10_benchmark_moves`: the move count from 1061 down to 26
11. `11_universality_pipeline`: the game can run any program
12. `12_complexity_map`: PSPACE and EXPTIME
13. `13_proof_map`: how the Lean proof fits together
14. `14_eli5_light_bulbs`: the explain-like-I'm-5 picture
15. `15_timeline`: the history of the problem

The slide outline in `09_presentation_kit.md` says which diagram goes on which slide.

## 4. Data and designs

| file | what |
|---|---|
| `sts material/data/design_26_moves.json` | the 26-move design (moves, block length, wire layout) |
| `sts material/data/five_move_records.csv` | record periods for small move sets |
| `subgame/best26.json` | the 26-move design at B = 260. This is the formally verified one. |
| `subgame/best29.json`, `best38.json`, `shrinklns_B240.json` | the alternative designs (29 moves at B = 377, 38 moves, 28 moves at B = 240) |

## 5. Code and checks: `subgame/`

* `run_all_checks.sh` runs every numerical check (period simulation, circuit verification, universality end to end).
* The layout search uses `cpsat_layout.py`, `cpsat_full.py` (exact CP-SAT), `shrink_lns.py` and `shrinkB.py` (large-neighbourhood search), and `anneal*.py` (simulated annealing).
* `univ*.py` and `e2e_univ*.py` handle the universal circuit and its end-to-end simulation.
* `retarget_lean.py` and `gen_lean.py` generate `lean/Sts/Design.lean` from a design JSON file.
* `simwin.c`, `period.c` and `sim.c` are fast C simulators. Compile them with any C compiler.

## 6. The formal proof: `lean/`

To check it, run `cd lean && lake build` (Lean 4 with Mathlib; see `lean-toolchain`). The first build takes about 30–60 minutes. The main files:

| file | contents |
|---|---|
| `Sts/Main.lean` | the main theorems (`Concrete.main_exact`, `guy_explicit`) |
| `Sts/Design.lean` | the 26-move design (generated) |
| `Sts/Layout.lean`, `Counter.lean`, `Period.lean`, `Exact.lean` | the General Layout Lemma, the counter, the period argument and exactness |
| `Sts/Universal.lean`, `UnivCore.lean`, `Transport.lean` | universality for cellular automata |
| `Sts/TuringSim.lean` | Turing-machine simulation |
| `Sts/OpenProblem.lean` | the formal statement of the 3–25 open problem, and the proof for every n ≥ 26 |
| `Sts/Tests.lean` | sanity checks |
