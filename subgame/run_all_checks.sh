#!/bin/bash
# Reproduce all computational checks (requires python + `pip install ziglang numpy ortools`).
set -e
cd "$(dirname "$0")"
python -m ziglang cc -O3 period.c -o period.exe
python -m ziglang cc -O3 sim.c -o sim.exe
python -m ziglang cc -O3 simwin.c -o simwin.exe
echo "== periods of classical examples"; ./period.exe 1 2; ./period.exe 1 3 4
echo "== exact verifier of the formalised 26-move design"
python -c "import json; from cpsat_layout import check_json; print('valid:', check_json(json.load(open('best26.json'))))"
echo "== formalised 26-move design: simulate the game, compare with the counter, exact least periods"
python verify2.py best26.json 2 3 4 5 6
echo "== General Layout Lemma on random circuits"
python gll.py 100 20
python gll_test2.py 7 200 12
echo "== PSPACE reduction with O(N) moves (logic level) against a Turing machine"
python tm_reduction_check.py
echo "== universal enumerating circuits (bounded number of moves) vs direct CA simulation"
python univ1.py
python univ2.py
echo "== universal game simulated end to end (rule 110, L = 4, three runs)"
python e2e_univ.py 110 4 3
