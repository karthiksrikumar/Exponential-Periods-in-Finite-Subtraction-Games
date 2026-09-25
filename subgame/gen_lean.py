# Generate Lean file Sts/Design.lean from a design JSON
import json, sys
L=json.load(open(sys.argv[1])); out=sys.argv[2]
B=L['B']; res=L['res']; clocks=L['clocks']
WIRES=['boot','nm','marker','ncin','nb','g1','carry','u']
taps=[]
for q,d in L['taps']:
    if isinstance(q,list): taps.append((1,1+q[1],d))   # q = k + c = K + 1 + c
    else: taps.append((0,q,d))
taps=sorted(set(taps))
assert all(b>=0 for a,b,d in taps)
reslist=', '.join(str(res[w]) for w in WIRES)
lean=f'''import Sts.Counter

/-!
# The concrete design

Block length `B = {B}`, {len(clocks)} clocks, 8 wires, {len(taps)} taps.
Generated automatically from `{sys.argv[1].split('/')[-1]}`.
-/

namespace SubGame
namespace Concrete

def resList : List ℕ := [{reslist}]

def D : Design 8 where
  B := {B}
  clocks := {clocks}
  res := fun j => resList.getD j.1 0
  taps := [{', '.join('(%d, %d, %d)'%t for t in taps)}]
  inputs := Counter.inputs

set_option maxRecDepth 100000 in
theorem valid : D.Valid where
  hB := by decide +kernel
  res_lt := by decide +kernel
  res_inj := by decide +kernel
  clk_lt := by decide +kernel
  clk_disj := by decide +kernel
  tap_lt := by decide +kernel
  hK := by decide +kernel
  hWc := by decide +kernel
  hWw := by decide +kernel
  hW' := by decide +kernel
  hZ1 := by decide +kernel

/-- block-0 values of the wires -/
def v0 : Fin 8 → Bool := fun j => [true, false, true, false, true, false, false, true].getD j.1 false

theorem val_zero (K : ℕ) (j : Fin 8) : Counter.val K j 0 = v0 j := by
  fin_cases j <;> simp [Counter.val, v0, Counter.cin, low, Nat.zero_div]

set_option maxRecDepth 100000 in
theorem z0v : ∀ r ∈ List.range D.B, ¬ D.IsX r → ∃ t ∈ D.taps, t.1 = 0 ∧ Design.tb t r = 0 ∧
    (landRes D.B t.2.2 r ∈ D.clocks ∨
      ∃ i ∈ List.finRange 8, D.res i = landRes D.B t.2.2 r ∧ v0 i = true) := by
  decide +kernel

theorem z0 (K : ℕ) : D.Z0 (Counter.val K) := by
  intro r hr hX
  obtain ⟨t, ht, h1, h2, h3⟩ := z0v r hr hX
  refine ⟨t, ht, h1, h2, ?_⟩
  simpa [val_zero] using h3

theorem taps_nonzero : ∀ t ∈ D.taps, 0 < t.1 ∨ 0 < t.2.1 ∨ 0 < t.2.2 := by decide +kernel

theorem moves_pos (K : ℕ) (hK : 1 ≤ K) : ∀ s ∈ D.movesL K, 0 < s := by
  intro s hs
  simp only [Design.movesL, List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hB : 0 < D.B := by decide +kernel
  rcases taps_nonzero t ht with h | h | h
  · have : 0 < t.1 * K := Nat.mul_pos h hK
    have : 0 < (t.1 * K + t.2.1) * D.B := Nat.mul_pos (by omega) hB
    omega
  · have : 0 < (t.1 * K + t.2.1) * D.B := Nat.mul_pos (by omega) hB
    omega
  · omega

/-- **The outcome sequence of the subtraction game `D.movesL K` is the counter pattern.** -/
theorem outcome_iff (K : ℕ) (hK : 1 ≤ K) (n : ℕ) :
    outcome (D.movesL K) n = true ↔ D.Pat (Counter.val K) n :=
  Design.outcome_eq_pat valid (moves_pos K hK) (Counter.val K) (Counter.norEqns K) (z0 K) n

end Concrete
end SubGame
'''
open(out,'w',encoding='utf8').write(lean)
print('taps',len(taps),'B',B,'clocks',len(clocks))
