import Sts.Counter

/-!
# The concrete design

Block length `B = 260`, 29 clocks, 8 wires, 26 taps.
Generated automatically from `best26.json`.
-/

namespace SubGame
namespace Concrete

def resList : List ℕ := [1, 10, 26, 35, 70, 98, 147, 222]

def D : Design 8 where
  B := 260
  clocks := [0, 2, 3, 4, 5, 6, 7, 8, 25, 27, 28, 29, 30, 31, 32, 33, 50, 60, 62, 64, 65, 67, 68, 123, 225, 228, 229, 230, 232]
  res := fun j => resList.getD j.1 0
  taps := [(0, 0, 9), (0, 0, 11), (0, 0, 13), (0, 0, 16), (0, 0, 51), (0, 0, 72), (0, 0, 75), (0, 0, 77), (0, 0, 84), (0, 0, 89), (0, 0, 104), (0, 0, 110), (0, 0, 112), (0, 0, 124), (0, 0, 135), (0, 0, 148), (0, 0, 156), (0, 0, 171), (0, 0, 176), (0, 0, 186), (0, 0, 209), (0, 0, 211), (0, 0, 249), (1, 0, 108), (1, 0, 136), (1, 0, 244)]
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
