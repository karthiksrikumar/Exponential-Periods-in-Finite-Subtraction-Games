import Sts.Tests

/-!
# Exact form of the main theorem

For the concrete design (`B = 260`, `26` taps) and every `K ≥ 1` (register length `k = K + 1`):

* the move set has **exactly** `26` elements, for every `K`;
* the largest move is `260 k - 16`;
* the least eventual period is `P = 260 k 2^k = (max S + 16) * 2^((max S + 16) / 260)`,
  in particular `2^(max S / 260) < P`: the period is exponential in the largest move;
* Guy's bound with the exponent `C(26, 2) = 325` fails already for `k = 6719`.
-/

namespace SubGame
namespace Concrete

open Design

theorem deltas_nodup : (D.taps.map fun t => t.2.2).Nodup := by decide

theorem tap_lt_B : ∀ t ∈ D.taps, t.2.2 < 260 := by decide

/-- the moves are pairwise distinct (their residues mod `260` already are) -/
theorem movesL_nodup (K : ℕ) : (D.movesL K).Nodup := by
  have hmod : (D.movesL K).map (· % 260) = D.taps.map fun t => t.2.2 := by
    simp only [Design.movesL, List.map_map]
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_apply, B_eq]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (tap_lt_B t ht)]
  exact List.Nodup.of_map _ (hmod ▸ deltas_nodup)

/-- **exactly 26 moves**, for every `K` -/
theorem card_eq (K : ℕ) : (D.movesL K).toFinset.card = 26 := by
  rw [List.toFinset_card_of_nodup (movesL_nodup K)]
  simp [Design.movesL, D]

theorem short_le : ∀ t ∈ D.taps, t.1 = 0 → t.2.1 * 260 + t.2.2 ≤ 249 := by decide

theorem long_form : ∀ t ∈ D.taps, t.1 = 1 → t.2.1 = 0 ∧ t.2.2 ≤ 244 := by decide

theorem taps_a : ∀ t ∈ D.taps, t.1 = 0 ∨ t.1 = 1 := by decide

theorem top_mem : ((1 : ℕ), (0 : ℕ), (244 : ℕ)) ∈ D.taps := by decide

/-- the largest move is `260 (K + 1) - 16` -/
theorem maxMove_eq (K : ℕ) (hK : 1 ≤ K) : maxMove K = K * 260 + 244 := by
  apply le_antisymm
  · have : maxMove K < K * 260 + 245 := by
      apply foldr_max_lt _ (by omega)
      intro s hs
      simp only [Design.movesL, List.mem_map] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      rw [B_eq]
      rcases taps_a t ht with h | h
      · have := short_le t ht h
        rw [h, zero_mul, zero_add]
        omega
      · obtain ⟨h1, h2⟩ := long_form t ht h
        rw [h, h1, one_mul, add_zero]
        omega
    omega
  · apply le_maxMove
    simp only [Design.movesL, List.mem_map]
    exact ⟨_, top_mem, by rw [B_eq]; ring⟩

/-- the period in terms of the largest move -/
theorem per_eq_maxMove (K : ℕ) (hK : 1 ≤ K) :
    per K = (maxMove K + 16) * 2 ^ ((maxMove K + 16) / 260) := by
  rw [maxMove_eq K hK]
  have e : K * 260 + 244 + 16 = (K + 1) * 260 := by ring
  rw [e, Nat.mul_div_cancel _ (by norm_num)]
  unfold per; rw [B_eq]; ring

/-- the period is exponential in the largest move -/
theorem two_pow_lt_per (K : ℕ) (hK : 1 ≤ K) : 2 ^ (maxMove K / 260) < per K := by
  rw [maxMove_eq K hK]
  have e : (K * 260 + 244) / 260 = K := by omega
  rw [e]
  unfold per; rw [B_eq]
  have h1 : 2 ^ K < 2 ^ (K + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (K + 1) ≤ (K + 1) * 2 ^ (K + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h3 : (K + 1) * 2 ^ (K + 1) ≤ 260 * ((K + 1) * 2 ^ (K + 1)) := Nat.le_mul_of_pos_left _ (by norm_num)
  omega

/-- **Main theorem, exact form.**  For every `K ≥ 1` the subtraction game `D.movesL K` has
exactly `26` moves, largest move `M = 260 (K+1) - 16`, all moves positive, and least eventual
period `P = (M + 16) * 2^((M + 16)/260) > 2^(M / 260)`. -/
theorem main_exact (K : ℕ) (hK : 1 ≤ K) :
    (D.movesL K).toFinset.card = 26 ∧
    (∀ s ∈ D.movesL K, 0 < s) ∧
    maxMove K = 260 * (K + 1) - 16 ∧
    IsEventualPeriod (outcome (D.movesL K)) (per K) ∧
    (∀ p, IsEventualPeriod (outcome (D.movesL K)) p → per K ∣ p) ∧
    per K = (maxMove K + 16) * 2 ^ ((maxMove K + 16) / 260) ∧
    2 ^ (maxMove K / 260) < per K :=
  ⟨card_eq K, moves_pos K hK, by rw [maxMove_eq K hK]; omega, (least_period K hK).1,
    (least_period K hK).2, per_eq_maxMove K hK, two_pow_lt_per K hK⟩

set_option maxRecDepth 100000 in
/-- **Guy's bound fails explicitly.**  For `k = 6719` the game has `26` moves and
`P > (max S)^C(26,2)`. -/
theorem guy_explicit :
    (D.movesL 6718).toFinset.card = 26 ∧ maxMove 6718 = 1746924 ∧ Nat.choose 26 2 = 325 ∧
    (maxMove 6718) ^ Nat.choose 26 2 < per 6718 := by
  have hm : maxMove 6718 = 1746924 := by rw [maxMove_eq 6718 (by norm_num)]
  have hc : Nat.choose 26 2 = 325 := by decide
  refine ⟨card_eq _, hm, hc, ?_⟩
  rw [hm, hc]
  unfold per; rw [B_eq]
  decide +kernel

end Concrete
end SubGame

#print axioms SubGame.Concrete.main_exact
#print axioms SubGame.Concrete.guy_explicit
