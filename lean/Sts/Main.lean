import Sts.Period
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Main results

`Concrete.D.movesL K` is an explicit list of moves (at most `26` distinct moves, all smaller
than `(K + 2) * 260`).  For every `K ≥ 1` the outcome (P/N) sequence of the subtraction game with
these moves has least eventual period exactly `260 * k * 2^k` where `k = K + 1`.

Consequently the least period of a subtraction game with a *bounded* number of moves is **not**
bounded by any polynomial in the largest move, contradicting Guy's conjecture that periods are
bounded by polynomials of degree `n(n-1)/2` in the largest move of an `n`-element subtraction set.
-/

namespace SubGame
namespace Concrete

theorem B_eq : D.B = 260 := rfl

theorem num_moves_le (K : ℕ) : (D.movesL K).toFinset.card ≤ 26 := by
  have h : (D.movesL K).length = 26 := by simp [Design.movesL, D]
  calc (D.movesL K).toFinset.card ≤ (D.movesL K).length := List.toFinset_card_le _
    _ = 26 := h

theorem taps_small : ∀ t ∈ D.taps, t.1 ≤ 1 ∧ t.2.1 ≤ 1 ∧ t.2.2 < D.B := by decide +kernel

theorem moves_lt (K : ℕ) : ∀ s ∈ D.movesL K, s < (K + 2) * D.B := by
  intro s hs
  simp only [Design.movesL, List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨ha, hb, hd⟩ := taps_small t ht
  have h1 : t.1 * K ≤ K := by
    calc t.1 * K ≤ 1 * K := Nat.mul_le_mul_right K ha
      _ = K := one_mul K
  have h2 : t.1 * K + t.2.1 ≤ K + 1 := by omega
  have h3 : (t.1 * K + t.2.1) * D.B ≤ (K + 1) * D.B := Nat.mul_le_mul_right _ h2
  have h4 : (K + 2) * D.B = (K + 1) * D.B + D.B := by ring
  omega

/-- **Theorem (exponential periods).** For all `K ≥ 1`, the subtraction game with move set
`D.movesL K` (≤ 26 moves, all `< 260 (K+2)`) has least eventual period `260 (K+1) 2^(K+1)`. -/
theorem exponential_period (K : ℕ) (hK : 1 ≤ K) :
    (D.movesL K).toFinset.card ≤ 26 ∧
    (∀ s ∈ D.movesL K, 0 < s ∧ s < (K + 2) * 260) ∧
    IsEventualPeriod (outcome (D.movesL K)) (260 * ((K + 1) * 2 ^ (K + 1))) ∧
    (∀ p, IsEventualPeriod (outcome (D.movesL K)) p → 260 * ((K + 1) * 2 ^ (K + 1)) ∣ p) :=
  ⟨num_moves_le K, fun s hs => ⟨moves_pos K hK s hs, moves_lt K s hs⟩,
    (least_period K hK).1, (least_period K hK).2⟩

/-- exponentials beat polynomials -/
theorem exists_poly_lt_exp (A d : ℕ) : ∃ n ≥ 3, A * n ^ d < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt d (r := (2 : ℝ)) (by norm_num)
  have hA : (0 : ℝ) < 1 / ((A : ℝ) + 1) := by positivity
  have hev := (h.eventually (gt_mem_nhds hA))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max N 3, le_max_right _ _, ?_⟩
  have hn := hN (max N 3) (le_max_left _ _)
  set n := max N 3
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at hn
  have : (A : ℝ) * (n : ℝ) ^ d < 2 ^ n := by
    have hnd : (0 : ℝ) ≤ (n : ℝ) ^ d := by positivity
    nlinarith
  exact_mod_cast this

/-- **Corollary (Guy's conjecture fails).** With a bounded number of moves (at most 26),
the least period is not bounded by any polynomial `C * (max move)^d`. -/
theorem not_polynomially_bounded (C d : ℕ) :
    ∃ K ≥ 1, ∀ M, (∀ s ∈ D.movesL K, s ≤ M) → M < (K + 2) * 260 →
      C * M ^ d < 260 * ((K + 1) * 2 ^ (K + 1)) := by
  obtain ⟨n, hn3, hn⟩ := exists_poly_lt_exp (2 * C * 260 ^ d) d
  refine ⟨n - 2, by omega, fun M _ hM => ?_⟩
  have hK2 : n - 2 + 2 = n := by omega
  have hK1 : n - 2 + 1 + 1 = n := by omega
  rw [hK2] at hM
  have hMd : M ^ d ≤ (n * 260) ^ d := Nat.pow_le_pow_left hM.le d
  have hpow : (n * 260) ^ d = n ^ d * 260 ^ d := Nat.mul_pow n 260 d
  have hper : 2 ^ n = 2 * 2 ^ (n - 2 + 1) := by
    rw [← pow_succ', hK1]
  -- C * M^d ≤ C * 260^d * n^d < 2^(n-1) ≤ 260 * (K+1) * 2^(K+1)
  have step1 : C * M ^ d ≤ C * 260 ^ d * n ^ d := by
    calc C * M ^ d ≤ C * (n ^ d * 260 ^ d) := Nat.mul_le_mul_left C (hpow ▸ hMd)
      _ = C * 260 ^ d * n ^ d := by ring
  have step2 : C * 260 ^ d * n ^ d < 2 ^ (n - 2 + 1) := by
    have : 2 * (C * 260 ^ d * n ^ d) < 2 * 2 ^ (n - 2 + 1) := by
      rw [← hper]; calc 2 * (C * 260 ^ d * n ^ d) = 2 * C * 260 ^ d * n ^ d := by ring
        _ < 2 ^ n := hn
    omega
  have step3 : 2 ^ (n - 2 + 1) ≤ 260 * ((n - 2 + 1) * 2 ^ (n - 2 + 1)) := by
    have : 1 ≤ 260 * (n - 2 + 1) := by omega
    calc 2 ^ (n - 2 + 1) = 1 * 2 ^ (n - 2 + 1) := (one_mul _).symm
      _ ≤ (260 * (n - 2 + 1)) * 2 ^ (n - 2 + 1) := Nat.mul_le_mul_right _ this
      _ = 260 * ((n - 2 + 1) * 2 ^ (n - 2 + 1)) := by ring
  omega

end Concrete
end SubGame

#print axioms SubGame.Concrete.exponential_period
#print axioms SubGame.Concrete.not_polynomially_bounded
