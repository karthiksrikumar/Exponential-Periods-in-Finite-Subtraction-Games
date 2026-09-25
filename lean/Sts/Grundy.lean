import Sts.Main
import Mathlib.Data.Fintype.EquivFin

/-!
# Nim-values (Sprague–Grundy values)

`grundy L n` is the Sprague–Grundy value of a heap of size `n` in the subtraction game with move
list `L`.  A position is a P-position iff its nim-value is `0`, hence every eventual period of the
nim-sequence is an eventual period of the outcome sequence.  In particular the nim-sequence of
`Concrete.D.movesL K` has least period divisible by `260 * k * 2^k` — Guy's conjecture on
nim-sequence periods fails as well.
-/

namespace SubGame

/-- minimum excludant of a list of naturals -/
def mex (l : List ℕ) : ℕ := Nat.find (Infinite.exists_notMem_finset l.toFinset)

theorem mex_eq_zero_iff (l : List ℕ) : mex l = 0 ↔ 0 ∉ l := by
  unfold mex
  rw [Nat.find_eq_zero]
  simp

/-- Sprague–Grundy value of heap `n` in the subtraction game with move list `L` -/
def grundy (L : List ℕ) (n : ℕ) : ℕ :=
  mex (L.attach.filterMap fun s =>
    if _h : 0 < s.1 ∧ s.1 ≤ n then some (grundy L (n - s.1)) else none)
termination_by n
decreasing_by omega

theorem grundy_eq (L : List ℕ) (n : ℕ) : grundy L n =
    mex (L.attach.filterMap fun s =>
      if _h : 0 < s.1 ∧ s.1 ≤ n then some (grundy L (n - s.1)) else none) := by
  rw [grundy]

theorem grundy_eq_zero_iff' (L : List ℕ) (n : ℕ) :
    grundy L n = 0 ↔ ∀ s ∈ L, 0 < s → s ≤ n → grundy L (n - s) ≠ 0 := by
  rw [grundy_eq, mex_eq_zero_iff, List.mem_filterMap]
  constructor
  · intro h s hs hpos hle h0
    exact h ⟨⟨s, hs⟩, List.mem_attach _ _, by rw [dif_pos ⟨hpos, hle⟩, h0]⟩
  · rintro h ⟨⟨s, hs⟩, _, hf⟩
    by_cases hc : 0 < s ∧ s ≤ n
    · rw [dif_pos hc] at hf
      exact h s hs hc.1 hc.2 (Option.some.inj hf)
    · rw [dif_neg hc] at hf; exact absurd hf (by simp)

/-- P-positions are exactly the positions of nim-value `0` (for positive moves). -/
theorem grundy_eq_zero_iff (L : List ℕ) (hL : ∀ s ∈ L, 0 < s) (n : ℕ) :
    grundy L n = 0 ↔ outcome L n = true := by
  have hP : IsPSet L.toFinset (fun n => grundy L n = 0) := by
    intro n
    show grundy L n = 0 ↔ ∀ s ∈ L.toFinset, s ≤ n → ¬ grundy L (n - s) = 0
    rw [grundy_eq_zero_iff']
    simp only [List.mem_toFinset]
    constructor
    · intro h s hs hle; exact h s hs (hL s hs) hle
    · intro h s hs _ hle; exact h s hs hle
  exact ((outcome_iff_of_isPSet hL hP n)).symm

/-- `p` is an eventual period of a natural-number sequence -/
def IsEventualPeriodN (f : ℕ → ℕ) (p : ℕ) : Prop := 0 < p ∧ ∃ N, ∀ n ≥ N, f (n + p) = f n

theorem isEventualPeriod_outcome_of_grundy {L : List ℕ} (hL : ∀ s ∈ L, 0 < s) {p : ℕ}
    (h : IsEventualPeriodN (grundy L) p) : IsEventualPeriod (outcome L) p := by
  obtain ⟨hp, N, hN⟩ := h
  refine ⟨hp, N, fun n hn => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [← grundy_eq_zero_iff L hL, ← grundy_eq_zero_iff L hL, hN n hn]

namespace Concrete

/-- **Nim-sequence version.** Every eventual period of the nim-sequence of `D.movesL K` is a
multiple of `260 * k * 2^k`. -/
theorem nim_period_dvd (K : ℕ) (hK : 1 ≤ K) (p : ℕ)
    (hp : IsEventualPeriodN (grundy (D.movesL K)) p) : 260 * ((K + 1) * 2 ^ (K + 1)) ∣ p :=
  (exponential_period K hK).2.2.2 p (isEventualPeriod_outcome_of_grundy (moves_pos K hK) hp)

end Concrete
end SubGame

#print axioms SubGame.Concrete.nim_period_dvd
