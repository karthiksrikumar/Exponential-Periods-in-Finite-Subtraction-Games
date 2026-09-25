import Sts.Grundy

/-!
# Sanity checks

The definition `outcome` is the standard normal-play outcome of the subtraction game.  We check it
against two classical examples: with moves `{1,2}` the P-positions are the multiples of `3`, and
with moves `{1,3,4}` they are the positions `≡ 0, 2 (mod 7)` (Winning Ways).

We also restate the failure of Guy's bound directly in terms of the largest move.
-/

namespace SubGame

theorem outcome_one_two (n : ℕ) : outcome [1, 2] n = true ↔ n % 3 = 0 := by
  have hP : IsPSet [1, 2].toFinset (fun n => n % 3 = 0) := by
    intro n
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    omega
  exact outcome_iff_of_isPSet (by decide) hP n

theorem outcome_one_three_four (n : ℕ) :
    outcome [1, 3, 4] n = true ↔ (n % 7 = 0 ∨ n % 7 = 2) := by
  have hP : IsPSet [1, 3, 4].toFinset (fun n => n % 7 = 0 ∨ n % 7 = 2) := by
    intro n
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    omega
  exact outcome_iff_of_isPSet (by decide) hP n

namespace Concrete

/-- the largest move of `D.movesL K` -/
def maxMove (K : ℕ) : ℕ := (D.movesL K).foldr max 0

theorem le_foldr_max (l : List ℕ) : ∀ s ∈ l, s ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro s hs
    simp only [List.mem_cons] at hs
    simp only [List.foldr_cons]
    rcases hs with rfl | hs
    · exact le_max_left _ _
    · exact le_trans (ih s hs) (le_max_right _ _)

theorem foldr_max_lt (l : List ℕ) {M : ℕ} (hM : 0 < M) (h : ∀ s ∈ l, s < M) :
    l.foldr max 0 < M := by
  induction l with
  | nil => simpa using hM
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_lt (h a (by simp)) (ih (fun s hs => h s (by simp [hs])))

theorem le_maxMove (K : ℕ) : ∀ s ∈ D.movesL K, s ≤ maxMove K := le_foldr_max _

theorem maxMove_lt (K : ℕ) : maxMove K < (K + 2) * 260 := by
  have h := moves_lt K
  rw [B_eq] at h
  exact foldr_max_lt _ (by positivity) h

/-- **Guy's bound fails** (clean form): for every polynomial bound `C * m^d` there is a subtraction
set with at most 26 moves whose least outcome period exceeds `C * (max S)^d`. -/
theorem guy_fails (C d : ℕ) : ∃ K ≥ 1, (D.movesL K).toFinset.card ≤ 26 ∧
    C * (maxMove K) ^ d < 260 * ((K + 1) * 2 ^ (K + 1)) := by
  obtain ⟨K, hK, h⟩ := not_polynomially_bounded C d
  exact ⟨K, hK, num_moves_le K, h _ (le_maxMove K) (maxMove_lt K)⟩

end Concrete
end SubGame

#print axioms SubGame.outcome_one_two
#print axioms SubGame.Concrete.guy_fails
