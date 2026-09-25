import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Data.List.Basic

/-!
# Subtraction games: basic theory

A *subtraction game* with finite move set `S ⊆ ℕ_{>0}` is played on a single heap; a move
removes `s ∈ S` tokens (only if at least `s` tokens remain) and the player unable to move loses.
A heap size `n` is a *P-position* (previous player wins) iff every move from `n` leads to a
position that is not a P-position.

We characterise the P-positions abstractly (`IsPSet`), prove uniqueness, and give a computable
outcome function `outcome` satisfying the characterisation.
-/

namespace SubGame

/-- `IsPSet S P`: the predicate `P` is the set of P-positions of the subtraction game `S`. -/
def IsPSet (S : Finset ℕ) (P : ℕ → Prop) : Prop :=
  ∀ n, P n ↔ ∀ s ∈ S, s ≤ n → ¬ P (n - s)

/-- The P-set of a subtraction game is unique (moves must be positive). -/
theorem IsPSet.iff {S : Finset ℕ} (hS : ∀ s ∈ S, 0 < s) {P Q : ℕ → Prop}
    (hP : IsPSet S P) (hQ : IsPSet S Q) (n : ℕ) : P n ↔ Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hP n, hQ n]
    constructor
    · intro h s hs hsn hq
      exact h s hs hsn ((ih (n - s) (by have := hS s hs; omega)).mpr hq)
    · intro h s hs hsn hp
      exact h s hs hsn ((ih (n - s) (by have := hS s hs; omega)).mp hp)

/-- Computable outcome function for a list of moves: `outcome L n = true` iff `n` is a
P-position of the subtraction game with move set `L`. -/
def outcome (L : List ℕ) (n : ℕ) : Bool :=
  !(L.attach.any fun s =>
      if h : 0 < s.1 ∧ s.1 ≤ n then outcome L (n - s.1) else false)
termination_by n
decreasing_by omega

theorem outcome_eq (L : List ℕ) (n : ℕ) :
    outcome L n = !(L.attach.any fun s =>
      if h : 0 < s.1 ∧ s.1 ≤ n then outcome L (n - s.1) else false) := by
  rw [outcome]

/-- The computable outcome function satisfies the P-set characterisation. -/
theorem isPSet_outcome (L : List ℕ) (hL : ∀ s ∈ L, 0 < s) :
    IsPSet L.toFinset (fun n => outcome L n = true) := by
  intro n
  show outcome L n = true ↔ ∀ s ∈ L.toFinset, s ≤ n → ¬ outcome L (n - s) = true
  rw [outcome_eq]
  simp only [Bool.not_eq_true', List.any_eq_false, List.mem_attach, true_implies,
    Subtype.forall, List.mem_toFinset]
  constructor
  · intro h s hs hsn hout
    have := h s hs
    rw [dif_pos ⟨hL s hs, hsn⟩] at this
    simp [hout] at this
  · intro h s hs
    split_ifs with h'
    · simpa using h s hs h'.2
    · simp

/-- Any P-set predicate agrees with `outcome`. -/
theorem outcome_iff_of_isPSet {L : List ℕ} (hL : ∀ s ∈ L, 0 < s) {P : ℕ → Prop}
    (hP : IsPSet L.toFinset P) (n : ℕ) : outcome L n = true ↔ P n :=
  IsPSet.iff (fun s hs => hL s (List.mem_toFinset.mp hs)) (isPSet_outcome L hL) hP n

end SubGame
