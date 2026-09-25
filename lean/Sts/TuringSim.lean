import Sts.Universal
import Mathlib.Data.Fintype.Option

/-!
# Turing machines inside subtraction games

A deterministic Turing machine with a bounded tape (cells `0, …, L-1`, the head is kept on the tape)
is simulated by a cellular automaton whose cells hold a tape symbol and, if the head is there, the
machine state.  Combined with `Univ.universal` this gives:

**Theorem (`TM.tm_universal`).**  For every Turing machine `M` there is a *fixed* list of taps such
that for every tape length `L = K + 2` the subtraction game with moves `(a K + c) B + δ` encodes, at
the positions `((j 2^L + T) L + i) B + ρ k`, the complete configuration of `M` after `T` steps on the
input whose `i`-th bit is bit `i` of `j + 1`, for every input and every `T < 2^L`.
-/

namespace SubGame
namespace TM

open Univ GLL

/-- head movement -/
inductive Dir | left | right | stay
  deriving DecidableEq

/-- a deterministic Turing machine with `nq` states and `ng` tape symbols -/
structure Machine (nq ng : ℕ) where
  δ : Fin nq → Fin ng → Fin nq × Fin ng × Dir
  q0 : Fin nq
  sym : Bool → Fin ng

/-- a configuration: state, head position, tape -/
structure Config (nq ng : ℕ) where
  q : Fin nq
  h : ℕ
  tape : ℕ → Fin ng

variable {nq ng : ℕ}

/-- the head moves but stays on the tape `0, …, L-1` -/
def move (L h : ℕ) : Dir → ℕ
  | .left => if h = 0 then 0 else h - 1
  | .right => if h + 1 = L then h else h + 1
  | .stay => h

/-- one step of the machine -/
def Machine.step (M : Machine nq ng) (L : ℕ) (c : Config nq ng) : Config nq ng :=
  { q := (M.δ c.q (c.tape c.h)).1
    h := move L c.h (M.δ c.q (c.tape c.h)).2.2
    tape := Function.update c.tape c.h (M.δ c.q (c.tape c.h)).2.1 }

/-- the initial configuration on input `X` (cell `i` holds bit `i` of `X`) -/
def Machine.init (M : Machine nq ng) (X : ℕ) : Config nq ng :=
  { q := M.q0, h := 0, tape := fun i => M.sym (X.testBit i) }

/-- the configuration after `T` steps -/
def Machine.conf (M : Machine nq ng) (L X : ℕ) : ℕ → Config nq ng
  | 0 => M.init X
  | T + 1 => M.step L (M.conf L X T)

theorem move_lt {L h : ℕ} (hh : h < L) (d : Dir) : move L h d < L := by
  cases d <;> simp only [move] <;> (try split_ifs) <;> omega

theorem conf_h_lt (M : Machine nq ng) {L : ℕ} (hL : 1 ≤ L) (X T : ℕ) : (M.conf L X T).h < L := by
  induction T with
  | zero => simp [Machine.conf, Machine.init]; omega
  | succ T ih => exact move_lt ih _

/-! ## The cellular automaton -/

/-- contents of a cell: `none` is the wall (boundary); otherwise a symbol and maybe the head -/
abbrev Cell (nq ng : ℕ) := Option (Fin ng × Option (Fin nq))

/-- the cell `i` of a configuration -/
def cellOf (c : Config nq ng) (i : ℕ) : Cell nq ng := some (c.tape i, if c.h = i then some c.q else none)

def pick {α : Type} : Option α → Option α → Option α → Option α
  | some a, _, _ => some a
  | none, some a, _ => some a
  | none, none, c => c

/-- the head arrives from the left neighbour -/
def fromL (M : Machine nq ng) : Cell nq ng → Option (Fin nq)
  | some (γ, some q) => if (M.δ q γ).2.2 = .right then some (M.δ q γ).1 else none
  | _ => none

/-- the head arrives from the right neighbour -/
def fromR (M : Machine nq ng) : Cell nq ng → Option (Fin nq)
  | some (γ, some q) => if (M.δ q γ).2.2 = .left then some (M.δ q γ).1 else none
  | _ => none

/-- the head stays (it may be blocked by a wall) -/
def fromC (M : Machine nq ng) (lft rgt : Cell nq ng) (γ : Fin ng) : Option (Fin nq) → Option (Fin nq)
  | some q =>
    match (M.δ q γ).2.2 with
    | .stay => some (M.δ q γ).1
    | .left => if lft = none then some (M.δ q γ).1 else none
    | .right => if rgt = none then some (M.δ q γ).1 else none
  | none => none

/-- the local rule of the simulating automaton -/
def tmRule (M : Machine nq ng) (lft cen rgt : Cell nq ng) : Cell nq ng :=
  match cen with
  | none => none
  | some (γ, hd) =>
    some ((match hd with | some q => (M.δ q γ).2.1 | none => γ),
      pick (fromC M lft rgt γ hd) (fromL M lft) (fromR M rgt))

theorem fromL_none (M : Machine nq ng) (x : Option (Fin ng × Option (Fin nq))) (hx : ∀ γ q, x ≠ some (γ, some q)) :
    fromL M x = none := by
  rcases x with _ | ⟨γ, _ | q⟩
  · rfl
  · rfl
  · exact absurd rfl (hx γ q)

theorem fromR_none (M : Machine nq ng) (x : Option (Fin ng × Option (Fin nq))) (hx : ∀ γ q, x ≠ some (γ, some q)) :
    fromR M x = none := by
  rcases x with _ | ⟨γ, _ | q⟩
  · rfl
  · rfl
  · exact absurd rfl (hx γ q)

/-- the head is on this cell -/
theorem head_here (M : Machine nq ng) {L h : ℕ} (q : Fin nq) (tape : ℕ → Fin ng)
    (lft rgt : Cell nq ng) (hl : lft = none ↔ h = 0) (hr : rgt = none ↔ h + 1 = L)
    (hl' : ∀ γ q, lft ≠ some (γ, some q)) (hr' : ∀ γ q, rgt ≠ some (γ, some q)) :
    pick (fromC M lft rgt (tape h) (some q)) (fromL M lft) (fromR M rgt) =
      if move L h (M.δ q (tape h)).2.2 = h then some (M.δ q (tape h)).1 else none := by
  rw [fromL_none M lft hl', fromR_none M rgt hr']
  simp only [fromC]
  rcases hδ : M.δ q (tape h) with ⟨q', γ', d⟩
  cases d
  · by_cases h0 : h = 0
    · have : lft = none := hl.mpr h0
      simp only [this, if_true, move, h0, pick]
    · have : lft ≠ none := fun e => h0 (hl.mp e)
      simp only [this, if_false, move, h0, pick]
      rw [if_neg (by omega)]
  · by_cases h1 : h + 1 = L
    · have : rgt = none := hr.mpr h1
      simp only [this, if_true, move, h1, pick]
    · have : rgt ≠ none := fun e => h1 (hr.mp e)
      simp only [this, if_false, move, h1, pick]
      rw [if_neg (by omega)]
  · simp only [move, pick, if_true]

/-- the head is on the left neighbour -/
theorem head_left (M : Machine nq ng) {L h i : ℕ} (hi : i < L) (hhi : h + 1 = i) (q : Fin nq)
    (tape : ℕ → Fin ng) (rgt : Cell nq ng) (hr' : ∀ γ q, rgt ≠ some (γ, some q)) :
    pick (fromC M (some (tape h, some q)) rgt (tape i) none) (fromL M (some (tape h, some q)))
        (fromR M rgt) =
      if move L h (M.δ q (tape h)).2.2 = i then some (M.δ q (tape h)).1 else none := by
  rw [fromR_none M rgt hr']
  rcases hδ : M.δ q (tape h) with ⟨q', γ', d⟩
  cases d
  · simp only [fromC, fromL, hδ, pick, move]
    split_ifs <;> first | rfl | omega | simp_all
  · simp only [fromC, fromL, hδ, pick, move]
    split_ifs <;> first | rfl | omega | simp_all
  · simp only [fromC, fromL, hδ, pick, move]
    split_ifs <;> first | rfl | omega | simp_all

/-- the head is on the right neighbour -/
theorem head_right (M : Machine nq ng) {L h i : ℕ} (hhi : h = i + 1) (q : Fin nq)
    (tape : ℕ → Fin ng) (lft : Cell nq ng) (hl' : ∀ γ q, lft ≠ some (γ, some q)) :
    pick (fromC M lft (some (tape h, some q)) (tape i) none) (fromL M lft)
        (fromR M (some (tape h, some q))) =
      if move L h (M.δ q (tape h)).2.2 = i then some (M.δ q (tape h)).1 else none := by
  rw [fromL_none M lft hl']
  rcases hδ : M.δ q (tape h) with ⟨q', γ', d⟩
  cases d
  · simp only [fromC, fromR, hδ, pick, move]
    split_ifs <;> first | rfl | omega | simp_all
  · simp only [fromC, fromR, hδ, pick, move]
    split_ifs <;> first | rfl | omega | simp_all
  · simp only [fromC, fromR, hδ, pick, move]
    split_ifs <;> first | rfl | omega | simp_all

/-- the head is far away -/
theorem head_far (M : Machine nq ng) {L h i : ℕ} (hhi : h ≠ i) (h1 : h + 1 ≠ i) (h2 : h ≠ i + 1)
    (q : Fin nq) (tape : ℕ → Fin ng) (γ : Fin ng) (lft rgt : Cell nq ng)
    (hl' : ∀ γ q, lft ≠ some (γ, some q)) (hr' : ∀ γ q, rgt ≠ some (γ, some q)) :
    pick (fromC M lft rgt γ none) (fromL M lft) (fromR M rgt) =
      if move L h (M.δ q (tape h)).2.2 = i then some (M.δ q (tape h)).1 else none := by
  rw [fromL_none M lft hl', fromR_none M rgt hr']
  have hm : ∀ d, move L h d ≠ i := by
    intro d; cases d <;> simp only [move] <;> (try split_ifs) <;> omega
  rw [if_neg (hm _)]
  rfl

/-- **one step of the automaton = one step of the machine** -/
theorem tmRule_step (M : Machine nq ng) {L : ℕ} (c : Config nq ng) (hh : c.h < L) {i : ℕ}
    (hi : i < L) :
    tmRule M (if i = 0 then none else cellOf c (i - 1)) (cellOf c i)
      (if i + 1 = L then none else cellOf c (i + 1)) = cellOf (M.step L c) i := by
  obtain ⟨q, h, tape⟩ := c
  simp only at hh
  simp only [cellOf, tmRule, Machine.step]
  -- the symbol
  have hsym : (match (if h = i then some q else none) with
      | some q' => (M.δ q' (tape i)).2.1 | none => tape i) =
      Function.update tape h (M.δ q (tape h)).2.1 i := by
    by_cases hhi : h = i
    · subst hhi; simp
    · simp [hhi, Function.update_of_ne (Ne.symm hhi)]
  rw [hsym]
  congr 2
  -- the head
  by_cases h1 : h = i
  · subst h1
    simp only [if_true]
    apply head_here M q tape
    · by_cases h0 : h = 0 <;> simp [h0]
    · by_cases h0 : h + 1 = L <;> simp [h0]
    · intro γ q'; by_cases h0 : h = 0 <;> simp [h0] <;> omega
    · intro γ q'; by_cases h0 : h + 1 = L <;> simp [h0]
  · simp only [h1, if_false]
    by_cases h2 : h + 1 = i
    · have e1 : (if i = 0 then (none : Cell nq ng) else
          some (tape (i - 1), if h = i - 1 then some q else none)) = some (tape h, some q) := by
        rw [if_neg (by omega), if_pos (by omega), show i - 1 = h by omega]
      rw [e1]
      apply head_left M hi h2 q tape
      intro γ q'; split_ifs <;> simp <;> omega
    · by_cases h3 : h = i + 1
      · have e2 : (if i + 1 = L then (none : Cell nq ng) else
            some (tape (i + 1), if h = i + 1 then some q else none)) = some (tape h, some q) := by
          rw [if_neg (by omega), if_pos h3, ← h3]
        rw [e2]
        apply head_right M h3 q tape
        intro γ q'; split_ifs <;> simp <;> omega
      · apply head_far M h1 h2 h3 q tape
        · intro γ q'; split_ifs <;> simp <;> omega
        · intro γ q'; split_ifs <;> simp <;> omega

/-! ## Encoding cells as bit vectors -/

/-- number of cell contents -/
abbrev NC (nq ng : ℕ) : ℕ := Fintype.card (Cell nq ng)

/-- one-hot encoding of cell contents -/
noncomputable def enc (x : Cell nq ng) : Fin (NC nq ng) → Bool :=
  fun k => decide (k = Fintype.equivFin (Cell nq ng) x)

theorem enc_inj {x y : Cell nq ng} (h : enc x = enc y) : x = y := by
  have h1 := congrFun h (Fintype.equivFin (Cell nq ng) x)
  simp only [enc] at h1
  have h2 : Fintype.equivFin (Cell nq ng) x = Fintype.equivFin (Cell nq ng) y := by
    by_contra hne
    simp [hne] at h1
  exact (Fintype.equivFin _).injective h2

open Classical in
/-- decoding (a left inverse of `enc`) -/
noncomputable def dec (v : Fin (NC nq ng) → Bool) : Cell nq ng :=
  if h : ∃ x, enc x = v then Classical.choose h else none

theorem dec_enc (x : Cell nq ng) : dec (enc x) = x := by
  have h : ∃ y, enc y = enc x := ⟨x, rfl⟩
  simp only [dec, h, dif_pos]
  exact enc_inj (Classical.choose_spec h)

/-- the simulating cellular automaton -/
noncomputable def caOf (M : Machine nq ng) : CA (NC nq ng) where
  rule := fun l c r => enc (tmRule M (dec l) (dec c) (dec r))
  init := fun v f _ => enc (some (M.sym v, if f then some M.q0 else none))
  bnd := enc none

/-- the automaton reproduces the machine -/
theorem run_eq (M : Machine nq ng) {L : ℕ} (hL : 1 ≤ L) (X : ℕ) :
    ∀ T i, i < L → (caOf M).run L X T i = enc (cellOf (M.conf L X T) i) := by
  intro T
  induction T with
  | zero =>
    intro i _
    simp only [CA.run, caOf, Machine.conf, Machine.init, cellOf]
    congr 3
    by_cases h : i = 0 <;> simp [h, eq_comm]
  | succ T ih =>
    intro i hi
    have hh := conf_h_lt M hL X T
    have hl : (if i = 0 then (caOf M).bnd else (caOf M).run L X T (i - 1)) =
        enc (if i = 0 then none else cellOf (M.conf L X T) (i - 1)) := by
      split_ifs with h0
      · rfl
      · exact ih (i - 1) (by omega)
    have hr : (if i + 1 = L then (caOf M).bnd else (caOf M).run L X T (i + 1)) =
        enc (if i + 1 = L then none else cellOf (M.conf L X T) (i + 1)) := by
      split_ifs with h0
      · rfl
      · exact ih (i + 1) (by omega)
    simp only [CA.run]
    rw [hl, hr, ih i hi]
    simp only [caOf, dec_enc]
    rw [tmRule_step M _ hh hi]
    rfl

/-- **Turing machines inside subtraction games with a bounded number of moves (formal).**
For every Turing machine `M` there are `B`, residues `ρ` and a fixed list of taps such that for every
tape length `L = K + 2`, input `j + 1`, time `T < 2^L`, cell `i < L` and code bit `k`, the position
`((j 2^L + T) L + i) B + ρ k` is a P-position of the subtraction game `movesOf B taps K` iff bit `k`
of the (one-hot) code of cell `i` of `M`'s configuration after `T` steps on input `j + 1` is set. -/
theorem tm_universal (M : Machine nq ng) :
    ∃ (B : ℕ) (taps : List (ℕ × ℕ × ℕ)) (ρ : Fin (NC nq ng) → ℕ),
      ∀ K j T i (k : Fin (NC nq ng)), T < 2 ^ (K + 2) → i < K + 2 →
        (outcome (movesOf B taps K) (((j * 2 ^ (K + 2) + T) * (K + 2) + i) * B + ρ k) = true ↔
          enc (cellOf (M.conf (K + 2) (j + 1) T) i) k = true) := by
  obtain ⟨B, taps, ρ, h⟩ := universal (caOf M)
  refine ⟨B, taps, ρ, fun K j T i k hT hi => ?_⟩
  rw [h K j T i k hT hi, run_eq M (by omega) (j + 1) T i hi]

/-- in particular the machine state can be read off the game: the head is on cell `i` in state
`q` after `T` steps iff the corresponding position is a P-position -/
theorem tm_state (M : Machine nq ng) :
    ∃ (B : ℕ) (taps : List (ℕ × ℕ × ℕ)) (ρ : Fin (NC nq ng) → ℕ),
      ∀ K j T i (γ : Fin ng) (q : Fin nq), T < 2 ^ (K + 2) → i < K + 2 →
        (outcome (movesOf B taps K) (((j * 2 ^ (K + 2) + T) * (K + 2) + i) * B +
            ρ (Fintype.equivFin (Cell nq ng) (some (γ, some q)))) = true ↔
          cellOf (M.conf (K + 2) (j + 1) T) i = some (γ, some q)) := by
  obtain ⟨B, taps, ρ, h⟩ := tm_universal M
  refine ⟨B, taps, ρ, fun K j T i γ q hT hi => ?_⟩
  rw [h K j T i _ hT hi]
  simp only [enc, decide_eq_true_eq]
  constructor
  · intro e; exact ((Fintype.equivFin _).injective e).symm
  · intro e; rw [e]

end TM
end SubGame

#print axioms SubGame.TM.tm_universal
#print axioms SubGame.TM.tm_state
