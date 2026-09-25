import Sts.Simulation
import Mathlib.Tactic.IntervalCases

/-!
# The General Layout Lemma

Every NOR circuit (satisfying mild conditions) is simulated by a subtraction game.

Construction: block length `B = 13 * Bp`; clocks at residues `1, 5, 12`; wire `j` at residue
`13 * y j`, where `y` is a Sidon sequence with `y 0 = 0`, `y j ≠ 1`, and `3 * y j + 3 ≤ Bp`.
Each input is realised by one move; every zero residue is covered by one move to a clock
(a fixed table for the residues below `13`).
-/

namespace SubGame
namespace GLL

variable {W : ℕ}

/-- landing residue, unfolded -/
theorem landRes_eq {B δ e : ℕ} (he : e < B) (hδ : δ < B) :
    landRes B δ e = if δ ≤ e then e - δ else e + B - δ := by
  unfold landRes
  split_ifs with h
  · rw [show e + B - δ = (e - δ) + B by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- residue of an input source: the clock is read at residue `5` -/
def srcRes (y : Fin W → ℕ) : Option (Fin W) → ℕ
  | none => 5
  | some i => 13 * y i

/-- the move realising input `p` of wire `j` -/
def itap (y : Fin W → ℕ) (Bp : ℕ) (j : Fin W) (p : Option (Fin W) × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if srcRes y p.1 < 13 * y j then (p.2.1, p.2.2, 13 * y j - srcRes y p.1)
  else (p.2.1, p.2.2 - 1, 13 * Bp + 13 * y j - srcRes y p.1)

/-- clock used to cover the zero residue `13 z + ρ` (`z ≥ 1`) -/
def cclk (Bp z ρ : ℕ) : ℕ :=
  if ρ = 0 ∨ ρ = 1 ∨ ρ = 2 ∨ ρ = 9 then 5
  else if ρ = 3 then (if z = Bp - 1 then 5 else 1)
  else if ρ = 7 ∨ ρ = 10 then (if z = Bp - 1 then 12 else 1)
  else if ρ = 6 then (if z = 1 then 1 else 12)
  else 1

/-- `r` is a zero residue -/
def IsZ (y : Fin W → ℕ) (r : ℕ) : Prop := r ≠ 1 ∧ r ≠ 5 ∧ r ≠ 12 ∧ ∀ j, 13 * y j ≠ r

instance (y : Fin W → ℕ) (r : ℕ) : Decidable (IsZ y r) := by unfold IsZ; infer_instance

/-- covering moves -/
def coverTaps (y : Fin W → ℕ) (Bp : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 2), (0, 0, 3), (0, 0, 6), (0, 0, 8), (0, 0, 9), (0, 0, 13 * Bp - 3), (0, 0, 13 * Bp - 6)] ++
  ((List.range (13 * Bp)).filter (fun r => decide (13 ≤ r) && decide (IsZ y r))).map
    (fun r => (0, 0, r - cclk Bp (r / 13) (r % 13)))

/-- the design of the General Layout Lemma -/
def design (y : Fin W → ℕ) (Bp : ℕ) (inp : Fin W → List (Option (Fin W) × ℕ × ℕ)) : Design W where
  B := 13 * Bp
  clocks := [1, 5, 12]
  res := fun j => 13 * y j
  taps := ((List.finRange W).flatMap fun j => (inp j).map (itap y Bp j)) ++ coverTaps y Bp
  inputs := inp

/-- hypotheses on the coarse positions -/
structure HypY (y : Fin W → ℕ) (Bp : ℕ) : Prop where
  inj : Function.Injective y
  ne1 : ∀ j, y j ≠ 1
  big : ∀ j, 3 * y j + 3 ≤ Bp
  sidon : ∀ a b c d : Fin W, y a + y b = y c + y d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- hypotheses on the circuit -/
structure HypC (y : Fin W → ℕ) (inp : Fin W → List (Option (Fin W) × ℕ × ℕ)) : Prop where
  /-- some wire (boot) sits at coarse position `0` and has value `1` in block `0` -/
  boot : ∃ j, y j = 0 ∧ inp j = [(none, 0, 1)]
  noself : ∀ j, ∀ p ∈ inp j, p.1 ≠ some j
  /-- inputs read from a higher residue need a delay `≥ 1` in the constant part -/
  back : ∀ j, ∀ p ∈ inp j, 13 * y j ≤ srcRes y p.1 → 1 ≤ p.2.2


variable {y : Fin W → ℕ} {Bp : ℕ} {inp : Fin W → List (Option (Fin W) × ℕ × ℕ)}

theorem isX_iff (r : ℕ) :
    (design y Bp inp).IsX r ↔ r = 1 ∨ r = 5 ∨ r = 12 ∨ ∃ j, 13 * y j = r := by
  simp only [Design.IsX, design, List.mem_cons, List.not_mem_nil, or_false, List.mem_finRange,
    true_and]
  tauto

theorem not_isX_iff (r : ℕ) : ¬ (design y Bp inp).IsX r ↔ IsZ y r := by
  rw [isX_iff]; unfold IsZ; push Not; tauto

/-- a move is *safe* if it never lets an element of `X` see an element of `X` -/
def Safe (y : Fin W → ℕ) (Bp δ : ℕ) : Prop :=
  ∀ e, (e = 1 ∨ e = 5 ∨ e = 12 ∨ ∃ m, 13 * y m = e) →
    ¬ (landRes (13 * Bp) δ e = 1 ∨ landRes (13 * Bp) δ e = 5 ∨ landRes (13 * Bp) δ e = 12 ∨
      ∃ l, 13 * y l = landRes (13 * Bp) δ e)

theorem cclk_mem (Bp z ρ : ℕ) : cclk Bp z ρ = 1 ∨ cclk Bp z ρ = 5 ∨ cclk Bp z ρ = 12 := by
  unfold cclk; split_ifs <;> simp

theorem cclk_le (Bp z ρ : ℕ) : cclk Bp z ρ ≤ 12 := by
  rcases cclk_mem Bp z ρ with h | h | h <;> omega

/-- the covering moves are safe -/
theorem cover_safe (hY : HypY y Bp) (hBp : 3 ≤ Bp) {t : ℕ × ℕ × ℕ} (ht : t ∈ coverTaps y Bp) :
    Safe y Bp t.2.2 := by
  intro e he hX
  have hB := hY.big
  have hne1 := hY.ne1
  have heB : e < 13 * Bp := by
    rcases he with rfl | rfl | rfl | ⟨m, rfl⟩
    · omega
    · omega
    · omega
    · have := hB m; omega
  unfold coverTaps at ht
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at ht
  rcases ht with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨r, ⟨hr, h13, hz⟩, rfl⟩
  all_goals simp only at hX
  -- small moves
  all_goals first
    | (rw [landRes_eq heB (by omega)] at hX
       split_ifs at hX
       all_goals
         rcases he with rfl | rfl | rfl | ⟨m, rfl⟩ <;>
         rcases hX with h | h | h | ⟨l, hl⟩ <;>
         first
         | omega
         | (have := hB m; have := hne1 m; omega)
         | (have := hB l; have := hne1 l; omega)
         | (have := hB m; have := hne1 m; have := hB l; have := hne1 l; omega))
    | skip
  -- generic covering moves
  all_goals
    obtain ⟨hz1, hz5, hz12, hzw⟩ := hz
    have hc := cclk_le Bp (r / 13) (r % 13)
    rw [landRes_eq heB (by omega)] at hX
    unfold cclk at hX hc
    split_ifs at hX hc
    all_goals
      rcases he with rfl | rfl | rfl | ⟨m, rfl⟩ <;>
      rcases hX with h | h | h | ⟨l, hl⟩ <;>
      first
      | omega
      | (have := hB m; have := hne1 m; have := hzw m; omega)
      | (have := hB l; have := hne1 l; omega)
      | (have := hB m; have := hne1 m; have := hzw m; have := hB l; have := hne1 l; omega)

theorem three_le (hY : HypY y Bp) (hC : HypC y inp) : 3 ≤ Bp := by
  obtain ⟨j, hj, _⟩ := hC.boot; have := hY.big j; omega

theorem mem_taps {t : ℕ × ℕ × ℕ} : t ∈ (design y Bp inp).taps ↔
    (∃ j, ∃ p ∈ inp j, itap y Bp j p = t) ∨ t ∈ coverTaps y Bp := by
  simp [design, List.mem_flatMap, List.mem_map, List.mem_finRange]

theorem srcRes_lt (hY : HypY y Bp) (hBp : 3 ≤ Bp) (σ : Option (Fin W)) : srcRes y σ < 13 * Bp := by
  cases σ with
  | none => simp [srcRes]; omega
  | some i => simp only [srcRes]; have := hY.big i; omega

/-- explicit form of an intended move -/
theorem itap_spec (hY : HypY y Bp) (hC : HypC y inp) {j : Fin W} {p : Option (Fin W) × ℕ × ℕ}
    (hp : p ∈ inp j) :
    (srcRes y p.1 < 13 * y j ∧ itap y Bp j p = (p.2.1, p.2.2, 13 * y j - srcRes y p.1)) ∨
    (13 * y j < srcRes y p.1 ∧ 1 ≤ p.2.2 ∧
      itap y Bp j p = (p.2.1, p.2.2 - 1, 13 * Bp + 13 * y j - srcRes y p.1)) := by
  unfold itap
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · push Not at h
    refine Or.inr ⟨lt_of_le_of_ne h ?_, hC.back j p hp h, rfl⟩
    intro heq
    rcases hq : p.1 with _ | i
    · rw [hq] at heq; simp [srcRes] at heq; omega
    · rw [hq] at heq; simp only [srcRes] at heq
      have hji : i = j := hY.inj (by omega)
      exact hC.noself j p hp (by rw [hq, hji])

theorem cover_lt (hBp : 3 ≤ Bp) {t : ℕ × ℕ × ℕ} (ht : t ∈ coverTaps y Bp) : t.2.2 < 13 * Bp ∧ t.1 = 0 := by
  unfold coverTaps at ht
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at ht
  rcases ht with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨r, ⟨hr, _, _⟩, rfl⟩
  all_goals exact ⟨by dsimp only; omega, rfl⟩

theorem tap_lt' (hY : HypY y Bp) (hC : HypC y inp) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ (design y Bp inp).taps) : t.2.2 < 13 * Bp := by
  have hBp := three_le hY hC
  rcases mem_taps.mp ht with ⟨j, p, hp, rfl⟩ | hc
  · have hs := srcRes_lt hY hBp p.1
    have hj := hY.big j
    rcases itap_spec hY hC hp with ⟨h1, h2⟩ | ⟨h1, _, h2⟩ <;> rw [h2] <;> simp only <;> omega
  · exact (cover_lt hBp hc).1

theorem ne_of_mem (hY : HypY y Bp) (hC : HypC y inp) {j i : Fin W} {p : Option (Fin W) × ℕ × ℕ}
    (hp : p ∈ inp j) (hi : p.1 = some i) : y i ≠ y j := by
  intro h
  exact hC.noself j p hp (by rw [hi, hY.inj h])

/-- clocks never see anything through an intended move -/
theorem intended_clock_safe (hY : HypY y Bp) (hC : HypC y inp) {j : Fin W}
    {p : Option (Fin W) × ℕ × ℕ} (hp : p ∈ inp j) (c : ℕ) (hc : c = 1 ∨ c = 5 ∨ c = 12) :
    ¬ (landRes (13 * Bp) (itap y Bp j p).2.2 c = 1 ∨ landRes (13 * Bp) (itap y Bp j p).2.2 c = 5 ∨
      landRes (13 * Bp) (itap y Bp j p).2.2 c = 12 ∨
      ∃ l, 13 * y l = landRes (13 * Bp) (itap y Bp j p).2.2 c) := by
  intro hX
  have hBp := three_le hY hC
  have hj := hY.big j
  have hs := srcRes_lt hY hBp p.1
  have hδ : (itap y Bp j p).2.2 < 13 * Bp := by
    rcases itap_spec hY hC hp with ⟨h1, h2⟩ | ⟨h1, _, h2⟩ <;> rw [h2] <;> dsimp only <;> omega
  rw [landRes_eq (by omega) hδ] at hX
  rcases itap_spec hY hC hp with ⟨h1, h2⟩ | ⟨h1, _, h2⟩ <;> rw [h2] at hX <;> dsimp only at hX <;>
  · rcases hq : p.1 with _ | i
    · simp only [hq, srcRes] at hX h1
      split_ifs at hX <;> rcases hX with h | h | h | ⟨l, hl⟩ <;>
        first | omega | (have := hY.big l; omega)
    · simp only [hq, srcRes] at hX h1
      have hi := hY.big i
      have hij := ne_of_mem hY hC hp hq
      split_ifs at hX <;> rcases hX with h | h | h | ⟨l, hl⟩ <;>
        first | omega | (have := hY.big l; omega)

/-- explicit numerical description of an intended move -/
theorem itap_num (hY : HypY y Bp) (hC : HypC y inp) {j : Fin W} {p : Option (Fin W) × ℕ × ℕ}
    (hp : p ∈ inp j) :
    (srcRes y p.1 < 13 * y j ∧ (itap y Bp j p).2.2 = 13 * y j - srcRes y p.1 ∧
        (itap y Bp j p).2.1 = p.2.2 ∧ (itap y Bp j p).1 = p.2.1) ∨
    (13 * y j < srcRes y p.1 ∧ 1 ≤ p.2.2 ∧ (itap y Bp j p).2.2 = 13 * Bp + 13 * y j - srcRes y p.1 ∧
        (itap y Bp j p).2.1 = p.2.2 - 1 ∧ (itap y Bp j p).1 = p.2.1) := by
  rcases itap_spec hY hC hp with ⟨h1, h2⟩ | ⟨h1, hb, h2⟩
  · exact Or.inl ⟨h1, by rw [h2], by rw [h2], by rw [h2]⟩
  · exact Or.inr ⟨h1, hb, by rw [h2], by rw [h2], by rw [h2]⟩

/-- what a wire sees through an intended move -/
theorem intended_wire (hY : HypY y Bp) (hC : HypC y inp) {j' : Fin W}
    {p' : Option (Fin W) × ℕ × ℕ} (hp' : p' ∈ inp j') (m : Fin W) :
    ((landRes (13 * Bp) (itap y Bp j' p').2.2 (13 * y m) = 1 ∨
        landRes (13 * Bp) (itap y Bp j' p').2.2 (13 * y m) = 5 ∨
        landRes (13 * Bp) (itap y Bp j' p').2.2 (13 * y m) = 12) →
        p'.1 = none ∧ m = j' ∧ Design.tb (itap y Bp j' p') (13 * y m) = p'.2.2) ∧
    (∀ l, 13 * y l = landRes (13 * Bp) (itap y Bp j' p').2.2 (13 * y m) →
        p'.1 = some l ∧ m = j' ∧ Design.tb (itap y Bp j' p') (13 * y m) = p'.2.2) := by
  have hBp := three_le hY hC
  have hm := hY.big m
  have hj := hY.big j'
  have hs := srcRes_lt hY hBp p'.1
  have hnum := itap_num hY hC hp'
  have hδ : (itap y Bp j' p').2.2 < 13 * Bp := by omega
  rw [landRes_eq (by omega) hδ]
  unfold Design.tb
  generalize (itap y Bp j' p').2.2 = δ at hnum hδ ⊢
  generalize (itap y Bp j' p').2.1 = tb1 at hnum ⊢
  rcases hq : p'.1 with _ | i
  · simp only [hq, srcRes] at hnum hs ⊢
    refine ⟨fun hX => ?_, fun l hl => ?_⟩
    · have hmj : m = j' := hY.inj (by split_ifs at hX <;> omega)
      subst hmj
      exact ⟨trivial, rfl, by split_ifs <;> omega⟩
    · exfalso; have := hY.big l; split_ifs at hl <;> omega
  · simp only [hq, srcRes] at hnum hs ⊢
    have hi := hY.big i
    have hij := ne_of_mem hY hC hp' hq
    refine ⟨fun hX => ?_, fun l hl => ?_⟩
    · exfalso; split_ifs at hX <;> omega
    · have hl' := hY.big l
      have heq : y m + y i = y j' + y l := by split_ifs at hl <;> omega
      rcases hY.sidon m i j' l heq with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · subst h3; subst h4
        exact ⟨rfl, rfl, by split_ifs <;> omega⟩
      · exact absurd (by rw [hq, h4]) (hC.noself j' p' hp')

theorem valid (hY : HypY y Bp) (hC : HypC y inp) : (design y Bp inp).Valid where
  hB := by have := three_le hY hC; show 0 < 13 * Bp; omega
  res_lt := by intro j _; show 13 * y j < 13 * Bp; have := hY.big j; omega
  res_inj := by
    intro i _ j _ h; exact hY.inj (by simp only [design] at h; omega)
  clk_lt := by
    intro c hc; have := three_le hY hC
    simp only [design, List.mem_cons, List.not_mem_nil, or_false] at hc
    show c < 13 * Bp; omega
  clk_disj := by
    intro c hc j _
    simp only [design, List.mem_cons, List.not_mem_nil, or_false] at hc
    show 13 * y j ≠ c; omega
  tap_lt := fun t ht => tap_lt' hY hC ht
  hK := by
    intro c hc t ht hX
    have hBp := three_le hY hC
    have hBdef : (design y Bp inp).B = 13 * Bp := rfl
    simp only [design, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [isX_iff, hBdef] at hX
    rcases mem_taps.mp ht with ⟨j, p, hp, rfl⟩ | hcov
    · exact intended_clock_safe hY hC hp c hc hX
    · exact cover_safe hY hBp hcov c (by omega) hX
  hWc := by
    intro j _ t ht hL
    have hBp := three_le hY hC
    have hBdef : (design y Bp inp).B = 13 * Bp := rfl
    simp only [design, List.mem_cons, List.not_mem_nil, or_false] at hL ⊢
    rcases mem_taps.mp ht with ⟨j', p', hp', rfl⟩ | hcov
    · obtain ⟨hn, hmj, htb⟩ := (intended_wire hY hC hp' j).1 hL
      subst hmj
      have h1 : (itap y Bp j p').1 = p'.2.1 := by
        rcases itap_num hY hC hp' with h | h
        · exact h.2.2.2
        · exact h.2.2.2.2
      rw [htb, h1, ← hn]
      exact hp'
    · exfalso
      apply cover_safe hY hBp hcov (13 * y j) (Or.inr (Or.inr (Or.inr ⟨j, rfl⟩)))
      rcases hL with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  hWw := by
    intro j _ t ht i _ hL
    have hBp := three_le hY hC
    simp only [design] at hL ⊢
    rcases mem_taps.mp ht with ⟨j', p', hp', rfl⟩ | hcov
    · obtain ⟨hn, hmj, htb⟩ := (intended_wire hY hC hp' j).2 i hL
      subst hmj
      have h1 : (itap y Bp j p').1 = p'.2.1 := by
        rcases itap_num hY hC hp' with h | h
        · exact h.2.2.2
        · exact h.2.2.2.2
      rw [htb, h1, ← hn]
      exact hp'
    · exact absurd (Or.inr (Or.inr (Or.inr ⟨i, hL⟩)))
        (cover_safe hY hBp hcov (13 * y j) (Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))))
  hW' := by
    intro j _ p hp
    have hBp := three_le hY hC
    have hj := hY.big j
    have hs := srcRes_lt hY hBp p.1
    refine ⟨itap y Bp j p, mem_taps.mpr (Or.inl ⟨j, p, hp, rfl⟩), ?_⟩
    have hnum := itap_num hY hC hp
    have hδ : (itap y Bp j p).2.2 < 13 * Bp := by omega
    simp only [design]
    rw [landRes_eq (by omega) hδ]
    unfold Design.tb
    generalize (itap y Bp j p).2.2 = δ at hnum hδ ⊢
    generalize (itap y Bp j p).2.1 = tb1 at hnum ⊢
    generalize (itap y Bp j p).1 = ta at hnum ⊢
    rcases hq : p.1 with _ | i
    · simp only [hq, srcRes] at hnum hs ⊢
      refine ⟨by omega, by split_ifs <;> omega, Or.inl ⟨trivial, ?_⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      split_ifs <;> omega
    · simp only [hq, srcRes] at hnum hs ⊢
      refine ⟨by omega, by split_ifs <;> omega, Or.inr ⟨i, List.mem_finRange i, rfl, ?_⟩⟩
      split_ifs <;> omega
  hZ1 := by
    intro r hr hX
    have hBp := three_le hY hC
    have hr' : r < 13 * Bp := List.mem_range.mp hr
    rw [not_isX_iff] at hX
    obtain ⟨jb, hjb, _⟩ := hC.boot
    obtain ⟨h1, h5, h12, hw⟩ := hX
    have h0 : r ≠ 0 := fun h => hw jb (by rw [hjb, h])
    have hBdef : (design y Bp inp).B = 13 * Bp := rfl
    have hCdef : (design y Bp inp).clocks = [1, 5, 12] := rfl
    rw [hBdef, hCdef]
    unfold Design.tb
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    by_cases h13 : 13 ≤ r
    · refine ⟨(0, 0, r - cclk Bp (r / 13) (r % 13)), mem_taps.mpr (Or.inr ?_), rfl, ?_⟩
      · unfold coverTaps
        simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
          decide_eq_true_eq]
        exact Or.inr ⟨r, ⟨hr', h13, h1, h5, h12, hw⟩, rfl⟩
      · have hc := cclk_mem Bp (r / 13) (r % 13)
        have hc' := cclk_le Bp (r / 13) (r % 13)
        dsimp only
        rw [landRes_eq (by omega) (by omega)]
        refine ⟨by split_ifs <;> omega, ?_⟩
        split_ifs <;> omega
    · have hmem : ∀ δ ∈ [2, 3, 6, 8, 9, 13 * Bp - 3, 13 * Bp - 6],
          ((0 : ℕ), (0 : ℕ), δ) ∈ (design y Bp inp).taps := by
        intro δ hδ
        apply mem_taps.mpr (Or.inr _)
        unfold coverTaps
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hδ
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        left
        rcases hδ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have key : ∀ δ ∈ [2, 3, 6, 8, 9, 13 * Bp - 3, 13 * Bp - 6], δ < 13 * Bp →
          ((if r < δ then 1 else 0) ≤ 1) →
          (landRes (13 * Bp) δ r = 1 ∨ landRes (13 * Bp) δ r = 5 ∨ landRes (13 * Bp) δ r = 12) →
          ∃ t ∈ (design y Bp inp).taps, t.1 = 0 ∧ (t.2.1 + if r < t.2.2 then 1 else 0) ≤ 1 ∧
            (landRes (13 * Bp) t.2.2 r = 1 ∨ landRes (13 * Bp) t.2.2 r = 5 ∨
              landRes (13 * Bp) t.2.2 r = 12) := by
        intro δ hδ _ htb hl
        exact ⟨(0, 0, δ), hmem δ hδ, rfl, by simpa using htb, hl⟩
      interval_cases r
      all_goals first | omega | skip
      · exact key (13 * Bp - 3) (by simp) (by omega) (by split_ifs <;> omega)
          (by rw [landRes_eq (by omega) (by omega)]; split_ifs <;> omega)
      · exact key 2 (by simp) (by omega) (by split_ifs <;> omega)
          (by rw [landRes_eq (by omega) (by omega)]; split_ifs <;> omega)
      · exact key 3 (by simp) (by omega) (by split_ifs <;> omega)
          (by rw [landRes_eq (by omega) (by omega)]; split_ifs <;> omega)
      · exact key (13 * Bp - 6) (by simp) (by omega) (by split_ifs <;> omega)
          (by rw [landRes_eq (by omega) (by omega)]; split_ifs <;> omega)
      · exact key 2 (by simp) (by omega) (by split_ifs <;> omega)
          (by rw [landRes_eq (by omega) (by omega)]; split_ifs <;> omega)
      · exact key 3 (by simp) (by omega) (by split_ifs <;> omega)
          (by rw [landRes_eq (by omega) (by omega)]; split_ifs <;> omega)
      · exact key 8 (by simp) (by omega) (by split_ifs <;> omega)
          (by rw [landRes_eq (by omega) (by omega)]; split_ifs <;> omega)
      · exact key 9 (by simp) (by omega) (by split_ifs <;> omega)
          (by rw [landRes_eq (by omega) (by omega)]; split_ifs <;> omega)
      · exact key 6 (by simp) (by omega) (by split_ifs <;> omega)
          (by rw [landRes_eq (by omega) (by omega)]; split_ifs <;> omega)


/-- the boot wire has value `1` in block `0` -/
theorem boot_zero (hC : HypC y inp) {K : ℕ} {ℓ : Fin W → ℕ → Bool}
    (hN : (design y Bp inp).NorEqns K ℓ) : ∃ jb, y jb = 0 ∧ ℓ jb 0 = true := by
  obtain ⟨jb, hjb, hinp⟩ := hC.boot
  refine ⟨jb, hjb, (hN jb 0).mpr ?_⟩
  intro q hq hle
  have : q ∈ [(none, 0, 1)] := by simpa [design, hinp] using hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  subst this
  simp at hle

theorem z0 (hY : HypY y Bp) (hC : HypC y inp) {K : ℕ} (ℓ : Fin W → ℕ → Bool)
    (hN : (design y Bp inp).NorEqns K ℓ) : (design y Bp inp).Z0 ℓ := by
  intro r hr hX
  have hBp := three_le hY hC
  obtain ⟨jb, hjb, hℓ⟩ := boot_zero hC hN
  have hv := (valid hY hC).hZ1 r hr hX
  have hr' : r < 13 * Bp := List.mem_range.mp hr
  rw [not_isX_iff] at hX
  obtain ⟨h1, h5, h12, hw⟩ := hX
  have h0 : r ≠ 0 := fun h => hw jb (by rw [hjb, h])
  have hBdef : (design y Bp inp).B = 13 * Bp := rfl
  have hCdef : (design y Bp inp).clocks = [1, 5, 12] := rfl
  rw [hBdef, hCdef]
  unfold Design.tb
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have hmem : ∀ δ ∈ [2, 6], ((0 : ℕ), (0 : ℕ), δ) ∈ (design y Bp inp).taps := by
    intro δ hδ
    apply mem_taps.mpr (Or.inr _)
    unfold coverTaps
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hδ
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    left
    rcases hδ with rfl | rfl <;> simp
  -- residues 2 and 6 are covered by boot in block 0; all others by a clock in the same block
  by_cases h26 : r = 2 ∨ r = 6
  · rcases h26 with rfl | rfl
    · refine ⟨(0, 0, 2), hmem 2 (by simp), rfl, by simp, Or.inr ⟨jb, List.mem_finRange jb, ?_, hℓ⟩⟩
      simp only [design]; rw [landRes_eq (by omega) (by omega), hjb]; simp
    · refine ⟨(0, 0, 6), hmem 6 (by simp), rfl, by simp, Or.inr ⟨jb, List.mem_finRange jb, ?_, hℓ⟩⟩
      simp only [design]; rw [landRes_eq (by omega) (by omega), hjb]; simp
  · -- reuse the hZ1 witness; for r ∉ {2, 6} it has effective delay 0
    by_cases h13 : 13 ≤ r
    · refine ⟨(0, 0, r - cclk Bp (r / 13) (r % 13)), mem_taps.mpr (Or.inr ?_), rfl, ?_⟩
      · unfold coverTaps
        simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
          decide_eq_true_eq]
        exact Or.inr ⟨r, ⟨hr', h13, h1, h5, h12, hw⟩, rfl⟩
      · have hc := cclk_mem Bp (r / 13) (r % 13)
        have hc' := cclk_le Bp (r / 13) (r % 13)
        dsimp only
        rw [landRes_eq (by omega) (by omega)]
        refine ⟨by split_ifs <;> omega, Or.inl ?_⟩
        split_ifs <;> omega
    · have hmem' : ∀ δ ∈ [3, 8, 9], ((0 : ℕ), (0 : ℕ), δ) ∈ (design y Bp inp).taps := by
        intro δ hδ
        apply mem_taps.mpr (Or.inr _)
        unfold coverTaps
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hδ
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        left
        rcases hδ with rfl | rfl | rfl <;> simp
      have hm2 := hmem 2 (by simp)
      have hm6 := hmem 6 (by simp)
      have key : ∀ δ, ((0 : ℕ), (0 : ℕ), δ) ∈ (design y Bp inp).taps → δ < 13 * Bp → δ ≤ r →
          (landRes (13 * Bp) δ r = 1 ∨ landRes (13 * Bp) δ r = 5 ∨ landRes (13 * Bp) δ r = 12) →
          ∃ t ∈ (design y Bp inp).taps, t.1 = 0 ∧ (t.2.1 + if r < t.2.2 then 1 else 0) = 0 ∧
            ((landRes (13 * Bp) t.2.2 r = 1 ∨ landRes (13 * Bp) t.2.2 r = 5 ∨
              landRes (13 * Bp) t.2.2 r = 12) ∨
             ∃ i ∈ List.finRange W, 13 * y i = landRes (13 * Bp) t.2.2 r ∧ ℓ i 0 = true) := by
        intro δ hδ hδB hle hl
        refine ⟨(0, 0, δ), hδ, rfl, ?_, Or.inl hl⟩
        dsimp only; split_ifs <;> omega
      interval_cases r
      all_goals first | omega | skip
      · exact key 2 hm2 (by omega) (by omega) (by rw [landRes_eq (by omega) (by omega)]; simp)
      · exact key 3 (hmem' 3 (by simp)) (by omega) (by omega) (by rw [landRes_eq (by omega) (by omega)]; simp)
      · exact key 2 hm2 (by omega) (by omega) (by rw [landRes_eq (by omega) (by omega)]; simp)
      · exact key 3 (hmem' 3 (by simp)) (by omega) (by omega) (by rw [landRes_eq (by omega) (by omega)]; simp)
      · exact key 8 (hmem' 8 (by simp)) (by omega) (by omega) (by rw [landRes_eq (by omega) (by omega)]; simp)
      · exact key 9 (hmem' 9 (by simp)) (by omega) (by omega) (by rw [landRes_eq (by omega) (by omega)]; simp)
      · exact key 6 hm6 (by omega) (by omega) (by rw [landRes_eq (by omega) (by omega)]; simp)

theorem taps_pos (hY : HypY y Bp) (hC : HypC y inp) : ∀ t ∈ (design y Bp inp).taps, 0 < t.2.2 := by
  intro t ht
  have hBp := three_le hY hC
  rcases mem_taps.mp ht with ⟨j, p, hp, rfl⟩ | hcov
  · have hj := hY.big j
    have hs := srcRes_lt hY hBp p.1
    rcases itap_num hY hC hp with h | h <;> omega
  · unfold coverTaps at hcov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hcov
    rcases hcov with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨r, ⟨hr, h13, _⟩, rfl⟩
    all_goals dsimp only
    all_goals first | omega | (have := cclk_le Bp (r / 13) (r % 13); omega)

theorem moves_pos (hY : HypY y Bp) (hC : HypC y inp) (K : ℕ) :
    ∀ s ∈ (design y Bp inp).movesL K, 0 < s := by
  intro s hs
  simp only [Design.movesL, List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have := taps_pos hY hC t ht
  omega

/-- **General Layout Lemma (universality).**  For every circuit satisfying `HypC` and every Sidon
sequence satisfying `HypY`, and every solution `ℓ` of the circuit's NOR equations, the P-positions
of the subtraction game `(design y Bp inp).movesL K` are exactly the designed pattern. -/
theorem simulate (hY : HypY y Bp) (hC : HypC y inp) {K : ℕ} (ℓ : Fin W → ℕ → Bool)
    (hN : (design y Bp inp).NorEqns K ℓ) (n : ℕ) :
    outcome ((design y Bp inp).movesL K) n = true ↔ (design y Bp inp).Pat ℓ n :=
  Design.outcome_eq_pat (valid hY hC) (moves_pos hY hC K) ℓ hN (z0 hY hC ℓ hN) n

end GLL
end SubGame

#print axioms SubGame.GLL.simulate
