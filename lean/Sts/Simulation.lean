import Sts.Basic
import Sts.Arith

/-!
# Simulating NOR circuits by subtraction games

A *design* consists of a block length `B`, a list of *clock* residues, `W` *wire* residues,
a list of symbolic *taps* `(a, b, δ)` (standing for the move `(a*K+b)*B + δ`, where `K` is a
size parameter), and for every wire a list of *inputs* `(src, a, b)` (source wire or the clock,
with block delay `a*K+b`).

Given logic values `ℓ j τ` of the wires satisfying the NOR equations of the circuit, and finitely
many local conditions on the design (all decidable), the set of P-positions of the subtraction
game with move set `D.moves K` is exactly the *pattern*: all clock positions, plus the position of
wire `j` in block `τ` whenever `ℓ j τ = true`.
-/

namespace SubGame

structure Design (W : ℕ) where
  B : ℕ
  clocks : List ℕ
  res : Fin W → ℕ
  /-- taps `(a, b, δ)` : the move `(a*K+b)*B + δ` -/
  taps : List (ℕ × ℕ × ℕ)
  /-- inputs `(src, a, b)` of each wire, `src = none` meaning the clock; delay `a*K+b` -/
  inputs : Fin W → List (Option (Fin W) × ℕ × ℕ)

namespace Design

variable {W : ℕ} (D : Design W)

/-- The move set for size parameter `K`. -/
def movesL (K : ℕ) : List ℕ :=
  D.taps.map fun t => (t.1 * K + t.2.1) * D.B + t.2.2

/-- The move set for size parameter `K`. -/
def moves (K : ℕ) : Finset ℕ := (D.movesL K).toFinset

/-- residue `r` carries a clock or a wire -/
def IsX (r : ℕ) : Prop := r ∈ D.clocks ∨ ∃ j ∈ List.finRange W, D.res j = r

instance decIsX (r : ℕ) : Decidable (D.IsX r) := by
  unfold IsX; infer_instance

/-- value of an input source (the clock is always `true`) -/
def srcVal (ℓ : Fin W → ℕ → Bool) : Option (Fin W) → ℕ → Bool
  | none, _ => true
  | some j, τ => ℓ j τ

/-- the NOR equations of the circuit (inputs from negative blocks read `false`) -/
def NorEqns (K : ℕ) (ℓ : Fin W → ℕ → Bool) : Prop :=
  ∀ j τ, ℓ j τ = true ↔
    ∀ p ∈ D.inputs j, p.2.1 * K + p.2.2 ≤ τ → srcVal ℓ p.1 (τ - (p.2.1 * K + p.2.2)) = false

/-- the designed pattern of P-positions -/
def Pat (ℓ : Fin W → ℕ → Bool) (n : ℕ) : Prop :=
  n % D.B ∈ D.clocks ∨ ∃ j, D.res j = n % D.B ∧ ℓ j (n / D.B) = true

/-- effective delay component `b` of tap `t` applied at residue `e` -/
def tb (t : ℕ × ℕ × ℕ) (e : ℕ) : ℕ := t.2.1 + if e < t.2.2 then 1 else 0

structure Valid : Prop where
  hB : 0 < D.B
  res_lt : ∀ j ∈ List.finRange W, D.res j < D.B
  res_inj : ∀ i ∈ List.finRange W, ∀ j ∈ List.finRange W, D.res i = D.res j → i = j
  clk_lt : ∀ c ∈ D.clocks, c < D.B
  clk_disj : ∀ c ∈ D.clocks, ∀ j ∈ List.finRange W, D.res j ≠ c
  tap_lt : ∀ t ∈ D.taps, t.2.2 < D.B
  /-- clocks never see a clock or wire -/
  hK : ∀ c ∈ D.clocks, ∀ t ∈ D.taps, ¬ D.IsX (landRes D.B t.2.2 c)
  /-- every clock/wire seen by a wire is one of its inputs, with the right delay -/
  hWc : ∀ j ∈ List.finRange W, ∀ t ∈ D.taps,
    landRes D.B t.2.2 (D.res j) ∈ D.clocks → (none, t.1, tb t (D.res j)) ∈ D.inputs j
  hWw : ∀ j ∈ List.finRange W, ∀ t ∈ D.taps, ∀ i ∈ List.finRange W,
    D.res i = landRes D.B t.2.2 (D.res j) → (some i, t.1, tb t (D.res j)) ∈ D.inputs j
  /-- every input of every wire is realised by some tap -/
  hW' : ∀ j ∈ List.finRange W, ∀ p ∈ D.inputs j, ∃ t ∈ D.taps, t.1 = p.2.1 ∧ tb t (D.res j) = p.2.2 ∧
    ((p.1 = none ∧ landRes D.B t.2.2 (D.res j) ∈ D.clocks) ∨
     (∃ i ∈ List.finRange W, p.1 = some i ∧ landRes D.B t.2.2 (D.res j) = D.res i))
  /-- zero residues are covered by a clock of the same or previous block -/
  hZ1 : ∀ r ∈ List.range D.B, ¬ D.IsX r → ∃ t ∈ D.taps, t.1 = 0 ∧ tb t r ≤ 1 ∧
    landRes D.B t.2.2 r ∈ D.clocks

/-- block-0 covering condition (depends on the block-0 logic values) -/
def Z0 (ℓ : Fin W → ℕ → Bool) : Prop :=
  ∀ r ∈ List.range D.B, ¬ D.IsX r → ∃ t ∈ D.taps, t.1 = 0 ∧ tb t r = 0 ∧
    (landRes D.B t.2.2 r ∈ D.clocks ∨
      ∃ i ∈ List.finRange W, D.res i = landRes D.B t.2.2 r ∧ ℓ i 0 = true)

variable {D}

theorem mem_moves {K s : ℕ} : s ∈ D.moves K ↔ ∃ t ∈ D.taps, (t.1 * K + t.2.1) * D.B + t.2.2 = s := by
  simp [moves, movesL]

/-- Decomposition of `n - s` for a tap. -/
theorem tap_sub (hv : D.Valid) {K τ e : ℕ} (he : e < D.B) {t : ℕ × ℕ × ℕ} (ht : t ∈ D.taps) :
    ((t.1 * K + t.2.1) * D.B + t.2.2 ≤ τ * D.B + e ↔ t.1 * K + tb t e ≤ τ) ∧
    (t.1 * K + tb t e ≤ τ →
      τ * D.B + e - ((t.1 * K + t.2.1) * D.B + t.2.2) =
        (τ - (t.1 * K + tb t e)) * D.B + landRes D.B t.2.2 e) := by
  have h := sub_decomp (q := t.1 * K + t.2.1) (τ := τ) he (hv.tap_lt t ht)
  have hq : effDelay (t.1 * K + t.2.1) t.2.2 e = t.1 * K + tb t e := by
    unfold effDelay tb; ring
  rw [hq] at h
  exact h

theorem pat_decomp (hv : D.Valid) (ℓ : Fin W → ℕ → Bool) {τ l : ℕ} (hl : l < D.B) :
    D.Pat ℓ (τ * D.B + l) ↔ l ∈ D.clocks ∨ ∃ j, D.res j = l ∧ ℓ j τ = true := by
  unfold Pat
  rw [mod_of_decomp hl, div_of_decomp hl]

/-- **Simulation theorem.** -/
theorem isPSet_pat (hv : D.Valid) {K : ℕ} (ℓ : Fin W → ℕ → Bool) (hN : D.NorEqns K ℓ)
    (hZ0 : D.Z0 ℓ) : IsPSet (D.moves K) (D.Pat ℓ) := by
  intro n
  have hB := hv.hB
  set τ := n / D.B with hτ
  set e := n % D.B with he
  have hel : e < D.B := Nat.mod_lt _ hB
  have hn : n = τ * D.B + e := by rw [hτ, he, mul_comm]; exact (Nat.div_add_mod n D.B).symm
  -- rewrite the right-hand side in terms of taps
  have key : (∀ s ∈ D.moves K, s ≤ n → ¬ D.Pat ℓ (n - s)) ↔
      ∀ t ∈ D.taps, t.1 * K + tb t e ≤ τ →
        ¬ (landRes D.B t.2.2 e ∈ D.clocks ∨
            ∃ j, D.res j = landRes D.B t.2.2 e ∧ ℓ j (τ - (t.1 * K + tb t e)) = true) := by
    constructor
    · intro h t ht hle
      have hs := (tap_sub hv hel ht (K := K) (τ := τ))
      have hmem : (t.1 * K + t.2.1) * D.B + t.2.2 ∈ D.moves K := mem_moves.mpr ⟨t, ht, rfl⟩
      have := h _ hmem (by rw [hn]; exact hs.1.mpr hle)
      rw [hn, hs.2 hle, pat_decomp hv ℓ (landRes_lt hB)] at this
      exact this
    · intro h s hs hsn
      obtain ⟨t, ht, rfl⟩ := mem_moves.mp hs
      have hsub := (tap_sub hv hel ht (K := K) (τ := τ))
      rw [hn] at hsn ⊢
      have hle := hsub.1.mp hsn
      rw [hsub.2 hle, pat_decomp hv ℓ (landRes_lt hB)]
      exact h t ht hle
  rw [key, hn, pat_decomp hv ℓ hel]
  by_cases hc : e ∈ D.clocks
  · -- clock residue
    simp only [hc, true_or, true_iff]
    intro t ht _ hX
    exact hv.hK e hc t ht (hX.imp id (fun ⟨j, hj, _⟩ => ⟨j, List.mem_finRange j, hj⟩))
  by_cases hw : ∃ j, D.res j = e
  · -- wire residue
    obtain ⟨j, hj⟩ := hw
    have hsimp : (e ∈ D.clocks ∨ ∃ j, D.res j = e ∧ ℓ j τ = true) ↔ ℓ j τ = true := by
      constructor
      · rintro (h | ⟨i, hi, hℓ⟩)
        · exact absurd h hc
        · rwa [hv.res_inj i (List.mem_finRange i) j (List.mem_finRange j) (hi.trans hj.symm)] at hℓ
      · intro h; exact Or.inr ⟨j, hj, h⟩
    rw [hsimp, hN j τ]
    constructor
    · intro hnor t ht hle hX
      have hWc := hv.hWc j (List.mem_finRange j) t ht
      have hWw := fun i => hv.hWw j (List.mem_finRange j) t ht i
      rw [hj] at hWc hWw
      rcases hX with hX | ⟨i, hi, hℓ⟩
      · have hin := hWc hX
        have := hnor _ hin (by simpa using hle)
        simp [srcVal] at this
      · have hin := hWw i (List.mem_finRange i) hi
        have := hnor _ hin (by simpa using hle)
        simp only [srcVal] at this
        rw [this] at hℓ
        exact Bool.false_ne_true hℓ
    · intro hall p hp hle
      obtain ⟨t, ht, ha, hb, hland⟩ := hv.hW' j (List.mem_finRange j) p hp
      rw [hj] at hb hland
      have hle' : t.1 * K + tb t e ≤ τ := by rw [ha, hb]; exact hle
      have hnot := hall t ht hle'
      rcases p with ⟨src, pa, pb⟩
      simp only at ha hb hle hland ⊢
      rcases hland with ⟨hsrc, hland⟩ | ⟨i, -, hsrc, hland⟩
      · exact absurd (Or.inl hland) hnot
      · subst hsrc
        simp only [srcVal]
        by_contra hcon
        apply hnot
        refine Or.inr ⟨i, hland.symm, ?_⟩
        rw [ha, hb]
        simpa using hcon
  · -- zero residue
    have hnX : ¬ D.IsX e := by
      rintro (h | ⟨j, -, hj⟩)
      · exact hc h
      · exact hw ⟨j, hj⟩
    have hlhs : ¬ (e ∈ D.clocks ∨ ∃ j, D.res j = e ∧ ℓ j τ = true) := by
      rintro (h | ⟨j, hj, _⟩)
      · exact hc h
      · exact hw ⟨j, hj⟩
    simp only [hlhs, false_iff, not_forall, not_not]
    rcases Nat.eq_zero_or_pos τ with h0 | hpos
    · obtain ⟨t, ht, ha, hb, hland⟩ := hZ0 e (List.mem_range.mpr hel) hnX
      refine ⟨t, ht, by rw [ha, hb, h0]; simp, ?_⟩
      rw [ha, hb, h0]
      rcases hland with h | ⟨i, -, hi, hℓ⟩
      · exact Or.inl (by simpa using h)
      · exact Or.inr ⟨i, hi, by simpa using hℓ⟩
    · obtain ⟨t, ht, ha, hb, hland⟩ := hv.hZ1 e (List.mem_range.mpr hel) hnX
      refine ⟨t, ht, by rw [ha]; omega, Or.inl hland⟩

/-- **Corollary**: the outcome function of `D.moves K` is the designed pattern. -/
theorem outcome_eq_pat (hv : D.Valid) {K : ℕ} (hpos : ∀ s ∈ D.movesL K, 0 < s)
    (ℓ : Fin W → ℕ → Bool) (hN : D.NorEqns K ℓ) (hZ0 : D.Z0 ℓ) (n : ℕ) :
    outcome (D.movesL K) n = true ↔ D.Pat ℓ n :=
  outcome_iff_of_isPSet hpos (isPSet_pat hv ℓ hN hZ0) n

end Design
end SubGame
