import Sts.Layout
import Mathlib.Data.Fintype.EquivFin

/-!
# The General Layout Lemma for arbitrary finite wire types

`GLL.simulate` is stated for wires indexed by `Fin W`.  Here we transport it along an
equivalence `α ≃ Fin (card α)`, so that circuits can use any finite type of wire names.
The resulting list of taps does not depend on the size parameter `K`.
-/

namespace SubGame
namespace GLL

variable {α : Type} [Fintype α]

/-- residue of an input source (the clock is read at residue `5`) -/
def srcResA (y : α → ℕ) : Option α → ℕ
  | none => 5
  | some i => 13 * y i

/-- hypotheses on the coarse positions -/
structure HypYA (y : α → ℕ) (Bp : ℕ) : Prop where
  inj : Function.Injective y
  ne1 : ∀ j, y j ≠ 1
  big : ∀ j, 3 * y j + 3 ≤ Bp
  sidon : ∀ a b c d : α, y a + y b = y c + y d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- hypotheses on the circuit -/
structure HypCA (y : α → ℕ) (inp : α → List (Option α × ℕ × ℕ)) : Prop where
  boot : ∃ j, y j = 0 ∧ inp j = [(none, 0, 1)]
  noself : ∀ j, ∀ p ∈ inp j, p.1 ≠ some j
  back : ∀ j, ∀ p ∈ inp j, 13 * y j ≤ srcResA y p.1 → 1 ≤ p.2.2

/-- value of an input source (the clock is always `true`) -/
def srcValA (ℓ : α → ℕ → Bool) : Option α → ℕ → Bool
  | none, _ => true
  | some j, τ => ℓ j τ

/-- NOR equations of a circuit with wire type `α` -/
def NorEqnsA (inp : α → List (Option α × ℕ × ℕ)) (K : ℕ) (ℓ : α → ℕ → Bool) : Prop :=
  ∀ j τ, ℓ j τ = true ↔
    ∀ p ∈ inp j, p.2.1 * K + p.2.2 ≤ τ → srcValA ℓ p.1 (τ - (p.2.1 * K + p.2.2)) = false

/-- the moves of a list of taps -/
def movesOf (B : ℕ) (taps : List (ℕ × ℕ × ℕ)) (K : ℕ) : List ℕ :=
  taps.map fun t => (t.1 * K + t.2.1) * B + t.2.2

/-- **General Layout Lemma, any finite wire type.**  There is a list of taps, independent of
`K`, such that for every `K` and every solution `ℓ` of the NOR equations the P-positions of the
subtraction game are the clocks `1, 5, 12` and the wire positions carrying `true`. -/
theorem simulateA (y : α → ℕ) (Bp : ℕ) (inp : α → List (Option α × ℕ × ℕ))
    (hY : HypYA y Bp) (hC : HypCA y inp) :
    ∃ taps : List (ℕ × ℕ × ℕ), ∀ (K : ℕ) (ℓ : α → ℕ → Bool), NorEqnsA inp K ℓ → ∀ n,
      (outcome (movesOf (13 * Bp) taps K) n = true ↔
        (n % (13 * Bp) = 1 ∨ n % (13 * Bp) = 5 ∨ n % (13 * Bp) = 12 ∨
          ∃ j, 13 * y j = n % (13 * Bp) ∧ ℓ j (n / (13 * Bp)) = true)) := by
  classical
  set e := Fintype.equivFin α with he
  set y' : Fin (Fintype.card α) → ℕ := fun j => y (e.symm j) with hy'
  set inp' : Fin (Fintype.card α) → List (Option (Fin (Fintype.card α)) × ℕ × ℕ) :=
    fun j => (inp (e.symm j)).map (fun p => (p.1.map e, p.2)) with hinp'
  have hsrc : ∀ o : Option α, srcRes y' (o.map e) = srcResA y o := by
    intro o; cases o <;> simp [srcRes, srcResA, hy']
  have hY' : HypY y' Bp :=
    { inj := fun a b h => e.symm.injective (hY.inj h)
      ne1 := fun j => hY.ne1 _
      big := fun j => hY.big _
      sidon := by
        intro a b c d h
        rcases hY.sidon _ _ _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨e.symm.injective h1, e.symm.injective h2⟩
        · exact Or.inr ⟨e.symm.injective h1, e.symm.injective h2⟩ }
  have hC' : HypC y' inp' :=
    { boot := by
        obtain ⟨j, hj0, hjinp⟩ := hC.boot
        exact ⟨e j, by simp [hy', hj0], by simp [hinp', hjinp]⟩
      noself := by
        intro j p hp
        simp only [hinp', List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        intro h
        have h2 := hC.noself (e.symm j) q hq
        apply h2
        cases hq1 : q.1 with
        | none => rw [hq1] at h; simp at h
        | some i =>
          rw [hq1] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]; simp
      back := by
        intro j p hp hle
        simp only [hinp', List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        rw [hsrc] at hle
        exact hC.back (e.symm j) q hq (by simpa [hy'] using hle) }
  refine ⟨(design y' Bp inp').taps, fun K ℓ hN n => ?_⟩
  set ℓ' : Fin (Fintype.card α) → ℕ → Bool := fun j τ => ℓ (e.symm j) τ with hℓ'
  have hsv : ∀ (o : Option α) τ, Design.srcVal ℓ' (o.map e) τ = srcValA ℓ o τ := by
    intro o τ; cases o <;> simp [Design.srcVal, srcValA, hℓ']
  have hN' : (design y' Bp inp').NorEqns K ℓ' := by
    intro j τ
    show ℓ (e.symm j) τ = true ↔ ∀ p ∈ inp' j, _
    rw [hN (e.symm j) τ]
    simp only [hinp', List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro h q hq hle
      rw [hsv]; exact h q hq hle
    · intro h q hq hle
      have := h q hq hle
      rwa [hsv] at this
  have key := simulate hY' hC' ℓ' hN' n
  have hmv : (design y' Bp inp').movesL K = movesOf (13 * Bp) (design y' Bp inp').taps K := rfl
  rw [← hmv, key]
  unfold Design.Pat
  simp only [design, List.mem_cons, List.not_mem_nil, or_false, hy', hℓ', or_assoc]
  apply or_congr_right; apply or_congr_right; apply or_congr_right
  constructor
  · rintro ⟨j, hj, hl⟩; exact ⟨e.symm j, hj, hl⟩
  · rintro ⟨j, hj, hl⟩; exact ⟨e j, by simpa using hj, by simpa using hl⟩

theorem movesOf_length (B : ℕ) (taps : List (ℕ × ℕ × ℕ)) (K : ℕ) :
    (movesOf B taps K).length = taps.length := by simp [movesOf]

end GLL
end SubGame
