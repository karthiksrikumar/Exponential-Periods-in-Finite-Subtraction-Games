import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Data.List.Basic

/-!
# Block arithmetic

Positions are written as `n = τ * B + e` with `e < B` (block `τ`, residue `e`).
A move `s = q * B + δ` with `δ < B` takes residue `e` of block `τ` to residue
`(e + B - δ) % B` of block `τ - q - [e < δ]`.
-/

namespace SubGame

/-- Effective block delay of a move `q*B+δ` applied at residue `e`. -/
def effDelay (q δ e : ℕ) : ℕ := q + if e < δ then 1 else 0

/-- Landing residue of a move with residue `δ` applied at residue `e`. -/
def landRes (B δ e : ℕ) : ℕ := (e + B - δ) % B

theorem landRes_lt {B δ e : ℕ} (hB : 0 < B) : landRes B δ e < B := Nat.mod_lt _ hB

/-- Main arithmetic lemma: `q*B+δ ≤ τ*B+e` iff the effective delay is at most `τ`, and in that
case the difference decomposes into block `τ - delay` and the landing residue. -/
theorem sub_decomp {B τ e q δ : ℕ} (he : e < B) (hδ : δ < B) :
    (q * B + δ ≤ τ * B + e ↔ effDelay q δ e ≤ τ) ∧
    (effDelay q δ e ≤ τ →
      τ * B + e - (q * B + δ) = (τ - effDelay q δ e) * B + landRes B δ e) := by
  unfold effDelay landRes
  by_cases h : e < δ
  · simp only [h, if_true]
    have hl : (e + B - δ) % B = e + B - δ := Nat.mod_eq_of_lt (by omega)
    rw [hl]
    constructor
    · constructor
      · intro hle
        by_contra hc
        push Not at hc
        have : τ ≤ q := by omega
        have : τ * B ≤ q * B := Nat.mul_le_mul_right B this
        omega
      · intro hle
        obtain ⟨m, rfl⟩ : ∃ m, τ = q + 1 + m := ⟨τ - (q + 1), by omega⟩
        have : (q + 1 + m) * B = q * B + B + m * B := by ring
        omega
    · intro hle
      obtain ⟨m, rfl⟩ : ∃ m, τ = q + 1 + m := ⟨τ - (q + 1), by omega⟩
      have h1 : (q + 1 + m) * B = q * B + B + m * B := by ring
      have h2 : q + 1 + m - (q + 1) = m := by omega
      rw [h2, h1]
      omega
  · simp only [h, if_false, add_zero]
    push Not at h
    have hl : (e + B - δ) % B = e - δ := by
      rw [show e + B - δ = (e - δ) + B by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hl]
    constructor
    · constructor
      · intro hle
        by_contra hc
        push Not at hc
        have : τ + 1 ≤ q := by omega
        have : (τ + 1) * B ≤ q * B := Nat.mul_le_mul_right B this
        have : (τ + 1) * B = τ * B + B := by ring
        omega
      · intro hle
        obtain ⟨m, rfl⟩ : ∃ m, τ = q + m := ⟨τ - q, by omega⟩
        have : (q + m) * B = q * B + m * B := by ring
        omega
    · intro hle
      obtain ⟨m, rfl⟩ : ∃ m, τ = q + m := ⟨τ - q, by omega⟩
      have h1 : (q + m) * B = q * B + m * B := by ring
      have h2 : q + m - q = m := by omega
      rw [h2, h1]
      omega

theorem div_of_decomp {B τ e : ℕ} (he : e < B) : (τ * B + e) / B = τ := by
  have hB : 0 < B := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt he, zero_add]

theorem mod_of_decomp {B τ e : ℕ} (he : e < B) : (τ * B + e) % B = e := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]

end SubGame
