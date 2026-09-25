import Sts.Simulation
import Sts.Bits
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-!
# A bit-serial binary counter built from NOR gates

Wires (indices): `0 boot`, `1 nm`, `2 marker`, `3 ncin`, `4 nb`, `5 g1`, `6 carry`, `7 u`.
Delays are written `(a, b)` meaning `a*K + b`; the register length is `k = K + 1`, so the long
delay `k` is `(1, 1)`.

* `boot = NOR(clock[-1])`            — `1` only in block `0`
* `nm   = NOR(boot, marker[-k])`
* `marker = NOR(nm)`                 — `1` exactly when `k ∣ τ`
* `ncin = NOR(carry[-1], marker)`    — negated carry-in
* `nb   = NOR(u[-k])`                — negated old bit
* `g1   = NOR(u[-k], carry[-1], marker)`
* `carry = NOR(nb, ncin)`            — `old bit ∧ carry-in`
* `u    = NOR(g1, carry)`            — `old bit ⊕ carry-in`

Writing `τ = w*k + i` (`i < k`), the word `w` stores the number `(w + 1) mod 2^k` in binary,
least significant bit first: `u` in block `τ` is bit `i` of `w + 1`.
-/

namespace SubGame
namespace Counter

/-- inputs of the eight wires -/
def inputs : Fin 8 → List (Option (Fin 8) × ℕ × ℕ)
  | 0 => [(none, 0, 1)]
  | 1 => [(some 0, 0, 0), (some 2, 1, 1)]
  | 2 => [(some 1, 0, 0)]
  | 3 => [(some 6, 0, 1), (some 2, 0, 0)]
  | 4 => [(some 7, 1, 1)]
  | 5 => [(some 7, 1, 1), (some 6, 0, 1), (some 2, 0, 0)]
  | 6 => [(some 4, 0, 0), (some 3, 0, 0)]
  | 7 => [(some 5, 0, 0), (some 6, 0, 0)]

/-- carry into bit `τ % k` of word `τ / k` -/
def cin (k τ : ℕ) : Bool := low (τ / k) (τ % k)

/-- closed-form logic values (register length `k = K + 1`) -/
def val (K : ℕ) : Fin 8 → ℕ → Bool
  | 0, τ => decide (τ = 0)
  | 1, τ => decide (τ % (K + 1) ≠ 0)
  | 2, τ => decide (τ % (K + 1) = 0)
  | 3, τ => !cin (K + 1) τ
  | 4, τ => !(τ / (K + 1)).testBit (τ % (K + 1))
  | 5, τ => !((τ / (K + 1)).testBit (τ % (K + 1)) || cin (K + 1) τ)
  | 6, τ => low (τ / (K + 1)) (τ % (K + 1) + 1)
  | 7, τ => (τ / (K + 1) + 1).testBit (τ % (K + 1))

theorem sub_k_div_mod {k τ : ℕ} (hk : 0 < k) (h : k ≤ τ) :
    (τ - k) / k + 1 = τ / k ∧ (τ - k) % k = τ % k := by
  obtain ⟨m, rfl⟩ : ∃ m, τ = m + k := ⟨τ - k, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_div_right _ hk, Nat.add_mod_right]
  exact ⟨rfl, rfl⟩

theorem pred_div_mod {k τ : ℕ} (hk : 0 < k) (hi : τ % k ≠ 0) :
    (τ - 1) / k = τ / k ∧ (τ - 1) % k = τ % k - 1 := by
  have h := Nat.div_add_mod τ k
  have hlt : τ % k < k := Nat.mod_lt _ hk
  have e : τ - 1 = k * (τ / k) + (τ % k - 1) := by omega
  constructor
  · rw [e, Nat.mul_add_div hk, Nat.div_eq_of_lt (show τ % k - 1 < k by omega), add_zero]
  · rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (show τ % k - 1 < k by omega)]

theorem div_zero_of_lt {k τ : ℕ} (h : τ < k) : τ / k = 0 := Nat.div_eq_of_lt h

theorem cin_zero_mod {k τ : ℕ} (hi : τ % k = 0) : cin k τ = true := by
  simp [cin, hi, low_zero]

/-- carry-in equals carry-out of the previous bit when not at a word boundary -/
theorem cin_of_pos {K τ : ℕ} (hi : τ % (K + 1) ≠ 0) :
    cin (K + 1) τ = val K 6 (τ - 1) := by
  obtain ⟨h1, h2⟩ := pred_div_mod (Nat.succ_pos K) hi
  show low (τ / (K + 1)) (τ % (K + 1)) = low ((τ - 1) / (K + 1)) ((τ - 1) % (K + 1) + 1)
  rw [h1, h2, show τ % (K + 1) - 1 + 1 = τ % (K + 1) by omega]

/-- the NOR equations hold for the closed-form values -/
theorem norEqns (K : ℕ) (j : Fin 8) (τ : ℕ) :
    val K j τ = true ↔ ∀ p ∈ inputs j, p.2.1 * K + p.2.2 ≤ τ →
      Design.srcVal (val K) p.1 (τ - (p.2.1 * K + p.2.2)) = false := by
  have hk : 0 < K + 1 := Nat.succ_pos K
  fin_cases j
  · -- boot
    simp [inputs, val, Design.srcVal]
  · -- nm
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Design.srcVal, val]
    simp only [zero_mul, zero_add, Nat.sub_zero, one_mul, decide_eq_true_eq, decide_eq_false_iff_not]
    constructor
    · intro h
      refine ⟨fun _ => by intro h0; rw [h0] at h; simp at h, fun hle => ?_⟩
      rw [(sub_k_div_mod hk (by omega)).2]; exact h
    · rintro ⟨h0, h1⟩
      intro hmod
      by_cases hle : K + 1 ≤ τ
      · have := h1 hle; rw [(sub_k_div_mod hk hle).2] at this; exact this hmod
      · have : τ = 0 := by
          have := Nat.mod_eq_of_lt (show τ < K + 1 by omega); omega
        exact h0 (Nat.zero_le _) this
  · -- marker
    simp [inputs, val, Design.srcVal]
  · -- ncin
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Design.srcVal, zero_mul, zero_add, Nat.sub_zero]
    by_cases hi : τ % (K + 1) = 0
    · simp [val, hi, cin_zero_mod hi]
    · have hτ : 1 ≤ τ := by
        rcases Nat.eq_zero_or_pos τ with h | h
        · simp [h] at hi
        · exact h
      show (!cin (K + 1) τ) = true ↔ (1 ≤ τ → val K 6 (τ - 1) = false) ∧ (0 ≤ τ → val K 2 τ = false)
      rw [cin_of_pos hi]
      have h2 : val K 2 τ = false := by simp [val, hi]
      rw [h2]
      cases val K 6 (τ - 1) <;> simp [hτ]
  · -- nb
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false, forall_eq, Design.srcVal, val,
      one_mul, Bool.not_eq_true']
    by_cases hle : K + 1 + 1 ≤ τ + 1
    · have hle' : K + 1 ≤ τ := by omega
      obtain ⟨h1, h2⟩ := sub_k_div_mod hk hle'
      constructor
      · intro h _; rw [h1, h2]; exact h
      · intro h; have := h (by omega); rw [h1, h2] at this; exact this
    · have hlt : τ < K + 1 := by omega
      rw [div_zero_of_lt hlt]
      simp only [Nat.zero_testBit, true_iff]
      intro h; omega
  · -- g1
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Design.srcVal, one_mul, zero_mul, zero_add, Nat.sub_zero]
    simp only [val]
    constructor
    · intro h
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at h
      obtain ⟨hb, hc⟩ := h
      refine ⟨fun hle => ?_, fun hτ => ?_, ?_⟩
      · obtain ⟨h1, h2⟩ := sub_k_div_mod hk (show K + 1 ≤ τ by omega)
        rw [h1, h2]; exact hb
      · by_cases hi : τ % (K + 1) = 0
        · rw [cin_zero_mod hi] at hc; exact absurd hc (by simp)
        · rw [cin_of_pos hi] at hc; simpa [val] using hc
      · by_cases hi : τ % (K + 1) = 0
        · rw [cin_zero_mod hi] at hc; exact absurd hc (by simp)
        · simp [hi]
    · rintro ⟨hb, hc, hm⟩
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff]
      have hi : τ % (K + 1) ≠ 0 := by simpa using hm
      refine ⟨?_, ?_⟩
      · by_cases hle : K + 1 ≤ τ
        · obtain ⟨h1, h2⟩ := sub_k_div_mod hk hle
          have := hb (by omega); rw [h1, h2] at this; exact this
        · rw [div_zero_of_lt (by omega)]; simp
      · have hτ : 1 ≤ τ := by
          rcases Nat.eq_zero_or_pos τ with h | h
          · simp [h] at hi
          · exact h
        rw [cin_of_pos hi]
        simpa [val] using hc hτ
  · -- carry
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Design.srcVal, zero_mul, zero_add, Nat.sub_zero, Nat.zero_le, true_implies]
    simp only [val, cin, low_succ, Bool.not_eq_false', Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_false]
  · -- u
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Design.srcVal, zero_mul, zero_add, Nat.sub_zero, Nat.zero_le, true_implies]
    simp only [val, cin, testBit_succ, low_succ]
    cases (τ / (K + 1)).testBit (τ % (K + 1)) <;> cases low (τ / (K + 1)) (τ % (K + 1)) <;> simp

end Counter
end SubGame
