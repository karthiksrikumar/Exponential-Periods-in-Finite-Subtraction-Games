import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Binary increment lemmas

`low w i` : the lowest `i` bits of `w` are all `1` (i.e. `w % 2^i = 2^i - 1`).
Adding `1` to `w` flips bit `i` exactly when `low w i` holds, and the carry out of bit `i`
is `low w (i+1)`.
-/

namespace SubGame

/-- the lowest `i` bits of `w` are all ones -/
def low (w i : ℕ) : Bool := decide (w % 2 ^ i = 2 ^ i - 1)

theorem mod_two_pow_succ (w i : ℕ) :
    w % 2 ^ (i + 1) = w % 2 ^ i + 2 ^ i * (w / 2 ^ i % 2) := by
  rw [pow_succ, Nat.mod_mul]

theorem testBit_iff_div (w i : ℕ) : w.testBit i = true ↔ w / 2 ^ i % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp

theorem low_zero (w : ℕ) : low w 0 = true := by
  simp [low, Nat.mod_one]

/-- carry out of bit `i` = bit `i` AND carry into bit `i` -/
theorem low_succ (w i : ℕ) : low w (i + 1) = (w.testBit i && low w i) := by
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have hlt : w % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpos
  have hb : w / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have e := mod_two_pow_succ w i
  have p2 : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
  unfold low
  by_cases hbit : w / 2 ^ i % 2 = 1
  · have ht : w.testBit i = true := (testBit_iff_div w i).mpr hbit
    rw [ht, e, hbit, p2]
    simp only [Bool.true_and]
    congr 1
    apply propext
    constructor <;> intro h <;> omega
  · have hbit0 : w / 2 ^ i % 2 = 0 := by omega
    have ht : w.testBit i = false := by
      rw [Bool.eq_false_iff]; intro h; exact hbit ((testBit_iff_div w i).mp h)
    rw [ht, e, hbit0, p2]
    simp only [Bool.false_and, mul_zero, add_zero, decide_eq_false_iff_not]
    omega

/-- bit `i` of `w + 1` -/
theorem testBit_succ (w i : ℕ) : (w + 1).testBit i = (w.testBit i ^^ low w i) := by
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have hlt : w % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpos
  have hw := Nat.div_add_mod w (2 ^ i)
  -- (w+1) / 2^i
  by_cases hl : w % 2 ^ i = 2 ^ i - 1
  · have hdiv : (w + 1) / 2 ^ i = w / 2 ^ i + 1 := by
      have : w + 1 = (w / 2 ^ i + 1) * 2 ^ i := by
        have : w + 1 = 2 ^ i * (w / 2 ^ i) + 2 ^ i := by omega
        rw [this]; ring
      rw [this, Nat.mul_div_cancel _ hpos]
    have hlow : low w i = true := by simp [low, hl]
    rw [hlow]
    have h1 : (w + 1).testBit i = decide ((w / 2 ^ i + 1) % 2 = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
    have h2 : w.testBit i = decide (w / 2 ^ i % 2 = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
    rw [h1, h2]
    rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ i) with h | h
    · have : (w / 2 ^ i + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (w / 2 ^ i + 1) % 2 = 0 := by omega
      simp [h, this]
  · have hdiv : (w + 1) / 2 ^ i = w / 2 ^ i := by
      have hlt2 : w % 2 ^ i + 1 < 2 ^ i := by omega
      have : w + 1 = 2 ^ i * (w / 2 ^ i) + (w % 2 ^ i + 1) := by omega
      rw [this, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt2, add_zero]
    have hlow : low w i = false := by simp [low, hl]
    rw [hlow, Bool.xor_false]
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hdiv]

end SubGame
