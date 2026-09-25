import Sts.Design

/-!
# The least eventual period

For `k = K + 1 ≥ 2` the outcome sequence of the subtraction game `Concrete.D.movesL K` is
eventually periodic, and its least eventual period is exactly `B * k * 2^k`.
-/

namespace SubGame

/-- `p` is an eventual period of `f` -/
def IsEventualPeriod (f : ℕ → Bool) (p : ℕ) : Prop := 0 < p ∧ ∃ N, ∀ n ≥ N, f (n + p) = f n

theorem add_two_pow_mod {x i k : ℕ} (h : i ≤ k) : (x + 2 ^ k) % 2 ^ i = x % 2 ^ i := by
  obtain ⟨m, rfl⟩ : ∃ m, k = i + m := ⟨k - i, by omega⟩
  rw [pow_add, Nat.add_mul_mod_self_left]

theorem low_add_two_pow {x i k : ℕ} (h : i ≤ k) : low (x + 2 ^ k) i = low x i := by
  simp [low, add_two_pow_mod h]

theorem testBit_add_two_pow {x i k : ℕ} (h : i < k) : (x + 2 ^ k).testBit i = x.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  congr 2
  obtain ⟨m, rfl⟩ : ∃ m, k = i + (m + 1) := ⟨k - i - 1, by omega⟩
  rw [pow_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i), pow_succ]
  rw [show 2 ^ m * 2 = 2 * 2 ^ m by ring, Nat.add_mul_mod_self_left]

namespace Counter

/-- the logic values are periodic with period `k * 2^k` from block `1` on -/
theorem val_periodic (K : ℕ) (j : Fin 8) {τ : ℕ} (hτ : 1 ≤ τ) :
    val K j (τ + (K + 1) * 2 ^ (K + 1)) = val K j τ := by
  have hk : 0 < K + 1 := Nat.succ_pos K
  have hmod : (τ + (K + 1) * 2 ^ (K + 1)) % (K + 1) = τ % (K + 1) := Nat.add_mul_mod_self_left _ _ _
  have hdiv : (τ + (K + 1) * 2 ^ (K + 1)) / (K + 1) = τ / (K + 1) + 2 ^ (K + 1) :=
    Nat.add_mul_div_left _ _ hk
  have hi : τ % (K + 1) < K + 1 := Nat.mod_lt _ hk
  fin_cases j
  · show decide (τ + (K + 1) * 2 ^ (K + 1) = 0) = decide (τ = 0)
    have : τ ≠ 0 := by omega
    have : τ + (K + 1) * 2 ^ (K + 1) ≠ 0 := by omega
    simp [*]
  · show decide (_ ≠ 0) = decide (_ ≠ 0); rw [hmod]
  · show decide (_ = 0) = decide (_ = 0); rw [hmod]
  · show (!cin (K + 1) _) = !cin (K + 1) τ
    simp only [cin, hmod, hdiv, low_add_two_pow hi.le]
  · show (!(_ / (K + 1)).testBit (_ % (K + 1))) = !(τ / (K + 1)).testBit (τ % (K + 1))
    rw [hmod, hdiv, testBit_add_two_pow hi]
  · show (!((_ / (K + 1)).testBit (_ % (K + 1)) || cin (K + 1) _)) =
      !((τ / (K + 1)).testBit (τ % (K + 1)) || cin (K + 1) τ)
    simp only [cin, hmod, hdiv, testBit_add_two_pow hi, low_add_two_pow hi.le]
  · show low (_ / (K + 1)) (_ % (K + 1) + 1) = low (τ / (K + 1)) (τ % (K + 1) + 1)
    rw [hmod, hdiv, low_add_two_pow (by omega)]
  · show (_ / (K + 1) + 1).testBit (_ % (K + 1)) = (τ / (K + 1) + 1).testBit (τ % (K + 1))
    rw [hmod, hdiv, show τ / (K + 1) + 2 ^ (K + 1) + 1 = τ / (K + 1) + 1 + 2 ^ (K + 1) by ring,
      testBit_add_two_pow hi]

end Counter

namespace Concrete

open Design

theorem hB : 0 < D.B := by decide

set_option maxRecDepth 100000 in
/-- every nontrivial shift of the residues moves some clock onto a zero residue -/
theorem shift_breaks : ∀ d ∈ List.range D.B, d ≠ 0 →
    ∃ c ∈ D.clocks, ¬ D.IsX ((c + d) % D.B) := by
  decide +kernel

theorem pat_iff (K : ℕ) (τ e : ℕ) (he : e < D.B) :
    D.Pat (Counter.val K) (τ * D.B + e) ↔
      e ∈ D.clocks ∨ ∃ j, D.res j = e ∧ Counter.val K j τ = true := by
  unfold Design.Pat
  rw [mod_of_decomp he, div_of_decomp he]

/-- the period `B * k * 2^k` -/
def per (K : ℕ) : ℕ := D.B * ((K + 1) * 2 ^ (K + 1))

theorem outcome_periodic (K : ℕ) (hK : 1 ≤ K) (n : ℕ) (hn : D.B ≤ n) :
    outcome (D.movesL K) (n + per K) = outcome (D.movesL K) n := by
  have hB := hB
  obtain ⟨τ, e, hlt, rfl⟩ : ∃ τ e, e < D.B ∧ n = τ * D.B + e :=
    ⟨n / D.B, n % D.B, Nat.mod_lt _ hB, by rw [mul_comm]; exact (Nat.div_add_mod n D.B).symm⟩
  have hτ : 1 ≤ τ := by
    by_contra h
    have : τ = 0 := by omega
    subst this; omega
  have hsum : τ * D.B + e + per K = (τ + (K + 1) * 2 ^ (K + 1)) * D.B + e := by
    unfold per; ring
  apply Bool.eq_iff_iff.mpr
  rw [hsum, outcome_iff K hK, pat_iff K _ _ hlt, outcome_iff K hK, pat_iff K _ _ hlt]
  simp only [Counter.val_periodic K _ hτ]

theorem isEventualPeriod_per (K : ℕ) (hK : 1 ≤ K) :
    IsEventualPeriod (outcome (D.movesL K)) (per K) := by
  refine ⟨?_, D.B, fun n hn => outcome_periodic K hK n hn⟩
  unfold per
  have := hB
  positivity

/-- marker residue and value -/
theorem outcome_marker (K : ℕ) (hK : 1 ≤ K) (τ : ℕ) :
    outcome (D.movesL K) (τ * D.B + D.res 2) = decide (τ % (K + 1) = 0) := by
  have hlt : D.res 2 < D.B := by decide
  have hnc : D.res 2 ∉ D.clocks := by decide
  apply Bool.eq_iff_iff.mpr
  rw [outcome_iff K hK, pat_iff K _ _ hlt]
  constructor
  · rintro (h | ⟨j, hj, hv⟩)
    · exact absurd h hnc
    · have : j = 2 := by
        have hinj := valid.res_inj j (List.mem_finRange j) 2 (List.mem_finRange 2) hj
        exact hinj
      subst this; simpa [Counter.val] using hv
  · intro h; exact Or.inr ⟨2, rfl, by simpa [Counter.val] using h⟩

/-- `u` residue and value -/
theorem outcome_u (K : ℕ) (hK : 1 ≤ K) (τ : ℕ) :
    outcome (D.movesL K) (τ * D.B + D.res 7) =
      (τ / (K + 1) + 1).testBit (τ % (K + 1)) := by
  have hlt : D.res 7 < D.B := by decide
  have hnc : D.res 7 ∉ D.clocks := by decide
  apply Bool.eq_iff_iff.mpr
  rw [outcome_iff K hK, pat_iff K _ _ hlt]
  constructor
  · rintro (h | ⟨j, hj, hv⟩)
    · exact absurd h hnc
    · have : j = 7 := valid.res_inj j (List.mem_finRange j) 7 (List.mem_finRange 7) hj
      subst this; simpa [Counter.val] using hv
  · intro h; exact Or.inr ⟨7, rfl, by simpa [Counter.val] using h⟩

theorem outcome_clock (K : ℕ) (hK : 1 ≤ K) (τ c : ℕ) (hc : c ∈ D.clocks) :
    outcome (D.movesL K) (τ * D.B + c) = true := by
  have hlt : c < D.B := valid.clk_lt c hc
  rw [outcome_iff K hK, pat_iff K _ _ hlt]
  exact Or.inl hc

theorem outcome_zero (K : ℕ) (hK : 1 ≤ K) (τ r : ℕ) (hr : r < D.B) (hX : ¬ D.IsX r) :
    outcome (D.movesL K) (τ * D.B + r) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [outcome_iff K hK, pat_iff K _ _ hr] at h
  rcases h with h | ⟨j, hj, _⟩
  · exact hX (Or.inl h)
  · exact hX (Or.inr ⟨j, List.mem_finRange j, hj⟩)

/-- **Least period**: every eventual period is a multiple of `per K`. -/
theorem per_dvd (K : ℕ) (hK : 1 ≤ K) (p : ℕ) (hp : IsEventualPeriod (outcome (D.movesL K)) p) :
    per K ∣ p := by
  obtain ⟨hp0, N, hN⟩ := hp
  have hB := hB
  -- Step 1: `B ∣ p`
  have hBp : D.B ∣ p := by
    by_contra hnd
    have hd : p % D.B ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    obtain ⟨c, hc, hX⟩ := shift_breaks (p % D.B) (List.mem_range.mpr (Nat.mod_lt _ hB)) hd
    have hclt : c < D.B := valid.clk_lt c hc
    have hn : N ≤ (N + 1) * D.B + c := by nlinarith
    have e1 := outcome_clock K hK (N + 1) c hc
    have e2 := hN ((N + 1) * D.B + c) hn
    have h1 := Nat.div_add_mod p D.B
    have h2 := Nat.div_add_mod (c + p % D.B) D.B
    have hdec : (N + 1) * D.B + c + p =
        (N + 1 + p / D.B + (c + p % D.B) / D.B) * D.B + (c + p % D.B) % D.B := by
      have e3 : (N + 1 + p / D.B + (c + p % D.B) / D.B) * D.B =
          (N + 1) * D.B + D.B * (p / D.B) + D.B * ((c + p % D.B) / D.B) := by ring
      linarith
    rw [hdec, outcome_zero K hK _ _ (Nat.mod_lt _ hB) hX, e1] at e2
    exact Bool.false_ne_true e2
  obtain ⟨m, rfl⟩ := hBp
  -- periodicity of the outcome along blocks
  have hblock : ∀ τ e, N ≤ τ * D.B + e →
      outcome (D.movesL K) ((τ + m) * D.B + e) = outcome (D.movesL K) (τ * D.B + e) := by
    intro τ e hle
    have := hN (τ * D.B + e) hle
    rw [show (τ + m) * D.B + e = τ * D.B + e + D.B * m by ring]
    exact this
  -- Step 2: `k ∣ m`
  have hkm : (K + 1) ∣ m := by
    have hle : N ≤ ((K + 1) * (N + 1)) * D.B + D.res 2 := by
      have h1 : N + 1 ≤ (K + 1) * (N + 1) := Nat.le_mul_of_pos_left (N + 1) (Nat.succ_pos K)
      have h2 : (K + 1) * (N + 1) ≤ (K + 1) * (N + 1) * D.B := Nat.le_mul_of_pos_right _ hB
      omega
    have e := hblock ((K + 1) * (N + 1)) (D.res 2) hle
    rw [outcome_marker K hK, outcome_marker K hK] at e
    have hτ0 : (K + 1) * (N + 1) % (K + 1) = 0 := Nat.mul_mod_right _ _
    rw [hτ0] at e
    simp only [decide_true, decide_eq_true_eq] at e
    rw [Nat.add_mod, hτ0, zero_add, Nat.mod_mod] at e
    exact Nat.dvd_of_mod_eq_zero e
  obtain ⟨m', rfl⟩ := hkm
  -- Step 3: `2^k ∣ m'`
  have hk : 0 < K + 1 := Nat.succ_pos K
  have hbits : ∀ i < K + 1, (N + 1 + m' + 1).testBit i = (N + 1 + 1).testBit i := by
    intro i hi
    have hle : N ≤ ((N + 1) * (K + 1) + i) * D.B + D.res 7 := by
      have h1 : N + 1 ≤ (N + 1) * (K + 1) := Nat.le_mul_of_pos_right (N + 1) (Nat.succ_pos K)
      have h2 : (N + 1) * (K + 1) + i ≤ ((N + 1) * (K + 1) + i) * D.B := Nat.le_mul_of_pos_right _ hB
      omega
    have e := hblock ((N + 1) * (K + 1) + i) (D.res 7) hle
    rw [outcome_u K hK, outcome_u K hK] at e
    have hq1 : ((N + 1) * (K + 1) + i + (K + 1) * m') / (K + 1) = N + 1 + m' := by
      rw [show (N + 1) * (K + 1) + i + (K + 1) * m' = i + (K + 1) * (N + 1 + m') by ring,
        Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hi, zero_add]
    have hr1 : ((N + 1) * (K + 1) + i + (K + 1) * m') % (K + 1) = i := by
      rw [show (N + 1) * (K + 1) + i + (K + 1) * m' = i + (K + 1) * (N + 1 + m') by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    have hq2 : ((N + 1) * (K + 1) + i) / (K + 1) = N + 1 := by
      rw [show (N + 1) * (K + 1) + i = i + (K + 1) * (N + 1) by ring, Nat.add_mul_div_left _ _ hk,
        Nat.div_eq_of_lt hi, zero_add]
    have hr2 : ((N + 1) * (K + 1) + i) % (K + 1) = i := by
      rw [show (N + 1) * (K + 1) + i = i + (K + 1) * (N + 1) by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hi]
    rw [hq1, hr1, hq2, hr2] at e
    exact e
  have hmodeq : (N + 1 + m' + 1) % 2 ^ (K + 1) = (N + 1 + 1) % 2 ^ (K + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < K + 1
    · simp [hi, hbits i hi]
    · simp [hi]
  have hmod : m' % 2 ^ (K + 1) = 0 := by
    have h := Nat.sub_mod_eq_zero_of_mod_eq (show (N + 2 + m') % 2 ^ (K + 1) = (N + 2) % 2 ^ (K + 1) by
      rw [show N + 2 + m' = N + 1 + m' + 1 by ring, show N + 2 = N + 1 + 1 by ring]; exact hmodeq)
    rwa [show N + 2 + m' - (N + 2) = m' by omega] at h
  obtain ⟨m'', rfl⟩ := Nat.dvd_of_mod_eq_zero hmod
  exact ⟨m'', by unfold per; ring⟩

/-- **Main theorem.** For every `K ≥ 1` (register length `k = K + 1 ≥ 2`), the least eventual
period of the outcome sequence of the subtraction game `D.movesL K` is `B * k * 2^k`. -/
theorem least_period (K : ℕ) (hK : 1 ≤ K) :
    IsEventualPeriod (outcome (D.movesL K)) (per K) ∧
      ∀ p, IsEventualPeriod (outcome (D.movesL K)) p → per K ∣ p :=
  ⟨isEventualPeriod_per K hK, per_dvd K hK⟩

end Concrete
end SubGame
