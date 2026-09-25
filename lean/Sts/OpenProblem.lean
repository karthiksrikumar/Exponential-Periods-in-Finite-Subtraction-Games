import Sts.Exact
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Guy's conjecture for `n` moves, and the open gap `3 ≤ n ≤ 25`

For every number of moves `n` we define

* `SuperPolyPeriods n`: the periods of `n`-move subtraction games are **not** bounded by any
  polynomial in the largest move;
* `GuyBound n`: Guy's conjectured bound — every `n`-move game has an eventual period at most
  `C * (max S) ^ (n choose 2)`, for one constant `C`.

We prove `SuperPolyPeriods n`, hence `¬ GuyBound n`, for **every** `n ≥ 26`: take the 26-move game
of `Exact.lean` and add `n - 26` harmless moves `q * 260 + 74` (they never lead from a P-position to
a P-position, so the outcome sequence does not change).

What remains is stated formally as `OpenGap`: is there `n` with `3 ≤ n ≤ 25` for which
`SuperPolyPeriods n` holds?  (For `n ≤ 2` the periods are at most `2 max S`; this classical fact is
not formalised here.)
-/

namespace SubGame

/-- the largest element of a list of moves -/
def maxL (L : List ℕ) : ℕ := L.foldr max 0

/-- `n`-move subtraction games have super-polynomial periods -/
def SuperPolyPeriods (n : ℕ) : Prop :=
  ∀ C d : ℕ, ∃ L : List ℕ, L.Nodup ∧ L.length = n ∧ (∀ s ∈ L, 0 < s) ∧
    ∀ p, IsEventualPeriod (outcome L) p → C * maxL L ^ d < p

/-- **Guy's conjecture** for `n`-move games: periods are bounded by a polynomial of degree
`n choose 2` in the largest move -/
def GuyBound (n : ℕ) : Prop :=
  ∃ C : ℕ, ∀ L : List ℕ, L.Nodup → L.length = n → (∀ s ∈ L, 0 < s) →
    ∃ p, IsEventualPeriod (outcome L) p ∧ p ≤ C * maxL L ^ n.choose 2

theorem not_guyBound_of_superPoly {n : ℕ} (h : SuperPolyPeriods n) : ¬ GuyBound n := by
  rintro ⟨C, hC⟩
  obtain ⟨L, hnd, hlen, hpos, hp⟩ := h C (n.choose 2)
  obtain ⟨p, hper, hle⟩ := hC L hnd hlen hpos
  have := hp p hper
  omega

/-- **Open problem.**  Is there a number of moves `n` with `3 ≤ n ≤ 25` for which the periods of
`n`-move subtraction games are not polynomially bounded?  (We prove it for all `n ≥ 26`.) -/
def OpenGap : Prop := ∃ n, 3 ≤ n ∧ n ≤ 25 ∧ SuperPolyPeriods n

namespace Concrete

open Design

/-! ## Harmless extra moves -/

/-- `r` extra moves `260, 520, … ` shifted by `74` -/
def extra (r : ℕ) : List ℕ := (List.range r).map fun i => (i + 1) * 260 + 74

/-- a move `≡ 74 (mod 260)` never leads from a clock or wire residue to a clock or wire residue -/
theorem land74 : ∀ e ∈ List.range 260, D.IsX e → ¬ D.IsX (landRes 260 74 e) := by decide +kernel

theorem taps_ne74 : ∀ t ∈ D.taps, t.2.2 ≠ 74 := by decide

theorem pat_isX (K τ l : ℕ) (hl : l < 260) (h : D.Pat (Counter.val K) (τ * 260 + l)) : D.IsX l := by
  have h' := (pat_decomp valid (Counter.val K) (τ := τ) (l := l) (by rw [B_eq]; exact hl)).mp
    (by rw [B_eq]; exact h)
  rcases h' with h1 | ⟨j, hj, _⟩
  · exact Or.inl h1
  · exact Or.inr ⟨j, List.mem_finRange j, hj⟩

/-- the extra moves never lead from a P-position to a P-position -/
theorem extra_safe (K r m : ℕ) (hP : D.Pat (Counter.val K) m) (s : ℕ) (hs : s ∈ extra r)
    (hsm : s ≤ m) : ¬ D.Pat (Counter.val K) (m - s) := by
  simp only [extra, List.mem_map, List.mem_range] at hs
  obtain ⟨i, _, rfl⟩ := hs
  have he : m % 260 < 260 := Nat.mod_lt _ (by norm_num)
  have hm : m = m / 260 * 260 + m % 260 := by
    have := Nat.div_add_mod m 260; rw [mul_comm] at this; omega
  have hX : D.IsX (m % 260) := by
    apply pat_isX K (m / 260) (m % 260) he
    rw [← hm]; exact hP
  have hdec := sub_decomp (B := 260) (τ := m / 260) (e := m % 260) (q := i + 1) (δ := 74) he
    (by norm_num)
  intro hP'
  have hsm' : (i + 1) * 260 + 74 ≤ m / 260 * 260 + m % 260 := by rw [← hm]; exact hsm
  have hle := hdec.1.mp hsm'
  have e2 := hdec.2 hle
  rw [← hm] at e2
  rw [e2] at hP'
  have hl : landRes 260 74 (m % 260) < 260 := landRes_lt (by norm_num)
  exact land74 (m % 260) (List.mem_range.mpr he) hX (pat_isX K _ _ hl hP')

theorem pos_pad (K r : ℕ) (hK : 1 ≤ K) : ∀ s ∈ D.movesL K ++ extra r, 0 < s := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact moves_pos K hK s h
  · simp only [extra, List.mem_map] at h
    obtain ⟨i, _, rfl⟩ := h
    omega

/-- the P-positions do not change when the extra moves are added -/
theorem isPSet_pad (K r : ℕ) (hK : 1 ≤ K) :
    IsPSet (D.movesL K ++ extra r).toFinset (D.Pat (Counter.val K)) := by
  intro m
  have hb := isPSet_pat valid (Counter.val K) (Counter.norEqns K) (z0 K) m
  simp only [Design.moves, List.mem_toFinset] at hb
  simp only [List.mem_toFinset, List.mem_append]
  constructor
  · intro hP s hs hsm
    rcases hs with hs | hs
    · exact (hb.mp hP) s hs hsm
    · exact extra_safe K r m hP s hs hsm
  · intro h
    exact hb.mpr (fun s hs hsm => h s (Or.inl hs) hsm)

theorem outcome_pad (K r : ℕ) (hK : 1 ≤ K) (m : ℕ) :
    outcome (D.movesL K ++ extra r) m = outcome (D.movesL K) m := by
  have h1 : outcome (D.movesL K ++ extra r) m = true ↔ D.Pat (Counter.val K) m :=
    outcome_iff_of_isPSet (pos_pad K r hK) (isPSet_pad K r hK) m
  have h2 := outcome_iff K hK m
  cases h : outcome (D.movesL K ++ extra r) m <;> cases h' : outcome (D.movesL K) m <;> simp_all

/-! ## Lists, lengths, maxima -/

theorem foldr_max_le (l : List ℕ) (M : ℕ) (h : ∀ s ∈ l, s ≤ M) : l.foldr max 0 ≤ M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih (fun s hs => h s (by simp [hs])))

theorem nodup_pad (K r : ℕ) : (D.movesL K ++ extra r).Nodup := by
  refine List.Nodup.append (movesL_nodup K) ?_ ?_
  · exact (List.nodup_range).map (fun a b h => by omega)
  · intro x hx hy
    simp only [extra, List.mem_map, List.mem_range] at hy
    obtain ⟨i, _, rfl⟩ := hy
    simp only [Design.movesL, List.mem_map] at hx
    obtain ⟨t, ht, e⟩ := hx
    have hmod := congrArg (· % 260) e
    simp only [B_eq] at hmod
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (tap_lt_B t ht)] at hmod
    have : ((i + 1) * 260 + 74) % 260 = 74 := by omega
    rw [this] at hmod
    exact taps_ne74 t ht hmod

theorem length_pad (K r : ℕ) : (D.movesL K ++ extra r).length = 26 + r := by
  simp [Design.movesL, D, extra] <;> omega

theorem maxL_pad (K r : ℕ) (hK : 1 ≤ K) (hr : r ≤ K) : maxL (D.movesL K ++ extra r) = maxMove K := by
  apply le_antisymm
  · apply foldr_max_le
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact le_maxMove K s h
    · simp only [extra, List.mem_map, List.mem_range] at h
      obtain ⟨i, hi, rfl⟩ := h
      clear hs
      rw [maxMove_eq K hK]
      have h1 : i + 1 ≤ K := by omega
      have h2 : (i + 1) * 260 ≤ K * 260 := Nat.mul_le_mul_right _ h1
      calc (i + 1) * 260 + 74 ≤ K * 260 + 74 := Nat.add_le_add_right h2 74
        _ ≤ K * 260 + 244 := Nat.add_le_add_left (by norm_num) _
  · show (D.movesL K).foldr max 0 ≤ (D.movesL K ++ extra r).foldr max 0
    apply foldr_max_le
    intro s hs
    exact le_foldr_max _ s (List.mem_append.mpr (Or.inl hs))

/-! ## Exponentials beat polynomials, with a large witness -/

theorem exists_poly_lt_exp_ge (A d m : ℕ) : ∃ n ≥ m, A * n ^ d < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt d (r := (2 : ℝ)) (by norm_num)
  have hA : (0 : ℝ) < 1 / ((A : ℝ) + 1) := by positivity
  have hev := (h.eventually (gt_mem_nhds hA))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max N m, le_max_right _ _, ?_⟩
  have hn := hN (max N m) (le_max_left _ _)
  set n := max N m
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at hn
  have : (A : ℝ) * (n : ℝ) ^ d < 2 ^ n := by
    have hnd : (0 : ℝ) ≤ (n : ℝ) ^ d := by positivity
    nlinarith
  exact_mod_cast this

theorem not_poly_bounded_ge (C d r : ℕ) :
    ∃ K ≥ r + 1, ∀ M, M < (K + 2) * 260 → C * M ^ d < 260 * ((K + 1) * 2 ^ (K + 1)) := by
  obtain ⟨n, hn3, hn⟩ := exists_poly_lt_exp_ge (2 * C * 260 ^ d) d (r + 3)
  refine ⟨n - 2, by omega, fun M hM => ?_⟩
  have hK2 : n - 2 + 2 = n := by omega
  have hK1 : n - 2 + 1 + 1 = n := by omega
  rw [hK2] at hM
  have hMd : M ^ d ≤ (n * 260) ^ d := Nat.pow_le_pow_left hM.le d
  have hpow : (n * 260) ^ d = n ^ d * 260 ^ d := Nat.mul_pow n 260 d
  have hper : 2 ^ n = 2 * 2 ^ (n - 2 + 1) := by
    rw [← pow_succ', hK1]
  have step1 : C * M ^ d ≤ C * 260 ^ d * n ^ d := by
    calc C * M ^ d ≤ C * (n ^ d * 260 ^ d) := Nat.mul_le_mul_left C (hpow ▸ hMd)
      _ = C * 260 ^ d * n ^ d := by ring
  have step2 : C * 260 ^ d * n ^ d < 2 ^ (n - 2 + 1) := by
    have : 2 * (C * 260 ^ d * n ^ d) < 2 * 2 ^ (n - 2 + 1) := by
      rw [← hper]; calc 2 * (C * 260 ^ d * n ^ d) = 2 * C * 260 ^ d * n ^ d := by ring
        _ < 2 ^ n := hn
    omega
  have step3 : 2 ^ (n - 2 + 1) ≤ 260 * ((n - 2 + 1) * 2 ^ (n - 2 + 1)) := by
    have : 1 ≤ 260 * (n - 2 + 1) := by omega
    calc 2 ^ (n - 2 + 1) = 1 * 2 ^ (n - 2 + 1) := (one_mul _).symm
      _ ≤ (260 * (n - 2 + 1)) * 2 ^ (n - 2 + 1) := Nat.mul_le_mul_right _ this
      _ = 260 * ((n - 2 + 1) * 2 ^ (n - 2 + 1)) := by ring
  omega

end Concrete

open Concrete

/-- **Super-polynomial periods for every `n ≥ 26` moves (formal).** -/
theorem superPoly_of_ge {n : ℕ} (hn : 26 ≤ n) : SuperPolyPeriods n := by
  intro C d
  obtain ⟨K, hK, hbound⟩ := not_poly_bounded_ge C d (n - 26)
  have hK1 : 1 ≤ K := by omega
  refine ⟨D.movesL K ++ extra (n - 26), nodup_pad K _, by rw [length_pad]; omega, pos_pad K _ hK1,
    fun p hp => ?_⟩
  have hfun : outcome (D.movesL K ++ extra (n - 26)) = outcome (D.movesL K) :=
    funext (outcome_pad K _ hK1)
  rw [hfun] at hp
  have hdvd := per_dvd K hK1 p hp
  have hple : per K ≤ p := Nat.le_of_dvd hp.1 hdvd
  rw [maxL_pad K _ hK1 (by omega)]
  have := hbound (maxMove K) (maxMove_lt K)
  have hper : per K = 260 * ((K + 1) * 2 ^ (K + 1)) := by unfold per; rw [B_eq]
  omega

/-- **Guy's conjecture fails for every `n ≥ 26` (formal).** -/
theorem guy_false_of_ge {n : ℕ} (hn : 26 ≤ n) : ¬ GuyBound n :=
  not_guyBound_of_superPoly (superPoly_of_ge hn)

end SubGame

#print axioms SubGame.superPoly_of_ge
#print axioms SubGame.guy_false_of_ge
