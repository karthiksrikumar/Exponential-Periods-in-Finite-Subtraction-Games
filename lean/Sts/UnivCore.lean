import Sts.Transport
import Sts.Counter
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-!
# A universal circuit with a fixed number of wires

For a cellular automaton `F` with `b`-bit states we build one NOR circuit `U_F` whose wire set
and input lists do not depend on the ring length.  Block `τ = t * L + i` (`L = K + 2`) is cell `i`
of round `t`; rounds are grouped into runs of `2^L` rounds.  At the start of run `j` an input
counter supplies the configuration whose cell `i` carries bit `i` of `j + 1`; during the run the
circuit applies `F` once per round (null boundary).  This file defines the circuit and proves that
the intended closed-form values satisfy its NOR equations.
-/

namespace SubGame
namespace Univ

open GLL

/-! ## Cellular automata -/

/-- a `b`-bit cellular automaton with null boundary: local rule, initialisation map
(input bit, first cell?, last cell?) and boundary state -/
structure CA (b : ℕ) where
  rule : (Fin b → Bool) → (Fin b → Bool) → (Fin b → Bool) → (Fin b → Bool)
  init : Bool → Bool → Bool → (Fin b → Bool)
  bnd : Fin b → Bool

variable {b : ℕ}

/-- the state of cell `i` after `T` steps on a ring of length `L`, started from input `X` -/
def CA.run (F : CA b) (L X : ℕ) : ℕ → ℕ → (Fin b → Bool)
  | 0, i => F.init (X.testBit i) (decide (i = 0)) (decide (i + 1 = L))
  | T + 1, i => F.rule (if i = 0 then F.bnd else F.run L X T (i - 1)) (F.run L X T i)
      (if i + 1 = L then F.bnd else F.run L X T (i + 1))

/-! ## Wires -/

/-- framing, timer, run-start and input-counter wires -/
inductive Fx
  | boot | nm | mk | nlc | lc | tncin | tnb | tg1 | tcarry | tu | novf | inj | hold | nrs | rs
  | xnc | xc2 | xncin | xnb | xg1 | xcarry | xu | nxu
  deriving DecidableEq

instance : Fintype Fx where
  elems := {.boot, .nm, .mk, .nlc, .lc, .tncin, .tnb, .tg1, .tcarry, .tu, .novf, .inj, .hold, .nrs,
    .rs, .xnc, .xc2, .xncin, .xnb, .xg1, .xcarry, .xu, .nxu}
  complete := by intro x; cases x <;> simp

/-- literal wires of one state bit -/
inductive Lk | nc | nl | nlm | lm | nlmm | nr | nrm | rm | nrmm
  deriving DecidableEq

instance : Fintype Lk where
  elems := {.nc, .nl, .nlm, .lm, .nlmm, .nr, .nrm, .rm, .nrmm}
  complete := by intro x; cases x <;> simp

/-- the wires of `U_F` -/
inductive UW (b : ℕ)
  | fx : Fx → UW b
  | lit : Fin b → Lk → UW b
  | mt : (Fin 3 → Fin b → Bool) → UW b
  | nF : Fin b → UW b
  | t2 : Fin b → UW b
  | it : Fin b → Bool → Bool → Bool → UW b
  | ns : Fin b → UW b
  | s : Fin b → UW b

/-- encoding into a sum type (for the `Fintype` instance) -/
def UW.toSum : UW b → Fx ⊕ (Fin b × Lk) ⊕ (Fin 3 → Fin b → Bool) ⊕ Fin b ⊕ Fin b ⊕
    (Fin b × Bool × Bool × Bool) ⊕ Fin b ⊕ Fin b
  | .fx w => Sum.inl w
  | .lit q k => Sum.inr (Sum.inl (q, k))
  | .mt p => Sum.inr (Sum.inr (Sum.inl p))
  | .nF q => Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))
  | .t2 q => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))
  | .it q v f l => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (q, v, f, l))))))
  | .ns q => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))))
  | .s q => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr q))))))

theorem UW.toSum_injective : Function.Injective (UW.toSum (b := b)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [UW.toSum]

noncomputable instance : Fintype (UW b) := Fintype.ofInjective UW.toSum UW.toSum_injective

/-- all patterns of three neighbour states -/
noncomputable def allPats (b : ℕ) : List (Fin 3 → Fin b → Bool) :=
  (Finset.univ : Finset (Fin 3 → Fin b → Bool)).toList

theorem mem_allPats (p : Fin 3 → Fin b → Bool) : p ∈ allPats b := by simp [allPats]

/-- all triples (input bit, first, last) -/
def vfl : List (Bool × Bool × Bool) :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
   (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

theorem mem_vfl (x : Bool × Bool × Bool) : x ∈ vfl := by
  rcases x with ⟨v, f, l⟩; cases v <;> cases f <;> cases l <;> decide

/-- complemented literal inputs of a minterm (left, centre, right neighbour) -/
def litL (q : Fin b) (pb : Bool) : Option (UW b) × ℕ × ℕ :=
  (some (if pb then .lit q .nlmm else .lit q .lm), 0, 0)
def litC (q : Fin b) (pb : Bool) : Option (UW b) × ℕ × ℕ :=
  if pb then (some (.lit q .nc), 0, 0) else (some (.s q), 1, 2)
def litR (q : Fin b) (pb : Bool) : Option (UW b) × ℕ × ℕ :=
  (some (if pb then .lit q .nrmm else .lit q .rm), 0, 0)

/-- inputs `(source, a, c)` (delay `a * K + c`; ring length `L = K + 2`) -/
noncomputable def inp (F : CA b) : UW b → List (Option (UW b) × ℕ × ℕ)
  | .fx .boot => [(none, 0, 1)]
  | .fx .nm => [(some (.fx .boot), 0, 0), (some (.fx .mk), 1, 2)]
  | .fx .mk => [(some (.fx .nm), 0, 0)]
  | .fx .nlc => [(some (.fx .mk), 1, 1)]
  | .fx .lc => [(some (.fx .nlc), 0, 0)]
  | .fx .tncin => [(some (.fx .tcarry), 0, 1), (some (.fx .mk), 0, 0)]
  | .fx .tnb => [(some (.fx .tu), 1, 2)]
  | .fx .tg1 => [(some (.fx .tu), 1, 2), (some (.fx .tcarry), 0, 1), (some (.fx .mk), 0, 0)]
  | .fx .tcarry => [(some (.fx .tnb), 0, 0), (some (.fx .tncin), 0, 0)]
  | .fx .tu => [(some (.fx .tg1), 0, 0), (some (.fx .tcarry), 0, 0)]
  | .fx .novf => [(some (.fx .boot), 0, 0), (some (.fx .tcarry), 0, 1)]
  | .fx .inj => [(some (.fx .nm), 0, 0), (some (.fx .novf), 0, 0)]
  | .fx .hold => [(some (.fx .mk), 0, 0), (some (.fx .nrs), 0, 1)]
  | .fx .nrs => [(some (.fx .inj), 0, 0), (some (.fx .hold), 0, 0)]
  | .fx .rs => [(some (.fx .nrs), 0, 0)]
  | .fx .xnc => [(some (.fx .xcarry), 0, 1)]
  | .fx .xc2 => [(some (.fx .mk), 0, 0), (some (.fx .xnc), 0, 0)]
  | .fx .xncin => [(some (.fx .inj), 0, 0), (some (.fx .xc2), 0, 0)]
  | .fx .xnb => [(some (.fx .xu), 1, 2)]
  | .fx .xg1 => [(some (.fx .xu), 1, 2), (some (.fx .inj), 0, 0), (some (.fx .xc2), 0, 0)]
  | .fx .xcarry => [(some (.fx .xnb), 0, 0), (some (.fx .xncin), 0, 0)]
  | .fx .xu => [(some (.fx .xg1), 0, 0), (some (.fx .xcarry), 0, 0)]
  | .fx .nxu => [(some (.fx .xu), 0, 0)]
  | .lit q .nc => [(some (.s q), 1, 2)]
  | .lit q .nl => [(some (.s q), 1, 3)]
  | .lit q .nlm => [(some (.s q), 1, 3), (some (.fx .mk), 0, 0)]
  | .lit q .lm => if F.bnd q then [(some (.lit q .nlm), 0, 0)]
      else [(some (.lit q .nl), 0, 0), (some (.fx .mk), 0, 0)]
  | .lit q .nlmm => [(some (.lit q .lm), 0, 0)]
  | .lit q .nr => [(some (.s q), 1, 1)]
  | .lit q .nrm => [(some (.s q), 1, 1), (some (.fx .lc), 0, 0)]
  | .lit q .rm => if F.bnd q then [(some (.lit q .nrm), 0, 0)]
      else [(some (.lit q .nr), 0, 0), (some (.fx .lc), 0, 0)]
  | .lit q .nrmm => [(some (.lit q .rm), 0, 0)]
  | .mt p => (List.finRange b).map (fun q => litL q (p 0 q)) ++
      (List.finRange b).map (fun q => litC q (p 1 q)) ++
      (List.finRange b).map (fun q => litR q (p 2 q))
  | .nF q => (allPats b).filterMap fun p =>
      if F.rule (p 0) (p 1) (p 2) q then some (some (.mt p), 0, 0) else none
  | .t2 q => [(some (.fx .rs), 0, 0), (some (.nF q), 0, 0)]
  | .it q v f l => [(some (.fx .nrs), 0, 0), (some (.fx (if v then .nxu else .xu)), 0, 0),
      (some (.fx (if f then .nm else .mk)), 0, 0), (some (.fx (if l then .nlc else .lc)), 0, 0)]
  | .ns q => (some (.t2 q), 0, 0) :: vfl.filterMap fun x =>
      if F.init x.1 x.2.1 x.2.2 q then some (some (.it q x.1 x.2.1 x.2.2), 0, 0) else none
  | .s q => [(some (.ns q), 0, 0)]

/-! ## Intended values -/

/-- cell index -/
def ci (K τ : ℕ) : ℕ := τ % (K + 2)
/-- round -/
def rd (K τ : ℕ) : ℕ := τ / (K + 2)
/-- run -/
def rn (K τ : ℕ) : ℕ := τ / (K + 2) / 2 ^ (K + 2)
/-- time within the run -/
def tm (K τ : ℕ) : ℕ := τ / (K + 2) % 2 ^ (K + 2)

/-- intended cell state in block `τ` -/
def st (F : CA b) (K τ : ℕ) : Fin b → Bool := F.run (K + 2) (rn K τ + 1) (tm K τ) (ci K τ)

/-- state read with delay `d` (`false` before the start) -/
def sd (F : CA b) (K d τ : ℕ) : Fin b → Bool := if d ≤ τ then st F K (τ - d) else fun _ => false

/-- neighbourhood seen in block `τ` (left, centre, right) -/
def lv (F : CA b) (K τ : ℕ) : Fin b → Bool :=
  fun q => if ci K τ = 0 then F.bnd q else sd F K (K + 3) τ q
def cv (F : CA b) (K τ : ℕ) : Fin b → Bool := sd F K (K + 2) τ
def rv (F : CA b) (K τ : ℕ) : Fin b → Bool :=
  fun q => if ci K τ + 1 = K + 2 then F.bnd q else sd F K (K + 1) τ q

/-- old bit of the input counter -/
def oldX (K τ : ℕ) : Bool :=
  if tm K τ = 0 then (rn K τ).testBit (ci K τ) else (rn K τ + 1).testBit (ci K τ)

/-- the closed-form values of all wires -/
def val (F : CA b) (K : ℕ) : UW b → ℕ → Bool
  | .fx .boot, τ => decide (τ = 0)
  | .fx .nm, τ => decide (ci K τ ≠ 0)
  | .fx .mk, τ => decide (ci K τ = 0)
  | .fx .nlc, τ => decide (ci K τ + 1 ≠ K + 2)
  | .fx .lc, τ => decide (ci K τ + 1 = K + 2)
  | .fx .tncin, τ => !(low (rd K τ) (ci K τ))
  | .fx .tnb, τ => !((rd K τ).testBit (ci K τ))
  | .fx .tg1, τ => !((rd K τ).testBit (ci K τ) || low (rd K τ) (ci K τ))
  | .fx .tcarry, τ => low (rd K τ) (ci K τ + 1)
  | .fx .tu, τ => (rd K τ + 1).testBit (ci K τ)
  | .fx .novf, τ => if ci K τ = 0 then !(decide (tm K τ = 0)) else !(low (rd K τ) (ci K τ))
  | .fx .inj, τ => decide (ci K τ = 0 ∧ tm K τ = 0)
  | .fx .hold, τ => decide (ci K τ ≠ 0 ∧ tm K τ = 0)
  | .fx .nrs, τ => decide (tm K τ ≠ 0)
  | .fx .rs, τ => decide (tm K τ = 0)
  | .fx .xnc, τ =>
      !(decide (1 ≤ τ) && (decide (tm K (τ - 1) = 0) && low (rn K (τ - 1)) (ci K (τ - 1) + 1)))
  | .fx .xc2, τ => decide (ci K τ ≠ 0 ∧ tm K τ = 0) && low (rn K τ) (ci K τ)
  | .fx .xncin, τ => !(decide (tm K τ = 0) && low (rn K τ) (ci K τ))
  | .fx .xnb, τ => !(oldX K τ)
  | .fx .xg1, τ => !(oldX K τ || (decide (tm K τ = 0) && low (rn K τ) (ci K τ)))
  | .fx .xcarry, τ => decide (tm K τ = 0) && low (rn K τ) (ci K τ + 1)
  | .fx .xu, τ => (rn K τ + 1).testBit (ci K τ)
  | .fx .nxu, τ => !((rn K τ + 1).testBit (ci K τ))
  | .lit q .nc, τ => !(sd F K (K + 2) τ q)
  | .lit q .nl, τ => !(sd F K (K + 3) τ q)
  | .lit q .nlm, τ => !(sd F K (K + 3) τ q || decide (ci K τ = 0))
  | .lit q .lm, τ => lv F K τ q
  | .lit q .nlmm, τ => !(lv F K τ q)
  | .lit q .nr, τ => !(sd F K (K + 1) τ q)
  | .lit q .nrm, τ => !(sd F K (K + 1) τ q || decide (ci K τ + 1 = K + 2))
  | .lit q .rm, τ => rv F K τ q
  | .lit q .nrmm, τ => !(rv F K τ q)
  | .mt p, τ => decide (lv F K τ = p 0 ∧ cv F K τ = p 1 ∧ rv F K τ = p 2)
  | .nF q, τ => !(F.rule (lv F K τ) (cv F K τ) (rv F K τ) q)
  | .t2 q, τ => !(decide (tm K τ = 0)) && F.rule (lv F K τ) (cv F K τ) (rv F K τ) q
  | .it q v f l, τ => decide (tm K τ = 0) && ((rn K τ + 1).testBit (ci K τ) == v) &&
      (decide (ci K τ = 0) == f) && (decide (ci K τ + 1 = K + 2) == l)
  | .ns q, τ => !(st F K τ q)
  | .s q, τ => st F K τ q

/-! ## Arithmetic -/

theorem dm_sub {m n : ℕ} (hm : 0 < m) (h : m ≤ n) : (n - m) / m = n / m - 1 ∧ (n - m) % m = n % m := by
  obtain ⟨h1, h2⟩ := Counter.sub_k_div_mod hm h
  exact ⟨Nat.eq_sub_of_add_eq h1, h2⟩

theorem dm_pred {m n : ℕ} (hm : 0 < m) (h : n % m ≠ 0) :
    (n - 1) / m = n / m ∧ (n - 1) % m = n % m - 1 := Counter.pred_div_mod hm h

theorem dm_pred0 {m n : ℕ} (hm : 0 < m) (h : n % m = 0) (hn : 1 ≤ n) :
    (n - 1) / m = n / m - 1 ∧ (n - 1) % m = m - 1 := by
  have hd := Nat.div_add_mod n m
  have hq : 1 ≤ n / m := by
    rcases Nat.eq_zero_or_pos (n / m) with h0 | h0
    · rw [h0, h] at hd; omega
    · exact h0
  have e1 : m * (n / m - 1) = m * (n / m) - m := Nat.mul_sub_one m (n / m)
  have e2 : m ≤ m * (n / m) := Nat.le_mul_of_pos_right m hq
  have e : n - 1 = m * (n / m - 1) + (m - 1) := by omega
  constructor
  · rw [e, Nat.mul_add_div hm, Nat.div_eq_of_lt (show m - 1 < m by omega), add_zero]
  · rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (show m - 1 < m by omega)]

theorem dm_succ {m n : ℕ} (hm : 0 < m) (h : n % m + 1 < m) :
    (n + 1) / m = n / m ∧ (n + 1) % m = n % m + 1 := by
  have hd := Nat.div_add_mod n m
  have e : n + 1 = m * (n / m) + (n % m + 1) := by omega
  constructor
  · rw [e, Nat.mul_add_div hm, Nat.div_eq_of_lt h, add_zero]
  · rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt h]

theorem dm_succ' {m n : ℕ} (hm : 0 < m) (h : n % m + 1 = m) :
    (n + 1) / m = n / m + 1 ∧ (n + 1) % m = 0 := by
  have hd := Nat.div_add_mod n m
  have e : n + 1 = m * (n / m + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  rw [e, Nat.mul_div_cancel_left _ hm, Nat.mul_mod_right]
  exact ⟨rfl, rfl⟩

theorem dm_small {m n : ℕ} (h : n < m) : n / m = 0 ∧ n % m = n :=
  ⟨Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h⟩

variable {K : ℕ}

theorem hL : 0 < K + 2 := by omega
theorem hP : 0 < 2 ^ (K + 2) := Nat.two_pow_pos _

theorem ci_lt (τ : ℕ) : ci K τ < K + 2 := Nat.mod_lt _ hL

/-- `τ` in round `0` -/
theorem rd_eq_zero {τ : ℕ} (h : τ < K + 2) : rd K τ = 0 := Nat.div_eq_of_lt h

theorem rd_pos {τ : ℕ} (h : K + 2 ≤ τ) : 1 ≤ rd K τ := by
  unfold rd; exact (Nat.le_div_iff_mul_le hL).mpr (by omega)

theorem le_of_rd_pos {τ : ℕ} (h : 1 ≤ rd K τ) : K + 2 ≤ τ := by
  unfold rd at h
  have := (Nat.le_div_iff_mul_le hL).mp h
  omega

/-- shift by one block inside a round -/
theorem sh1 {τ : ℕ} (hi : ci K τ ≠ 0) : rd K (τ - 1) = rd K τ ∧ ci K (τ - 1) = ci K τ - 1 :=
  dm_pred hL hi

/-- shift by one block across a round boundary -/
theorem sh1' {τ : ℕ} (hi : ci K τ = 0) (hτ : 1 ≤ τ) :
    rd K (τ - 1) = rd K τ - 1 ∧ ci K (τ - 1) = K + 1 := by
  have := dm_pred0 (hL (K := K)) hi hτ
  exact ⟨this.1, by rw [ci, this.2]; omega⟩

/-- shift by one round -/
theorem shL {τ : ℕ} (hτ : K + 2 ≤ τ) : rd K (τ - (K + 2)) = rd K τ - 1 ∧ ci K (τ - (K + 2)) = ci K τ :=
  dm_sub hL hτ

/-- shift by one round plus one block -/
theorem shL1 {τ : ℕ} (hi : ci K τ ≠ 0) (hτ : K + 2 ≤ τ) :
    K + 3 ≤ τ ∧ rd K (τ - (K + 3)) = rd K τ - 1 ∧ ci K (τ - (K + 3)) = ci K τ - 1 := by
  obtain ⟨h1, h2⟩ := shL hτ
  have hi' : ci K (τ - (K + 2)) ≠ 0 := by rw [h2]; exact hi
  obtain ⟨h3, h4⟩ := sh1 hi'
  have e : τ - (K + 2) - 1 = τ - (K + 3) := by omega
  rw [e] at h3 h4
  refine ⟨?_, by rw [h3, h1], by rw [h4, h2]⟩
  by_contra hc
  have : τ = K + 2 := by omega
  subst this
  have : ci K (K + 2) = 0 := by simp [ci]
  exact hi this

/-- shift by one round minus one block -/
theorem shLm {τ : ℕ} (hi : ci K τ + 1 < K + 2) (hτ : K + 1 ≤ τ) :
    K + 2 ≤ τ ∧ rd K (τ - (K + 1)) = rd K τ - 1 ∧ ci K (τ - (K + 1)) = ci K τ + 1 := by
  have hτ2 : K + 2 ≤ τ := by
    by_contra hc
    have : ci K τ = τ := Nat.mod_eq_of_lt (by omega)
    omega
  obtain ⟨h1, h2⟩ := shL hτ2
  have hs := dm_succ (hL (K := K)) (n := τ - (K + 2)) (by rw [← ci, h2]; exact hi)
  have e : τ - (K + 2) + 1 = τ - (K + 1) := by omega
  rw [e] at hs
  exact ⟨hτ2, by rw [rd, hs.1, ← rd, h1], by rw [ci, hs.2, ← ci, h2]⟩

/-- the marker read with delay `L - 1` -/
theorem shLm' {τ : ℕ} (hτ : K + 1 ≤ τ) : ci K (τ - (K + 1)) = 0 ↔ ci K τ + 1 = K + 2 := by
  by_cases hi : ci K τ + 1 < K + 2
  · obtain ⟨_, _, h⟩ := shLm hi hτ
    rw [h]; omega
  · have hi' : ci K τ + 1 = K + 2 := by have := ci_lt (K := K) τ; omega
    simp only [hi', iff_true]
    by_cases hτ2 : K + 2 ≤ τ
    · obtain ⟨_, h2⟩ := shL hτ2
      have hs := dm_succ' (hL (K := K)) (n := τ - (K + 2)) (by rw [← ci, h2]; exact hi')
      have e : τ - (K + 2) + 1 = τ - (K + 1) := by omega
      rw [e] at hs
      exact hs.2
    · have : τ = K + 1 := by
        have : ci K τ = τ := Nat.mod_eq_of_lt (by omega)
        omega
      subst this; simp [ci]

/-- run arithmetic: one round back inside a run -/
theorem run_pred {t : ℕ} (hT : t % 2 ^ (K + 2) ≠ 0) :
    (t - 1) / 2 ^ (K + 2) = t / 2 ^ (K + 2) ∧ (t - 1) % 2 ^ (K + 2) = t % 2 ^ (K + 2) - 1 :=
  dm_pred hP hT

/-- run arithmetic: one round back across a run boundary -/
theorem run_pred0 {t : ℕ} (hT : t % 2 ^ (K + 2) = 0) (ht : 1 ≤ t) :
    (t - 1) / 2 ^ (K + 2) = t / 2 ^ (K + 2) - 1 ∧ (t - 1) % 2 ^ (K + 2) = 2 ^ (K + 2) - 1 :=
  dm_pred0 hP hT ht

/-- carry out of the last bit of the previous round = start of a run -/
theorem low_pred_L {t : ℕ} (ht : 1 ≤ t) : low (t - 1) (K + 2) = decide (t % 2 ^ (K + 2) = 0) := by
  unfold low
  by_cases hT : t % 2 ^ (K + 2) = 0
  · rw [(run_pred0 hT ht).2]; simp [hT]
  · rw [(run_pred hT).2]
    have := Nat.mod_lt t (hP (K := K))
    simp only [hT, decide_false, decide_eq_false_iff_not]
    omega

theorem tm_rn_of_rd {τ τ' : ℕ} (h : rd K τ' = rd K τ) : tm K τ' = tm K τ ∧ rn K τ' = rn K τ := by
  unfold tm rn; unfold rd at h; rw [h]; exact ⟨rfl, rfl⟩

/-- previous round inside the same run -/
theorem tm_prev {τ τ' : ℕ} (h : rd K τ' = rd K τ - 1) (hT : tm K τ ≠ 0) :
    tm K τ' = tm K τ - 1 ∧ rn K τ' = rn K τ := by
  unfold tm rn; unfold rd at h; rw [h]
  obtain ⟨h1, h2⟩ := run_pred (K := K) hT
  exact ⟨h2, h1⟩

/-- previous round in the previous run -/
theorem tm_prev0 {τ τ' : ℕ} (h : rd K τ' = rd K τ - 1) (hT : tm K τ = 0) (ht : 1 ≤ rd K τ) :
    rn K τ' + 1 = rn K τ := by
  unfold tm at hT; unfold rn; unfold rd at h ht; rw [h]
  obtain ⟨h1, h2⟩ := run_pred0 (K := K) hT ht
  rw [h1]
  have : 1 ≤ τ / (K + 2) / 2 ^ (K + 2) := by
    have hd := Nat.div_add_mod (τ / (K + 2)) (2 ^ (K + 2))
    rw [hT] at hd
    rcases Nat.eq_zero_or_pos (τ / (K + 2) / 2 ^ (K + 2)) with h0 | h0
    · rw [h0] at hd; omega
    · exact h0
  omega

/-! ## The NOR equations -/

variable (F : CA b)

/-- value read through an input `p` in block `τ` -/
def rdi (p : Option (UW b) × ℕ × ℕ) (τ : ℕ) : Bool :=
  decide (p.2.1 * K + p.2.2 ≤ τ) && srcValA (val F K) p.1 (τ - (p.2.1 * K + p.2.2))

theorem rdi_00 (w : UW b) (τ : ℕ) : rdi (K := K) F (some w, 0, 0) τ = val F K w τ := by
  simp [rdi, srcValA]

theorem rdi_01 (w : UW b) (τ : ℕ) :
    rdi (K := K) F (some w, 0, 1) τ = (decide (1 ≤ τ) && val F K w (τ - 1)) := by
  simp [rdi, srcValA]

theorem rdi_1c (w : UW b) (c τ : ℕ) :
    rdi (K := K) F (some w, 1, c) τ = (decide (K + c ≤ τ) && val F K w (τ - (K + c))) := by
  simp [rdi, srcValA]

theorem rdi_none (τ : ℕ) : rdi (K := K) F (none, 0, 1) τ = decide (1 ≤ τ) := by
  simp [rdi, srcValA]

theorem norEqn_of {j : UW b} {τ : ℕ}
    (h : val F K j τ = !((inp F j).any fun p => rdi (K := K) F p τ)) :
    val F K j τ = true ↔ ∀ p ∈ inp F j, p.2.1 * K + p.2.2 ≤ τ →
      srcValA (val F K) p.1 (τ - (p.2.1 * K + p.2.2)) = false := by
  rw [h]
  simp only [Bool.not_eq_true', List.any_eq_false, rdi, Bool.and_eq_true, decide_eq_true_eq,
    not_and, Bool.not_eq_true]

/-- the state read with delay `d` equals the value of the state wires -/
theorem sd_eq (d τ : ℕ) (q : Fin b) :
    (decide (d ≤ τ) && val F K (.s q) (τ - d)) = sd F K d τ q := by
  unfold sd; split_ifs with h <;> simp [h, val]

theorem sd_def (d τ : ℕ) (q : Fin b) : sd F K d τ q = (decide (d ≤ τ) && st F K (τ - d) q) := by
  unfold sd; split_ifs with h <;> simp [h]

/-- the pattern `(l, c, r)` -/
def pat3 (l c r : Fin b → Bool) : Fin 3 → Fin b → Bool :=
  fun k => if k = 0 then l else if k = 1 then c else r

theorem eq_fx (w : Fx) (τ : ℕ) : val F K (.fx w) τ = !((inp F (.fx w)).any fun p => rdi (K := K) F p τ) := by
  have hci := ci_lt (K := K) τ
  cases w
  · -- boot
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_none, val]
    by_cases h : τ = 0 <;> simp [h] <;> omega
  · -- nm
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, rdi_1c, val]
    by_cases hi : ci K τ = 0
    · by_cases h0 : τ = 0
      · subst h0; simp [ci]
      · have hτ : K + 2 ≤ τ := by
          by_contra hc; have : ci K τ = τ := Nat.mod_eq_of_lt (by omega)
          omega
        have := (shL hτ).2
        simp [hi, h0, hτ, this]
    · have h0 : τ ≠ 0 := by intro h; apply hi; simp [h, ci]
      by_cases hτ : K + 2 ≤ τ
      · have := (shL hτ).2
        simp [hi, h0, hτ, this]
      · simp [hi, h0, hτ]
  · -- mk
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val]
    by_cases hi : ci K τ = 0 <;> simp [hi]
  · -- nlc
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_1c, val]
    by_cases hτ : K + 1 ≤ τ
    · have := shLm' hτ
      by_cases hi : ci K τ + 1 = K + 2 <;> simp [hτ, this, hi]
    · have : ci K τ = τ := Nat.mod_eq_of_lt (by omega)
      have : ci K τ + 1 ≠ K + 2 := by omega
      simp [hτ]; omega
  · -- lc
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val]
    by_cases hi : ci K τ + 1 = K + 2 <;> simp [hi]
  · -- tncin
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, rdi_01, val]
    by_cases hi : ci K τ = 0
    · simp [hi, low_zero]
    · have h1 : 1 ≤ τ := by
        rcases Nat.eq_zero_or_pos τ with h | h
        · exact absurd (by simp [h, ci]) hi
        · exact h
      obtain ⟨e1, e2⟩ := sh1 hi
      rw [e1, e2, show ci K τ - 1 + 1 = ci K τ by omega]
      simp [hi, h1]
  · -- tnb
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_1c, val]
    by_cases hτ : K + 2 ≤ τ
    · obtain ⟨e1, e2⟩ := shL hτ
      have := rd_pos hτ
      rw [e1, e2, show rd K τ - 1 + 1 = rd K τ by omega]
      simp [hτ]
    · rw [rd_eq_zero (by omega)]
      simp [hτ]
  · -- tg1
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, rdi_01, rdi_1c, val]
    by_cases hi : ci K τ = 0
    · simp [hi, low_zero]
    · have h1 : 1 ≤ τ := by
        rcases Nat.eq_zero_or_pos τ with h | h
        · exact absurd (by simp [h, ci]) hi
        · exact h
      obtain ⟨e1, e2⟩ := sh1 hi
      rw [e1, e2, show ci K τ - 1 + 1 = ci K τ by omega]
      by_cases hτ : K + 2 ≤ τ
      · obtain ⟨e3, e4⟩ := shL hτ
        have := rd_pos hτ
        rw [e3, e4, show rd K τ - 1 + 1 = rd K τ by omega]
        simp [hi, h1, hτ]
      · rw [rd_eq_zero (by omega)]
        simp [hi, h1, hτ]
  · -- tcarry
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val, low_succ]
    cases (rd K τ).testBit (ci K τ) <;> cases low (rd K τ) (ci K τ) <;> rfl
  · -- tu
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val, low_succ, testBit_succ]
    cases (rd K τ).testBit (ci K τ) <;> cases low (rd K τ) (ci K τ) <;> rfl
  · -- novf
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, rdi_01, val]
    by_cases hi : ci K τ = 0
    · by_cases h0 : τ = 0
      · subst h0; simp [hi, tm]
      · have h1 : 1 ≤ τ := by omega
        obtain ⟨e1, e2⟩ := sh1' hi h1
        have hτ : K + 2 ≤ τ := by
          by_contra hc; have : ci K τ = τ := Nat.mod_eq_of_lt (by omega)
          omega
        have hr := rd_pos hτ
        rw [e1, e2, show K + 1 + 1 = K + 2 by omega, low_pred_L hr]
        simp only [hi, if_true, h0, decide_false, Bool.false_or, h1, decide_true, Bool.true_and]
        rfl
    · have h0 : τ ≠ 0 := by intro h; apply hi; simp [h, ci]
      have h1 : 1 ≤ τ := by omega
      obtain ⟨e1, e2⟩ := sh1 hi
      rw [e1, e2, show ci K τ - 1 + 1 = ci K τ by omega]
      simp [hi, h0, h1]
  · -- inj
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val]
    by_cases hi : ci K τ = 0 <;> simp [hi]
  · -- hold
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, rdi_01, val]
    by_cases hi : ci K τ = 0
    · simp [hi]
    · have h1 : 1 ≤ τ := by
        rcases Nat.eq_zero_or_pos τ with h | h
        · exact absurd (by simp [h, ci]) hi
        · exact h
      obtain ⟨e1, _⟩ := sh1 hi
      have := (tm_rn_of_rd e1).1
      simp [hi, h1, this]
  · -- nrs
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val]
    by_cases hi : ci K τ = 0 <;> by_cases hT : tm K τ = 0 <;> simp [hi, hT]
  · -- rs
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val]
    by_cases hT : tm K τ = 0 <;> simp [hT]
  · -- xnc
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_01, val]
  · -- xc2
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val]
    by_cases hi : ci K τ = 0
    · simp [hi]
    · have h1 : 1 ≤ τ := by
        rcases Nat.eq_zero_or_pos τ with h | h
        · exact absurd (by simp [h, ci]) hi
        · exact h
      obtain ⟨e1, e2⟩ := sh1 hi
      obtain ⟨e3, e4⟩ := tm_rn_of_rd e1
      rw [e3, e4, e2, show ci K τ - 1 + 1 = ci K τ by omega]
      by_cases hT : tm K τ = 0 <;> simp [hi, h1, hT]
  · -- xncin
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val]
    by_cases hi : ci K τ = 0
    · by_cases hT : tm K τ = 0 <;> simp [hi, hT, low_zero]
    · by_cases hT : tm K τ = 0 <;> simp [hi, hT]
  · -- xnb
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_1c, val]
    by_cases hτ : K + 2 ≤ τ
    · obtain ⟨e1, e2⟩ := shL hτ
      have hr := rd_pos hτ
      rw [e2]
      unfold oldX
      by_cases hT : tm K τ = 0
      · have := tm_prev0 e1 hT hr
        rw [this]; simp [hτ, hT]
      · obtain ⟨_, e4⟩ := tm_prev e1 hT
        rw [e4]; simp [hτ, hT]
    · have h0 : rd K τ = 0 := rd_eq_zero (by omega)
      have hT : tm K τ = 0 := by unfold tm; rw [show τ / (K + 2) = 0 from h0]; simp
      have hR : rn K τ = 0 := by unfold rn; rw [show τ / (K + 2) = 0 from h0]; simp
      simp [hτ, oldX, hT, hR]
  · -- xg1
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, rdi_1c, val]
    have hx : (decide (K + 2 ≤ τ) && (rn K (τ - (K + 2)) + 1).testBit (ci K (τ - (K + 2)))) =
        oldX K τ := by
      by_cases hτ : K + 2 ≤ τ
      · obtain ⟨e1, e2⟩ := shL hτ
        have hr := rd_pos hτ
        rw [e2]
        unfold oldX
        by_cases hT : tm K τ = 0
        · have := tm_prev0 e1 hT hr
          rw [this]; simp [hτ, hT]
        · obtain ⟨_, e4⟩ := tm_prev e1 hT
          rw [e4]; simp [hτ, hT]
      · have h0 : rd K τ = 0 := rd_eq_zero (by omega)
        have hT : tm K τ = 0 := by unfold tm; rw [show τ / (K + 2) = 0 from h0]; simp
        have hR : rn K τ = 0 := by unfold rn; rw [show τ / (K + 2) = 0 from h0]; simp
        simp [hτ, oldX, hT, hR]
    rw [hx]
    by_cases hi : ci K τ = 0
    · by_cases hT : tm K τ = 0 <;> simp [hi, hT, low_zero]
    · by_cases hT : tm K τ = 0 <;> simp [hi, hT]
  · -- xcarry
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val, low_succ]
    unfold oldX
    by_cases hT : tm K τ = 0
    · simp only [hT, if_true, decide_true, Bool.true_and]
      cases (rn K τ).testBit (ci K τ) <;> cases low (rn K τ) (ci K τ) <;> rfl
    · simp [hT]
  · -- xu
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val, low_succ]
    unfold oldX
    by_cases hT : tm K τ = 0
    · simp only [hT, if_true, decide_true, Bool.true_and, testBit_succ]
      cases (rn K τ).testBit (ci K τ) <;> cases low (rn K τ) (ci K τ) <;> rfl
    · simp only [hT, if_false, decide_false, Bool.false_and, Bool.or_false]
      cases (rn K τ + 1).testBit (ci K τ) <;> rfl
  · -- nxu
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val]

theorem eq_lit (q : Fin b) (k : Lk) (τ : ℕ) :
    val F K (.lit q k) τ = !((inp F (.lit q k)).any fun p => rdi (K := K) F p τ) := by
  cases k
  · simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_1c, val, sd_def]
  · simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_1c, val, sd_def]
  · simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_1c, rdi_00, val, sd_def]
  · -- lm
    by_cases hb : F.bnd q = true
    · simp only [inp, hb, if_true, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val, lv]
      by_cases hi : ci K τ = 0 <;> simp [hi, hb]
    · simp only [inp, hb, if_false, Bool.false_eq_true, List.any_cons, List.any_nil, Bool.or_false,
        rdi_00, val, lv]
      by_cases hi : ci K τ = 0 <;> simp [hi, hb]
  · simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val, Bool.not_not]
  · simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_1c, val, sd_def]
  · simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_1c, rdi_00, val, sd_def]
  · -- rm
    by_cases hb : F.bnd q = true
    · simp only [inp, hb, if_true, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val, rv]
      by_cases hi : ci K τ + 1 = K + 2
      · simp [hi, hb]
      · have hi' : ci K τ ≠ K + 1 := by omega
        simp [hi, hi', hb]
    · simp only [inp, hb, if_false, Bool.false_eq_true, List.any_cons, List.any_nil, Bool.or_false,
        rdi_00, val, rv]
      by_cases hi : ci K τ + 1 = K + 2
      · simp [hi, hb]
      · have hi' : ci K τ ≠ K + 1 := by omega
        simp [hi, hi', hb]
  · simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val, Bool.not_not]

/-- reading a complemented literal gives `false` iff the literal equals the pattern bit -/
theorem rdi_litL (q : Fin b) (pb : Bool) (τ : ℕ) :
    rdi (K := K) F (litL q pb) τ = (lv F K τ q != pb) := by
  cases pb <;> simp [litL, rdi_00, val]

theorem rdi_litC (q : Fin b) (pb : Bool) (τ : ℕ) :
    rdi (K := K) F (litC q pb) τ = (cv F K τ q != pb) := by
  cases pb
  · simp only [litC, Bool.false_eq_true, if_false, rdi_1c, sd_eq, cv]
    cases sd F K (K + 2) τ q <;> rfl
  · simp [litC, rdi_00, val, cv]

theorem rdi_litR (q : Fin b) (pb : Bool) (τ : ℕ) :
    rdi (K := K) F (litR q pb) τ = (rv F K τ q != pb) := by
  cases pb <;> simp [litR, rdi_00, val]

theorem eq_mt (p : Fin 3 → Fin b → Bool) (τ : ℕ) :
    val F K (.mt p) τ = !((inp F (.mt p)).any fun x => rdi (K := K) F x τ) := by
  simp only [inp, List.any_append, List.any_map, Function.comp_def, rdi_litL, rdi_litC, rdi_litR,
    val]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_or, Bool.and_eq_true, Bool.not_eq_true',
    List.any_eq_false, List.mem_finRange, true_implies, bne_iff_ne, ne_eq, not_not]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨fun q => by rw [h1], fun q => by rw [h2]⟩, fun q => by rw [h3]⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨funext h1, funext h2, funext h3⟩

theorem eq_nF (q : Fin b) (τ : ℕ) :
    val F K (.nF q) τ = !((inp F (.nF q)).any fun x => rdi (K := K) F x τ) := by
  have key : ((inp F (.nF q)).any fun x => rdi (K := K) F x τ) =
      F.rule (lv F K τ) (cv F K τ) (rv F K τ) q := by
    rw [Bool.eq_iff_iff, List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hrx⟩
      simp only [inp, List.mem_filterMap] at hx
      obtain ⟨p, _, hp⟩ := hx
      by_cases hpr : F.rule (p 0) (p 1) (p 2) q = true
      · rw [if_pos hpr] at hp
        rw [← Option.some.inj hp, rdi_00] at hrx
        simp only [val, decide_eq_true_eq] at hrx
        obtain ⟨e0, e1, e2⟩ := hrx
        rw [e0, e1, e2]; exact hpr
      · rw [if_neg hpr] at hp; exact absurd hp (by simp)
    · intro hr
      refine ⟨(some (.mt (pat3 (lv F K τ) (cv F K τ) (rv F K τ))), 0, 0), ?_, ?_⟩
      · simp only [inp, List.mem_filterMap]
        refine ⟨pat3 (lv F K τ) (cv F K τ) (rv F K τ), mem_allPats _, ?_⟩
        simp [pat3, hr]
      · rw [rdi_00]; simp [val, pat3]
  simp only [val, key]

/-- the key cellular-automaton step -/
theorem st_eq (τ : ℕ) : st F K τ = if tm K τ = 0 then
    F.init ((rn K τ + 1).testBit (ci K τ)) (decide (ci K τ = 0)) (decide (ci K τ + 1 = K + 2))
    else F.rule (lv F K τ) (cv F K τ) (rv F K τ) := by
  unfold st
  split_ifs with hT
  · rw [hT]; rfl
  · obtain ⟨T', hT'⟩ : ∃ T', tm K τ = T' + 1 := ⟨tm K τ - 1, by omega⟩
    rw [hT', CA.run]
    have hr : 1 ≤ rd K τ := by
      by_contra hc
      have : rd K τ = 0 := by omega
      exact hT (by unfold tm; rw [show τ / (K + 2) = 0 from this]; simp)
    have hτ : K + 2 ≤ τ := le_of_rd_pos hr
    congr 1
    · -- left neighbour
      funext q
      unfold lv
      split_ifs with hi
      · rfl
      · obtain ⟨h3, e1, e2⟩ := shL1 hi hτ
        obtain ⟨e3, e4⟩ := tm_prev e1 hT
        simp only [sd, h3, if_true, st, e3, e4, e2, hT']
        rfl
    · -- centre
      funext q
      obtain ⟨e1, e2⟩ := shL hτ
      obtain ⟨e3, e4⟩ := tm_prev e1 hT
      simp only [cv, sd, hτ, if_true, st, e3, e4, e2, hT']
      rfl
    · -- right neighbour
      funext q
      unfold rv
      split_ifs with hi
      · rfl
      · have hi' : ci K τ + 1 < K + 2 := by have := ci_lt (K := K) τ; omega
        obtain ⟨_, e1, e2⟩ := shLm hi' (by omega)
        obtain ⟨e3, e4⟩ := tm_prev e1 hT
        simp only [sd, show K + 1 ≤ τ by omega, if_true, st, e3, e4, e2, hT']
        rfl

theorem eq_rest (j : UW b) (τ : ℕ) (hj : ∀ w, j ≠ .fx w) (hl : ∀ q k, j ≠ .lit q k)
    (hm : ∀ p, j ≠ .mt p) (hn : ∀ q, j ≠ .nF q) :
    val F K j τ = !((inp F j).any fun x => rdi (K := K) F x τ) := by
  cases j with
  | fx w => exact absurd rfl (hj w)
  | lit q k => exact absurd rfl (hl q k)
  | mt p => exact absurd rfl (hm p)
  | nF q => exact absurd rfl (hn q)
  | t2 q =>
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val]
    by_cases hT : tm K τ = 0 <;> simp [hT]
  | it q v f l =>
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00]
    have e0 : val F K (.fx .nrs) τ = !(decide (tm K τ = 0)) := by simp [val]
    have e1 : val F K (.fx (if v then .nxu else .xu)) τ = (if v then !((rn K τ + 1).testBit (ci K τ))
        else (rn K τ + 1).testBit (ci K τ)) := by cases v <;> rfl
    have e2 : val F K (.fx (if f then .nm else .mk)) τ = (if f then !(decide (ci K τ = 0))
        else decide (ci K τ = 0)) := by cases f <;> simp [val]
    have e3 : val F K (.fx (if l then .nlc else .lc)) τ = (if l then !(decide (ci K τ + 1 = K + 2))
        else decide (ci K τ + 1 = K + 2)) := by cases l <;> simp [val]
    rw [e0, e1, e2, e3]
    simp only [val]
    generalize decide (tm K τ = 0) = D
    generalize (rn K τ + 1).testBit (ci K τ) = X
    generalize decide (ci K τ = 0) = M
    generalize decide (ci K τ + 1 = K + 2) = C
    cases D <;> cases X <;> cases M <;> cases C <;> cases v <;> cases f <;> cases l <;> rfl
  | ns q =>
    simp only [inp, List.any_cons, rdi_00]
    rw [Bool.eq_iff_iff]
    have hit : (List.any (vfl.filterMap fun x => if F.init x.1 x.2.1 x.2.2 q = true then
          some (some (UW.it q x.1 x.2.1 x.2.2), 0, 0) else none) fun x => rdi (K := K) F x τ) =
        (decide (tm K τ = 0) && F.init ((rn K τ + 1).testBit (ci K τ)) (decide (ci K τ = 0))
          (decide (ci K τ + 1 = K + 2)) q) := by
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, List.mem_filterMap, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨x, ⟨y, _, hy⟩, hx⟩
        by_cases hyi : F.init y.1 y.2.1 y.2.2 q = true
        · rw [if_pos hyi] at hy
          rw [← Option.some.inj hy, rdi_00] at hx
          simp only [val, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
          obtain ⟨⟨⟨hT, hv⟩, hf⟩, hl⟩ := hx
          refine ⟨hT, ?_⟩
          rw [hv, hf, hl]; exact hyi
        · rw [if_neg hyi] at hy; exact absurd hy (by simp)
      · rintro ⟨hT, hi⟩
        set xv := (rn K τ + 1).testBit (ci K τ) with hxv
        set xf := decide (ci K τ = 0) with hxf
        set xl := decide (ci K τ + 1 = K + 2) with hxl
        refine ⟨(some (.it q xv xf xl), 0, 0), ⟨(xv, xf, xl), mem_vfl _, ?_⟩, ?_⟩
        · show (if F.init xv xf xl q = true then some (some (UW.it q xv xf xl), 0, 0) else none) = _
          rw [if_pos hi]
        · rw [rdi_00]
          simp only [val, hT, decide_true, Bool.true_and, beq_self_eq_true, Bool.and_self, hxv,
            hxf, hxl]
    rw [hit]
    simp only [val, st_eq F τ]
    by_cases hT : tm K τ = 0
    · simp [hT]
    · simp [hT]
  | s q =>
    simp only [inp, List.any_cons, List.any_nil, Bool.or_false, rdi_00, val, Bool.not_not]

/-- **The closed forms solve the NOR equations of `U_F`.** -/
theorem norEqns : NorEqnsA (inp F) K (val F K) := by
  intro j τ
  apply norEqn_of
  cases j with
  | fx w => exact eq_fx F w τ
  | lit q k => exact eq_lit F q k τ
  | mt p => exact eq_mt F p τ
  | nF q => exact eq_nF F q τ
  | t2 q => exact eq_rest F _ τ (by simp) (by simp) (by simp) (by simp)
  | it q v f l => exact eq_rest F _ τ (by simp) (by simp) (by simp) (by simp)
  | ns q => exact eq_rest F _ τ (by simp) (by simp) (by simp) (by simp)
  | s q => exact eq_rest F _ τ (by simp) (by simp) (by simp) (by simp)

end Univ
end SubGame
