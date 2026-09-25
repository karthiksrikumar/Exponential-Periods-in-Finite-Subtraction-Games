import Sts.UnivCore

/-!
# Universality with a bounded number of moves

For every `b`-bit cellular automaton `F` there is a *fixed* list of taps such that, for every ring
length `L = K + 2`, the subtraction game with the moves `(a * K + c) * B + δ` runs `F` on the ring of
length `L` from every initial configuration in turn: the configuration of run `j` carries bit `i`
of `j + 1` on cell `i`, and position `((j * 2^L + T) * L + i) * B + ρ q` is a P-position iff bit `q`
of cell `i` after `T` steps is `1`.

The circuit is `UnivCore.inp F`; it is laid out by the General Layout Lemma with the coarse
positions `3^rank - 1`, a super-increasing (hence Sidon) sequence.
-/

namespace SubGame
namespace Univ

open GLL

variable {b : ℕ}

/-! ## Ranks: a topological order of the wires -/

def Fx.idx : Fx → ℕ
  | .boot => 0 | .nm => 1 | .mk => 2 | .nlc => 3 | .lc => 4 | .tncin => 5 | .tnb => 6
  | .tg1 => 7 | .tcarry => 8 | .tu => 9 | .novf => 10 | .inj => 11 | .hold => 12 | .nrs => 13
  | .rs => 14 | .xnc => 15 | .xc2 => 16 | .xncin => 17 | .xnb => 18 | .xg1 => 19 | .xcarry => 20
  | .xu => 21 | .nxu => 22

theorem Fx.idx_lt (w : Fx) : w.idx < 23 := by cases w <;> decide

theorem Fx.idx_inj {w w' : Fx} (h : w.idx = w'.idx) : w = w' := by
  cases w <;> cases w' <;> first | rfl | (simp [Fx.idx] at h)

def Lk.idx : Lk → ℕ
  | .nc => 0 | .nl => 1 | .nlm => 2 | .lm => 3 | .nlmm => 4 | .nr => 5 | .nrm => 6 | .rm => 7
  | .nrmm => 8

theorem Lk.idx_lt (k : Lk) : k.idx < 9 := by cases k <;> decide

theorem Lk.idx_inj {k k' : Lk} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [Lk.idx] at h)

/-- number of neighbourhood patterns -/
def nP (b : ℕ) : ℕ := Fintype.card (Fin 3 → Fin b → Bool)

noncomputable def patIdx (p : Fin 3 → Fin b → Bool) : ℕ :=
  (Fintype.equivFin (Fin 3 → Fin b → Bool) p : ℕ)

theorem patIdx_lt (p : Fin 3 → Fin b → Bool) : patIdx p < nP b :=
  (Fintype.equivFin (Fin 3 → Fin b → Bool) p).isLt

theorem patIdx_inj {p p' : Fin 3 → Fin b → Bool} (h : patIdx p = patIdx p') : p = p' :=
  (Fintype.equivFin _).injective (Fin.ext h)

def bidx (v f l : Bool) : ℕ := (if v then 4 else 0) + (if f then 2 else 0) + (if l then 1 else 0)

theorem bidx_lt (v f l : Bool) : bidx v f l < 8 := by
  cases v <;> cases f <;> cases l <;> decide

theorem bidx_inj {v f l v' f' l' : Bool} (h : bidx v f l = bidx v' f' l') :
    v = v' ∧ f = f' ∧ l = l' := by
  cases v <;> cases f <;> cases l <;> cases v' <;> cases f' <;> cases l' <;>
    simp_all [bidx]

/-- the rank of a wire (inputs with delay `0` always come from smaller ranks) -/
noncomputable def rank : UW b → ℕ
  | .fx w => w.idx
  | .lit q k => 23 + 9 * q + k.idx
  | .mt p => 23 + 9 * b + patIdx p
  | .nF q => 23 + 9 * b + nP b + q
  | .t2 q => 23 + 10 * b + nP b + q
  | .it q v f l => 23 + 11 * b + nP b + 8 * q + bidx v f l
  | .ns q => 23 + 19 * b + nP b + q
  | .s q => 23 + 20 * b + nP b + q

/-- an upper bound for all ranks -/
def rmax (b : ℕ) : ℕ := 23 + 21 * b + nP b

theorem rank_lt (w : UW b) : rank w < rmax b := by
  cases w with
  | fx w => have := w.idx_lt; simp only [rank, rmax]; omega
  | lit q k => have := k.idx_lt; have := q.isLt; simp only [rank, rmax]; omega
  | mt p => have := patIdx_lt p; simp only [rank, rmax]; omega
  | nF q => have := q.isLt; simp only [rank, rmax]; omega
  | t2 q => have := q.isLt; simp only [rank, rmax]; omega
  | it q v f l => have := q.isLt; have := bidx_lt v f l; simp only [rank, rmax]; omega
  | ns q => have := q.isLt; simp only [rank, rmax]; omega
  | s q => have := q.isLt; simp only [rank, rmax]; omega

theorem rank_inj {w w' : UW b} (h : rank w = rank w') : w = w' := by
  cases w with
  | fx a =>
    cases w' with
    | fx a' => simp only [rank] at h; rw [Fx.idx_inj h]
    | lit q k => simp only [rank] at h; have := a.idx_lt; omega
    | mt p => simp only [rank] at h; have := a.idx_lt; omega
    | nF q => simp only [rank] at h; have := a.idx_lt; omega
    | t2 q => simp only [rank] at h; have := a.idx_lt; omega
    | it q v f l => simp only [rank] at h; have := a.idx_lt; omega
    | ns q => simp only [rank] at h; have := a.idx_lt; omega
    | s q => simp only [rank] at h; have := a.idx_lt; omega
  | lit q k =>
    have := k.idx_lt; have := q.isLt
    cases w' with
    | fx a => simp only [rank] at h; have := a.idx_lt; omega
    | lit q' k' =>
      simp only [rank] at h; have := k'.idx_lt
      have hq : (q : ℕ) = q' := by omega
      have hk : k.idx = k'.idx := by omega
      rw [Fin.ext hq, Lk.idx_inj hk]
    | mt p => simp only [rank] at h; omega
    | nF q' => simp only [rank] at h; omega
    | t2 q' => simp only [rank] at h; omega
    | it q' v f l => simp only [rank] at h; omega
    | ns q' => simp only [rank] at h; omega
    | s q' => simp only [rank] at h; omega
  | mt p =>
    have := patIdx_lt p
    cases w' with
    | fx a => simp only [rank] at h; have := a.idx_lt; omega
    | lit q k => simp only [rank] at h; have := k.idx_lt; have := q.isLt; omega
    | mt p' => simp only [rank] at h; rw [patIdx_inj (by omega : patIdx p = patIdx p')]
    | nF q => simp only [rank] at h; omega
    | t2 q => simp only [rank] at h; omega
    | it q v f l => simp only [rank] at h; omega
    | ns q => simp only [rank] at h; omega
    | s q => simp only [rank] at h; omega
  | nF q =>
    have := q.isLt
    cases w' with
    | fx a => simp only [rank] at h; have := a.idx_lt; omega
    | lit q' k => simp only [rank] at h; have := k.idx_lt; have := q'.isLt; omega
    | mt p => simp only [rank] at h; have := patIdx_lt p; omega
    | nF q' => simp only [rank] at h; rw [Fin.ext (by omega : (q : ℕ) = q')]
    | t2 q' => simp only [rank] at h; omega
    | it q' v f l => simp only [rank] at h; omega
    | ns q' => simp only [rank] at h; omega
    | s q' => simp only [rank] at h; omega
  | t2 q =>
    have := q.isLt
    cases w' with
    | fx a => simp only [rank] at h; have := a.idx_lt; omega
    | lit q' k => simp only [rank] at h; have := k.idx_lt; have := q'.isLt; omega
    | mt p => simp only [rank] at h; have := patIdx_lt p; omega
    | nF q' => simp only [rank] at h; have := q'.isLt; omega
    | t2 q' => simp only [rank] at h; rw [Fin.ext (by omega : (q : ℕ) = q')]
    | it q' v f l => simp only [rank] at h; omega
    | ns q' => simp only [rank] at h; omega
    | s q' => simp only [rank] at h; omega
  | it q v f l =>
    have := q.isLt; have := bidx_lt v f l
    cases w' with
    | fx a => simp only [rank] at h; have := a.idx_lt; omega
    | lit q' k => simp only [rank] at h; have := k.idx_lt; have := q'.isLt; omega
    | mt p => simp only [rank] at h; have := patIdx_lt p; omega
    | nF q' => simp only [rank] at h; have := q'.isLt; omega
    | t2 q' => simp only [rank] at h; have := q'.isLt; omega
    | it q' v' f' l' =>
      simp only [rank] at h; have := bidx_lt v' f' l'; have := q'.isLt
      have hq : (q : ℕ) = q' := by omega
      obtain ⟨h1, h2, h3⟩ := bidx_inj (by omega : bidx v f l = bidx v' f' l')
      rw [Fin.ext hq, h1, h2, h3]
    | ns q' => simp only [rank] at h; omega
    | s q' => simp only [rank] at h; omega
  | ns q =>
    have := q.isLt
    cases w' with
    | fx a => simp only [rank] at h; have := a.idx_lt; omega
    | lit q' k => simp only [rank] at h; have := k.idx_lt; have := q'.isLt; omega
    | mt p => simp only [rank] at h; have := patIdx_lt p; omega
    | nF q' => simp only [rank] at h; have := q'.isLt; omega
    | t2 q' => simp only [rank] at h; have := q'.isLt; omega
    | it q' v f l => simp only [rank] at h; have := q'.isLt; have := bidx_lt v f l; omega
    | ns q' => simp only [rank] at h; rw [Fin.ext (by omega : (q : ℕ) = q')]
    | s q' => simp only [rank] at h; omega
  | s q =>
    have := q.isLt
    cases w' with
    | fx a => simp only [rank] at h; have := a.idx_lt; omega
    | lit q' k => simp only [rank] at h; have := k.idx_lt; have := q'.isLt; omega
    | mt p => simp only [rank] at h; have := patIdx_lt p; omega
    | nF q' => simp only [rank] at h; have := q'.isLt; omega
    | t2 q' => simp only [rank] at h; have := q'.isLt; omega
    | it q' v f l => simp only [rank] at h; have := q'.isLt; have := bidx_lt v f l; omega
    | ns q' => simp only [rank] at h; have := q'.isLt; omega
    | s q' => simp only [rank] at h; rw [Fin.ext (by omega : (q : ℕ) = q')]

/-! ## The inputs respect the order -/

/-- every input is the clock (for `boot`, delay `1`), or another wire that is either earlier in
the order or read with a positive constant delay -/
theorem inp_spec (F : CA b) (w : UW b) (p : Option (UW b) × ℕ × ℕ) (hp : p ∈ inp F w) :
    (p.1 = none ∧ p.2.2 = 1) ∨ ∃ i, p.1 = some i ∧ i ≠ w ∧ (rank i < rank w ∨ 1 ≤ p.2.2) := by
  cases w with
  | fx a =>
    cases a <;> simp only [inp, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl <;> simp [rank, Fx.idx]
  | lit q k =>
    cases k <;> simp only [inp] at hp
    all_goals first
      | (split_ifs at hp <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
          rcases hp with rfl | rfl <;> simp [rank, Lk.idx, Fx.idx])
      | (simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
         rcases hp with rfl | rfl <;> simp [rank, Lk.idx, Fx.idx] <;> omega)
  | mt p =>
    simp only [inp, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hp
    rcases hp with (⟨q, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩
    · right
      refine ⟨if p 0 q then .lit q .nlmm else .lit q .lm, by simp [litL], by split_ifs <;> simp, ?_⟩
      left; have := q.isLt; split_ifs <;> simp [rank, Lk.idx] <;> omega
    · unfold litC; split_ifs
      · right; refine ⟨.lit q .nc, rfl, by simp, Or.inl ?_⟩
        have := q.isLt; simp [rank, Lk.idx]; omega
      · right; exact ⟨.s q, rfl, by simp, Or.inr (by simp)⟩
    · right
      refine ⟨if p 2 q then .lit q .nrmm else .lit q .rm, by simp [litR], by split_ifs <;> simp, ?_⟩
      left; have := q.isLt; split_ifs <;> simp [rank, Lk.idx] <;> omega
  | nF q =>
    simp only [inp, List.mem_filterMap] at hp
    obtain ⟨p', _, hp'⟩ := hp
    by_cases h : F.rule (p' 0) (p' 1) (p' 2) q = true
    · rw [if_pos h] at hp'
      rw [← Option.some.inj hp']
      right; refine ⟨.mt p', rfl, by simp, Or.inl ?_⟩
      have := patIdx_lt p'; simp [rank]; omega
    · rw [if_neg h] at hp'; exact absurd hp' (by simp)
  | t2 q =>
    simp only [inp, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · right; refine ⟨.fx .rs, rfl, by simp, Or.inl ?_⟩; simp [rank, Fx.idx]; omega
    · right; refine ⟨.nF q, rfl, by simp, Or.inl ?_⟩; have := q.isLt; simp [rank]; omega
  | it q v f l =>
    simp only [inp, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · right; refine ⟨.fx .nrs, rfl, by simp, Or.inl ?_⟩; simp [rank, Fx.idx]; omega
    · right; refine ⟨.fx (if v then .nxu else .xu), rfl, by simp, Or.inl ?_⟩
      have := (if v then Fx.nxu else Fx.xu).idx_lt; simp only [rank]; omega
    · right; refine ⟨.fx (if f then .nm else .mk), rfl, by simp, Or.inl ?_⟩
      have := (if f then Fx.nm else Fx.mk).idx_lt; simp only [rank]; omega
    · right; refine ⟨.fx (if l then .nlc else .lc), rfl, by simp, Or.inl ?_⟩
      have := (if l then Fx.nlc else Fx.lc).idx_lt; simp only [rank]; omega
  | ns q =>
    simp only [inp, List.mem_cons, List.mem_filterMap] at hp
    rcases hp with rfl | ⟨x, _, hx⟩
    · right; refine ⟨.t2 q, rfl, by simp, Or.inl ?_⟩; have := q.isLt; simp [rank]; omega
    · by_cases h : F.init x.1 x.2.1 x.2.2 q = true
      · rw [if_pos h] at hx
        rw [← Option.some.inj hx]
        right; refine ⟨.it q x.1 x.2.1 x.2.2, rfl, by simp, Or.inl ?_⟩
        have := q.isLt; have := bidx_lt x.1 x.2.1 x.2.2; simp only [rank]; omega
      · rw [if_neg h] at hx; exact absurd hx (by simp)
  | s q =>
    simp only [inp, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    right; refine ⟨.ns q, rfl, by simp, Or.inl ?_⟩; have := q.isLt; simp [rank]; omega

/-! ## Coarse positions -/

/-- coarse position of a wire: `3^rank - 1` -/
noncomputable def yy (w : UW b) : ℕ := 3 ^ rank w - 1

noncomputable def Bp (b : ℕ) : ℕ := 3 ^ (rmax b + 1) + 3

theorem one_le_pow3 (n : ℕ) : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)

theorem pow3_inj {m n : ℕ} (h : 3 ^ m = 3 ^ n) : m = n :=
  Nat.pow_right_injective (by norm_num : 2 ≤ 3) h

theorem sidon3 {a b c d : ℕ} (h : 3 ^ a + 3 ^ b = 3 ^ c + 3 ^ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have key : ∀ x y : ℕ, x < y → 2 * 3 ^ x < 3 ^ y := by
    intro x y hxy
    have h1 : 2 * 3 ^ x < 3 ^ (x + 1) := by rw [pow_succ]; have := one_le_pow3 x; omega
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hxy)
  have mono : ∀ x y : ℕ, x ≤ y → 3 ^ x ≤ 3 ^ y := fun x y hxy => Nat.pow_le_pow_right (by norm_num) hxy
  -- reduce to the case a ≤ b, c ≤ d
  suffices H : ∀ a b c d : ℕ, a ≤ b → c ≤ d → 3 ^ a + 3 ^ b = 3 ^ c + 3 ^ d → a = c ∧ b = d by
    rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
    · exact Or.inl (H a b c d hab hcd h)
    · obtain ⟨h1, h2⟩ := H a b d c hab hcd (by omega); exact Or.inr ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := H b a c d hab hcd (by omega); exact Or.inr ⟨h2, h1⟩
    · obtain ⟨h1, h2⟩ := H b a d c hab hcd (by omega); exact Or.inl ⟨h2, h1⟩
  intro a b c d hab hcd h
  rcases lt_trichotomy b d with hbd | hbd | hbd
  · have := key b d hbd; have := mono a b hab; have := one_le_pow3 c; omega
  · subst hbd
    exact ⟨pow3_inj (by omega), rfl⟩
  · have := key d b hbd; have := mono c d hcd; have := one_le_pow3 a; omega

theorem hypY : HypYA (yy (b := b)) (Bp b) where
  inj := by
    intro w w' h
    unfold yy at h
    have := one_le_pow3 (rank w); have := one_le_pow3 (rank w')
    exact rank_inj (pow3_inj (by omega))
  ne1 := by
    intro w h
    unfold yy at h
    have h2 : 3 ^ rank w = 2 := by have := one_le_pow3 (rank w); omega
    rcases Nat.eq_zero_or_pos (rank w) with h0 | h0
    · rw [h0] at h2; norm_num at h2
    · have : 3 ∣ 3 ^ rank w := dvd_pow_self 3 (by omega)
      rw [h2] at this; norm_num at this
  big := by
    intro w
    unfold yy Bp
    have hr := rank_lt w
    have h1 : 3 ^ (rank w + 1) ≤ 3 ^ (rmax b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := one_le_pow3 (rank w)
    have h3 : 3 ^ (rank w + 1) = 3 * 3 ^ rank w := by rw [pow_succ]; ring
    omega
  sidon := by
    intro a b' c d h
    unfold yy at h
    have := one_le_pow3 (rank a); have := one_le_pow3 (rank b')
    have := one_le_pow3 (rank c); have := one_le_pow3 (rank d)
    rcases sidon3 (by omega : 3 ^ rank a + 3 ^ rank b' = 3 ^ rank c + 3 ^ rank d) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨rank_inj h1, rank_inj h2⟩
    · exact Or.inr ⟨rank_inj h1, rank_inj h2⟩

theorem yy_lt {w w' : UW b} (h : rank w < rank w') : yy w < yy w' := by
  unfold yy
  have := Nat.pow_lt_pow_right (by norm_num : 1 < 3) h
  have := one_le_pow3 (rank w)
  omega

theorem hypC (F : CA b) : HypCA (yy (b := b)) (inp F) where
  boot := ⟨.fx .boot, by simp [yy, rank, Fx.idx], rfl⟩
  noself := by
    intro w p hp
    rcases inp_spec F w p hp with ⟨h, _⟩ | ⟨i, hi, hne, _⟩
    · rw [h]; simp
    · rw [hi]; simp [hne]
  back := by
    intro w p hp hle
    rcases inp_spec F w p hp with ⟨_, h⟩ | ⟨i, hi, _, hr | hr⟩
    · omega
    · rw [hi] at hle
      simp only [srcResA] at hle
      have := yy_lt hr
      omega
    · exact hr

/-! ## The main theorem -/

theorem st_at (F : CA b) (K j T i : ℕ) (hT : T < 2 ^ (K + 2)) (hi : i < K + 2) :
    st F K ((j * 2 ^ (K + 2) + T) * (K + 2) + i) = F.run (K + 2) (j + 1) T i := by
  have hL : 0 < K + 2 := by omega
  have hP : 0 < 2 ^ (K + 2) := Nat.two_pow_pos _
  have e1 : ((j * 2 ^ (K + 2) + T) * (K + 2) + i) / (K + 2) = j * 2 ^ (K + 2) + T := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hi, zero_add]
  have e2 : ((j * 2 ^ (K + 2) + T) * (K + 2) + i) % (K + 2) = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have e3 : (j * 2 ^ (K + 2) + T) / 2 ^ (K + 2) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hT, zero_add]
  have e4 : (j * 2 ^ (K + 2) + T) % 2 ^ (K + 2) = T := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hT]
  simp only [st, rn, tm, ci, e1, e2, e3, e4]

/-- **Universality with a bounded number of moves (formal).**  For every `b`-bit cellular
automaton `F` there are a block length `B`, residues `ρ` and a finite list of taps such that for
every `K` (ring length `L = K + 2`) the subtraction game with moves
`movesOf B taps K = [(a * K + c) * B + δ]` (at most `taps.length` of them) satisfies: position
`((j * 2^L + T) * L + i) * B + ρ q` is a P-position iff bit `q` of cell `i` after `T < 2^L` steps of
`F`, started from the configuration with bit `i` of `j + 1` on cell `i`, is `true`. -/
theorem universal (F : CA b) : ∃ (B : ℕ) (taps : List (ℕ × ℕ × ℕ)) (ρ : Fin b → ℕ),
    ∀ K j T i (q : Fin b), T < 2 ^ (K + 2) → i < K + 2 →
      (outcome (movesOf B taps K) (((j * 2 ^ (K + 2) + T) * (K + 2) + i) * B + ρ q) = true ↔
        F.run (K + 2) (j + 1) T i q = true) := by
  obtain ⟨taps, htaps⟩ := simulateA (yy (b := b)) (Bp b) (inp F) hypY (hypC F)
  refine ⟨13 * Bp b, taps, fun q => 13 * yy (UW.s q), fun K j T i q hT hi => ?_⟩
  set τ := (j * 2 ^ (K + 2) + T) * (K + 2) + i with hτ
  have hB : 13 * yy (b := b) (UW.s q) < 13 * Bp b := by
    have := (hypY (b := b)).big (UW.s q); omega
  have hmod : (τ * (13 * Bp b) + 13 * yy (UW.s q)) % (13 * Bp b) = 13 * yy (UW.s q) :=
    mod_of_decomp hB
  have hdiv : (τ * (13 * Bp b) + 13 * yy (UW.s q)) / (13 * Bp b) = τ := div_of_decomp hB
  have hst : st F K τ = F.run (K + 2) (j + 1) T i := st_at F K j T i hT hi
  rw [htaps K (val F K) (norEqns F) _, hmod, hdiv]
  constructor
  · rintro (h | h | h | ⟨w, hw, hv⟩)
    · omega
    · omega
    · omega
    · have hw' : w = UW.s q := (hypY (b := b)).inj (by omega)
      subst hw'
      simpa [val, hst] using hv
  · intro h
    refine Or.inr (Or.inr (Or.inr ⟨UW.s q, rfl, ?_⟩))
    simpa [val, hst] using h

end Univ
end SubGame

#print axioms SubGame.Univ.universal
