module

public import NativeVm.Code.Phase3.SelEq

/-!
# Phase 3's padding weights: `paddingWeight`

`padAb_spec`: `A := paddingWeight (point.extract 0 lr) R`, `lr` at word `src + 2 i`, `R` at word
`rows + i` (`r14 = 2 i`). Through `EW.toE` it is `padAcc`, the statement's fold over the
coordinates (`paddingWeight_list`), times the top bit's factor. The code forms each step as
`(A + c)·(y + c) + c`, `c = 1 + bit` (`padStep`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field
open LeanVM.Protocol.Verifier (eOfNat)

/-- The fold of `paddingWeight`, from coordinate `k`. -/
def padAcc (R : Nat) : List LeanVM.Parameters.E → Nat → LeanVM.Parameters.E → LeanVM.Parameters.E
  | [], _, acc => acc
  | r :: L, k, acc => padAcc R L (k + 1)
      ((1 + eOfNat ((R >>> k) % 2)) * r + (1 + eOfNat ((R >>> k) % 2) + r) * acc)

theorem foldl_zipIdx_pad (R : Nat) : ∀ (L : List LeanVM.Parameters.E) (k : Nat) acc,
    (L.zipIdx k).foldl (fun pad (p : LeanVM.Parameters.E × Nat) ↦
      (1 + eOfNat ((R >>> p.2) % 2)) * p.1 + (1 + eOfNat ((R >>> p.2) % 2) + p.1) * pad) acc =
      padAcc R L k acc
  | [], _, _ => rfl
  | r :: L, k, acc => by
    rw [List.zipIdx_cons, List.foldl_cons, foldl_zipIdx_pad R L (k + 1)]
    rfl

theorem paddingWeight_list (pts : Array EW) (R : Nat) :
    (paddingWeight pts R).toE =
      (1 + eOfNat ((R >>> pts.size) % 2)) * padAcc R (pts.toList.map EW.toE) 0 1 := by
  rw [NativeVm.Equiv.toE_paddingWeight, LeanVM.Protocol.Verifier.paddingWeight, List.length_map,
    Array.length_toList, ← foldl_zipIdx_pad]

theorem eOfNat_bit (b : Nat) (hb : b < 2) : eOfNat b = 0 ∨ eOfNat b = 1 := by
  interval_cases b
  · left; rw [eOfNat_eq', show (0 : Nat).toUInt64 = 0 from rfl, eOf_zero]
  · right; rw [eOfNat_eq', show (1 : Nat).toUInt64 = 1 from rfl, eOf_one]

theorem two_E : (2 : LeanVM.Parameters.E) = 0 := CharTwo.two_eq_zero

/-- One step of the fold, as the code forms it: `c = 1 + b`, `b` a bit. -/
theorem padStep (A y b : LeanVM.Parameters.E) (hb : b = 0 ∨ b = 1) :
    (A + (1 + b)) * (y + (1 + b)) + (1 + b) = (1 + b) * y + (1 + b + y) * A := by
  rcases hb with rfl | rfl
  · linear_combination two_E
  · linear_combination 3 * two_E

theorem bit_lt (R k : Nat) : (R >>> k) % 2 < 2 := Nat.mod_lt _ (by omega)

theorem shr_lt {R : Nat} (h : R < 2 ^ 64) (k : Nat) : R >>> k < 2 ^ 64 := by
  rw [Nat.shiftRight_eq_div_pow]; exact lt_of_le_of_lt (Nat.div_le_self _ _) h

/-- `c = 1 + bit`, as the code forms it. -/
theorem flip_eq {x : Nat} (hx : x < 2 ^ 64) :
    eOf ((x.toUInt64 &&& 1) ^^^ 1) 0 = 1 + eOfNat (x % 2) := by
  rw [toUInt64_and_one hx, show (0 : UInt64) = 0 ^^^ 0 from rfl, eOf_add, eOf_one, ← eOfNat_eq',
    add_comm]

theorem test_bit {s : QState} {r : Reg64} {x : Nat} (hx : x < 2 ^ 64) (h : s.reg r = x.toUInt64) :
    (Cond.test true r (.imm 1)).eval s = decide (x % 2 = 0) := by
  simp only [Cond.eval, Rhs.eval, h, Field.int64One_toUInt64, toUInt64_and_one hx]
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem eOf_xor_lo' (a b c : UInt64) : eOf (a ^^^ b) c = eOf a c + eOf b 0 := by
  rw [← eOf_add, UInt64.xor_zero]

variable {s : QState} {F : QState → Prop}

theorem padAb_spec {p : UInt64} {src rows i lr R : Nat} {point : Array EW}
    (h15 : s.reg .r15 = p) (h14 : s.reg .r14 = (2 * i).toUInt64)
    (hlr : s.mem (wd p (src + 2 * i)) = some lr.toUInt64)
    (hR : s.mem (wd p (rows + i)) = some R.toUInt64)
    (hn : s.mem (wd p depthR.off) = some point.size.toUInt64)
    (hlb : lr < 2 ^ 64) (hRb : R < 2 ^ 64) (hps : point.size < 64) (hp : PointAt s.mem p point) :
    WP (padAb src rows) s (fun s' ↦ s'.reg .r9 = (paddingWeight (point.extract 0 lr) R).c0 ∧
      s'.reg .r10 = (paddingWeight (point.extract 0 lr) R).c1 ∧ s'.mem = s.mem ∧
      RegsFrame selRegs s s') F := by
  have a1 := eval_aI (s := s) (k := src) h15 h14
  rw [show 2 * i + src = src + 2 * i by omega] at a1
  simp only [padAb, padFlip, List.cons_append, List.nil_append]
  refine wp_load a1 hlr ?_
  have a2 := eval_aH (s := s.setReg .rsi lr.toUInt64) (ix := .r14) (i := i) (k := rows)
    (by rsimp; exact h15) (by rsimp; exact h14)
  rw [show i + rows = rows + i by omega] at a2
  refine wp_load a2 hR ?_
  refine wp_load (eval_aW (by rsimp; exact h15) _) hn ?_
  fstep; fstep
  set n := point.size with hn'
  set mm := min lr n with hmm
  set Q := (point.toList.map EW.toE).take lr with hQ
  have hQl : Q.length = mm := by simp [hQ, hmm, hn']
  have hres : ∀ {a b : UInt64}, eOf a b = (paddingWeight (point.extract 0 lr) R).toE →
      a = (paddingWeight (point.extract 0 lr) R).c0 ∧ b = (paddingWeight (point.extract 0 lr) R).c1 :=
    fun h ↦ eOf_eq_toE.mp h
  have hpw : (paddingWeight (point.extract 0 lr) R).toE =
      (1 + eOfNat ((R >>> mm) % 2)) * padAcc R Q 0 1 := by
    rw [paddingWeight_list]
    congr 4
    · simp [hmm, hn']
    · simp [hQ, Array.toList_extract, List.extract_eq_take_drop]
  refine wp_then (Q := fun u ↦ u.reg .rsi = mm.toUInt64 ∧ u.reg .rbp = R.toUInt64 ∧
      u.reg .r9 = 1 ∧ u.reg .r10 = 0 ∧ u.reg .r15 = p ∧ u.mem = s.mem ∧ RegsFrame selRegs s u)
    (wp_ite_of (cmp_ltu_reg (a := n) (b := lr) (by omega) (by omega) (by rsimp) (by rsimp))
      (fun ht ↦ WP.ins rfl ?_) (fun he ↦ WP.skip ?_)) fun u₀ ⟨c0, c1, c2, c3, c4, c5, c6⟩ ↦ ?_
  · have : n < lr := of_decide_eq_true ht
    refine ⟨?_, by rsimp, by rsimp, by rsimp, by rsimp; exact h15, by rsimp, by rf_tac⟩
    rsimp; rw [hmm, Nat.min_eq_right (by omega)]
  · have : ¬ n < lr := of_decide_eq_false he
    refine ⟨?_, by rsimp, by rsimp, by rsimp, by rsimp; exact h15, by rsimp, by rf_tac⟩
    rsimp; rw [hmm, Nat.min_eq_left (by omega)]
  fstep
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ t ≤ mm, u.reg .rsi = (mm - t).toUInt64 ∧
      u.reg .rbp = (R >>> t).toUInt64 ∧ u.reg .r13 = wd p (pointR.off + 2 * t) ∧
      padAcc R (Q.drop t) t (eOf (u.reg .r9) (u.reg .r10)) = padAcc R Q 0 1 ∧ u.mem = s.mem ∧
      RegsFrame selRegs s u)
    (fun u ↦ (u.reg .rsi).toNat)
  · refine ⟨0, by omega, by rsimp; rw [c0, Nat.sub_zero], by rsimp; rw [c1]; rfl, ?_, ?_, by rsimp; exact c5,
      by rf_tac; exact c6⟩
    · rsimp; rw [eval_aW c4, Nat.mul_zero, Nat.add_zero]
    · rsimp; rw [c2, c3, eOf_one, List.drop_zero]
  · rintro u ⟨t, ht, hsi, hbp, h13, hI, hm, hf⟩ hc
    rw [cmp_ne_zero (a := mm - t) (by omega) hsi] at hc
    have htm : t < mm := by simp at hc; omega
    have htn : t < n := by omega
    obtain ⟨hc0, hc1⟩ := hp t htn
    fstep; fstep; fstep; fstep
    refine wp_load (x := wd p (pointR.off + 2 * t))
      (by rw [Transcript.eval_at]; rsimp; rw [h13, UInt64.add_zero])
      (by rsimp; rw [hm]; exact hc0) ?_
    fstep
    refine wp_load (x := wd p (pointR.off + 2 * t + 1)) (by
        rw [Transcript.eval_at]; rsimp
        rw [h13, show (8 : UInt64) = (8 * 1 : Nat).toUInt64 from rfl, wd_add])
      (by rsimp; rw [hm]; exact hc1) ?_
    refine wp_then (emul_spec _) fun u₁ ⟨e1, e2, e3⟩ ↦ ?_
    have k : ∀ r ∉ eRegs, r ≠ .r11 → r ≠ .r12 → u₁.reg r = u.reg r := fun r hr h11 h12 ↦ by
      rw [e3 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨ha, -, -, -, -, h9, -⟩ := hr
      simp [ha, h9, h11, h12]
    fstep; fstep; fstep; fstep; fstep; fstep; fstep; fdone
    rsimp at e1 e2
    have kbp : u₁.reg .rbp = u.reg .rbp := k .rbp (by decide) (by decide) (by decide)
    have k13 : u₁.reg .r13 = u.reg .r13 := k .r13 (by decide) (by decide) (by decide)
    have ksi : u₁.reg .rsi = u.reg .rsi := k .rsi (by decide) (by decide) (by decide)
    have hRt := shr_lt hRb t
    have hcf := flip_eq hRt
    have hQt : Q[t]'(by omega) = point[t].toE := by simp [hQ]
    refine ⟨⟨t + 1, by omega, ?_, ?_, ?_, ?_, e2.trans hm, ?_⟩, ?_⟩
    · rw [ksi, hsi, toUInt64_sub_one (by omega) (by omega), Nat.sub_sub]
    · rw [kbp, hbp, toUInt64_shr_one hRt, ← Nat.shiftRight_add]
    · rw [k13, h13, show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]; congr 1
    · have key : eOf (u₁.reg .r9 ^^^ ((u₁.reg .rbp &&& 1) ^^^ 1)) (u₁.reg .r10) =
          (1 + eOfNat ((R >>> t) % 2)) * point[t].toE +
            (1 + eOfNat ((R >>> t) % 2) + point[t].toE) * eOf (u.reg .r9) (u.reg .r10) := by
        rw [kbp, hbp, eOf_xor_lo', hcf, e1, hbp, eOf_xor_lo' (u.reg .r9), eOf_xor_lo' point[t].c0, hcf,
          show eOf point[t].c0 point[t].c1 = point[t].toE from rfl]
        exact padStep _ _ _ (eOfNat_bit _ (bit_lt R t))
      rw [key, ← hI, List.drop_eq_getElem_cons (by omega : t < Q.length), padAcc.eq_2, hQt]
    · intro r hr
      have hr' := hr
      simp only [selRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr'
      have hk : r ∉ eRegs := by simp [eRegs, *]
      simp only [QState.setReg_reg, h1, h5, h6, h8, h12, ↓reduceIte, k r hk h10 h11]
      exact hf r hr
    · rw [ksi, hsi, toUInt64_sub_one (by omega) (by omega), Transcript.toNat_toUInt64 (by omega),
        Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨t, ht, hsi, hbp, h13, hI, hm, hf⟩ hc
    rw [cmp_ne_zero (a := mm - t) (by omega) hsi] at hc
    have htm : t = mm := by simp at hc; omega
    rw [htm, List.drop_eq_nil_of_le (by omega), padAcc] at hI
    rw [htm] at hbp
    have hRt := shr_lt hRb mm
    have hbit := toUInt64_and_one hRt
    apply WP.blk_cons
    have hpw' := hpw
    rw [← hI] at hpw'
    rcases Nat.mod_two_eq_zero_or_one (R >>> mm) with h0 | h1
    · refine wp_ite_true (by rw [test_bit hRt hbp, h0]; rfl) (WP.skip (WP.blk_nil ?_))
      rw [h0, eOfNat_eq', show (0 : Nat).toUInt64 = 0 from rfl, eOf_zero, add_zero, one_mul] at hpw'
      exact ⟨(hres hpw'.symm).1, (hres hpw'.symm).2, hm, hf⟩
    · refine wp_ite_false (by rw [test_bit hRt hbp, h1]; rfl) ?_
      fstep; fstep; fdone
      rw [h1, eOfNat_eq', show (1 : Nat).toUInt64 = 1 from rfl, eOf_one, one_add_one_eq_two, two_E,
        zero_mul, ← eOf_zero] at hpw'
      exact WP.blk_nil ⟨(hres hpw'.symm).1, (hres hpw'.symm).2, hm, by rf_tac; exact hf⟩

end NativeVm.Code.P3
