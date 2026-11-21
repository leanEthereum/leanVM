module

public import NativeVm.Code.Phase3.SelCode
public import NativeVm.Code.Phase3.LayoutBase
public import NativeVm.Equiv.Field

/-!
# Phase 3's selectors: `eqAbove`

`eqAb_spec`: `A := eqAbove ⟨vc, idx⟩ point`, the placement at words `src + 2 i`, `src + 2 i + 1`
(`r14 = 2 i`), the point's `n` coordinates at `pointR`, `n` at `depthR`. Through `EW.toE`, it is
`eqEval` of the bits of `idx` from bit `vc` and the point's coordinates from `vc`
(`eqAbove_list`); the code multiplies one factor `1 + bit + y` at a time.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field
open LeanVM.Protocol.Verifier (eOfNat)

/-! ## Words and elements -/

/-- `eOf a b` is the element of the lanes `⟨a, b⟩`. -/
theorem eOf_mk (a b : UInt64) : eOf a b = (EW.mk a b).toE := rfl

theorem eOfNat_eq' (n : Nat) : eOfNat n = eOf n.toUInt64 0 := by
  rw [← NativeVm.Equiv.EW.toE_ofNat]; rfl

/-- The low bit of a word. -/
theorem toUInt64_and_one {n : Nat} (h : n < 2 ^ 64) : n.toUInt64 &&& 1 = (n % 2).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, Transcript.toNat_toUInt64 h, Transcript.toNat_toUInt64 (by omega)]
  simp [Nat.and_one_is_mod]

/-- A word shifted right once. -/
theorem toUInt64_shr_one {n : Nat} (h : n < 2 ^ 64) : n.toUInt64 >>> 1 = (n >>> 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, Transcript.toNat_toUInt64 h, Transcript.toNat_toUInt64 (by rw [Nat.shiftRight_eq_div_pow]; omega)]
  rfl

/-- The factor `1 + bit + y` of `eqEval`, as the code forms it. -/
theorem eqFactor (c0 c1 b : UInt64) :
    eOf (c0 ^^^ b ^^^ 1) c1 = 1 + eOf b 0 + eOf c0 c1 := by
  rw [eOf_xor_one, show c1 = c1 ^^^ 0 from (UInt64.xor_zero).symm, eOf_add, UInt64.xor_zero]
  ring

/-! ## `eqAbove` as lists -/

theorem eqAbove_list (vc idx : Nat) (point : Array EW) :
    (eqAbove ⟨vc, idx⟩ point).toE =
      LeanVM.Protocol.Verifier.eqEval
        ((List.range (point.size - vc)).map fun t ↦ eOfNat ((idx >>> (vc + t)) % 2))
        ((point.toList.map EW.toE).drop vc) := by
  rw [eqAbove, NativeVm.Equiv.toE_eqEval, NativeVm.Equiv.toList_map_selectorPoint]
  simp only [LeanVM.Protocol.Verifier.selectorPoint, Nat.shiftRight_add, Array.toList_extract,
    List.extract_eq_take_drop, List.map_take, List.map_drop]
  rw [List.take_of_length_le (by simp)]

theorem eqEval_nil (ys : List LeanVM.Parameters.E) : LeanVM.Protocol.Verifier.eqEval [] ys = 1 := by
  simp [LeanVM.Protocol.Verifier.eqEval]

/-! ## The code -/

/-- The registers the selectors' code writes: all but `rdi`, `rsp`, `r14`, `r15`. -/
abbrev selRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13]

variable {s : QState} {F : QState → Prop}

/-- The point's coordinates, element `t` at words `pointR.off + 2 t`, `+ 1`. -/
def PointAt (mem : UInt64 → Option UInt64) (p : UInt64) (point : Array EW) : Prop :=
  ∀ t (h : t < point.size), mem (wd p (pointR.off + 2 * t)) = some point[t].c0 ∧
    mem (wd p (pointR.off + 2 * t + 1)) = some point[t].c1

theorem eqAb_spec {p : UInt64} {src i vc idx : Nat} {point : Array EW}
    (h15 : s.reg .r15 = p) (h14 : s.reg .r14 = (2 * i).toUInt64)
    (hvc : s.mem (wd p (src + 2 * i)) = some vc.toUInt64)
    (hidx : s.mem (wd p (src + 2 * i + 1)) = some idx.toUInt64)
    (hn : s.mem (wd p depthR.off) = some point.size.toUInt64)
    (hvb : vc < 2 ^ 64) (hib : idx < 2 ^ 64) (hps : point.size < 64)
    (hp : PointAt s.mem p point) :
    WP (eqAb src) s (fun s' ↦ s'.reg .r9 = (eqAbove ⟨vc, idx⟩ point).c0 ∧
      s'.reg .r10 = (eqAbove ⟨vc, idx⟩ point).c1 ∧ s'.mem = s.mem ∧ RegsFrame selRegs s s') F := by
  have a1 := eval_aI (s := s) (k := src) h15 h14
  rw [show 2 * i + src = src + 2 * i by omega] at a1
  unfold eqAb
  refine wp_load a1 hvc ?_
  have a2 := eval_aI (s := s.setReg .rsi vc.toUInt64) (ix := .r14) (i := 2 * i) (k := src + 1) (by rsimp; exact h15)
    (by rsimp; exact h14)
  rw [show 2 * i + (src + 1) = src + 2 * i + 1 by omega] at a2
  refine wp_load a2 hidx ?_
  refine wp_load (eval_aW (by rsimp; exact h15) _) hn ?_
  fstep; fstep
  set n := point.size with hn'
  have hres : ∀ {a b : UInt64}, eOf a b = (eqAbove ⟨vc, idx⟩ point).toE →
      a = (eqAbove ⟨vc, idx⟩ point).c0 ∧ b = (eqAbove ⟨vc, idx⟩ point).c1 :=
    fun h ↦ eOf_eq_toE.mp h
  apply WP.blk_cons
  refine wp_ite_of (cmp_geu_reg (a := vc) (b := n) (by omega) (by omega) (by rsimp) (by rsimp))
    (fun ht ↦ ?_) (fun he ↦ ?_)
  · -- no coordinate above the placement
    have hle : n ≤ vc := of_decide_eq_true ht
    refine WP.skip (WP.blk_nil ?_)
    have e := hres (a := 1) (b := 0) (by
      rw [eqAbove_list, show n - vc = 0 by omega, List.range_zero, List.map_nil, eqEval_nil, eOf_one])
    refine ⟨by rsimp; exact e.1, by rsimp; exact e.2, by rsimp, by rf_tac⟩
  · have hlt : vc < n := by have := of_decide_eq_false he; omega
    fstep; fstep
    -- skip the coordinates below the placement
    apply WP.blk_cons
    apply WP.loop (fun u ↦ ∃ t ≤ vc, u.reg .rsi = (vc - t).toUInt64 ∧
        u.reg .rbp = (idx >>> t).toUInt64 ∧ u.reg .r13 = wd p (pointR.off + 2 * t) ∧
        u.reg .r11 = (n - vc).toUInt64 ∧ u.reg .r9 = 1 ∧ u.reg .r10 = 0 ∧ u.mem = s.mem ∧
        RegsFrame selRegs s u) (fun u ↦ (u.reg .rsi).toNat)
    · refine ⟨0, by omega, by rsimp; rfl, by rsimp; rfl, ?_, ?_, by rsimp, by rsimp, by rsimp, by rf_tac⟩
      · rsimp; rw [eval_aW (by rsimp; exact h15), Nat.mul_zero, Nat.add_zero]
      · rsimp; rw [toUInt64_sub (by omega) (by omega)]
    · rintro u ⟨t, ht, hsi, hbp, h13, h11, h9, h10, hm, hf⟩ hc
      rw [cmp_ne_zero (a := vc - t) (by omega) hsi] at hc
      have htv : t < vc := by simp at hc; omega
      fstep; fstep; fstep; fdone
      refine ⟨⟨t + 1, by omega, ?_, ?_, ?_, h11, h9, h10, hm, by rf_tac; exact hf⟩, ?_⟩
      · rw [hsi, toUInt64_sub_one (by omega) (by omega), Nat.sub_sub]
      · rw [hbp, toUInt64_shr_one (by rw [Nat.shiftRight_eq_div_pow]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hib),
          Nat.shiftRight_add]
      · rw [h13, show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]; congr 1
      · rw [hsi, toUInt64_sub_one (by omega) (by omega), Transcript.toNat_toUInt64 (by omega),
          Transcript.toNat_toUInt64 (by omega)]
        omega
    rintro u ⟨t, ht, hsi, hbp, h13, h11, h9, h10, hm, hf⟩ hc
    rw [cmp_ne_zero (a := vc - t) (by omega) hsi] at hc
    have htv : t = vc := by simp at hc; omega
    rw [htv] at hbp h13
    fstep
    -- the factors
    set m := n - vc with hm'
    set Ls := (List.range m).map fun t ↦ eOfNat ((idx >>> (vc + t)) % 2) with hLs
    set Ps := (point.toList.map EW.toE).drop vc with hPs
    have hLl : Ls.length = m := by simp [hLs]
    have hPl : Ps.length = m := by simp [hPs, hm', hn']
    apply WP.loop (fun u ↦ ∃ t ≤ m, u.reg .rsi = (m - t).toUInt64 ∧
        u.reg .rbp = (idx >>> (vc + t)).toUInt64 ∧ u.reg .r13 = wd p (pointR.off + 2 * (vc + t)) ∧
        eOf (u.reg .r9) (u.reg .r10) * LeanVM.Protocol.Verifier.eqEval (Ls.drop t) (Ps.drop t) =
          LeanVM.Protocol.Verifier.eqEval Ls Ps ∧ u.mem = s.mem ∧ RegsFrame selRegs s u)
      (fun u ↦ (u.reg .rsi).toNat)
    · refine ⟨0, by omega, by rsimp; exact h11, by rsimp; rw [Nat.add_zero]; exact hbp, ?_, ?_,
        hm, by rf_tac; exact hf⟩
      · rsimp; rw [h13, Nat.add_zero]
      · rsimp; rw [h9, h10, eOf_one, one_mul, List.drop_zero, List.drop_zero]
    · rintro u ⟨t, ht, hsi, hbp, h13, hI, hm, hf⟩ hc
      rw [cmp_ne_zero (a := m - t) (by omega) hsi] at hc
      have htm : t < m := by simp at hc; omega
      have hvt : vc + t < n := by omega
      obtain ⟨hc0, hc1⟩ := hp (vc + t) hvt
      refine wp_load (by rw [Transcript.eval_at, h13, Field.int64Zero_toUInt64, UInt64.add_zero]) (by rw [hm]; exact hc0) ?_
      fstep; fstep; fstep; fstep
      refine wp_load (x := wd p (pointR.off + 2 * (vc + t) + 1)) (by
          rw [Transcript.eval_at]; rsimp
          rw [h13, show (8 : UInt64) = (8 * 1 : Nat).toUInt64 from rfl, wd_add])
        (by rsimp; rw [hm]; exact hc1) ?_
      refine wp_then (emul_spec _) fun u₁ ⟨e1, e2, e3⟩ ↦ ?_
      have k : ∀ r ∉ eRegs, r ≠ .r11 → r ≠ .r12 → u₁.reg r = u.reg r := fun r hr h11 h12 ↦ by
        rw [e3 r hr]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hr.1, h11, h12]
      fstep; fstep; fstep; fdone
      rsimp at e1 e2
      have kbp : u₁.reg .rbp = u.reg .rbp := k .rbp (by decide) (by decide) (by decide)
      have k13 : u₁.reg .r13 = u.reg .r13 := k .r13 (by decide) (by decide) (by decide)
      have ksi : u₁.reg .rsi = u.reg .rsi := k .rsi (by decide) (by decide) (by decide)
      have hib' : idx >>> (vc + t) < 2 ^ 64 := by
        rw [Nat.shiftRight_eq_div_pow]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hib
      have hL : Ls[t]'(by omega) = eOfNat ((idx >>> (vc + t)) % 2) := by simp [hLs]
      have hP : Ps[t]'(by omega) = point[vc + t].toE := by simp [hPs]
      refine ⟨⟨t + 1, by omega, ?_, ?_, ?_, ?_, e2.trans hm, ?_⟩, ?_⟩
      · rw [ksi, hsi, toUInt64_sub_one (by omega) (by omega), Nat.sub_sub]
      · rw [kbp, hbp, toUInt64_shr_one hib', ← Nat.shiftRight_add, ← Nat.add_assoc]
      · rw [k13, h13, show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]; congr 1
      · rw [← hI, e1, hbp, toUInt64_and_one hib', eqFactor, ← eOfNat_eq',
          List.drop_eq_getElem_cons (by omega : t < Ls.length),
          List.drop_eq_getElem_cons (by omega : t < Ps.length), eqEval_cons, hL, hP, mul_assoc]
        rfl
      · intro r hr
        have hr' := hr
        simp only [selRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr'
        have hk : r ∉ eRegs := by simp [eRegs, *]
        simp only [QState.setReg_reg, h5, h6, h12, ↓reduceIte, k r hk h10 h11]
        exact hf r hr
      · rw [ksi, hsi, toUInt64_sub_one (by omega) (by omega), Transcript.toNat_toUInt64 (by omega),
          Transcript.toNat_toUInt64 (by omega)]
        omega
    · rintro u ⟨t, ht, hsi, hbp, h13, hI, hm, hf⟩ hc
      rw [cmp_ne_zero (a := m - t) (by omega) hsi] at hc
      have htm : t = m := by simp at hc; omega
      rw [htm, List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega), eqEval_nil,
        mul_one, ← eqAbove_list] at hI
      exact WP.blk_nil ⟨(hres hI).1, (hres hI).2, hm, hf⟩

end NativeVm.Code.P3
