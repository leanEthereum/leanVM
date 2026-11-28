module

public import NativeRustcVmArm.Bus.BytecodeShare.Copy

/-!
# `bytecode_share`: the copy's loops

`b12` sets the point's end and length and skips an empty `bytecode_low`; `b13` sends a single
element to the odd tail (`b14`), more to the pair loop (`b17`). The pair loop's head
`.LBytecodeShare_12` (`PairHead`): `b18` copies two elements; at the even end `b19` goes to
`b22`, else to the odd tail `.LBytecodeShare_14` (`b20`, then `b21` copies the last element).
`copy_spec`: from `b12` to the return, given what `b22` needs (`Fin`).
-/

namespace NativeRustcVmArm.Bus.BytecodeShare

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BytecodeShare
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr

public section

/-- The writes of a block in a three-region environment, in region 2, inside the outputs. -/
theorem writeOk_r2 {m : MachineData} {vars : Nat → BitVec 64} {F : Nat}
    {slots : List (Nat × XReg)} {outs : BitVec 64 → Prop} {b0 b1 b2 : BitVec 64} {n1 n2 : Nat}
    (hout2 : ∀ i < n2, outs (b2 + BitVec.ofNat 64 i)) {w : Write}
    (h : w.r = 2 ∧ w.off + w.n ≤ n2) :
    WriteOk (Env.ofMachine m [(b0, F), (b1, n1), (b2, n2)] vars) F slots outs w := by
  refine .inr ⟨by omega, fun b sz hb ↦ ?_⟩
  change [(b0, F), (b1, n1), (b2, n2)][w.r]? = some (b, sz) at hb
  rw [h.1] at hb
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  exact ⟨h.2, hout2⟩

/-- What a three-region block, writing region 2 only, changed. -/
theorem same_r2 [Labels] {m m' : MachineData} {b0 b1 b2 : BitVec 64} {F n1 n2 : Nat}
    {S : SState} (hm : Match (Env.ofMachine m [(b0, F), (b1, n1), (b2, n2)]) S m')
    (hwf : (Env.ofMachine m [(b0, F), (b1, n1), (b2, n2)]).WF)
    (h : ∀ w ∈ S.mem, w.r = 2 ∧ w.off + w.n ≤ n2) :
    SameOutside m.dmem m'.dmem (InRange b2 n2) :=
  NativeRustcVm.SameOutside.mono (hm.sameOutside hwf) fun q hq ↦ by
    obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
    obtain ⟨hr, hle⟩ := h w hw
    change [(b0, F), (b1, n1), (b2, n2)][w.r]? = some (b, sz) at hb
    rw [hr] at hb
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have := hwf.noWrap 2 b2 n2 rfl
    rw [Sym.inRange_iff this]
    omega

theorem eval_ptr_off [Labels] (m : MachineData) (rs : List (BitVec 64 × Nat)) {r n : Nat}
    {b : BitVec 64} (hb : rs[r]? = some (b, n)) (o : Nat) :
    (Sym.ptr r (o : Int)).eval (Env.ofMachine m rs) = b + BitVec.ofNat 64 o := by
  simp only [Sym.eval, Env.base_ofMachine m rs _ hb, BitVec.ofInt_natCast]

/-- The pair loop's head `.LBytecodeShare_12`, `j` elements copied. -/
structure PairHead (m0 m : MachineData) (sh v : EW) (j : Nat) (st : MachineData) : Prop where
  cp : Cp m0 m sh v j st
  even : j % 2 = 0
  lt : j + 2 ≤ m0.regs.X4.toNat - m0.regs.X4.toNat % 2
  x10 : (st.regs.getXReg .X10).toNat = m0.regs.X4.toNat - m0.regs.X4.toNat % 2
  x13 : (st.regs.getXReg .X13).toNat + j = m0.regs.X4.toNat - m0.regs.X4.toNat % 2
  x11 : (st.regs.getXReg .X11).toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j + 16)
  x12 : (st.regs.getXReg .X12).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * j + 16)

variable {a : DecArea} {s0 : TState} {m0 m : MachineData} {k : Nat} {sh v : EW}

/-- `Cp` through a block that wrote nothing and kept the registers. -/
theorem Cp.ofRun [Labels] {j : Nat} {st st' : MachineData} {S : SState} (hc : Cp m0 m sh v j st)
    (hfr : Fr m0 432 bytecodeShareStack slots keep (outsP m0) st') (hd : st'.dmem = st.dmem)
    (hm : Match (Env.ofMachine st [(base m0 432, 432)]) S st')
    (hk : ([.X8, .X9, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26] : List XReg).all
      (fun r ↦ S.reg r == some (.reg r)) = true) : Cp m0 m sh v j st' := by
  have kk := fun r (hr : r ∈ ([.X8, .X9, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26] :
      List XReg)) ↦ mov_reg hm (beq_iff_eq.mp (List.all_eq_true.mp hk r hr))
  refine ⟨hfr, Regs.block hc.regs hm (by
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hk ⊢
      simp only [Bool.and_eq_true] at hk ⊢
      exact ⟨hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1,
        hk.2.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.2.2⟩),
    (kk .X8 (by simp)).trans hc.x8, by rw [kk .X9 (by simp)]; exact hc.x9, hc.le,
    fun i hi ↦ by rw [hd]; exact hc.cpy i hi, fun q hq ↦ by rw [hd]; exact hc.same q hq,
    by rw [hd]; exact hc.kept⟩

variable [Host]

/-- The continuations: `b22` with every element copied, the odd tail with one left. -/
structure Fin (a : DecArea) (s0 : TState) (m0 m : MachineData) (sh v : EW) (k : Nat) : Prop where
  fin : ∀ st, Cp m0 m sh v m0.regs.X4.toNat st →
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b22Offset)⟩

/-- The odd tail `.LBytecodeShare_14` (`b20`, `b21`): the last element copied. -/
theorem odd (hp : Placed code k) (h : BytecodeSharePre a s0 m0) (F : Fin a s0 m0 m sh v k)
    {j : Nat} {st : MachineData} (hc : Cp m0 m sh v j st)
    (h10 : (st.regs.getXReg .X10).toNat = j) (hj : j + 1 = m0.regs.X4.toNat) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b20Offset)⟩ := by
  obtain ⟨hS, -, -, -, -, -, hbl, -, hpo, -⟩ := pre_parts h
  have A := addr_of h
  have hN := A.sp
  have hlen := A.len
  refine Fr.runBlock hS N_ge rfl hc.fr (b20_in_code.trans hp.1 (by simp [b20])) run_b20 rfl rfl
    (by decide) (by decide) fun st1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have hc1 := Cp.ofRun hc hfr1 hd1 hm1 (by decide)
  have e10 := hm1.regs .X10 _ rfl
  have e11 := hm1.regs .X11 _ rfl
  have e12 := hm1.regs .X12 _ rfl
  simp only [Sym.eval, BinOp.apply, UnOp.apply, Sym.ext_W64, Sym.low_W64, Env.ofMachine_regs,
    shiftW] at e10 e11 e12
  have h10' : (st.regs.getXReg .X10).toBitVec.toNat < 64 := by
    rw [UInt64.toNat_toBitVec, h10]; omega
  rw [orr8 _ h10', UInt64.toNat_toBitVec, h10, hc.regs.x24] at e11
  rw [orr8 _ h10', UInt64.toNat_toBitVec, h10, hc.regs.x23] at e12
  have f10 : (st1.data.regs.getXReg .X10).toNat = 1 := by
    rw [← UInt64.toNat_toBitVec, e10, BitVec.toNat_sub_of_le, UInt64.toNat_toBitVec,
      UInt64.toNat_toBitVec, hc.regs.x22, h10]
    · omega
    · rw [BitVec.le_def, UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, hc.regs.x22, h10]; omega
  simp only [PcOk] at hpc1
  -- `b21`: the last element.
  have hj16 : 16 * j + 16 ≤ 16 * m0.regs.X4.toNat := by omega
  obtain ⟨hmB, hnwB, hB⟩ := sub_range (d := st1.data.dmem) (o := 16 * j) (n := 16)
    (fun i hi ↦ hc1.fr.kept _ (hbl.1.1 i hi)) A.bnw hj16
  obtain ⟨hmP, hnwP, hP⟩ := sub_range (d := st1.data.dmem) (o := 16 * j) (n := 16)
    (fun i hi ↦ hc1.fr.kept _ (hpo.1 i hi)) A.pnw (by show _ ≤ 1072; omega)
  have hB' := hB (by omega)
  have hP' := hP (by show _ < 1072; omega)
  have hwf : (Env.ofMachine st1.data [(base m0 432, 432),
      (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 16),
      (m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * j), 16)]).WF :=
    wf_frame3 hS N_ge hc1.fr.kept hmB hnwB hmP hnwP
      (by have := A.bst; unfold Apart at this ⊢; rw [hB']; omega)
      (by have := A.pst; rw [ptBytes_eq] at this; unfold Apart at this ⊢; rw [hP']; omega)
      (by have := A.pb; rw [ptBytes_eq] at this; unfold Apart at this ⊢; rw [hB', hP']; omega)
  have hm := match_frame3 (n1 := 16) (n2 := 16) (c1 := 8) (c2 := 8) hS N_ge rfl hc1.fr.sp
    (r1 := .X11) (r2 := .X12) (x1 := m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j))
    (x2 := m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * j))
    (by rw [e11, NativeRustcVm.addr_add_add]) (by rw [e12, NativeRustcVm.addr_add_add])
  refine exec_at (b21_in_code.trans hp.1 (by simp [b21])) run_b21 hwf hpc1 hm
    fun st2 hm2 hpc2 ↦ ?_
  have hW : ∀ w ∈ (after b21 frOne).mem, w.r = 2 ∧ w.off + w.n ≤ 16 := by
    rw [Bus.after_eq run_b21]; decide
  rw [Bus.after_eq run_b21] at hW
  have hfr2 : Fr m0 432 bytecodeShareStack slots keep (outsP m0) st2.data :=
    Fr.ofBlockW hc1.fr hm hm2 hwf rfl rfl (fun r hr ↦ absurd hr List.not_mem_nil) rfl N_ge hN
      slots_le fun w hw ↦ writeOk_r2 (fun i hi ↦ .inr (by
        rw [NativeRustcVm.addr_add_add]
        exact NativeRustcVm.inRange_add (by show _ < 1072; omega) (by show 1072 ≤ _; omega)))
        (hW w hw)
  have hs := same_r2 hm2 hwf hW
  have hcpy := copy_words hm2 (rd := 2) (rr := 1) (od := 0) (os := 0) (nw := 2) rfl rfl
    (by omega) (by rw [NativeRustcVm.addr_add_zero]; exact hmB) (by decide)
  have hb := Fr.bytes_eq hc1.fr hS A.bnw A.bst (b_not_outsP h)
  have hc2 : Cp m0 m sh v (j + 1) st2.data := by
    refine ⟨hfr2, Regs.block hc1.regs hm2 (by decide), (mov_reg hm2 rfl).trans hc1.x8,
      by rw [mov_reg hm2 rfl]; exact hc1.x9, by omega, fun i hi ↦ ?_, fun q hq ↦ ?_,
      kept_trans hc1.kept (hm2.kept hwf)⟩
    · rcases Nat.lt_or_ge i (16 * j) with hi' | hi'
      · rw [hs _ fun hq ↦ ?_]
        · exact hc1.cpy i hi'
        · rw [Sym.inRange_iff hnwP, hP', toNat_in A.pnw (by show _ < 1072; omega)] at hq
          omega
      · have e := hcpy (i - 16 * j) (by omega)
        simp only [Nat.zero_add, NativeRustcVm.addr_add_add] at e
        rw [show 16 * j + (i - 16 * j) = i by omega] at e
        rw [e, hb i (by omega)]
    · have hpn : m0.regs.X5.toBitVec.toNat + 1072 ≤ 2 ^ 64 := A.pnw
      have h1 : ¬InRange (m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * j)) 16 q := fun h' ↦ hq (by
        rw [Sym.inRange_iff hnwP, hP'] at h'
        rw [Sym.inRange_iff (by omega)]
        omega)
      have h2 : ¬InRange m0.regs.X5.toBitVec (16 * j) q := fun h' ↦ hq (by
        rw [Sym.inRange_iff (by omega)] at h' ⊢
        omega)
      rw [hs q h1]
      exact hc1.same q h2
  have hc : SBool.eval (Env.ofMachine st1.data [(base m0 432, 432),
      (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 16),
      (m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * j), 16)])
      (.not (.cmp .eq .W64 (.reg .X10) (.lit 1))) = false := by
    show (!(SBool.cmp .eq .W64 (.reg .X10) (.lit 1)).eval _) = false
    rw [eval_eq_lit _ _ _ _ (by decide), f10]
    rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc2
  refine at_pc hpc2 (F.fin _ ?_)
  rw [← hj]
  exact hc2

end

end NativeRustcVmArm.Bus.BytecodeShare
