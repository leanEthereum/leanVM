module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.First

/-!
# `verify_stacked_opening`: the target's loop, its pieces (x86-64)

`Acc` across a block keeping its registers and words (`Acc.blk`) and across a call (`Acc.call`),
for an equal count of placed claims (`Acc.congr`). `Done i`: claim `i` done, at
`NativeRustcVmX64.Vm.VerifyStackedOpening.label_25` (`b33`); `mid_b33` steps to the next claim (`Tgt (i + 1)`) or after the
last to `NativeRustcVmX64.Vm.VerifyStackedOpening.label_30` (`b38`). The claim's environment (`clEnv`, `Ok.cl_wf`,
`Tgt.m_claim`), its column (`Ok.col_load`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

@[expose] public section

/-- **Claim `i` done**, at `NativeRustcVmX64.Vm.VerifyStackedOpening.label_25`. -/
structure Done [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (m0 : MachineData) (i : Nat) (st : MachineData) :
    Prop where
  acc : Acc a s layout target cs value m0 (i + 1) st
  w96 : NativeRustcVm.WordAt st.dmem (off (stackBelow m0 512) 96)
    (UInt64.ofBitVec (off (layA m0) 120))
  hi : i < cs.size
  rbp : (reg st .rbp).toNat = 608 * i
  r15 : (reg st .r15).toNat = 608 * cs.size

/-- Claim `i`'s environment: the frame and the claim. -/
abbrev clEnv (m0 st : MachineData) (i : Nat) (ret : BitVec 64) : Env :=
  frameEnv m0 st 512 [(off (clA m0) (8 + 608 * i), 608)] (fun _ ↦ 0) ret

/-- The registers `Acc` names. -/
def accRegs : List Reg64 := [.rbx, .r12, .r13, .r14]

end

public section

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- `Acc` for an equal count of placed claims. -/
theorem Acc.congr {i j : Nat} {st : MachineData} (hc : Acc a s layout target cs value m0 i st)
    (he : placedOf layout cs j = placedOf layout cs i) : Acc a s layout target cs value m0 j st :=
  ⟨hc.ok, hc.out, hc.fw, by rw [he]; exact hc.hi72, by rw [he]; exact hc.rbx, hc.r13,
    by rw [he]; exact hc.r14, hc.r12⟩

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

/-- **`Acc` across a block** keeping its registers and its words. -/
theorem Acc.blk {i : Nat} {st st' : MachineData} (hc : Acc a s layout target cs value m0 i st)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 st 512 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 512 rest vars ret) S st') (hok : Ok m0 st' 8)
    (hs : NativeRustcVm.SameOutside st.dmem st'.dmem
      (NativeRustcVm.InRange (stackBelow m0 512) 512))
    (hin : writesIn S = true) (hmiss : missAll [24, 40, 48, 56, 64, 32, 80, 88, 72] S = true)
    (hk : keeps accRegs S = true) : Acc a s layout target cs value m0 i st' := by
  have hfw := FW.block_os hwf hm hin (hc.fw.append (FW.one hc.hi72))
    [24, 40, 48, 56, 64, 32, 80, 88, 72] rfl hmiss
  have kr : ∀ r ∈ accRegs, reg st' r = reg st r := fun r hr ↦ kept_reg hm hk hr
  exact ⟨hok, Outs.keep h hc.out (hm.kept hwf) (h.blk_stack hs), hfw.left, hfw.right.get (by simp),
    by rw [kr .rbx (by simp [accRegs])]; exact hc.rbx,
    by rw [kr .r13 (by simp [accRegs])]; exact hc.r13,
    by rw [kr .r14 (by simp [accRegs])]; exact hc.r14,
    by rw [kr .r12 (by simp [accRegs])]; exact hc.r12⟩

/-- **`Acc` across a call** changing the stack only. -/
theorem Acc.call {i : Nat} {st st' : MachineData} (hc : Acc a s layout target cs value m0 i st)
    (hok : Ok m0 st' 8) (hfs : FrameSame m0 st.dmem st'.dmem) (hk : Keeps st.dmem st'.dmem)
    (hs : NativeRustcVm.SameOutside st.dmem st'.dmem (NativeRustcVm.InRange
      (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack))
    (hcs : ∀ r, calleeSaved r = true → reg st' r = reg st r) :
    Acc a s layout target cs value m0 i st' := by
  have hfw := (hc.fw.append (FW.one hc.hi72)).call hfs
    (le_of_map [24, 40, 48, 56, 64, 32, 80, 88, 72] rfl (by decide))
  exact ⟨hok, Outs.keep h hc.out hk hs, hfw.left, hfw.right.get (by simp),
    by rw [hcs .rbx rfl]; exact hc.rbx, by rw [hcs .r13 rfl]; exact hc.r13,
    by rw [hcs .r14 rfl]; exact hc.r14, by rw [hcs .r12 rfl]; exact hc.r12⟩

/-- Claim `i`'s environment is well formed. -/
theorem Ok.cl_wf {st : MachineData} {o : Nat} (hok : Ok m0 st o) {i : Nat} (hi : i < cs.size)
    {ret : BitVec 64} : (clEnv m0 st i ret).WF := by
  have hn := h.n_le
  have hc := (h.ins _ mem_cl).1
  have hcb : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
  simp only [hcb] at hc
  have hcn : (clA m0).toNat + 97288 ≤ 2 ^ 64 := hc.1.2
  have ho : (off (clA m0) (8 + 608 * i)).toNat = (clA m0).toNat + (8 + 608 * i) :=
    toNat_off (by omega)
  refine hok.wf1 h (mapped_off hc.1.1 (by omega)) (noWrap_off' hc.1.2 (by omega) (by omega)) ?_
  have : NativeRustcVm.Apart (clA m0) 97288 (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8) := hc.2
  unfold NativeRustcVm.Apart at this ⊢
  rw [ho]
  omega

/-- Claim `i`'s column, loaded. -/
theorem Ok.col_load {st : MachineData} {o : Nat} (hok : Ok m0 st o) {i : Nat} (hi : i < cs.size)
    {ret : BitVec 64} : ((clEnv m0 st i ret).load 1 0 8).toNat = cs[i].column := by
  rw [load_ofMachine (r := 1) (w := cs[i].column.toUInt64) rfl (by
    rw [off_zero]; exact hok.col h hi)]
  exact u64n ((hok.cl h).claims _ hi).column_lt

/-- Claim `i`'s value, loaded. -/
theorem Ok.val_load {st : MachineData} {o : Nat} (hok : Ok m0 st o) {i : Nat} (hi : i < cs.size)
    {ret : BitVec 64} : (clEnv m0 st i ret).load 1 592 8 = cs[i].value.c0.toBitVec ∧
      (clEnv m0 st i ret).load 1 (592 + 8) 8 = cs[i].value.c1.toBitVec :=
  ew_loads (b := off (clA m0) (8 + 608 * i)) (n := 608) rfl ((hok.cl h).claims _ hi).value

end

theorem clMatch [Labels] {m0 st : MachineData} {i : Nat} {ret : BitVec 64}
    (hok : Ok m0 st 8) (h13 : reg st .r13 = off (clA m0) 8) (hbp : (reg st .rbp).toNat = 608 * i) :
    Match (clEnv m0 st i ret) claimS st :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok.fr.rsp_eval, trivial⟩ trivial trivial
    ⟨by
      show (Sym.bin .add .W64 (.reg .r13) (.reg .rbp)).eval (clEnv m0 st i ret) = _
      rw [eval_add64]
      show reg st .r13 + reg st .rbp = _ + BitVec.ofInt 64 0
      rw [h13, bv_of_toNat hbp, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, off_add]
      rfl, trivial⟩

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **`b33`**: to the next claim, or after the last to `b38`. -/
theorem mid_b33 (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b33Offset))
    (hM : Done a s layout target cs value m0 i st.data) {R : MachineState → Prop}
    (cont1 : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b34Offset) →
      Tgt a s layout target cs value m0 (i + 1) st'.data → Eventually (step1 Host.exe) R st')
    (cont2 : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b38Offset) →
      Acc a s layout target cs value m0 cs.size st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hM.acc.ok
  have hn := h.n_le
  have hi := hM.hi
  refine h.run hp b33_in_code (List.cons_ne_nil _ _) hpc hok (vars := fun _ ↦ 0) (hok.wf0 h)
    hok.m_reg run_b33 (o := 8) (by decide +kernel) (by decide) fun st1 hok1 hs1 hm1 hpc1 ↦ ?_
  have hacc1 := Acc.blk h hM.acc (hok.wf0 h) hm1 hok1 hs1 rfl (by decide +kernel)
    (by decide +kernel)
  have hw96 := (FW.block_os (L := [(96, _)]) (hok.wf0 h) hm1 rfl (FW.one hM.w96) [96] rfl
    (by decide +kernel)).get List.mem_cons_self
  have hrbp : (reg st1.data .rbp).toNat = 608 * (i + 1) := by
    rw [show reg st1.data .rbp = _ from hm1.regs .rbp _ rfl, eval_add64]
    show (BitVec.ofNat 64 608 + reg st.data .rbp).toNat = _
    rw [toNat_add_small (by rw [hM.rbp]; simp; omega), hM.rbp]
    simp
    omega
  have h15 : (reg st1.data .r15).toNat = 608 * cs.size := by
    rw [regKeep hm1 .r15 rfl]; exact hM.r15
  simp only [PcOk] at hpc1
  rw [eval_eq64] at hpc1
  have hc : ((Sym.reg .r15).eval (frameEnv m0 st.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b33Offset + b33.length)).toBitVec)).toNat =
      ((Sym.bin .add .W64 (.lit 608) (.reg .rbp)).eval (frameEnv m0 st.data 512 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b33Offset + b33.length)).toBitVec)).toNat ↔ i + 1 = cs.size := by
    rw [← show reg st1.data .rbp = _ from hm1.regs .rbp _ rfl, hrbp]
    show (reg st.data .r15).toNat = _ ↔ _
    rw [hM.r15]
    omega
  by_cases he : i + 1 = cs.size
  · simp only [hc.mpr he, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_30_at] at hpc1
    exact cont2 st1 hpc1 (he ▸ hacc1)
  · have hne := mt hc.mp he
    simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact cont1 st1 (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b33_next))
      ⟨hacc1, hw96, by omega, hrbp, h15⟩

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
