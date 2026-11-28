module

public import NativeRustcVmArm.Whir.WhirLevels.Early
public import NativeRustcVmArm.Whir.State

/-!
# `whir_levels`: the entry

`b0` saves X30 and X19 to X28 in the 96-byte frame (`Fr.ofPrologue`) and branches to the
epilogue for no level (never: a ladder has at least `3`); `b1` keeps the arguments in X19 to X28
(`Regs`) and calls `fold_rounds` on level `0`'s fold (`Head 0`); `b2` tests its `None`, then
`level0` (`entry`).
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Layout.Ladder
open NativeRustcVmArm.Vm.WhirLevels

public section

theorem eval_dec [Labels] (env : Env) (r : XReg) :
    ((Sym.ite (.cmp .ult .W64 (.reg r) (.lit 1)) (.lit 0) (.bin .sub .W64 (.reg r) (.lit 1))).eval
      env).toNat = (env.regs r).toNat - 1 := by
  sym_simp
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  split
  · rename_i h
    rw [BitVec.ult_iff_lt, BitVec.lt_def, h1] at h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  · rename_i h
    rw [BitVec.ult_iff_lt, BitVec.lt_def, h1] at h
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]

section
variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **The entry**: the prologue, level `0`'s fold rounds, then `level0`. -/
theorem entry (hp : Placed code k0) (cs : Callees) (c : Ctx a s0 levels ba b claim m0 rate) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) ⟨m0, Host.addrOf (k0 + NativeRustcVmArm.Vm.WhirLevels.b0Offset)⟩ := by
  have hv := stack_val.1
  have hN := c.hN
  have hl6 := c.len_le
  have hlen := c.len
  let env0 := Env.ofMachine m0 [(base m0 96, 96)]
  have hwf0 : env0.WF := Env.wf_of ⟨⟨frame_mapped c.stack (by omega), base_noWrap (by omega)⟩,
    trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 := by
    refine match_ofMachine ⟨rfl, fun _ ↦ ?_, trivial⟩ ?_ trivial trivial trivial trivial
    · have e1 := base_toNat (m0 := m0) (F := 96) (by omega)
      have := c.stack.1
      show (base m0 96).toNat % 16 = 0
      omega
    · simp only [Sym.eval, Env.base_ofMachine_eq]
      show m0.regs.SP.toBitVec = base m0 96 + BitVec.ofInt 64 96
      rw [show BitVec.ofInt 64 96 = BitVec.ofNat 64 96 from rfl, base_add_eq]
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have ok0 := after_eq run_b0 ▸ ok_b0
  obtain ⟨oks, okm, oksp, ok29⟩ := ok0
  have hf1 : WFr m0 st1.data := Fr.ofPrologue (rs := []) hN (by omega) hm1 hwf0 oksp oks slots_le
    okm fun r hr ↦ by
      simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ok29
  -- `b0`'s branch: some level
  simp only [PcOk] at hpc1
  rw [eval_cmp_eq _ _ (by decide)] at hpc1
  have hx5 : ¬(env0.regs .X5).toNat = 0 := fun h ↦ by
    have : m0.regs.X5.toNat = 0 := h
    omega
  simp only [hx5, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  rw [show k0 + NativeRustcVmArm.Vm.WhirLevels.b0Offset + b0.length = k0 + NativeRustcVmArm.Vm.WhirLevels.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.WhirLevels.b0_next]] at hpc1
  -- what `b0` kept: the memory but the frame
  have hw1 : ∀ q, Written env0 (after b0 entryS) q → InRange (base m0 96) 96 q := fun q hq ↦
    written_r0 hwf0 rfl okm hq
  have hs1 : SameOutside m0.dmem st1.data.dmem (InRange (base m0 96) 96) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf0) fun q hq ↦ hw1 q
      (by rw [after_eq run_b0]; exact hq)
  have hfs : ∀ q, InRange (base m0 96) 96 q →
      InRange (stackBelow m0 whirLevelsStack) whirLevelsStack q := fun q hq ↦
    frame_sub hN (by omega) hq
  have hnN := base_noWrap (m0 := m0) (F := whirLevelsStack) hN
  have hfp := c.ts0.footprint
  have hts1 : TStateAt st1.data.dmem (tA m0) a s0 :=
    c.ts0.frame hf1.kept (fun q hq ↦ ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange c.tok.1 hfp.1.2
      hnN ht (hfs q hq), fun hd ↦ NativeRustcVm.Apart.not_inRange c.tok.2.1 hfp.2.1.2 hnN hd
        (hfs q hq)⟩) hs1
  have hws1 : WhirStateAt st1.data.dmem (pA m0) ⟨claim, #[], #[]⟩ :=
    c.ws0.agree fun j hj _ ↦ hs1 _ fun hq ↦ c.outs_not_frame (by omega)
      (Or.inl (NativeRustcVm.inRange_add (by unfold stateBytes at hj; unfold whirBytes; omega)
        (by have := c.pout.1.2.1; unfold NoWrap at this; omega))) hq
  -- `b1`
  have hx4 : (st1.data.regs.getXReg .X4).toBitVec = lvA m0 :=
    reg_val hm1 (r := .X4) (v := .reg .X4) rfl
  obtain ⟨hmap, hnw⟩ := levels_region c hf1 (n := 8) (by unfold levelBytes; omega)
  refine readBlock hf1 (inf hp b1_in_code (by simp [b1])) run_b1 hpc1 hx4 hmap hnw rfl rfl
    ⟨rfl, rfl⟩ fun st2 hf2 hd2 _ hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [show k0 + NativeRustcVmArm.Vm.WhirLevels.b1Offset + b1.length = k0 + NativeRustcVmArm.Vm.WhirLevels.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.WhirLevels.b1_next]] at hpc2
  have k1 : ∀ r : XReg, r ≠ .X8 → r ≠ .X24 → st1.data.regs.getXReg r = m0.regs.getXReg r :=
    fun r h8 h24 ↦ reg_of hm1 (v := .reg r) (by cases r <;> first | rfl | exact absurd rfl h8 |
      exact absurd rfl h24) rfl
  have hr2 : Regs m0 levels.length st2.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (reg_of hm2 (r := .X19) (v := .reg .X6) rfl rfl).trans (k1 .X6 (by decide) (by decide))
    · exact (reg_of hm2 (r := .X20) (v := .reg .X3) rfl rfl).trans (k1 .X3 (by decide) (by decide))
    · exact (reg_of hm2 (r := .X21) (v := .reg .X0) rfl rfl).trans (k1 .X0 (by decide) (by decide))
    · exact (reg_of hm2 (r := .X22) (v := .reg .X2) rfl rfl).trans (k1 .X2 (by decide) (by decide))
    · refine UInt64.toBitVec_inj.mp ((reg_val hm2 (r := .X23) rfl).trans ?_)
      exact (eval_ptr0 0).trans (NativeRustcVm.addr_add_zero _)
    · rw [reg_of hm2 (r := .X24) (v := .reg .X24) (w := st1.data.regs.getXReg .X24) rfl rfl]
      have := eval_dec env0 .X5
      rw [← reg_val hm1 (r := .X24) rfl] at this
      show (st1.data.regs.getXReg .X24).toBitVec.toNat = _
      rw [this]
      show m0.regs.X5.toNat - 1 = _
      omega
    · exact (reg_of hm2 (r := .X25) (v := .reg .X1) rfl rfl).trans (k1 .X1 (by decide) (by decide))
    · rw [reg_val hm2 (r := .X27) rfl]
      exact eval_ptr0 24
    · rw [show (st2.data.regs.getXReg .X28).toNat = (st2.data.regs.getXReg .X28).toBitVec.toNat
        from rfl, reg_val hm2 (r := .X28) rfl]
      rfl
  have hh0 : Head a s0 levels b claim m0 0 s0 ⟨claim, #[], #[]⟩ st2.data :=
    ⟨hf2, hr2, by rw [hd2]; exact hts1, by rw [hd2]; exact hws1, by omega, rfl, rfl,
      by have := c.roots0; omega, by rw [List.drop_zero]⟩
  have e0 : st2.data.regs.X0 = m0.regs.X0 :=
    (reg_of hm2 (r := .X0) (v := .reg .X0) rfl rfl).trans (k1 .X0 (by decide) (by decide))
  have e1 : st2.data.regs.X1.toNat = foldAt 0 := by
    have := (load_level c hf1 (n := 8) (k := 0) (by omega)).1
    rw [show 24 * 0 = 0 from rfl] at this
    rw [← this, show st2.data.regs.X1 = st2.data.regs.getXReg .X1 from rfl]
    exact congrArg BitVec.toNat (reg_val hm2 (r := .X1) (v := .load 0 0 8) rfl)
  have e2 : st2.data.regs.X2 = m0.regs.X6 :=
    (reg_of hm2 (r := .X2) (v := .reg .X6) rfl rfl).trans (k1 .X6 (by decide) (by decide))
  have e3 : st2.data.regs.X3.toBitVec = pA m0 + BitVec.ofNat 64 roundsOff := by
    rw [show st2.data.regs.X3 = st2.data.regs.getXReg .X3 from rfl,
      reg_val hm2 (r := .X3) (v := .bin .add .W64 (.reg .X6) (.lit 61152)) rfl]
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [k1 .X6 (by decide) (by decide)]
    rfl
  have e26 : X26Ok m0 levels.length 0 st2.data := by
    unfold X26Ok
    simp only [show 0 < 5 by omega, ↓reduceIte]
    rw [reg_of hm2 (r := .X26) (v := .reg .X5) (w := st1.data.regs.getXReg .X5) rfl rfl,
      k1 .X5 (by decide) (by decide)]
    exact hlen.symm
  refine fold_call cs.fr c hh0 hpc2 e0 e1 e2 e3 e26 fun m3 hf3 hr3 hres ↦ ?_
  have hx01 : m3.regs.X0 = 0 ∨ m3.regs.X0 = 1 := by
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr h
  refine cbz_step hp b2_in_code (st := ⟨m3, Host.addrOf (k0 + NativeRustcVmArm.Vm.WhirLevels.b2Offset)⟩) hf3 rfl hx01
    (fun h0 st' hpc' hf' _ _ ↦ ?_) fun h1 st' hpc' hf' hd' he' ↦ ?_
  · rcases hres with ⟨-, hnone⟩ | ⟨h, -⟩
    · exact exit_none hp c hf' hpc' hnone
    · rw [h0] at h; cases h
  · rcases hres with ⟨h, -⟩ | ⟨-, s', w', rs, hmid⟩
    · rw [h1] at h; cases h
    · exact level0 hp cs c (hmid.congr hf' hd' (hmid.regs.congr he') (he' .X26)) hpc'

end

end

end NativeRustcVmArm.Whir.WhirLevels
