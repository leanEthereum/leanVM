module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Basic

/-!
# `each_row` with `final_level`'s closure: up to `b3`

`b0` saves the registers and calls `subspace_table(μ)` into the frame at 552; `b1` checks its
`Some`; `b2` calls `memcpy` to copy the table's pairs to 56. At `b3` (`AtB3`): the pairs at 56,
their count in X29, the arguments in callee-saved registers, memory changed in the stack only.
-/

namespace NativeRustcVmArm.Whir.EachRowOfFinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfFinalLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- **At `b3`.** -/
structure AtB3 (m0 m : MachineData) : Prop where
  fr : FR m0 m
  copy : PairsAt m.dmem (fb m0 + BitVec.ofNat 64 56) (tableOf m0).toList
  tlen : (tableOf m0).size ≤ 31
  x29 : m.regs.getXReg .X29 = (tableOf m0).size.toUInt64
  x26 : (m.regs.getXReg .X26).toBitVec = fb m0 + BitVec.ofNat 64 56
  x20 : m.regs.getXReg .X20 = m0.regs.X6
  x21 : m.regs.getXReg .X21 = m0.regs.X5
  x22 : m.regs.getXReg .X22 = m0.regs.X3
  x23 : m.regs.getXReg .X23 = m0.regs.X1
  x24 : m.regs.getXReg .X24 = m0.regs.X0
  x27 : m.regs.getXReg .X27 = m0.regs.X2

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

/-- The frame's bytes are mapped in every state of the body. -/
theorem frame_mapped (hpre : EachRowFinalPre rows op m0) {m : MachineData} (hfr : FR m0 m)
    {o c : Nat} (h : o + c ≤ 1952) : NativeRustcVm.Mapped m.dmem (fb m0 + BitVec.ofNat 64 o) c :=
  fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]
    exact hfr.kept _ (Ring.frame_mapped hpre.1.1 (by decide) _ (by omega))

/-- **An output in the frame**, for a callee using `N'` bytes of stack. -/
theorem whirIn_frame (hpre : EachRowFinalPre rows op m0) {m : MachineData} (hfr : FR m0 m)
    {o c N' : Nat} (h : o + c ≤ 1952) (ho : o < 1952) (hN' : 1952 + N' ≤ eachRowFinalStack) :
    WhirIn m (fb m0 + BitVec.ofNat 64 o) c N' := by
  have hl := lay hpre
  have hS := hpre.1.1.2.1
  rw [stack_eq] at hS hN'
  have hlt := m0.regs.SP.toNat_lt
  have e := hl.frame_toNat (o := o) ho
  refine ⟨⟨frame_mapped hpre hfr h, show _ + c ≤ _ by rw [e]; omega⟩, Or.inr ?_⟩
  have hsb : (stackBelow m N').toNat = m0.regs.SP.toNat - 1952 - N' := by
    unfold stackBelow
    rw [hfr.sp, NativeRustcVm.toNat_sub_ofNat (by rw [hl.base_F]; omega), hl.base_F]
  rw [hsb, e]
  omega

variable [Host] {k : Nat}

/-- **From the entry to `b3`.** -/
theorem entry_a (hp : Placed code k)
    (htab : Spec (label NativeRustcVmArm.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hpre : EachRowFinalPre rows op m0) {R : MachineState → Prop}
    (cont : ∀ m, AtB3 m0 m → Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b3Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b0Offset)⟩ := by
  have hstk := hpre.1.1
  have hmu : m0.regs.X4.toNat ≤ stackCap := hpre.1.2.2.2.2.2.1
  have hl := lay hpre
  have hS : 3184 ≤ m0.regs.SP.toNat := hstk.2.1
  let env0 := Env.ofMachine m0 [(fb m0, 1952)]
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨Ring.frame_mapped hstk (by decide), Ring.base_noWrap (by omega)⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, trivial⟩
      (by simp [Sym.eval, base]) trivial trivial trivial trivial
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk0 run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : FR m0 st1.data :=
    Ring.Fr.ofPrologue hstk.2.1 (by decide) hm1 hwf0 rfl (by decide) slots_le (by decide) (by simp)
  have e1x0 : st1.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 552 :=
    (hm1.regs .X0 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 552)
  have e1x1 : st1.data.regs.X1 = m0.regs.X4 := (rv hm1 (r := .X1) rfl).trans rfl
  have e1x19 : (st1.data.regs.getXReg .X19).toBitVec = fb m0 + BitVec.ofNat 64 552 :=
    (hm1.regs .X19 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 552)
  -- `subspace_table(μ)`
  have hP1 : SubspaceTablePre st1.data := by
    refine ⟨hfr1.stackOk hstk (by decide) (by decide), ?_⟩
    rw [e1x0]
    exact whirIn_frame hpre hfr1 (by decide) (by decide) (by decide)
  refine call_then hpc1 htab hP1 fun ⟨d2, pc2⟩ hpc2 ⟨hval, hch, hsv⟩ ↦ ?_
  simp only at hpc2
  subst hpc2
  rw [e1x1, e1x0] at hval
  obtain ⟨htag, htabb⟩ : _ ∧ _ := by
    split at hval
    · exact hval
    · contradiction
  rw [e1x0] at hch
  have hfr2 : FR m0 d2 :=
    EachRow.fr_hit hl hfr1 hsv.2.1 hsv.2.2
      (EachRow.hit_of_call hl hfr1.sp (N' := 1024) (o := 552) (n := 512) (by decide) le_rfl
        (by decide) hch) slots_ok
  have hs2 := hsv.1
  -- `b1`, `b2`
  let env1 := Env.ofMachine d2 [(fb m0, 1952)]
  have hwf1 : env1.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hfr2.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm1' : Match env1 tableS d2 :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, trivial⟩
      (by rw [hfr2.sp]; simp [Sym.eval])
      ⟨by
        show (d2.regs.getXReg .X19).toBitVec = _
        rw [hs2 .X19 rfl, e1x19]
        rfl, trivial⟩ trivial trivial trivial
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hl552 : env1.load 0 552 8 = (1 : UInt64).toBitVec := Ring.load_word htag
  have hlen : (tableOf m0).toList.length = (tableOf m0).size := Array.length_toList
  have hl560 : env1.load 0 560 8 = (tableOf m0).size.toUInt64.toBitVec := by
    have := htabb.2.1
    have e : off (fb m0 + BitVec.ofNat 64 552) 8 = fb m0 + BitVec.ofNat 64 560 :=
      NativeRustcVm.addr_add_add _ _ _
    rw [hlen, e] at this
    exact Ring.load_word this
  refine exec_then hk1 run_b1 hwf1 hm1' fun st3 hm3 hpc3 ↦ ?_
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b2Offset) := by
    simp only [PcOk] at hpc3
    sym_simp at hpc3
    rw [hl552] at hpc3
    exact hpc3
  refine exec_at hk2 (exec_after run_b1 run_b2) hwf1 hpc3' hm3 fun st4 hm4 hpc4 ↦ ?_
  have hd4 : st4.data.dmem = d2.dmem := hm4.dmem_eq hwf1 rfl
  have hfr4 : FR m0 st4.data :=
    Ring.Fr.ofBlock hfr2 hm1' hm4 hwf1 rfl rfl rfl (by simp)
  have e4x0 : st4.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 56 :=
    (hm4.regs .X0 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 56)
  have e4x1 : st4.data.regs.X1.toBitVec = fb m0 + BitVec.ofNat 64 568 :=
    (hm4.regs .X1 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 568)
  have e4x2 : st4.data.regs.X2.toNat = 496 := by
    rw [← UInt64.toNat_toBitVec, show st4.data.regs.X2.toBitVec = _ from hm4.regs .X2 _ rfl]; rfl
  have k4 : ∀ r, calleeSaved r = true → (after b2 (after b1 tableS)).reg r = some (.reg r) →
      st4.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hc hr ↦ by
    rw [(rv hm4 (by rw [← after_eq (exec_after run_b1 run_b2)]; exact hr)).trans rfl]
    exact hs2 r hc
  -- `memcpy`
  have hnw : ∀ o c, o + c ≤ 1952 → o < 1952 → NoWrap (fb m0 + BitVec.ofNat 64 o) c :=
    fun o c h ho ↦ by
    unfold NoWrap
    rw [hl.frame_toNat ho]
    have := m0.regs.SP.toNat_lt
    omega
  have hP4 : MemcpyPre st4.data := by
    unfold MemcpyPre
    rw [e4x0, e4x1, e4x2]
    exact ⟨frame_mapped hpre hfr4 (by decide), frame_mapped hpre hfr4 (by decide),
      hnw _ _ (by decide) (by decide), hnw _ _ (by decide) (by decide), Or.inl (by
        rw [hl.frame_toNat (by decide), hl.frame_toNat (by decide)]; omega)⟩
  refine call_then hpc4 hmemcpy hP4 fun ⟨d5, pc5⟩ hpc5 ⟨_, hcopy, hsame5, hsv5⟩ ↦ ?_
  simp only at hpc5
  subst hpc5
  simp only [e4x0, e4x1, e4x2] at hcopy hsame5
  have hl2 : EachRow.Lay m0 1952 eachRowFinalStack 56 552 := ⟨by decide, by decide, by decide, hS⟩
  have hfr5 : FR m0 d5 :=
    EachRow.fr_hit hl2 hfr4 hsv5.2.1 hsv5.2.2 (fun q hq ↦ hsame5 q fun h ↦ hq (.inl h))
      (by decide)
  have hsrc : PairsAt st4.data.dmem (fb m0 + BitVec.ofNat 64 568) (tableOf m0).toList := by
    have := htabb.2.2
    have e : off (off (fb m0 + BitVec.ofNat 64 552) 8) 8 = fb m0 + BitVec.ofNat 64 568 := by
      rw [NativeRustcVm.Transcript.off_off]; exact NativeRustcVm.addr_add_add _ _ _
    rw [e] at this
    unfold PairsAt at this ⊢
    exact this.of_sameOutside (fun q _ ↦ by rw [hd4]) (R := fun _ ↦ False) fun _ _ h ↦ h
  refine cont d5 ⟨hfr5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine EachRow.bytesAt_copy hcopy hsrc ?_
    rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords]
    have := htabb.1
    rw [hlen] at this ⊢
    show _ ≤ 496
    have : rootCap = 31 := rfl
    omega
  · have := htabb.1
    rw [hlen] at this
    exact this
  · rw [hsv5.1 .X29 rfl]
    refine (rv hm4 (r := .X29) rfl).trans ?_
    show UInt64.ofBitVec (env1.load 0 560 8) = _
    rw [hl560]
  · rw [hsv5.1 .X26 rfl]
    exact (hm4.regs .X26 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 56)
  · rw [hsv5.1 .X20 rfl, k4 .X20 rfl rfl]; exact (rv hm1 (r := .X20) rfl).trans rfl
  · rw [hsv5.1 .X21 rfl, k4 .X21 rfl rfl]; exact (rv hm1 (r := .X21) rfl).trans rfl
  · rw [hsv5.1 .X22 rfl, k4 .X22 rfl rfl]; exact (rv hm1 (r := .X22) rfl).trans rfl
  · rw [hsv5.1 .X23 rfl, k4 .X23 rfl rfl]; exact (rv hm1 (r := .X23) rfl).trans rfl
  · rw [hsv5.1 .X24 rfl, k4 .X24 rfl rfl]; exact (rv hm1 (r := .X24) rfl).trans rfl
  · rw [hsv5.1 .X27 rfl, k4 .X27 rfl rfl]; exact (rv hm1 (r := .X27) rfl).trans rfl

end

end NativeRustcVmArm.Whir.EachRowOfFinalLevel
