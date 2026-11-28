module

public import NativeRustcVmArm.Ring.Switch.Basic

/-!
# `ring_switch`: what its steps keep, the prologue with the grind, the epilogue

Memory changes after the grind are in the stack or the `RingW` (`Within`): they keep the
`TState` (`ts_keep`), the round constants (`rc_keep`) and the bytes apart from both
(`bytes_keep`). `stepEntry`: the prologue and `grind` (`b0`); `stepExit`: the epilogue (`b6`).
-/

namespace NativeRustcVmArm.Ring.Switch

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.RingSwitch

@[expose] public section

/-- The bytes the code changes after the grind: the stack, the `RingW`. -/
def Within (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (base m0 ringSwitchStack) ringSwitchStack q ∨ InRange (oA m0) ringWBytes q

end

public section

variable {m0 : MachineData} {a : DecArea} {s : TState}

section
variable [Labels]

theorem nw_stack (h : RingSwitchPre a s m0) :
    NoWrap (base m0 ringSwitchStack) ringSwitchStack := base_noWrap (hN h)

/-- **Bytes apart from the stack and the `RingW`** are kept. -/
theorem bytes_keep (h : RingSwitchPre a s m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) (hR : ∀ q, R q → Within m0 q) {b : BitVec 64} {bs : List UInt8}
    (hb : NativeRustcVm.BytesAt d b bs) (hw : NoWrap b bs.length)
    (h1 : Apart b bs.length (stackBelow m0 ringSwitchStack) ringSwitchStack)
    (h2 : Apart b bs.length (oA m0) ringWBytes) : NativeRustcVm.BytesAt d' b bs :=
  NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ by
    rcases hR _ hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange_add h1 hw (nw_stack h) hi hq
    · exact NativeRustcVm.Apart.not_inRange_add h2 hw (o_noWrap h) hi hq

/-- **The `TState`** is kept. -/
theorem ts_keep (h : RingSwitchPre a s m0) {d d' : Mem 64} {R : BitVec 64 → Prop} {s' : TState}
    (hts : TStateAt d (tA m0) a s') (hk : Keeps d d') (hs : SameOutside d d' R)
    (hR : ∀ q, R q → Within m0 q) : TStateAt d' (tA m0) a s' := by
  have hwt := hts.footprint.1.2
  have hww := hts.footprint.2.1.2
  refine hts.frame hk (fun q hq ↦ ?_) hs
  have o1 := h.2.2.2.2.1.2.2.1
  have o2 := h.2.2.2.2.1.2.2.2.1
  rcases hR q hq with hq | hq
  · exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange h.2.2.2.1.1 hwt (nw_stack h) ht hq,
      fun ht ↦ NativeRustcVm.Apart.not_inRange h.2.2.2.1.2.1 hww (nw_stack h) ht hq⟩
  · exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange o1 (o_noWrap h) hwt hq ht,
      fun ht ↦ NativeRustcVm.Apart.not_inRange o2 (o_noWrap h) hww hq ht⟩

/-- **The round constants** in every state of the frame, for a callee of `N'` bytes of stack. -/
theorem rc_of (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) {N' : Nat}
    (hle : 432 + N' ≤ ringSwitchStack) : RcAt m N' := by
  obtain ⟨hw, hnw, hap⟩ := h.2.1
  refine ⟨NativeRustcVm.BytesAt.of_sameOutside hw hfr.same fun i hi hq ↦ ?_, hnw,
    hfr.apart (hN h) hap hle⟩
  have hl : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 := by
    rw [NativeRustcVm.length_flatMap_const NativeRustcVm.length_wordBytes]
    rfl
  rw [hl] at hi
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add hap hnw (nw_stack h) hi hq
  · exact NativeRustcVm.Apart.not_inRange_add h.2.2.2.2.1.2.2.2.2.2.symm hnw (o_noWrap h) hi hq
  · exact NativeRustcVm.Apart.not_inRange_add h.2.2.2.1.2.2.symm hnw (t_noWrap h) hi hq

/-- **The `TState`'s footprint** apart from a callee's stack. -/
theorem tok_of (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) {N' : Nat}
    (hle : 432 + N' ≤ ringSwitchStack) : TStateOk m (tA m0) a N' :=
  ⟨hfr.apart (hN h) h.2.2.2.1.1 hle, hfr.apart (hN h) h.2.2.2.1.2.1 hle, h.2.2.2.1.2.2⟩

end

theorem keep_ok {S S' : SState} (hS : keep.all (fun r ↦ S'.reg r == S.reg r) = true)
    (h0 : keep.all (fun r ↦ (S.reg r).isSome) = true) :
    ∀ r ∈ keep, ∃ v, S.reg r = some v ∧ S'.reg r = some v := by
  intro r hr
  simp only [List.all_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hS h0
  obtain ⟨v, hv⟩ := h0 r hr
  exact ⟨v, hv, (hS r hr).trans hv⟩

/-- The block's writes are in the frame below the slots. -/
theorem writeOk_low {env : Env} {S : SState} (hw : wrLow S = true) :
    ∀ w ∈ S.mem, WriteOk env 432 slots (outs m0) w := by
  simp only [wrLow, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  intro w hw'
  exact .inl ⟨(hw w hw').1, by have := (hw w hw').2; omega,
    fun q hq ↦ .inl (by have := slots_ge q hq; have := (hw w hw').2; omega)⟩

variable [Host]

/-- **The epilogue** (`b6`): the entry's return address, its callee-saved registers and SP, the
memory and X0 kept. -/
theorem stepExit (h : RingSwitchPre a s m0) {i : Nat} (hk : b6.IsInfixAt Host.prog i)
    {m : MachineData} (hfr : SFr m0 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ Saved m0 st.data ∧
      st.data.dmem = m.dmem ∧ st.data.regs.X0 = m.regs.X0) ⟨m, Host.addrOf i⟩ := by
  have hwf := envM_wf h hfr
  refine exec_then hk run_b6 hwf (matchM h hfr) fun st hm1 hpc ↦ ?_
  obtain ⟨hret, hsaved⟩ := hfr.exit (rs := []) hm1 hwf (by decide)
  simp only [PcOk] at hpc
  exact .done _ ⟨by rw [hpc, hret], hsaved, hm1.dmem_eq hwf rfl,
    Match.reg_eq (matchM h hfr) hm1 (r := .X0) rfl rfl⟩

end

end NativeRustcVmArm.Ring.Switch
