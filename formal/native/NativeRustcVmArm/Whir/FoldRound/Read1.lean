module

public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Whir.FoldRound.Checks

/-!
# `fold_round`: the entry and the first scalar

`stage1`: the prologue (`b0`) and the first `read_scalar`; `stage2`: its tag (`b1`, `None` to the
epilogue), the scalar `u0` into X29, X24 and the second `read_scalar` (`b2`).
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

/-- After a `read_scalar` of the state `s`: the frame's `Option<EW>` and the `TState`. -/
structure AfterRs (s : TState) (m0 st : MachineData) : Prop where
  opt : OptEWAt st.dmem (loc m0 88) ((readScalar.run s).map (·.1))
  next : NextAt st.dmem (tA m0) a (readScalar.run s)

/-- **The prologue and the first scalar.** -/
theorem stage1 (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {R : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b1Offset) → Base w m0 st.data →
      AfterRs (a := a) s0 m0 st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b0Offset)⟩ := by
  have hN := pre_hN h
  have hN' : 800 ≤ m0.regs.SP.toNat := by rw [← stack_eq]; exact hN
  have hwf : (Env.ofMachine m0 [(base m0 208, 208)]).WF :=
    Env.wf_of ⟨⟨frame_mapped h.1.1 (by rw [stack_eq]; decide), base_noWrap (by omega)⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m0 [(base m0 208, 208)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1.1 (by rw [stack_eq]; decide) rfl, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]; rw [show BitVec.ofInt 64 208 = BitVec.ofNat 64 208 from rfl,
        base_add_eq]) trivial trivial trivial trivial
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hmem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 208 := by
    rw [after_eq run_b0]; decide
  rw [after_eq run_b0] at hmem
  have hf1 : FFr m0 st1.data := Fr.ofPrologue hN (by rw [stack_eq]; decide) hm1 hwf rfl
    (by decide) slots_le hmem (fun _ h ↦ by cases h)
  have hs1 : SameOutside m0.dmem st1.data.dmem (InRange (base m0 208) 208) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦ written_r0 hwf rfl hmem hq
  have hb1 : Base w m0 st1.data :=
    ⟨hf1, reg_of hm1 (r := .X19) (v := .reg .X0) rfl rfl,
      reg_of hm1 (r := .X20) (v := .reg .X2) rfl rfl,
      reg_of hm1 (r := .X23) (v := .reg .X1) rfl rfl,
      ws_keep h h.2.2.1 hs1 fun q hq ↦ frame_away h hq⟩
  have hts1 : TStateAt st1.data.dmem (tA m0) a s0 :=
    h.2.1.frame (hm1.kept hwf) (fun q hq ↦ frame_not_t h hq) hs1
  rw [show k + NativeRustcVmArm.Vm.FoldRound.b0Offset + b0.length = k + NativeRustcVmArm.Vm.FoldRound.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FoldRound.b0_next]] at hpc1
  refine rs_call h hrs hb1 hpc1 ?_ (reg_of hm1 (r := .X1) (v := .reg .X1) rfl rfl) hts1
    fun m2 hb2 hopt hnext _ _ ↦ cont ⟨m2, _⟩ rfl hb2 ⟨hopt, hnext⟩
  have := reg_val hm1 (r := .X0) rfl
  simp only [Sym.eval] at this
  exact this

end

end NativeRustcVmArm.Whir.FoldRound
