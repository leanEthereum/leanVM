module

public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Code.Vm.WhirLevels.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.CallPre

/-!
# `verify_stacked_opening`: `whir_levels` and the return

`run_eq`: the model's run is `whirLevels`' from the squeezed state, with the ladder's levels, the
basis `basisOf` and the batched target `claimOf`. `call_whir`: from the call of `whir_levels`
(`AtCall`), its contract, `b35`, the epilogue: the function's postcondition.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening
open LeanVM.Parameters

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData} {ls : List Whir.Level}

omit [Host] in
/-- **The model's run** at the call of `whir_levels`. -/
theorem run_eq [Labels] (h : Parts a s layout target coefficients point slices cs z value m0)
    {st : MachineData} (hc : AtCall a s layout target cs value ls m0 st) :
    (verifyStackedOpening layout.stackLog m0.regs.X2.toNat
      (stackClaims layout target point coefficients cs z value)).run s =
    (whirLevels st.regs.X1.toNat st.regs.X2.toNat
      (basisOf s layout target point coefficients cs z value) 0 ls
      ⟨claimOf s layout target cs value, #[], #[]⟩).run (sq s).2 := by
  have e1 : st.regs.X1.toNat = layout.stackLog := by
    rw [hc.x1]; exact natCast_toUInt64_toNat h.lay.stack_log_lt
  have hsz := size_stackClaims (layout := layout) (cs := cs) target point coefficients z value
  have hb : basisOf s layout target point coefficients cs z value =
      ⟨powers (sq s).1 (stackClaims layout target point coefficients cs z value).size,
        stackClaims layout target point coefficients cs z value⟩ := by
    rw [hsz]; rfl
  have hcl : claimOf s layout target cs value =
      dot (powers (sq s).1 (stackClaims layout target point coefficients cs z value).size)
        ((stackClaims layout target point coefficients cs z value).map (·.value)) := by
    rw [dot_eq, vals_stackClaims, hsz]; rfl
  rw [vso_run _ _ _ (size_claims_le h), hc.lad, e1, hc.x2, hb, hcl]
  rfl

/-- **From the call of `whir_levels`** to the return. -/
theorem call_whir (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hwl : ∀ a s levels ba b claim, Spec (Labels.label NativeRustcVmArm.Vm.WhirLevels.entryLabel)
      (WhirLevelsPre a s levels ba b claim) (WhirLevelsPost a s levels b claim))
    {st : MachineState} (hc : AtCall a s layout target cs value ls m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.WhirLevels.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b35Offset)) :
    Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0) st := by
  have hF : ∀ q, outsF m0 q → outsF m0 q := fun _ hq ↦ hq
  have cF : TCtx m0 512 verifyStackedOpeningStack (tA m0) a (outsF m0) :=
    h.ctxOf hF fun _ hq ↦ .inr (.inr hq)
  have e0 : st.data.regs.X0.toBitVec = tA m0 := by rw [hc.x0]
  refine Fr.leafAt (N' := whirLevelsStack) hc.fr h.hN (by rw [stack_eq]; decide)
    (fun _ h ↦ by cases h) slots_le cF.frame_outs (hwl _ _ _ _ _ _) hpc (pre_of h hc)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 hf2 hq2 hcs2 ↦ ?_
  · rcases hq' with ⟨r, hr, hq'⟩ | hq'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have : InRange st.data.regs.X6.toBitVec whirBytes q := hq'
        rw [hc.x6] at this
        exact .inr (.inl this)
      · have : InRange st.data.regs.X0.toBitVec tstateBytes q := hq'
        rw [e0] at this
        exact .inr (.inr (.inr this))
    · exact .inl hq'
  obtain ⟨hx0, hnext, -, -⟩ := hq2
  rw [← run_eq h hc] at hx0 hnext
  rw [e0] at hnext
  -- `b35`
  have hk35 : b35.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b35Offset) := b35_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hf2.regsBlock (st := ⟨m2, _⟩) hk35 run_b35 rfl rfl rfl rfl fun st3 hf3 hd3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_28 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b37Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b37Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_28_at]
    at hpc3
  obtain ⟨d3, pc3⟩ := st3
  simp only at hpc3
  subst hpc3
  have e3 : d3.regs.X0 = m2.regs.X0 := (rv hm3 (r := .X0) rfl).trans rfl
  refine exit_b37 hp h hf3 fun m' e0' hd hS ↦ ⟨rfl, post_of ?_ ?_ ?_ hS⟩
  · rw [e0', e3, hx0]
  · rw [hd, hd3]; exact hnext
  · rw [hd]; exact hf3.same

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
