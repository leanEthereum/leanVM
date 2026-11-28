module

public import NativeRustcVmX64.Whir.GlueLevel.Steps
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `glue_level` up to its first store (x86-64)

`b0` pushes, spills `μ` and the out-of-domain point, keeps `λ` and the claim, and calls `EW::mul`
for `λ · oodValue`; `b1` adds the claim and calls it for `λ²`; `b2` calls it for `λ² · batched`.
At `b3` (`head_step`): the template `t3` with the values `v3`, memory changed in the stack only.
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Whir.Rows
open NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Vm.GlueLevel
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero toNat_off)

public section

variable {s : WhirStateW} {m0 : MachineData}

/-- The aliases of the state's head. -/
theorem headA_ok [Labels] {m : MachineData} {vals : Nat → BitVec 64} {ret : BitVec 64}
    {x : Sym} {r : Nat} {o : Int} (hx : (x, r, o) ∈ headA) :
    x.eval (envG s m0 m vals ret) = (envG s m0 m vals ret).base r + BitVec.ofInt 64 o := by
  simp only [headA, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hx
  rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact off_eq 16 (by decide) rfl
  · exact off_eq 504 (by decide) rfl

/-- The claim's words at the entry, as region `1` holds them. -/
theorem claim_words (hpre : GlueLevelPre s m0) :
    WordAt m0.dmem (off (pOf m0) 0 + BitVec.ofNat 64 0) s.claim.c0 ∧
      WordAt m0.dmem (off (pOf m0) 0 + BitVec.ofNat 64 8) s.claim.c1 := by
  have h := NativeRustcVm.ewAt_iff.mp hpre.2.2.1.claim
  simp only [off, BitVec.add_zero]
  exact h

variable [Host] {k : Nat}

/-- **From the entry to `b3`.** -/
theorem head_step (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hpre : GlueLevelPre s m0) :
    Eventually (step1 Host.exe) (At s m0 k NativeRustcVmX64.Vm.GlueLevel.b3Offset noWr t3 (v3 s m0)) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.GlueLevel.b0Offset)⟩ := by
  have hl := lay hpre
  have h0 : BndG s m0 noWr t0 (fun _ ↦ 0) m0 :=
    startA (by rw [rs_sizes]; rfl)
      (fun ret ↦ ⟨(NativeRustcVmX64.Field.frame_rsp 96 0).trans (BitVec.add_zero _) |>.symm,
        by
          show reg m0 .rdi = pOf m0 + BitVec.ofNat 64 0 + BitVec.ofInt 64 0
          simp, trivial⟩)
      fun ret ↦ aliasesOk_of fun x r o hx ↦ headA_ok hx
  have hw := claim_words hpre
  refine mulStepA hl hmul (by decide) h0 (b0_in_code.trans hp.1 (by simp [b0])) run_b0 noWr
    (fun _ h ↦ h) (by rw [rs_sizes]; rfl) rfl (T' := t1) (vals' := v1 s m0) rfl rfl
    (fun ret ↦ by
      vtac0
      · exact (ldW hw.1).trans rfl
      · exact (ldW hw.2).trans rfl)
    (fun i hi mc hR ↦ ?_) (fun i hi mc hR ↦ ?_) (by rw [rs_sizes]; rfl) rfl rfl
    (fun _ _ ↦ aliasesOk_of fun x r o hx ↦ headA_ok hx) rfl fun st hpc hB _ ↦ ?_
  · cases hi
    exact congrArg Prod.fst (mulRes_of (x := lamOf m0) (y := oodOf m0) hR rfl rfl rfl rfl rfl rfl
      (hl.loadArg h0.same (i := 0) (by decide)) (hl.loadArg h0.same (i := 1) (by decide)))
  · cases hi
    exact congrArg Prod.snd (mulRes_of (x := lamOf m0) (y := oodOf m0) hR rfl rfl rfl rfl rfl rfl
      (hl.loadArg h0.same (i := 0) (by decide)) (hl.loadArg h0.same (i := 1) (by decide)))
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc hB
  subst hpc
  rw [show k + NativeRustcVmX64.Vm.GlueLevel.b0Offset + b0.length = k + NativeRustcVmX64.Vm.GlueLevel.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.GlueLevel.b0_next]]
  refine mulStepA hl hmul (by decide) hB (b1_in_code.trans hp.1 (by simp [b1])) run_b1 noWr
    (fun _ h ↦ h) (by rw [rs_sizes]; rfl) rfl (T' := t2) (vals' := v2 s m0) rfl rfl
    (fun ret ↦ by vtac0)
    (fun i hi mc hR ↦ ?_) (fun i hi mc hR ↦ ?_) (by rw [rs_sizes]; rfl) rfl rfl
    (fun _ _ ↦ aliasesOk_of fun x r o hx ↦ headA_ok hx) rfl fun st hpc hB _ ↦ ?_
  · cases hi
    exact congrArg Prod.fst (mulRes_of (x := lamOf m0) (y := lamOf m0) hR rfl rfl rfl rfl rfl rfl
      rfl rfl)
  · cases hi
    exact congrArg Prod.snd (mulRes_of (x := lamOf m0) (y := lamOf m0) hR rfl rfl rfl rfl rfl rfl
      rfl rfl)
  obtain ⟨d2, pc2⟩ := st
  simp only at hpc hB
  subst hpc
  rw [show k + NativeRustcVmX64.Vm.GlueLevel.b1Offset + b1.length = k + NativeRustcVmX64.Vm.GlueLevel.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.GlueLevel.b1_next]]
  refine mulStepA hl hmul (by decide) hB (b2_in_code.trans hp.1 (by simp [b2])) run_b2 noWr
    (fun _ h ↦ h) (by rw [rs_sizes]; rfl) rfl (T' := t3) (vals' := v3 s m0) rfl rfl
    (fun ret ↦ by vtac0)
    (fun i hi mc hR ↦ ?_) (fun i hi mc hR ↦ ?_) (by rw [rs_sizes]; rfl) rfl rfl
    (fun _ _ ↦ aliasesOk_of fun x r o hx ↦ headA_ok hx) rfl fun st hpc hB _ ↦ .done _ ⟨hpc.trans (by rw [show k + NativeRustcVmX64.Vm.GlueLevel.b2Offset + b2.length = k + NativeRustcVmX64.Vm.GlueLevel.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.GlueLevel.b2_next]]), hB⟩
  · cases hi
    exact congrArg Prod.fst (mulRes_of (x := l2 m0) (y := batOf m0) hR rfl rfl rfl rfl rfl rfl
      (hl.loadArg hB.same (i := 6) (by decide)) (hl.loadArg hB.same (i := 7) (by decide)))
  · cases hi
    exact congrArg Prod.snd (mulRes_of (x := l2 m0) (y := batOf m0) hR rfl rfl rfl rfl rfl rfl
      (hl.loadArg hB.same (i := 6) (by decide)) (hl.loadArg hB.same (i := 7) (by decide)))

end

end NativeRustcVmX64.Whir.GlueLevel
