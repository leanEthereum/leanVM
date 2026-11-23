module

public import NativeRustcVmX64.Field.Kmul.Exec
public import NativeRustcVmX64.Field.Leaf
public import NativeRustcVm.Field.Clmul
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `kmul` on x86-64

`kmul_spec_rust`: rustc's `kmul`, placed anywhere in the program, returns `Field.kmul a b`
(`NativeRustcVm.Field.Rust`, `field.rs` transcribed) of its arguments, using its 48 bytes of
pushes only and keeping the callee-saved registers. Its block runs in five parts (`Kmul.Exec`),
the bit reversals and the reversed factors' product variables of the environment (`vars`). `kmul_spec`:
the model's product (`NativeRustcVm.Field.kmul_toBitVec`).
-/

namespace NativeRustcVmX64.Field.Kmul

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.Kmul

@[expose] public section

/-- The variables: the factors reversed, their carry-less product's low word, its reversal. -/
def vars (a b : BitVec 64) : Nat → BitVec 64
  | 0 => a.reverse
  | 1 => b.reverse
  | 2 => NativeRustcVm.Field.clmulLow a.reverse b.reverse
  | 3 => (NativeRustcVm.Field.clmulLow a.reverse b.reverse).reverse
  | _ => 0

/-- `kmul`'s postcondition against the transcription. -/
def RustPost (m m' : MachineData) : Prop :=
  reg m' .rax = NativeRustcVm.Field.kmul (reg m .rdi) (reg m .rsi) ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kmulStack) kmulStack) ∧ Saved m m'

end

public section

variable [Host] {k : Nat}

/-- **`kmul` computes `Field.kmul`.** -/
theorem kmul_spec_rust (hp : Placed code k) : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre RustPost := by
  intro m hpre
  obtain ⟨l1, l2, l3, l4, l5⟩ := lens
  have hk : b0.IsInfixAt Host.prog k :=
    (b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _) :)
  rw [show Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel = Host.addrOf k from hp.label NativeRustcVmX64.Vm.Kmul.entry_at]
  let env := frameEnv m m 48 (vars (reg m .rdi) (reg m .rsi))
  have hwf : env.WF := frame_wf hpre fun _ h ↦ h
  -- These semantic slices use raw instruction positions, not generated block boundaries.
  refine exec_then (hk.slice 0 100 (by omega)) r1.run hwf (by rw [r1_exit]; nofun) match_frame
    fun st1 hm1 hpc1 ↦ ?_
  rw [r1_exit, l1] at hpc1
  refine exec_at (hk.slice 100 16 (by omega)) r2.run hwf (by rw [r2_exit]; nofun) hpc1
    (hm1.absRev c1 rfl) fun st2 hm2 hpc2 ↦ ?_
  rw [r2_exit, l2] at hpc2
  refine exec_at (hk.slice 116 66 (by omega)) r3.run hwf (by rw [r3_exit]; nofun) hpc2
    (hm2.absRev c2 rfl) fun st3 hm3 hpc3 ↦ ?_
  rw [r3_exit, l3] at hpc3
  refine exec_at (hk.slice 182 19 (by omega)) r4.run hwf (by rw [r4_exit]; nofun) hpc3
    (hm3.abs c3 ((eval_clmulLowS env _ _).trans rfl)) fun st4 hm4 hpc4 ↦ ?_
  rw [r4_exit, l4] at hpc4
  refine exec_at (hk.slice 201 22 (by omega)) r5.run hwf (by rw [r5_exit]; nofun) hpc4
    (hm4.absRev c4 rfl) fun st5 hm5 hpc5 ↦ ?_
  rw [r5_exit] at hpc5
  obtain ⟨hpc, hsp, hso, hsv⟩ := leaf_done hpre hm5 hpc5 r5_rsp r5_keeps r5_mem
  refine .done _ ⟨hpc, hsp, ?_, hso, hsv⟩
  refine (hm5.reg_check c5).trans ?_
  rw [eval_reduceS, eval_clmulLowS, eval_shrS env _ (by decide)]
  rfl

/-- **`kmul` computes the model's product.** -/
theorem kmul_spec (hp : Placed code k) : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost := by
  intro m hpre
  refine Eventually.mono (kmul_spec_rust hp m hpre) fun st ⟨hpc, hsp, h0, hso, hsv⟩ ↦
    ⟨hpc, hsp, ?_, hso, hsv⟩
  rw [h0, ← NativeRustcVm.Field.kmul_toBitVec]

end

end NativeRustcVmX64.Field.Kmul
