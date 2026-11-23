module

public import NativeRustcVmX64.Field.EWMul.Exec
public import NativeRustcVmX64.Field.Leaf
public import NativeRustcVm.Field.EW
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `EW::mul` on x86-64

`ewMul_spec_rust`: rustc's `EW::mul`, placed anywhere in the program, returns `Field.ewMul` of its
arguments' limbs (`NativeRustcVm.Field.Rust`) in RAX, RDX, using its 144 bytes of pushes and frame
only and keeping the callee-saved registers. Its block runs in eleven parts (`EWMul.Exec`), the
bit reversals and the reversed words' products variables of the environment (`vars`); rustc
interleaves and shares the three carry-less products and the two reductions, and each result is
the transcription's by `Lin.check` (`eval_ewMulS`). `ewMul_spec`: the model's product
(`NativeRustcVm.Field.ewMul_eq`).
-/

namespace NativeRustcVmX64.Field.EWMul

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.EWMul
open NativeRustcVm.Field (clmulLow)

@[expose] public section

/-- The variables: the limbs reversed, and the reversed limbs' carry-less products' low words, the
first's reversal. -/
def vars (a0 a1 b0 b1 : BitVec 64) : Nat → BitVec 64
  | 0 => a0.reverse
  | 1 => b0.reverse
  | 2 => clmulLow a0.reverse b0.reverse
  | 3 => (clmulLow a0.reverse b0.reverse).reverse
  | 4 => a1.reverse
  | 5 => b1.reverse
  | 6 => clmulLow a1.reverse b1.reverse
  | 7 => (a0 ^^^ a1).reverse
  | 8 => (b0 ^^^ b1).reverse
  | 9 => clmulLow (a0 ^^^ a1).reverse (b0 ^^^ b1).reverse
  | _ => 0

/-- `EW::mul`'s postcondition against the transcription. -/
def RustPost (m m' : MachineData) : Prop :=
  reg m' .rax = (NativeRustcVm.Field.ewMul (reg m .rdi) (reg m .rsi) (reg m .rdx) (reg m .rcx)).1 ∧
    reg m' .rdx =
      (NativeRustcVm.Field.ewMul (reg m .rdi) (reg m .rsi) (reg m .rdx) (reg m .rcx)).2 ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m ewMulStack) ewMulStack) ∧ Saved m m'

end

public section

/-- `ewMulS` is the transcription's product. -/
theorem eval_ewMulS [Labels] (env : Env)
    (hv : env.vars = vars (env.regs .rdi) (env.regs .rsi) (env.regs .rdx) (env.regs .rcx)) :
    (ewMulS.1.eval env, ewMulS.2.eval env) =
      NativeRustcVm.Field.ewMul (env.regs .rdi) (env.regs .rsi) (env.regs .rdx) (env.regs .rcx) := by
  simp only [ewMulS, eval_reduceS, eval_clmulLowS, eval_revS, xorS, orS, Sym.eval, Lin.xor_apply,
    Lin.or_apply, eval_shrS env _ (show 1 < 64 by decide), eval_shrS env _ (show 63 < 64 by decide),
    eval_shlS env _ (show 1 < 64 by decide), hv]
  rfl

variable [Host] {k : Nat}

/-- **`EW::mul` computes `Field.ewMul`.** -/
theorem ewMul_spec_rust (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre RustPost := by
  intro m hpre
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11⟩ := exits
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := lens
  have hk : b0.IsInfixAt Host.prog k :=
    (b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _) :)
  rw [show Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel = Host.addrOf k from hp.label NativeRustcVmX64.Vm.EWMul.entry_at]
  let env := frameEnv m m 144 (vars (reg m .rdi) (reg m .rsi) (reg m .rdx) (reg m .rcx))
  have hwf : env.WF := frame_wf hpre fun _ h ↦ h
  -- These semantic slices use raw instruction positions, not generated block boundaries.
  refine exec_then (hk.slice 0 125 (by omega)) r1.run hwf (by rw [x1]; nofun) match_frame
    fun st hm hpc ↦ ?_
  rw [x1, l1] at hpc
  refine exec_at (hk.slice 125 16 (by omega)) r2.run hwf (by rw [x2]; nofun) hpc
    (hm.absRev c1 rfl) fun st hm hpc ↦ ?_
  rw [x2, l2] at hpc
  refine exec_at (hk.slice 141 66 (by omega)) r3.run hwf (by rw [x3]; nofun) hpc
    (hm.absRev c2 rfl) fun st hm hpc ↦ ?_
  rw [x3, l3] at hpc
  refine exec_at (hk.slice 207 20 (by omega)) r4.run hwf (by rw [x4]; nofun) hpc
    (hm.abs c3 ((eval_clmulLowS env _ _).trans rfl)) fun st hm hpc ↦ ?_
  rw [x4, l4] at hpc
  refine exec_at (hk.slice 227 95 (by omega)) r5.run hwf (by rw [x5]; nofun) hpc
    (hm.absRev c4 rfl) fun st hm hpc ↦ ?_
  rw [x5, l5] at hpc
  refine exec_at (hk.slice 322 18 (by omega)) r6.run hwf (by rw [x6]; nofun) hpc
    (hm.absRev c5 rfl) fun st hm hpc ↦ ?_
  rw [x6, l6] at hpc
  refine exec_at (hk.slice 340 68 (by omega)) r7.run hwf (by rw [x7]; nofun) hpc
    (hm.absRev c6 rfl) fun st hm hpc ↦ ?_
  rw [x7, l7] at hpc
  refine exec_at (hk.slice 408 107 (by omega)) r8.run hwf (by rw [x8]; nofun) hpc
    (hm.abs c7 ((eval_clmulLowS env _ _).trans rfl)) fun st hm hpc ↦ ?_
  rw [x8, l8] at hpc
  refine exec_at (hk.slice 515 16 (by omega)) r9.run hwf (by rw [x9]; nofun) hpc
    (hm.absRev c8 ((congrArg BitVec.reverse (Lin.xor_apply _ _)).trans rfl)) fun st hm hpc ↦ ?_
  rw [x9, l9] at hpc
  refine exec_at (hk.slice 531 67 (by omega)) r10.run hwf (by rw [x10]; nofun) hpc
    (hm.absRev c9 ((congrArg BitVec.reverse (Lin.xor_apply _ _)).trans rfl)) fun st hm hpc ↦ ?_
  rw [x10, l10] at hpc
  refine exec_at (hk.slice 598 81 (by omega)) r11.run hwf (by rw [x11]; nofun) hpc
    (hm.abs c10 ((eval_clmulLowS env _ _).trans rfl)) fun st hm hpc ↦ ?_
  rw [x11] at hpc
  obtain ⟨hpc, hsp, hso, hsv⟩ := leaf_done hpre hm hpc r11_rsp r11_keeps r11_mem
  have he := eval_ewMulS env rfl
  exact .done _ ⟨hpc, hsp, (hm.reg_check c11).trans (congrArg Prod.fst he),
    (hm.reg_check c12).trans (congrArg Prod.snd he), hso, hsv⟩

/-- **`EW::mul` computes the model's product.** -/
theorem ewMul_spec (hp : Placed code k) : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost := by
  intro m hpre
  refine Eventually.mono (ewMul_spec_rust hp m hpre) fun st ⟨hpc, hsp, h0, h1, hso, hsv⟩ ↦
    ⟨hpc, hsp, ?_, ?_, hso, hsv⟩
  · rw [h0, NativeRustcVm.Field.ewMul_eq]
  · rw [h1, NativeRustcVm.Field.ewMul_eq]

end

end NativeRustcVmX64.Field.EWMul
