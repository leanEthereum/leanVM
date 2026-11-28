module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Field.BitLength.Exec
public import NativeRustcVmArm.Field.W32
public import NativeRustcVmArm.Spec.Field
public import NativeRustcVm.Field.BitLength

/-!
# `bit_length` on AArch64

`bitLength_spec`: rustc's `bit_length(v)`, placed anywhere in the program, returns the bit length
of `v` (`Verifier.bitLength`). rustc unrolls the halving loop into `csel`s and assembles the count
by `orr`s of the shifts taken: its result is `blS` (`x0_eq`), worth `asmV v` (`eval_blS`), which is
`Field.bitLength v` (`asmV_eq`), the bit length by `Field.bitLength_eq`.
-/

namespace NativeRustcVmArm.Field.BitLength

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.BitLength
open NativeRustcArm

@[expose] public section

/-- `v >>> s` as the executor writes it. -/
def shrS (s : Nat) (v : Sym) : Sym := .un (.ubfm s 63) .W64 v

/-- The halving step at `s`: `v >>> s` if nonzero, else `v`. -/
def stepS (s : Nat) (v : Sym) : Sym := .ite (.cmp .eq .W64 (shrS s v) (.lit 0)) v (shrS s v)

/-- The count's part at `s`: `s` if `v >>> s` is nonzero. -/
def bitS (s : Nat) (v : Sym) : Sym := .ite (.cmp .eq .W64 (shrS s v) (.lit 0)) (.lit 0) (.lit s)

/-- X0 at the return. -/
def blS : Sym :=
  let v1 := stepS 32 (.reg .X0)
  let v2 := stepS 16 v1
  let v3 := stepS 8 v2
  let v4 := stepS 4 v3
  let v5 := stepS 2 v4
  let n := Sym.bin .orr .W64 (bitS 2 v4) (.bin .orr .W64 (bitS 4 v3) (.bin .orr .W64 (bitS 8 v2)
    (.bin .orr .W64 (bitS 16 v1) (bitS 32 (.reg .X0)))))
  let n' := Sym.ite (.or (.cmp .ult .W64 v5 (.lit 1)) (.cmp .eq .W64 v5 (.lit 1))) n
    (.un .inc .W64 n)
  .ite (.cmp .eq .W64 v5 (.lit 0)) n' (.un .inc .W64 n')

/-- The step's value. -/
def asmStep (s : Nat) (v : BitVec 64) : BitVec 64 := if v >>> s = 0 then v else v >>> s

/-- The count's part's value. -/
def asmBit (s : Nat) (v : BitVec 64) : BitVec 64 := if v >>> s = 0 then 0 else BitVec.ofNat 64 s

/-- `blS`'s value. -/
def asmV (x : BitVec 64) : BitVec 64 :=
  let v1 := asmStep 32 x
  let v2 := asmStep 16 v1
  let v3 := asmStep 8 v2
  let v4 := asmStep 4 v3
  let v5 := asmStep 2 v4
  let n := asmBit 2 v4 ||| (asmBit 4 v3 ||| (asmBit 8 v2 ||| (asmBit 16 v1 ||| asmBit 32 x)))
  let n' := if v5 >>> 1 = 0 then n else n + 1
  if v5 = 0 then n' else n' + 1

end

public section

theorem eval_shrS [Labels] (env : Env) {s : Nat} (hs : s < 64) (v : Sym) :
    (shrS s v).eval env = v.eval env >>> s :=
  ubfm_lsr _ _ hs

theorem eval_eq0 [Labels] (env : Env) (a : Sym) :
    (SBool.cmp .eq .W64 a (.lit 0)).eval env = decide (a.eval env = 0) := by
  simp only [SBool.eval, Sym.eval, eq64_lit _ 0 (by decide)]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← BitVec.toNat_inj]
  rfl

theorem eval_stepS [Labels] (env : Env) {s : Nat} (hs : s < 64) (v : Sym) :
    (stepS s v).eval env = asmStep s (v.eval env) := by
  simp only [stepS, Sym.eval, eval_eq0, eval_shrS env hs, asmStep, decide_eq_true_eq]

theorem eval_bitS [Labels] (env : Env) {s : Nat} (hs : s < 64) (v : Sym) :
    (bitS s v).eval env = asmBit s (v.eval env) := by
  simp only [bitS, Sym.eval, eval_eq0, eval_shrS env hs, asmBit, decide_eq_true_eq]
  rfl

theorem le_one_iff (v : BitVec 64) :
    (CmpOp.apply .ult .W64 v (BitVec.ofNat 64 1) || CmpOp.apply .eq .W64 v (BitVec.ofNat 64 1)) =
      decide (v >>> 1 = 0) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, Bool.or_eq_true, beq_iff_eq, decide_eq_true_iff]
  have e1 : v.ult 1#64 = true ↔ v.toNat < 1 := by simp [BitVec.ult]
  have e2 : v = 1#64 ↔ v.toNat = 1 := by rw [← BitVec.toNat_inj]; simp
  have e3 : v >>> 1 = 0 ↔ v.toNat / 2 = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp
  rw [e1, e2, e3]
  omega

theorem eq_zero_apply (x : BitVec 64) : CmpOp.apply .eq .W64 x 0#64 = decide (x = 0) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact Iff.rfl

theorem inc_apply (x : BitVec 64) : UnOp.apply .inc .W64 x = x + 1 := by
  simp only [UnOp.apply, low_W64, ext_W64]
  rfl

/-- **The return value**. -/
theorem eval_blS [Labels] (env : Env) : blS.eval env = asmV (env.regs .X0) := by
  simp only [blS, asmV, eval_stepS env (show 32 < 64 by decide),
    eval_stepS env (show 16 < 64 by decide), eval_stepS env (show 8 < 64 by decide),
    eval_stepS env (show 4 < 64 by decide), eval_stepS env (show 2 < 64 by decide),
    eval_bitS env (show 32 < 64 by decide), eval_bitS env (show 16 < 64 by decide),
    eval_bitS env (show 8 < 64 by decide), eval_bitS env (show 4 < 64 by decide),
    eval_bitS env (show 2 < 64 by decide), SBool.eval, Sym.eval, le_one_iff,
    orr_apply, inc_apply, decide_eq_true_eq, eq_zero_apply]

theorem step_eq (s : Nat) (n v : BitVec 64) :
    NativeRustcVm.Field.bitLengthStep s (n, v) = (n + asmBit s v, asmStep s v) := by
  unfold NativeRustcVm.Field.bitLengthStep asmBit asmStep
  by_cases h : v >>> s = 0#64 <;> simp [h]

theorem asmBit_cases (s : Nat) (v : BitVec 64) :
    asmBit s v = 0 ∨ asmBit s v = BitVec.ofNat 64 s := by
  unfold asmBit
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **`blS`'s value is the transcription's.** -/
theorem asmV_eq (x : BitVec 64) : asmV x = NativeRustcVm.Field.bitLength x := by
  simp only [asmV, NativeRustcVm.Field.bitLength, step_eq]
  generalize asmStep 2 (asmStep 4 (asmStep 8 (asmStep 16 (asmStep 32 x)))) = v5
  rcases asmBit_cases 32 x with h32 | h32 <;> rw [h32] <;>
  rcases asmBit_cases 16 (asmStep 32 x) with h16 | h16 <;> rw [h16] <;>
  rcases asmBit_cases 8 (asmStep 16 (asmStep 32 x)) with h8 | h8 <;> rw [h8] <;>
  rcases asmBit_cases 4 (asmStep 8 (asmStep 16 (asmStep 32 x))) with h4 | h4 <;> rw [h4] <;>
  rcases asmBit_cases 2 (asmStep 4 (asmStep 8 (asmStep 16 (asmStep 32 x)))) with h2 | h2 <;>
    rw [h2] <;>
  by_cases h1 : v5 >>> 1 = 0 <;> by_cases h0 : v5 = 0 <;>
    simp only [asmBit, asmStep, h1, h0, ite_true, ite_false, ne_eq, not_false_eq_true] <;> decide

/-- **`bit_length` is the bit length.** -/
theorem asmV_toNat (x : BitVec 64) :
    (asmV x).toNat = LeanVM.Protocol.Verifier.bitLength x.toNat := by
  rw [asmV_eq, NativeRustcVm.Field.bitLength_eq]

/-- The block's X0 is `blS`. -/
theorem x0_eq : (match exec b0 regS with
    | some (S, _) => S.reg .X0
    | none => none) = some blS := by
  decide +kernel

/-- **`bit_length` returns the bit length.** -/
theorem bitLength_spec [Host] {k : Nat} (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost := by
  intro m _
  rw [show Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.BitLength.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.BitLength.entryOffset) NativeRustcVmArm.Vm.BitLength.entry_at]
  have hx := x0_eq
  rw [run_b0] at hx
  refine exec_then (b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _)) run_b0
    (Env.wf_nil m) (match_nil m) fun st hm hpc ↦ .done _ ⟨?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    unfold retOf
    rw [show st.data.regs.X30 = m.regs.X30 from Match.reg_eq (r := .X30) (match_nil m) hm rfl rfl]
  · show (st.data.regs.getXReg .X0).toBitVec.toNat = _
    rw [hm.regs .X0 _ hx, eval_blS, asmV_toNat]
    rfl
  · intro p _
    rw [hm.dmem_eq (Env.wf_nil m) rfl]
    rfl
  · exact Match.saved (match_nil m) hm (Env.wf_nil m) rfl (by decide +kernel)

end

end NativeRustcVmArm.Field.BitLength
