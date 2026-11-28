module

public import NativeRustcVmX64.Field.BitLength.Exec
public import NativeRustcVmX64.Field.Leaf
public import NativeRustcVmX64.Field.LinSound
public import NativeRustcVm.Field.BitLength
public import NativeRustcVmX64.Code.Vm.BitLength.Names

/-!
# `bit_length` on x86-64

`bitLength_spec`: rustc's `bit_length(v)`, placed anywhere in the program, returns the bit length
of `v` (`Verifier.bitLength`). Its result is `blS` (`BitLength.Exec`), worth `Field.bitLength v`
(`eval_blS`): with the halving steps' values (`asmStep`) and their tests' bits (`asmB`), the count
is the transcription's whatever the tests give.
-/

namespace NativeRustcVmX64.Field.BitLength

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.BitLength

@[expose] public section

/-- The step's value. -/
def asmStep (s : Nat) (v : BitVec 64) : BitVec 64 := if v >>> s = 0 then v else v >>> s

/-- The test's bit: `1` if `v >>> s` is nonzero. -/
def asmB (s : Nat) (v : BitVec 64) : BitVec 64 := if v >>> s = 0 then 0 else 1

end

public section

theorem eq_zero_apply (x : BitVec 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 0) = decide (x = 0) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact Iff.rfl

theorem ult_two (v : BitVec 64) :
    CmpOp.apply .ult .W64 v (BitVec.ofNat 64 2) = decide (v >>> 1 = 0) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  have e1 : v.ult (BitVec.ofNat 64 2) = true ↔ v.toNat < 2 := by simp [BitVec.ult]
  have e3 : v >>> 1 = 0 ↔ v.toNat / 2 = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp
  rw [e1, e3]
  omega

theorem ult_one (v : BitVec 64) :
    CmpOp.apply .ult .W64 v (BitVec.ofNat 64 1) = decide (v = 0) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  have e1 : v.ult (BitVec.ofNat 64 1) = true ↔ v.toNat < 1 := by simp [BitVec.ult]
  have e2 : v = 0 ↔ v.toNat = 0 := by rw [← BitVec.toNat_inj]; simp
  rw [e1, e2]
  omega

variable [Labels] (env : Env)

theorem eval_shrS {s : Nat} (hs : s < 64) (v : Sym) :
    (shrS s v).eval env = v.eval env >>> s :=
  Lin.shr_apply _ hs

theorem eval_stepS {s : Nat} (hs : s < 64) (v : Sym) :
    (stepS s v).eval env = asmStep s (v.eval env) := by
  simp only [stepS, Sym.eval, SBool.eval, eval_shrS env hs, eq_zero_apply, asmStep,
    decide_eq_true_eq]

theorem eval_bitS {s : Nat} (hs : s < 64) (v : Sym) :
    (bitS s v).eval env = asmB s (v.eval env) := by
  simp only [bitS, Sym.eval, SBool.eval, eval_shrS env hs, eq_zero_apply, asmB]
  by_cases h : v.eval env >>> s = 0 <;> simp only [h, decide_true, decide_false, Bool.not_true,
    Bool.not_false, ite_true, ite_false, Bool.false_eq_true] <;> decide

omit [Labels] in
theorem step_eq (s : Nat) (n v : BitVec 64) :
    NativeRustcVm.Field.bitLengthStep s (n, v) =
      (n + (if v >>> s = 0 then 0 else BitVec.ofNat 64 s), asmStep s v) := by
  unfold NativeRustcVm.Field.bitLengthStep asmStep
  by_cases h : v >>> s = 0#64 <;> simp [h]

omit [Labels] in
theorem asmB_cases (s : Nat) (v : BitVec 64) :
    (v >>> s = 0 ∧ asmB s v = 0) ∨ (¬v >>> s = 0 ∧ asmB s v = 1) := by
  unfold asmB
  by_cases h : v >>> s = 0
  · exact Or.inl ⟨h, by rw [ite_eq_left h]⟩
  · exact Or.inr ⟨h, by rw [ite_eq_right h]⟩

/-- **The return value is the transcription's.** -/
theorem eval_blS : blS.eval env = NativeRustcVm.Field.bitLength (env.regs .rdi) := by
  simp only [blS, Sym.eval, SBool.eval, eval_stepS env (show 32 < 64 by decide),
    eval_stepS env (show 16 < 64 by decide), eval_stepS env (show 8 < 64 by decide),
    eval_stepS env (show 4 < 64 by decide), eval_stepS env (show 2 < 64 by decide),
    eval_bitS env (show 32 < 64 by decide), eval_bitS env (show 16 < 64 by decide),
    eval_bitS env (show 8 < 64 by decide), eval_bitS env (show 4 < 64 by decide),
    eval_bitS env (show 2 < 64 by decide), ult_two, ult_one, NativeRustcVm.Field.bitLength,
    step_eq]
  generalize env.regs .rdi = x
  generalize asmStep 2 (asmStep 4 (asmStep 8 (asmStep 16 (asmStep 32 x)))) = v5
  rcases asmB_cases 32 x with ⟨h32, e32⟩ | ⟨h32, e32⟩ <;> simp only [h32, e32, ite_true, ite_false] <;>
  rcases asmB_cases 16 (asmStep 32 x) with ⟨h16, e16⟩ | ⟨h16, e16⟩ <;>
    simp only [h16, e16, ite_true, ite_false] <;>
  rcases asmB_cases 8 (asmStep 16 (asmStep 32 x)) with ⟨h8, e8⟩ | ⟨h8, e8⟩ <;>
    simp only [h8, e8, ite_true, ite_false] <;>
  rcases asmB_cases 4 (asmStep 8 (asmStep 16 (asmStep 32 x))) with ⟨h4, e4⟩ | ⟨h4, e4⟩ <;>
    simp only [h4, e4, ite_true, ite_false] <;>
  rcases asmB_cases 2 (asmStep 4 (asmStep 8 (asmStep 16 (asmStep 32 x)))) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
    simp only [h2, e2, ite_true, ite_false] <;>
  by_cases h1 : v5 >>> 1 = 0 <;> by_cases h0 : v5 = 0 <;>
    simp only [asmStep, h1, h0, decide_true, decide_false, Bool.not_true, Bool.not_false,
      ite_true, ite_false, ne_eq, not_false_eq_true] <;>
    decide

end

public section

/-- **`bit_length` returns the bit length.** -/
theorem bitLength_spec [Host] {k : Nat} (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost := by
  intro m hpre
  rw [show Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel = Host.addrOf k from hp.label NativeRustcVmX64.Vm.BitLength.entry_at]
  have hk : b0.IsInfixAt Host.prog k :=
    (b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _) :)
  have hwf := frame_wf (m := m) (vars := fun _ ↦ 0) (ret := 0) hpre fun _ h ↦ h
  refine exec_then hk r.run hwf (by rw [exit_eq]; nofun) match_frame fun st hm hpc ↦ ?_
  rw [exit_eq] at hpc
  obtain ⟨hpc, hsp, hso, hsv⟩ := leaf_done hpre hm hpc rsp_eq keeps_eq mem_eq
  refine .done _ ⟨hpc, hsp, ?_, hso, hsv⟩
  show (st.data.regs.get64 .rax).toNat = _
  rw [hm.regs .rax _ rax_eq, eval_blS, NativeRustcVm.Field.bitLength_eq]
  rfl

end

end NativeRustcVmX64.Field.BitLength
