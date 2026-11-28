module

public import NativeRustcVmX64.Bus.ComputedBytecodeValue.Exec
public import NativeRustcVmX64.Bus.Common
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfComputedBytecodeValue.Names

/-!
# `computed_bytecode_value` on x86-64

`b0` pushes R14, RBX (and RAX, for alignment), keeps the value in R14, RBX and calls
`multilinear_eval_by` on the words and the point; `b1` compares the result with the value
(`xor`, `or`, `sete`) and returns (`computedBytecodeValue_spec`).
-/

namespace NativeRustcVmX64.Bus.ComputedBytecodeValue

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ComputedBytecodeValue
open NativeRustcVmX64.Transcript NativeVm.Model

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 32 := by decide

variable [Host] {k : Nat}

/-- **`computed_bytecode_value`'s contract.** -/
theorem computedBytecodeValue_spec (hp : Placed code k)
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.entryLabel) MleOfComputedBytecodeValuePre
      MleOfComputedBytecodeValuePost) :
    Spec (Labels.label NativeRustcVmX64.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost := by
  rintro m0 ⟨hst, hwr, hwo, hpt⟩
  have hN : computedBytecodeValueStack = 32 + mleStack := rfl
  have hF : 32 ≤ computedBytecodeValueStack := by rw [hN]; omega
  have hle : 32 + mleStack ≤ computedBytecodeValueStack := le_of_eq hN.symm
  have hwf0 := wf0 (d := m0) hst hF (fun _ h ↦ h) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ComputedBytecodeValue.b0Offset + b0.length)).toBitVec)
  unfold NativeRustcVmX64.Vm.ComputedBytecodeValue.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.ComputedBytecodeValue.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw0, hdi, hsi, hdx, hcx, h8, hbx, h14⟩ := after_eq run_b0 ▸ ok_b0
  have hb1 : Body m0 32 computedBytecodeValueStack slots 0 st1.data :=
    Body.of_prologue hst hF hwf0 hm1 hpro hw0 slots_le (by decide)
  have edi : reg st1.data .rdi = reg m0 .rsi := hm1.regs .rdi _ hdi
  have esi : reg st1.data .rsi = reg m0 .rdi := hm1.regs .rsi _ hsi
  have edx : reg st1.data .rdx = reg m0 .rsi := hm1.regs .rdx _ hdx
  have ecx : reg st1.data .rcx = reg m0 .rdx := hm1.regs .rcx _ hcx
  have e8 : reg st1.data .r8 = reg m0 .rcx := hm1.regs .r8 _ h8
  have ebx : reg st1.data .rbx = reg m0 .r9 := hm1.regs .rbx _ hbx
  have e14 : reg st1.data .r14 = reg m0 .r8 := hm1.regs .r14 _ h14
  have hpre : MleOfComputedBytecodeValuePre st1.data := by
    refine ⟨hb1.stackOk hst hle, by rw [edi, edx], ?_, ?_, ?_⟩
    · rw [esi, edx]; exact hb1.readable hwr
    · rw [esi, edx]; exact fun h ↦ hb1.offStack hst hle (hwo h)
    · rw [ecx, e8]; exact hb1.sliceOk hst hle hpt
  refine call_then hpc1 hmle hpre fun st2 hpc2 hrsp2 ⟨hres, hch, hsv⟩ ↦ ?_
  have hb2 : Body m0 32 computedBytecodeValueStack slots 8 st2.data :=
    Body.call hst hF hb1 hle hsv hrsp2 hch slots_le
  -- `b1`.
  have hwf2 := wf0 (d := st2.data) hst hF hb2.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ComputedBytecodeValue.b0_next))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.fr.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := after_eq run_b1 ▸ ok_b1
  obtain ⟨hsv3, hrsp3, hso3⟩ := hb2.epilogue hwf2 hm3 hepi hmem
  simp only [PcOk] at hpc3
  refine .done _ ⟨by rw [hpc3]; exact hb2.fr.load_ret hst hF, hrsp3, ?_, ?_, hsv3⟩
  · -- The result: AL.
    have hw : wordSliceE st1.data (reg st1.data .rsi) (reg st1.data .rdx) =
        wordSliceE m0 (reg m0 .rdi) (reg m0 .rsi) := by
      unfold wordSliceE
      rw [esi, edx]
      by_cases h0 : (reg m0 .rsi).toNat = 0
      · simp only [h0, NativeRustcVm.wordsOf, List.range_zero, List.map_nil]
      · rw [NativeRustcVm.wordsOf_congr fun i hi ↦
          get_keep hst hb1.same (hwo (by omega)) hwr.2 hi]
    have hs : slice st1.data (reg st1.data .rcx) (reg st1.data .r8) =
        slice m0 (reg m0 .rdx) (reg m0 .rcx) := by
      rw [ecx, e8]; exact hb1.slice_eq hst hpt
    have hr : ewArg (reg st2.data .rax) (reg st2.data .rdx) =
        multilinearEval (wordSliceE m0 (reg m0 .rdi) (reg m0 .rsi))
          (slice m0 (reg m0 .rdx) (reg m0 .rcx)) := by
      rw [← hw, ← hs]; exact hres
    have k14 : reg st2.data .r14 = reg m0 .r8 := (hsv.1 .r14 rfl).trans e14
    have kbx : reg st2.data .rbx = reg m0 .r9 := (hsv.1 .rbx rfl).trans ebx
    show (reg st3.data .rax).toNat % 256 = _
    rw [show reg st3.data .rax = _ from hm3.regs .rax _ hrax]
    refine (sete_ew _ _ _ _ _).trans ?_
    show (okWord (ewArg (reg st2.data .rax) (reg st2.data .rdx) ==
      ewArg (reg st2.data .r14) (reg st2.data .rbx))).toNat = _
    rw [hr, k14, kbx]
  · intro q hq
    exact hso3 q fun h ↦ hq (.inr h)

end

end NativeRustcVmX64.Bus.ComputedBytecodeValue
