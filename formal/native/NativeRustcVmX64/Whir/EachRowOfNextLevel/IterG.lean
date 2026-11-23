module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.IterF
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `each_row` with `next_level`'s closure: row `j`'s term (x86-64)

At `b23` (`AtB23`): `b23` compares `j` with the query weights' count; below it, `b6` reads query
weight `j`, else `b24` takes `0`; `b7` loads the batched value's limbs, adds the folded row and the
scaled value and calls `EW::mul` (`mul_then`); then `b8_step` (`iter_g`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

theorem qw_size : (qwOf m0).size = (nextEnv m0 5).toNat := by simp [qwOf, slice]

/-- Query weight `j`, as the entry's memory holds it. -/
theorem qw_getD (hj : j < (qwOf m0).size) :
    (qwOf m0).getD j 0 = NativeRustcVm.ewOf m0.dmem (nextEnv m0 4 + BitVec.ofNat 64 (16 * j)) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
  simp [qwOf, slice]

/-- Past the query weights, `0`. -/
theorem qw_getD_none (hj : (qwOf m0).size ≤ j) : (qwOf m0).getD j 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hj]
  rfl

variable [Host] {k : Nat}

/-- **`EW::mul` called** at the end of `b7`, then `b8_step`. -/
theorem mul_then (hp : Placed code k) (hmul : Spec (label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (c : Ctx rows op m0) {st : MachineState} (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel)
    (hret : retOf st.data = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b8Offset)) (hfr : FR m0 0 st.data)
    (hj : j < rows.size) (hjq : j < (qsOf m0).size) (hmm : MidN rows m0 j st.data.dmem)
    (hq : (⟨UInt64.ofBitVec (reg st.data .rdi), UInt64.ofBitVec (reg st.data .rsi)⟩ : EW) =
      (qwOf m0).getD j 0)
    (hx : (⟨UInt64.ofBitVec (reg st.data .rdx), UInt64.ofBitVec (reg st.data .rcx)⟩ : EW) =
      foldJ rows m0 j hj hjq + scaleJ m0 ((qsOf m0)[j]'hjq))
    (h12 : reg st.data .r12 = (parOf rows m0 j).c0.toBitVec)
    (h13 : reg st.data .r13 = (parOf rows m0 j).c1.toBitVec)
    (hbx : reg st.data .rbx = BitVec.ofNat 64 (j + 1))
    (h15 : reg st.data .r15 = reg m0 .rsi + BitVec.ofNat 64 (8 * (j + 1)))
    (h14 : reg st.data .r14 = bOf m0)
    (cont : ∀ m', Inv rows m0 (j + 1) m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b9Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) st := by
  have hl := lay c
  refine Eventually.bind (Spec.apply hmul hpc (hfr.stackOk hl (by decide)))
    fun ⟨d, pc⟩ ⟨hpc', hrsp, hq'⟩ ↦ ?_
  simp only at hpc' hrsp hq'
  rw [hpc', hret]
  obtain ⟨hax, hdx, hch, hsv⟩ := hq'
  have hs := EachRow.hit_of_stack hl (lo := 1432) (hi := 1432) le_rfl (by decide) hfr.rsp0
    (N' := ewMulStack) (by decide) hch
  have hfr' : FR m0 8 d := EachRow.Fr.call hl le_rfl (by decide) hfr hrsp hsv hs (by decide)
  have hT : EW.mul ⟨.ofBitVec (reg st.data .rdi), .ofBitVec (reg st.data .rsi)⟩
      ⟨.ofBitVec (reg st.data .rdx), .ofBitVec (reg st.data .rcx)⟩ = termJ rows m0 j := by
    rw [hq, hx, nextTerm_eq hj hjq]
    rfl
  rw [hT] at hax hdx
  exact b8_step hp c ⟨hfr', hj, hjq, hmm.keep c le_rfl (by decide) (by decide) (by decide) hs,
    hax, hdx, (sv hsv .r12 rfl).trans h12, (sv hsv .r13 rfl).trans h13,
    (sv hsv .rbx rfl).trans hbx, (sv hsv .r15 rfl).trans h15, (sv hsv .r14 rfl).trans h14⟩ cont

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
