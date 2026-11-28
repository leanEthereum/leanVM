module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EWSqIter.Names
public import NativeRustcVmArm.Code.Vm.RingCoefficients.Names
public import NativeRustcVmArm.Ring.Coeff.Ends

/-!
# `ring_coefficients`' contract

The prologue (`b0`) loads `g` into `G`'s locations; each of the 8 turns (from `.LRingCoefficients_1`)
multiplies `f_p` by `G_0 … G_7` into `out`'s row `p` (`b1` to `b9`), replaces `G` by its
Frobenius images (`b9` to `b17`) and branches back while turns remain; the epilogue (`b18`).
-/

namespace NativeRustcVmArm.Ring.Coeff

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingCoefficients

public section

variable [Host] {k : Nat} {m0 : MachineData}

theorem hb {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j) (hne : ds ≠ [])
    (hp : Placed code k) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **A turn**: from the head of turn `p`, the next turn's head or `Done` at the epilogue. -/
theorem turn (hp : Placed code k) (h : P m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hsq : Spec (Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost) {p : Nat} {m : MachineData}
    (hH : Head m0 p m) :
    Eventually (step1 Host.exe) (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingCoefficients.b1Offset) ∧ Head m0 (p + 1) st.data) ∨
      (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingCoefficients.b18Offset) ∧ Done m0 st.data)) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingCoefficients.b1Offset)⟩ := by
  refine stepHead h hmul (hb b1_in_code (by simp [b1]) hp) run_b1 (by decide) hH fun m h1 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b1Offset + b1.length = k + NativeRustcVmArm.Vm.RingCoefficients.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b1_next]]
  refine stepMul (b := 0) h hmul (hb b2_in_code (by simp [b2]) hp) run_b2 (by decide) (by decide) h1
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b2Offset + b2.length = k + NativeRustcVmArm.Vm.RingCoefficients.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b2_next]]
  refine stepMul (b := 1) h hmul (hb b3_in_code (by simp [b3]) hp) run_b3 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b3Offset + b3.length = k + NativeRustcVmArm.Vm.RingCoefficients.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b3_next]]
  refine stepMul (b := 2) h hmul (hb b4_in_code (by simp [b4]) hp) run_b4 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b4Offset + b4.length = k + NativeRustcVmArm.Vm.RingCoefficients.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b4_next]]
  refine stepMul (b := 3) h hmul (hb b5_in_code (by simp [b5]) hp) run_b5 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b5Offset + b5.length = k + NativeRustcVmArm.Vm.RingCoefficients.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b5_next]]
  refine stepMul (b := 4) h hmul (hb b6_in_code (by simp [b6]) hp) run_b6 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b6Offset + b6.length = k + NativeRustcVmArm.Vm.RingCoefficients.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b6_next]]
  refine stepMul (b := 5) h hmul (hb b7_in_code (by simp [b7]) hp) run_b7 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b7Offset + b7.length = k + NativeRustcVmArm.Vm.RingCoefficients.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b7_next]]
  refine stepMul (b := 6) h hmul (hb b8_in_code (by simp [b8]) hp) run_b8 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b8Offset + b8.length = k + NativeRustcVmArm.Vm.RingCoefficients.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b8_next]]
  refine stepSq0 h hsq (hb b9_in_code (by simp [b9]) hp) run_b9 (by decide) hs fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b9Offset + b9.length = k + NativeRustcVmArm.Vm.RingCoefficients.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b9_next]]
  refine stepSq (b := 0) h hsq (hb b10_in_code (by simp [b10]) hp) run_b10 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b10Offset + b10.length = k + NativeRustcVmArm.Vm.RingCoefficients.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b10_next]]
  refine stepSq (b := 1) h hsq (hb b11_in_code (by simp [b11]) hp) run_b11 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b11Offset + b11.length = k + NativeRustcVmArm.Vm.RingCoefficients.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b11_next]]
  refine stepSq (b := 2) h hsq (hb b12_in_code (by simp [b12]) hp) run_b12 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b12Offset + b12.length = k + NativeRustcVmArm.Vm.RingCoefficients.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b12_next]]
  refine stepSq (b := 3) h hsq (hb b13_in_code (by simp [b13]) hp) run_b13 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b13Offset + b13.length = k + NativeRustcVmArm.Vm.RingCoefficients.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b13_next]]
  refine stepSq (b := 4) h hsq (hb b14_in_code (by simp [b14]) hp) run_b14 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b14Offset + b14.length = k + NativeRustcVmArm.Vm.RingCoefficients.b15Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b14_next]]
  refine stepSq (b := 5) h hsq (hb b15_in_code (by simp [b15]) hp) run_b15 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b15Offset + b15.length = k + NativeRustcVmArm.Vm.RingCoefficients.b16Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b15_next]]
  refine stepSq (b := 6) h hsq (hb b16_in_code (by simp [b16]) hp) run_b16 (by decide) (by decide) hs
    fun m hs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b16Offset + b16.length = k + NativeRustcVmArm.Vm.RingCoefficients.b17Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b16_next]]
  refine stepTail h (hb b17_in_code (by simp [b17]) hp) run_b17 (by decide) hs
    (fun m hs ↦ ?_) fun m hs ↦ ?_
  · rw [show Labels.label NativeRustcVmArm.Vm.RingCoefficients.label_1 = Host.addrOf (k + NativeRustcVmArm.Vm.RingCoefficients.b1Offset) from hp.label (j := NativeRustcVmArm.Vm.RingCoefficients.b1Offset) NativeRustcVmArm.Vm.RingCoefficients.label_1_at]
    exact .done _ (.inl ⟨rfl, hs⟩)
  · exact .done _ (.inr ⟨rfl, hs⟩)

/-- **`ring_coefficients`' contract.** -/
theorem ringCoefficients_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hsq : Spec (Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.RingCoefficients.entryLabel) RingCoefficientsPre RingCoefficientsPost := by
  intro m0 hpre
  have h := P.intro hpre
  rw [show Labels.label NativeRustcVmArm.Vm.RingCoefficients.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.RingCoefficients.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.RingCoefficients.entryOffset) NativeRustcVmArm.Vm.RingCoefficients.entry_at]
  refine stepEntry h (hb b0_in_code (by simp [b0]) hp) run_b0 (by decide) fun m1 h1 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingCoefficients.b0Offset + b0.length = k + NativeRustcVmArm.Vm.RingCoefficients.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingCoefficients.b0_next]]
  refine Eventually.bind (q := fun st ↦ st.pc = retOf m0 ∧ RingCoefficientsPost m0 st.data)
    (p := fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingCoefficients.b18Offset) ∧ Done m0 st.data) ?_ fun ⟨m, pc⟩ ⟨hpc, hD⟩ ↦ by
      simp only at hpc hD
      subst hpc
      exact stepExit h (hb b18_in_code (by simp [b18]) hp) hD
  refine Sym.loop (I := fun n st ↦ ∃ p, n = 8 - p ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingCoefficients.b1Offset) ∧ Head m0 p st.data)
    (fun n st ⟨p, hn, hpc, hH⟩ ↦ ?_) ⟨0, rfl, rfl, h1⟩
  obtain ⟨m, pc⟩ := st
  simp only at hpc hH
  subst hpc
  refine (turn hp h hmul hsq hH).mono fun st hst ↦ ?_
  rcases hst with ⟨hpc, hH'⟩ | hD
  · exact .inr ⟨8 - (p + 1), by have := hH.lt; have := hH'.lt; omega, ⟨p + 1, rfl, hpc, hH'⟩⟩
  · exact .inl hD

end

end NativeRustcVmArm.Ring.Coeff
