module

public import NativeRustcVmArm.Tables.TableWeights.Inv

/-!
# `table_weights`: the values its blocks compute

A weight's update (`W_succ`), a height read from the frame (`H_getD`, `ult_hword`), the factor a
block passes `EW::mul` (`factor_eq`), the frame's words through the environment (`load_fw`).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm (wordOf wordsOf)

public section

variable {m0 : MachineData}

theorem size_H : (H m0).size = 6 := by simp [H, heightsOf, nTables]

theorem size_P : (P m0).size = n m0 := by simp [P, slice, n]

theorem H_getD {j : Nat} (hj : j < 6) : (H m0).getD j 0 = (hword m0 j).toNat := by
  simp [H, heightsOf, hword, nTables, Array.getD, hj, wordsOf]

theorem getD_of_lt {α : Type} {a : Array α} {j : Nat} {d : α} (h : j < a.size) :
    a.getD j d = a[j] := by
  simp [Array.getD, h]

theorem W_succ {c j : Nat} (hc : c < n m0) (hj : j < 6) :
    (W m0 (c + 1)).getD j 0 =
      EW.mul ((W m0 c).getD j 0) (if c < (H m0).getD j 0 then fac m0 c else ch m0 c) := by
  have hcP : c < (P m0).size := by rw [size_P]; exact hc
  have hW : (twPrefix (H m0) (E m0) (P m0) c).size = 6 := by rw [size_twPrefix, size_H]
  have hs' : (twStep (H m0) (E m0) (twPrefix (H m0) (E m0) (P m0) c) ((P m0)[c], c)).size = 6 := by
    rw [size_twStep _ _ _ _ (by rw [size_twPrefix]), size_H]
  unfold W fac ch
  rw [twPrefix_succ _ _ _ hcP, getD_of_lt (by omega), getElem_twStep,
    getD_of_lt (a := twPrefix (H m0) (E m0) (P m0) c) (by omega),
    getD_of_lt (a := H m0) (by rw [size_H]; omega), getD_of_lt (a := P m0) hcP]
  rfl

theorem ult_hword {c j : Nat} (hc : c < 2 ^ 64) (hj : j < 6) :
    (BitVec.ofNat 64 c).ult (hword m0 j) = decide (c < (H m0).getD j 0) := by
  rw [H_getD hj, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

/-- A frame word through the environment of a state with SP the frame's base. -/
theorem load_fw (m : MachineData) (rs : List (BitVec 64 × Nat)) (o : Nat) :
    (Env.ofMachine m ((fb m0, 240) :: rs)).load 0 o 8 = fw m0 m o := by
  rw [load8]
  rfl

theorem toBitVec_xor (a b : UInt64) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

/-- **The factor a block passes `EW::mul`.** -/
theorem factor_eq {c j : Nat} (hc : c < 2 ^ 64) (hj : j < 6) {a25 a26 a29 a24 : BitVec 64}
    (x25 : a25 = ((fac m0 c).c0 ^^^ (ch m0 c).c0).toBitVec) (x26 : a26 = (fac m0 c).c1.toBitVec)
    (x29 : a29 = (ch m0 c).c0.toBitVec) (x24 : a24 = (ch m0 c).c1.toBitVec) :
    (⟨.ofBitVec ((if (BitVec.ofNat 64 c).ult (hword m0 j) then a25 else 0#64) ^^^ a29),
      .ofBitVec (if (BitVec.ofNat 64 c).ult (hword m0 j) then a26 else a24)⟩ : EW) =
      if c < (H m0).getD j 0 then fac m0 c else ch m0 c := by
  rw [ult_hword hc hj, x25, x26, x29, x24]
  by_cases h : c < (H m0).getD j 0
  · simp only [h, decide_true, ite_true]
    rw [← toBitVec_xor, UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, BitVec.zero_xor]

variable [Labels]

/-- A weight a block passes `EW::mul`: a register and a frame word. -/
theorem weight_sym {m : MachineData} {rs : List (BitVec 64 × Nat)} {r : XReg} {o : Nat} {w : EW}
    (h0 : rg m r = w.c0.toBitVec)
    (h1 : fw m0 m o = w.c1.toBitVec) :
    (⟨.ofBitVec ((Sym.reg r).eval (Env.ofMachine m ((fb m0, 240) :: rs))),
      .ofBitVec ((Sym.load 0 o 8).eval (Env.ofMachine m ((fb m0, 240) :: rs)))⟩ : EW) = w := by
  simp only [Sym.eval, load_fw, Env.ofMachine_regs]
  rw [show (m.regs.getXReg r).toBitVec = rg m r from rfl, h0, h1]

/-- A weight a block passes `EW::mul`: two frame words. -/
theorem weight_sym2 {m : MachineData} {rs : List (BitVec 64 × Nat)} {o o' : Nat} {w : EW}
    (h0 : fw m0 m o = w.c0.toBitVec)
    (h1 : fw m0 m o' = w.c1.toBitVec) :
    (⟨.ofBitVec ((Sym.load 0 o 8).eval (Env.ofMachine m ((fb m0, 240) :: rs))),
      .ofBitVec ((Sym.load 0 o' 8).eval (Env.ofMachine m ((fb m0, 240) :: rs)))⟩ : EW) = w := by
  simp only [Sym.eval, load_fw]
  rw [h0, h1]

end

end NativeRustcVmArm.Tables.TableWeights
