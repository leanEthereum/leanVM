module

public import NativeRustcVmArm.Whir.NovelEval.Exec
public import NativeRustcVm.Whir.MathNovel

/-!
# `novel_eval`'s loop invariants

The basis lives in the frame from SP (`fbOf`), `novelPre` of the `What`s read so far
(`basisOf`).
- `OInv j` at the doubling loop's head (`b4`): `j` values read, the basis shorter than the
  coefficients;
- `IInv j t` at the inner loop's head (`b6`): `t` products of value `j` written after the basis;
- `Post8 j` after the inner loop (`b8`): the basis of `j + 1` values;
- `Mid` when the basis is complete (`b9`);
- `SInv t` at the sum's head (`b11`): `t` products summed.
-/

namespace NativeRustcVmArm.Whir.NovelEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir

@[expose] public section

/-- The frame's base (the basis). -/
def fbOf (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 1120
/-- The coefficients' count. -/
def cnt (m0 : MachineData) : Nat := m0.regs.X2.toNat
/-- The `What`s' count. -/
def wn (m0 : MachineData) : Nat := m0.regs.X4.toNat
/-- The `What`s. -/
def whatOf (m0 : MachineData) : Array UInt64 := wordSlice m0 m0.regs.X3.toBitVec (wn m0)
/-- The coefficients. -/
def csOf (m0 : MachineData) : Array EW := slice m0 m0.regs.X1 m0.regs.X2
/-- The basis after `j` values. -/
def basisOf (m0 : MachineData) (j : Nat) : Array UInt64 := novelPre (whatOf m0) (cnt m0) j

/-- The body's frame: no output written yet. -/
abbrev NFrame (m0 st : MachineData) : Prop := Frame m0 1120 novelEvalStack slots [] st

/-- The argument registers kept. -/
structure Regs (m0 st : MachineData) : Prop where
  x19 : st.regs.X19 = m0.regs.X0
  x20 : st.regs.X20 = m0.regs.X1
  x21 : st.regs.X21 = m0.regs.X2

/-- The doubling loop's head after `j` values. -/
structure OInv (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : NFrame m0 st
  rg : Regs m0 st
  hj : j ≤ wn m0
  lt : (basisOf m0 j).size < cnt m0
  x22 : st.regs.X22.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * j)
  x25 : st.regs.X25.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * wn m0)
  x24 : st.regs.X24.toNat = (basisOf m0 j).size
  basis : NativeRustcVm.WordsAt st.dmem (fbOf m0) (basisOf m0 j).toList

/-- The inner loop's head: `t` products of value `j`. -/
structure IInv (m0 : MachineData) (j t : Nat) (st : MachineData) : Prop where
  fr : NFrame m0 st
  rg : Regs m0 st
  hj : j < wn m0
  lt : (basisOf m0 j).size < cnt m0
  x22 : st.regs.X22.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * j)
  x25 : st.regs.X25.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * wn m0)
  x24 : st.regs.X24.toNat = (basisOf m0 j).size
  x23 : st.regs.X23 = (whatOf m0).getD j 0
  x26 : st.regs.X26.toBitVec = fbOf m0 + BitVec.ofNat 64 (8 * t)
  x27 : st.regs.X27.toNat = (basisOf m0 j).size - t
  basis : NativeRustcVm.WordsAt st.dmem (fbOf m0) (basisOf m0 j).toList
  new : NativeRustcVm.WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 (8 * (basisOf m0 j).size))
    (((basisOf m0 j).toList.take t).map (kmul · ((whatOf m0).getD j 0)))

/-- After the inner loop: the basis of `j + 1` values. -/
structure Post8 (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : NFrame m0 st
  rg : Regs m0 st
  hj : j < wn m0
  lt : (basisOf m0 j).size < cnt m0
  x22 : st.regs.X22.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * j)
  x25 : st.regs.X25.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * wn m0)
  x24 : st.regs.X24.toNat = (basisOf m0 j).size
  basis : NativeRustcVm.WordsAt st.dmem (fbOf m0) (basisOf m0 (j + 1)).toList

/-- The basis complete. -/
structure Mid (m0 : MachineData) (st : MachineData) : Prop where
  fr : NFrame m0 st
  rg : Regs m0 st
  x24 : st.regs.X24.toNat = (basisOf m0 (wn m0)).size
  basis : NativeRustcVm.WordsAt st.dmem (fbOf m0) (basisOf m0 (wn m0)).toList

/-- The products' count. -/
def lenOf (m0 : MachineData) : Nat := min (basisOf m0 (wn m0)).size (cnt m0)

/-- The sum's head after `t` products. -/
structure SInv (m0 : MachineData) (t : Nat) (st : MachineData) : Prop where
  fr : NFrame m0 st
  x19 : st.regs.X19 = m0.regs.X0
  x25 : st.regs.X25.toNat = lenOf m0 - t
  x26 : st.regs.X26.toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * t + 8)
  x27 : st.regs.X27.toBitVec = fbOf m0 + BitVec.ofNat 64 (8 * t)
  x24 : st.regs.X24 = (novelAcc (csOf m0) (basisOf m0 (wn m0)) t).c0
  x23 : st.regs.X23 = (novelAcc (csOf m0) (basisOf m0 (wn m0)) t).c1
  basis : NativeRustcVm.WordsAt st.dmem (fbOf m0) (basisOf m0 (wn m0)).toList

/-- The sum done. -/
structure Done (m0 : MachineData) (st : MachineData) : Prop where
  fr : NFrame m0 st
  x19 : st.regs.X19 = m0.regs.X0
  x24 : st.regs.X24 = (novelAcc (csOf m0) (basisOf m0 (wn m0)) (lenOf m0)).c0
  x23 : st.regs.X23 = (novelAcc (csOf m0) (basisOf m0 (wn m0)) (lenOf m0)).c1

end

public section

theorem stack_eq : novelEvalStack = 1232 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1120 := by decide

theorem slots_ge : ∀ p ∈ slots, 1024 ≤ p.1 := by decide

theorem x30_mem : XReg.X30 ∈ slots.map (·.2) :=
  List.mem_map.mpr ⟨(1040, .X30), by simp [slots], rfl⟩

theorem whatOf_size (m0 : MachineData) : (whatOf m0).size = wn m0 := by simp [whatOf, wordSlice]

theorem csOf_size (m0 : MachineData) : (csOf m0).size = cnt m0 := by simp [csOf, slice, cnt]

theorem whatOf_getD (m0 : MachineData) {j : Nat} (hj : j < wn m0) :
    (whatOf m0).getD j 0 = NativeRustcVm.wordOf m0.dmem
      (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * j)) := by
  simp [whatOf, wordSlice, hj]

theorem csOf_get (m0 : MachineData) {t : Nat} (ht : t < (csOf m0).size) :
    (csOf m0)[t] = NativeRustcVm.ewOf m0.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * t)) := by
  simp [csOf, slice]

/-- A doubled basis fits the 64 words: at most 32 long. -/
theorem basis_le_32 (m0 : MachineData) (j : Nat) (hc : cnt m0 ≤ 64)
    (hlt : (basisOf m0 j).size < cnt m0) : (basisOf m0 j).size ≤ 32 := by
  obtain ⟨e, he⟩ := novelPre_pow (whatOf m0) (cnt m0) j
  exact size_le_32 he (by unfold basisOf at hlt ⊢; omega)

/-- The basis after a value it doubles. -/
theorem basisOf_succ (m0 : MachineData) {j : Nat} (hj : j < wn m0)
    (hlt : (basisOf m0 j).size < cnt m0) :
    basisOf m0 (j + 1) = basisOf m0 j ++ (basisOf m0 j).map (kmul · ((whatOf m0).getD j 0)) := by
  have h : ¬cnt m0 ≤ (novelPre (whatOf m0) (cnt m0) j).size := by unfold basisOf at hlt; omega
  rw [basisOf, novelPre_succ _ _ (by rw [whatOf_size]; exact hj), novelStep]
  simp [h, basisOf, hj, whatOf_size]

end

end NativeRustcVmArm.Whir.NovelEval
