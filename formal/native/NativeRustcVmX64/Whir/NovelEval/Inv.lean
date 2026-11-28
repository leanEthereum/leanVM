module

public import NativeRustcVmX64.Whir.NovelEval.Exec
public import NativeRustcVmX64.Whir.SubspaceAtTable.Leaf
public import NativeRustcVm.Whir.MathNovel

/-!
# `novel_eval`'s loop invariants (x86-64)

The frame's base `fbOf m0` (the 1104 bytes below the entry's RSP); the basis from `fb + 32`,
`novelPre` of the `What`s read so far (`basisOf`); spilled: the output pointer at `fb + 16`, the
coefficients' pointer at `fb + 24` (`Spill`), the `What`s' end at `fb + 8` (`endAt`).
- `OInv j` at the doubling loop's head (`b4`): `j` values read, the basis shorter than the
  coefficients;
- `IInv j t` at the inner loop's head (`b6a`): `t` products of value `j` written after the basis;
- `Mid` when the basis is complete (`b9`);
- `SInv t` at the sum's head (`b11a`): `t` products summed; `Done` after the sum (`b16`).
-/

namespace NativeRustcVmX64.Whir.NovelEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (Region WordAt WordsAt)

@[expose] public section

/-- The frame's base. -/
def fbOf (m0 : MachineData) : BitVec 64 := stackBelow m0 1104
/-- The coefficients' count. -/
def cnt (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
/-- The `What`s' count. -/
def wn (m0 : MachineData) : Nat := (reg m0 .r8).toNat
/-- The `What`s. -/
def whatOf (m0 : MachineData) : Array UInt64 := wordSlice m0 (reg m0 .rcx) (wn m0)
/-- The coefficients. -/
def csOf (m0 : MachineData) : Array EW := slice m0 (reg m0 .rsi) (reg m0 .rdx)
/-- The basis after `j` values. -/
def basisOf (m0 : MachineData) (j : Nat) : Array UInt64 := novelPre (whatOf m0) (cnt m0) j
/-- The products' count. -/
def lenOf (m0 : MachineData) : Nat := min (basisOf m0 (wn m0)).size (cnt m0)
/-- The sum after `t` products. -/
def accOf (m0 : MachineData) (t : Nat) : EW := novelAcc (csOf m0) (basisOf m0 (wn m0)) t

/-- The body's frame: no output written yet. -/
abbrev NFrame (m0 st : MachineData) : Prop := Frame m0 1104 novelEvalStack slots [] st

/-- The spilled pointers. -/
structure Spill (m0 st : MachineData) : Prop where
  out : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (.ofBitVec (reg m0 .rdi))
  cs : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofBitVec (reg m0 .rsi))

/-- The `What`s' end, spilled. -/
def EndAt (m0 st : MachineData) : Prop :=
  WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8)
    (.ofBitVec (reg m0 .rcx + BitVec.ofNat 64 (8 * wn m0)))

/-- The doubling loop's head after `j` values. -/
structure OInv (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : NFrame m0 st
  sp : Spill m0 st
  ed : EndAt m0 st
  hj : j ≤ wn m0
  lt : (basisOf m0 j).size < cnt m0
  r12 : reg st .r12 = reg m0 .rcx + BitVec.ofNat 64 (8 * j)
  rbp : (reg st .rbp).toNat = (basisOf m0 j).size
  r14 : reg st .r14 = reg m0 .rdx
  basis : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 32) (basisOf m0 j).toList

/-- The inner loop's head: `t` products of value `j`. -/
structure IInv (m0 : MachineData) (j t : Nat) (st : MachineData) : Prop where
  fr : NFrame m0 st
  sp : Spill m0 st
  ed : EndAt m0 st
  hj : j < wn m0
  lt : (basisOf m0 j).size < cnt m0
  ht : t < (basisOf m0 j).size
  r12 : reg st .r12 = reg m0 .rcx + BitVec.ofNat 64 (8 * j)
  rbp : (reg st .rbp).toNat = (basisOf m0 j).size
  rbx : reg st .rbx = reg m0 .rdx
  r13 : reg st .r13 = ((whatOf m0).getD j 0).toBitVec
  r14 : reg st .r14 = fbOf m0 + BitVec.ofNat 64 (32 + 8 * t)
  r15 : (reg st .r15).toNat = (basisOf m0 j).size - t
  basis : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 32) (basisOf m0 j).toList
  new : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 (32 + 8 * (basisOf m0 j).size))
    (((basisOf m0 j).toList.take t).map (kmul · ((whatOf m0).getD j 0)))

/-- The basis complete. -/
structure Mid (m0 : MachineData) (st : MachineData) : Prop where
  fr : NFrame m0 st
  sp : Spill m0 st
  rbp : (reg st .rbp).toNat = (basisOf m0 (wn m0)).size
  r14 : reg st .r14 = reg m0 .rdx
  basis : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 32) (basisOf m0 (wn m0)).toList

/-- The sum's head after `t` products. -/
structure SInv (m0 : MachineData) (t : Nat) (st : MachineData) : Prop where
  fr : NFrame m0 st
  sp : Spill m0 st
  len : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8) (.ofNat (8 * lenOf m0))
  ht : t < lenOf m0
  r15 : reg st .r15 = BitVec.ofNat 64 (8 * t)
  r14 : reg st .r14 = (accOf m0 t).c0.toBitVec
  rbx : reg st .rbx = (accOf m0 t).c1.toBitVec
  basis : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 32) (basisOf m0 (wn m0)).toList

/-- The sum done. -/
structure Done (m0 : MachineData) (st : MachineData) : Prop where
  fr : NFrame m0 st
  sp : Spill m0 st
  r14 : reg st .r14 = (accOf m0 (lenOf m0)).c0.toBitVec
  rbx : reg st .rbx = (accOf m0 (lenOf m0)).c1.toBitVec

end

public section

theorem stack_eq : novelEvalStack = 1152 := rfl

theorem whatOf_size (m0 : MachineData) : (whatOf m0).size = wn m0 := by
  simp [whatOf, wordSlice, wn]

theorem csOf_size (m0 : MachineData) : (csOf m0).size = cnt m0 := by simp [csOf, slice, cnt]

theorem whatOf_getD (m0 : MachineData) {j : Nat} (hj : j < wn m0) :
    (whatOf m0).getD j 0 = NativeRustcVm.wordOf m0.dmem (reg m0 .rcx + BitVec.ofNat 64 (8 * j)) := by
  unfold whatOf wordSlice
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_eq_getElem (by simp; exact hj), Option.getD_some,
    NativeRustcVm.getElem_wordsOf]

theorem csOf_get (m0 : MachineData) {t : Nat} (ht : t < (csOf m0).size) :
    (csOf m0)[t] = NativeRustcVm.ewOf m0.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * t)) := by
  simp [csOf, slice]

/-- A doubled basis fits: at most 32 long. -/
theorem basis_le_32 (m0 : MachineData) (j : Nat) (hc : cnt m0 ≤ 64)
    (hlt : (basisOf m0 j).size < cnt m0) : (basisOf m0 j).size ≤ 32 := by
  obtain ⟨e, he⟩ := novelPre_pow (whatOf m0) (cnt m0) j
  exact size_le_32 he (by unfold basisOf at hlt ⊢; omega)

theorem basis_pos (m0 : MachineData) (j : Nat) : 0 < (basisOf m0 j).size :=
  novelPre_size_pos _ _ _

/-- The basis after a value it doubles. -/
theorem basisOf_succ (m0 : MachineData) {j : Nat} (hj : j < wn m0)
    (hlt : (basisOf m0 j).size < cnt m0) :
    basisOf m0 (j + 1) = basisOf m0 j ++ (basisOf m0 j).map (kmul · ((whatOf m0).getD j 0)) := by
  have h : ¬cnt m0 ≤ (novelPre (whatOf m0) (cnt m0) j).size := by unfold basisOf at hlt; omega
  rw [basisOf, novelPre_succ _ _ (by rw [whatOf_size]; exact hj), novelStep]
  simp [h, basisOf, hj, whatOf_size]

/-- Once long enough, the basis is the final one. -/
theorem basisOf_final (m0 : MachineData) {j : Nat} (hj : j ≤ wn m0)
    (hc : cnt m0 ≤ (basisOf m0 j).size) : basisOf m0 (wn m0) = basisOf m0 j :=
  novelPre_stable (whatOf m0) hc (wn m0) hj

theorem accOf_succ (m0 : MachineData) {t : Nat} (ht : t < lenOf m0) :
    accOf m0 (t + 1) = accOf m0 t +
      EW.scale ((basisOf m0 (wn m0))[t]'(by unfold lenOf at ht; omega))
        ((csOf m0)[t]'(by rw [csOf_size]; unfold lenOf at ht; omega)) :=
  novelAcc_succ _ _ (by rw [csOf_size]; unfold lenOf at ht; omega)
    (by unfold lenOf at ht; omega)

/-- **The result**: the sum of all products. -/
theorem novelEval_eq' (m0 : MachineData) :
    novelEval (slice m0 (reg m0 .rsi) (reg m0 .rdx)) (wordSlice m0 (reg m0 .rcx) (reg m0 .r8).toNat) =
      accOf m0 (lenOf m0) := by
  rw [novelEval_eq]
  show novelAcc (csOf m0) (novelPre (whatOf m0) (csOf m0).size (whatOf m0).size)
    (min (novelPre (whatOf m0) (csOf m0).size (whatOf m0).size).size (csOf m0).size) = _
  rw [csOf_size, whatOf_size]
  rfl

end

end NativeRustcVmX64.Whir.NovelEval
