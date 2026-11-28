module

public import NativeRustcVmX64.Whir.FoldRow.Exec
public import NativeRustcVmX64.Whir.SubspaceAtTable.Leaf
public import NativeRustcVm.Whir.MathFold

/-!
# `fold_row`'s loop invariants (x86-64)

The lanes at RDI (`aOf`) after `r` rounds are `foldMem` of the entry's (`lanesOf`, `LanesAt`);
the frame from `fbOf` spills `x` at 32, the rounds' end at 24 (`Base`), the round's pointer at 40,
the factor's limbs at 16 (`c0`), 8 (`c1`).
- `RInv r` at a round's head (`b4`); `TInv r i` at the turn's head (`b10`): turn `i` of round
  `r`; `EInv r` after round `r` (`b3`); `Done` after the rounds (`b13`).
-/

namespace NativeRustcVmX64.Whir.FoldRow

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt EWAt ewOf)

@[expose] public section

/-- The frame's base. -/
def fbOf (m0 : MachineData) : BitVec 64 := stackBelow m0 96
/-- The lanes. -/
def aOf (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- `n`. -/
def nOf (m0 : MachineData) : Nat := (reg m0 .rsi).toNat
/-- `x`. -/
def xOf (m0 : MachineData) : UInt64 := .ofBitVec (reg m0 .rdx)
/-- The rounds' pointer. -/
def rpOf (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- The rounds' count. -/
def rnOf (m0 : MachineData) : Nat := (reg m0 .r8).toNat
/-- The rounds. -/
def roundsAr (m0 : MachineData) : Array FoldRoundW := (roundsOf m0.dmem (rpOf m0) (rnOf m0)).toArray
/-- The entry's lanes. -/
def v0 (m0 : MachineData) (j : Nat) : EW := ewOf m0.dmem (aOf m0 + BitVec.ofNat 64 (16 * j))
/-- The lanes after `r` rounds. -/
def lanesAt (m0 : MachineData) (r : Nat) : Nat → EW := foldMem (xOf m0) (roundsAr m0) (nOf m0) (v0 m0) r
/-- Round `r`. -/
def rdOf (m0 : MachineData) (r : Nat) : FoldRoundW := (roundsAr m0).getD r default
/-- Round `r`'s factor. -/
def facOf (m0 : MachineData) (r : Nat) : EW := foldFactor (xOf m0) (rdOf m0 r)
/-- The output. -/
def outsOf (m0 : MachineData) : List Region := [⟨aOf m0, lanesBytes⟩]

/-- The 64 lanes in memory. -/
def LanesAt (m0 : MachineData) (d : DataMem) (f : Nat → EW) : Prop :=
  ∀ j < 64, EWAt d (aOf m0 + BitVec.ofNat 64 (16 * j)) (f j)

/-- A body of `fold_row`. -/
abbrev Fr (m0 st : MachineData) : Prop := Frame m0 96 foldRowStack slots (outsOf m0) st

/-- What every state of the loops has. -/
structure Base (m0 st : MachineData) : Prop where
  fr : Fr m0 st
  x : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 32) (xOf m0)
  ed : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24)
    (.ofBitVec (rpOf m0 + BitVec.ofNat 64 (32 * rnOf m0)))
  r14 : reg st .r14 = aOf m0

/-- A round's head. -/
structure RInv (m0 : MachineData) (r : Nat) (st : MachineData) : Prop where
  base : Base m0 st
  hr : r < rnOf m0
  rcx : reg st .rcx = rpOf m0 + BitVec.ofNat 64 (32 * r)
  rbx : reg st .rbx = BitVec.ofNat 64 (nOf m0 >>> r)
  lanes : LanesAt m0 st.dmem (lanesAt m0 r)

/-- A turn's head. -/
structure TInv (m0 : MachineData) (r i : Nat) (st : MachineData) : Prop where
  base : Base m0 st
  hr : r < rnOf m0
  rd : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 40) (.ofBitVec (rpOf m0 + BitVec.ofNat 64 (32 * r)))
  f0 : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (facOf m0 r).c0
  f1 : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8) (facOf m0 r).c1
  hi : i < nOf m0 >>> (r + 1)
  rbx : reg st .rbx = BitVec.ofNat 64 (nOf m0 >>> (r + 1))
  r12 : reg st .r12 = BitVec.ofNat 64 i
  r13 : reg st .r13 = BitVec.ofNat 64 (8 + 16 * i)
  lanes : LanesAt m0 st.dmem (foldPart (xOf m0) (rdOf m0 r) i (lanesAt m0 r))

/-- After round `r`. -/
structure EInv (m0 : MachineData) (r : Nat) (st : MachineData) : Prop where
  base : Base m0 st
  hr : r < rnOf m0
  rd : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 40) (.ofBitVec (rpOf m0 + BitVec.ofNat 64 (32 * r)))
  rbx : reg st .rbx = BitVec.ofNat 64 (nOf m0 >>> (r + 1))
  lanes : LanesAt m0 st.dmem (lanesAt m0 (r + 1))

/-- After the rounds. -/
structure Done (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  r14 : reg st .r14 = aOf m0
  rbx : reg st .rbx = BitVec.ofNat 64 (nOf m0 >>> rnOf m0)
  lanes : LanesAt m0 st.dmem (lanesAt m0 (rnOf m0))

end

public section

theorem stack_le : 96 ≤ foldRowStack ∧ 96 + kmulStack ≤ foldRowStack ∧
    96 + ewMulStack ≤ foldRowStack := by decide

theorem roundsAr_size (m0 : MachineData) : (roundsAr m0).size = rnOf m0 := by
  simp [roundsAr, roundsOf]

theorem rdOf_eq (m0 : MachineData) {r : Nat} (hr : r < rnOf m0) :
    rdOf m0 r = ⟨ewOf m0.dmem (rpOf m0 + BitVec.ofNat 64 (32 * r)),
      ewOf m0.dmem (rpOf m0 + BitVec.ofNat 64 (32 * r + 16))⟩ := by
  simp [rdOf, roundsAr, roundsOf, hr]

theorem lanesAt_succ (m0 : MachineData) (r : Nat) :
    lanesAt m0 (r + 1) = foldPart (xOf m0) (rdOf m0 r) (nOf m0 >>> (r + 1)) (lanesAt m0 r) := rfl

/-- **The result**: lane `0` after the rounds, `0` once no lane is left. -/
theorem foldRow_eq' (m0 : MachineData) (hR : rnOf m0 ≤ 6) :
    foldRow (ewSlice m0 (reg m0 .rdi) (min (reg m0 .rsi).toNat laneCap)) (.ofBitVec (reg m0 .rdx))
      (roundsOf m0.dmem (reg m0 .rcx) (reg m0 .r8).toNat).toArray =
      if nOf m0 >>> rnOf m0 = 0 then 0 else lanesAt m0 (rnOf m0) 0 := by
  have := foldRow_eq (xOf m0) (roundsAr m0) (nOf m0) (v0 m0)
    (ewSlice m0 (reg m0 .rdi) (min (reg m0 .rsi).toNat laneCap))
    (by simp [ewSlice, nOf, laneCap]) (fun j hj ↦ by simp [ewSlice, v0, aOf])
    (by rw [roundsAr_size]; exact hR)
  rw [roundsAr_size] at this
  exact this

/-- Lanes after a store of lane `i`. -/
theorem lanesAt_update {m0 : MachineData} {d d' : DataMem} {f : Nat → EW} {i : Nat} {v : EW}
    (hf : LanesAt m0 d f) (hi : i < 64) (hnw : NoWrap (aOf m0) lanesBytes)
    (hv : EWAt d' (aOf m0 + BitVec.ofNat 64 (16 * i)) v)
    (hs : SameOutside d d' (InRange (aOf m0 + BitVec.ofNat 64 (16 * i)) 16)) :
    LanesAt m0 d' (Function.update f i v) := by
  intro j hj
  by_cases hji : j = i
  · subst hji; rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne hji]
    have hlb : lanesBytes = 1024 := rfl
    unfold NoWrap at hnw
    rw [hlb] at hnw
    refine NativeRustcVm.BytesAt.of_sameOutside_apart (hf j hj) hs ?_ ?_ ?_
    rotate_left
    · unfold NativeRustcVm.NoWrap
      rw [NativeRustcVm.length_ewBytes, toNat_add_ofNat _ _ (by omega)]; omega
    · unfold NativeRustcVm.NoWrap
      rw [toNat_add_ofNat _ _ (by omega)]; omega
    rw [NativeRustcVm.length_ewBytes]
    unfold NativeRustcVm.Apart
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
    omega

/-- Lanes kept by a change apart from them. -/
theorem lanesAt_keep {m0 : MachineData} {d d' : DataMem} {f : Nat → EW} {R : BitVec 64 → Prop}
    (hf : LanesAt m0 d f) (hs : SameOutside d d' R)
    (hR : ∀ j < 1024, ¬R (aOf m0 + BitVec.ofNat 64 j)) : LanesAt m0 d' f := fun j hj ↦
  NativeRustcVm.BytesAt.of_sameOutside (hf j hj) hs fun i hi ↦ by
    rw [NativeRustcVm.length_ewBytes] at hi
    rw [addr_add]
    exact hR _ (by omega)

end

end NativeRustcVmX64.Whir.FoldRow
