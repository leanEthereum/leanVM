module

public import NativeRustcVmArm.Whir.FoldRow.Inv

/-!
# What `fold_row`'s rounds share

The rounds' words in a body (`rd_words`), the spills (`spill_word`) and the lanes across a call
(`Spills.call`, `lanes_call`), across a store to a lane (`Spills.of_store`), across a block
writing the frame (`lanes_frame`).
-/

namespace NativeRustcVmArm.Whir.FoldRow

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (Region wordOf ewOf ewsOf)

public section

variable {m0 st st' : MachineData}

theorem pre_parts (hpre : FoldRowPre m0) :
    StackOk m0 foldRowStack ∧ WhirIn m0 (vOf m0) 1024 foldRowStack ∧
      WhirIn m0 m0.regs.X3.toBitVec (32 * rnOf m0) foldRowStack ∧
      NativeRustcVm.Apart (vOf m0) 1024 m0.regs.X3.toBitVec (32 * rnOf m0) ∧ rnOf m0 ≤ 6 :=
  hpre

/-- **The rounds' words** in a body. -/
theorem rd_words (hpre : FoldRowPre m0) (hfr : Fr m0 st) {r : Nat} (hr : r < rnOf m0) :
    wordOf st.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (32 * r)) = (rdOf m0 r).alpha.c0 ∧
    wordOf st.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (32 * r + 8)) =
      (rdOf m0 r).alpha.c1 ∧
    wordOf st.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (32 * r + 16)) =
      (rdOf m0 r).beta.c0 ∧
    wordOf st.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (32 * r + 24)) =
      (rdOf m0 r).beta.c1 := by
  obtain ⟨hS, hvin, hrin, hap, -⟩ := pre_parts hpre
  have key : ∀ o, o + 8 ≤ 32 * rnOf m0 →
      wordOf st.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 o) =
        wordOf m0.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 o) := fun o ho ↦
    NativeRustcVm.wordOf_congr fun i hi ↦ by
      rw [addr_add]
      refine hfr.get?_arg hS hrin (fun q hq ↦ ?_) _ (by omega)
      simp only [outsOf, List.mem_singleton] at hq
      subst hq
      exact ⟨hap.symm, hvin.1.2⟩
  rw [rdOf_eq m0 hr]
  simp only [ewOf, addr_add]
  exact ⟨key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega)⟩

/-- A spilled word. -/
theorem spill_word (h : Spills m0 st) {i : Nat} (hi : i < 4) :
    NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 (8 * i))
      [m0.regs.X2, m0.regs.X1, m0.regs.X4, m0.regs.X0][i] :=
  NativeRustcVm.wordsAt_getElem h (by simpa using hi)

theorem spills_len :
    ([m0.regs.X2, m0.regs.X1, m0.regs.X4, m0.regs.X0].flatMap NativeRustcVm.wordBytes).length =
      32 := by
  rw [NativeRustcVm.length_wordsBytes]; rfl

/-- The spills across a call. -/
theorem Spills.call (h : Spills m0 st) (hfr : Fr m0 st) (hS : StackOk m0 foldRowStack) {N : Nat}
    (hle : 128 + N ≤ foldRowStack)
    (hsame : SameOutside st.dmem st'.dmem (InRange (stackBelow st N) N)) : Spills m0 st' := by
  have := hfr.bytes_call hS hle hsame (o := 0) (by rw [spills_len (m0 := m0)]; omega)
    (by rw [NativeRustcVm.addr_add_zero]; exact h)
  rwa [NativeRustcVm.addr_add_zero] at this

/-- The spills where memory is kept. -/
theorem Spills.of_dmem (h : Spills m0 st) (hd : st'.dmem = st.dmem) : Spills m0 st' := by
  unfold Spills; rw [hd]; exact h

theorem Spills.of_same (h : Spills m0 st) {R : BitVec 64 → Prop}
    (hs : SameOutside st.dmem st'.dmem R) (hR : ∀ i < 32, ¬R (fbOf m0 + BitVec.ofNat 64 i)) :
    Spills m0 st' := fun i hi ↦ (hs _ (hR i (by rw [spills_len] at hi; exact hi))).trans (h i hi)

/-- The lanes across a call. -/
theorem lanes_call (hpre : FoldRowPre m0) (hfr : Fr m0 st) {N : Nat} (hle : 128 + N ≤ foldRowStack)
    (hsame : SameOutside st.dmem st'.dmem (InRange (stackBelow st N) N)) {f : Nat → EW}
    (h : LanesAt st.dmem (vOf m0) f) : LanesAt st'.dmem (vOf m0) f := by
  obtain ⟨hS, hvin, -, -, -⟩ := pre_parts hpre
  refine h.of_same hsame fun i hi ↦ not_inRange_of_apart (hfr.offStack hS hle hvin.2) hvin.1.2
    (stack_noWrap (hfr.stackOk hS rfl hle)) hi

/-- The frame is apart from a lane. -/
theorem frame_not_lane (hpre : FoldRowPre m0) {i : Nat} (hi : i < 64) :
    ∀ j < 128, ¬InRange (vOf m0 + BitVec.ofNat 64 (16 * i)) 16 (fbOf m0 + BitVec.ofNat 64 j) := by
  obtain ⟨hS, hvin, -, -, -⟩ := pre_parts hpre
  have hF : 128 ≤ foldRowStack := by decide
  have hap := apart_frame hvin.2 hF hS.2.1
  have hnw := hvin.1.2
  obtain ⟨-, hfnw, hfe⟩ := frame_ok hS hF
  have hfb : (fbOf m0).toNat = m0.regs.SP.toBitVec.toNat - 128 := hfe
  intro j hj
  refine not_inRange_of_apart (n := 128) ?_ hfnw (NativeRustcVm.NoWrap.sub hnw (by omega))
    (by omega)
  unfold Apart NoWrap at *
  rw [toNat_add_ofNat' (by omega), hfb]
  rw [hfe] at hap
  omega

/-- The lanes across a block writing the frame only. -/
theorem lanes_frame (hpre : FoldRowPre m0) {f : Nat → EW}
    (h : LanesAt st.dmem (vOf m0) f)
    (hs : SameOutside st.dmem st'.dmem (InRange (fbOf m0) 128)) : LanesAt st'.dmem (vOf m0) f := by
  obtain ⟨hS, hvin, -, -, -⟩ := pre_parts hpre
  have hF : 128 ≤ foldRowStack := by decide
  obtain ⟨-, hfnw, -⟩ := frame_ok hS hF
  exact h.of_same hs fun i hi ↦ not_inRange_of_apart (apart_frame hvin.2 hF hS.2.1) hvin.1.2
    hfnw hi

/-- Round `r`'s turn `i` done (`r ≤ 5`), at the counting block. -/
structure Turned (m0 : MachineData) (r i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  x22 : st.regs.X22 = m0.regs.X3
  fac : (⟨st.regs.X24 ^^^ st.regs.X27, st.regs.X25 ^^^ st.regs.X28⟩ : EW) =
    foldFactor m0.regs.X2 (rdOf m0 (r - 1))
  x26 : st.regs.X26.toNat = nOf m0 >>> r
  x29 : st.regs.X29.toNat = i
  hi : i < nOf m0 >>> r
  x20 : st.regs.X20.toBitVec = vOf m0 + BitVec.ofNat 64 (16 * i + 8)
  x23 : st.regs.X23.toBitVec = vOf m0 + BitVec.ofNat 64 (32 * i + 16)
  lanes : LanesAt st.dmem (vOf m0)
    (foldPart m0.regs.X2 (rdOf m0 (r - 1)) (i + 1) (memOf m0 (r - 1)))
  hr : r ≤ rnOf m0

/-- Round 6's turn `i` done. -/
structure Turned6 (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  fac : (⟨st.regs.X22 ^^^ st.regs.X24, st.regs.X20 ^^^ st.regs.X25⟩ : EW) =
    foldFactor m0.regs.X2 (rdOf m0 5)
  x21 : st.regs.X21.toNat = nOf m0 >>> 6
  x26 : st.regs.X26 = 1
  x23 : st.regs.X23.toNat = i
  hi : i < nOf m0 >>> 6
  x27 : st.regs.X27.toBitVec = vOf m0 + BitVec.ofNat 64 (16 * i + 8)
  x28 : st.regs.X28.toBitVec = vOf m0 + BitVec.ofNat 64 (32 * i + 16)
  lanes : LanesAt st.dmem (vOf m0) (foldPart m0.regs.X2 (rdOf m0 5) (i + 1) (memOf m0 5))
  hr : 6 ≤ rnOf m0

end

end NativeRustcVmArm.Whir.FoldRow
