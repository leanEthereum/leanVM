module

public import NativeRustcVmArm.Keccak.WordsHash.Call
public import NativeRustcVmArm.Keccak.WordsHash.PadVals
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.MemLemmas

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`: what holds between its blocks

From the machine state `m0` at the entry (`out`, `count = n + 2`, `len = 9 + 8 n`, the bytecode
`bc` of `n` words in X0 to X4): the frame, the lanes and the whole blocks' count are
`keccak256_words::<hash_words's closure>`'s (`WordsHash.frame`, `Lanes`, `pre`, `nb`). The
bytecode's words at entry `bcw` (any words there are them, `eq_bcw`), and the closure's word `i`
(`wv`: `ivWord`, zero from the count). `Ctx m0 m`: SP the frame, X19 to X24 the function's values
(`out`, `len`, `n`, `bc`, `count`, `17 nb`), X26 to X28 the entry's, the frame's slots the
entry's X19 to X25, X29, X30, memory the entry's outside the stack the function uses, every
mapped byte mapped. `ctx_step` carries `Ctx` over a block that writes below the saved slots.
-/

namespace NativeRustcVmArm.WordsIv

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_keep)
open NativeRustcVmArm.WordsHash (frame nb frame_toNat stack_toNat frame_noWrap frame_aligned
  frame_mapped inStack_of_frame sp_lt firstOverlap_none_of_below)
open NativeRustcVmArm.Keccak (bytesAt_of_same not_inRange_of_apart)

@[expose] public section

/-- The bytecode's words at the entry. -/
def bcw (m0 : MachineData) : List UInt64 :=
  NativeRustcVm.wordsOf m0.dmem m0.regs.X3.toBitVec m0.regs.X4.toNat

/-- Word `i` the closure gives `keccak256_words`: `ivWord` of the bytecode, zero from the
count. -/
def wv (m0 : MachineData) (i : Nat) : UInt64 :=
  if i < m0.regs.X1.toNat then NativeRustcVm.Keccak.ivWord (bcw m0) i else 0

/-- The frame slots that hold the entry's registers. -/
def savedSlots : List (Nat × XReg) :=
  [(208, .X29), (224, .X30), (232, .X25), (240, .X24), (248, .X23), (256, .X22), (264, .X21),
    (272, .X20), (280, .X19)]

/-- The registers every block of the body keeps. -/
def ctxRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X26, .X27, .X28]

/-- **What holds throughout the body.** -/
structure Ctx (m0 m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = frame m0
  x19 : (m.regs.getXReg .X19).toBitVec = m0.regs.X0.toBitVec
  x20 : (m.regs.getXReg .X20).toBitVec = m0.regs.X2.toBitVec
  x21 : (m.regs.getXReg .X21).toBitVec = m0.regs.X4.toBitVec
  x22 : (m.regs.getXReg .X22).toBitVec = m0.regs.X3.toBitVec
  x23 : (m.regs.getXReg .X23).toBitVec = m0.regs.X1.toBitVec
  x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (17 * nb m0)
  x26 : m.regs.getXReg .X26 = m0.regs.getXReg .X26
  x27 : m.regs.getXReg .X27 = m0.regs.getXReg .X27
  x28 : m.regs.getXReg .X28 = m0.regs.getXReg .X28
  saved : AllOf (fun p : Nat × XReg => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (m0.regs.getXReg p.2).toBitVec) savedSlots
  same : SameOutside m0.dmem m.dmem
    (InRange (stackBelow m0 NativeRustcVmArm.keccak256WordsStack) NativeRustcVmArm.keccak256WordsStack)
  kept : Kept m0.dmem m.dmem

/-- The facts of the precondition the steps use. -/
structure Geo (m0 : MachineData) : Prop where
  stk : StackOk m0 NativeRustcVmArm.keccak256WordsStack
  cnt : m0.regs.X1.toNat = m0.regs.X4.toNat + 2
  len : m0.regs.X2.toNat = 9 + 8 * m0.regs.X4.toNat
  small : 9 + 8 * m0.regs.X4.toNat < 2 ^ 32
  map : Mapped m0.dmem m0.regs.X3.toBitVec (8 * m0.regs.X4.toNat)
  nw : NoWrap m0.regs.X3.toBitVec (8 * m0.regs.X4.toNat)
  ap : 0 < m0.regs.X4.toNat → Apart m0.regs.X3.toBitVec (8 * m0.regs.X4.toNat)
    (stackBelow m0 NativeRustcVmArm.keccak256WordsStack) NativeRustcVmArm.keccak256WordsStack

end

public section

theorem wv_of_lt {m0 : MachineData} {i : Nat} (h : i < m0.regs.X1.toNat) :
    wv m0 i = NativeRustcVm.Keccak.ivWord (bcw m0) i := by
  simp [wv, h]

theorem wv_of_ge {m0 : MachineData} {i : Nat} (h : m0.regs.X1.toNat ≤ i) : wv m0 i = 0 := by
  simp [wv, show ¬ i < m0.regs.X1.toNat by omega]

/-- Every word of a whole block is below the count. -/
theorem full_lt {m0 : MachineData} (g : Geo m0) {b j : Nat} (hb : b < nb m0) (hj : j ≤ 16) :
    17 * b + j < m0.regs.X1.toNat := by
  have := g.len
  have := g.cnt
  unfold nb at hb
  omega

/-- The bytecode's bytes are the entry's. -/
theorem bc_same {m0 : MachineData} (g : Geo m0) {i : Nat}
    (hi : i < 8 * m0.regs.X4.toNat) :
    ¬ InRange (stackBelow m0 NativeRustcVmArm.keccak256WordsStack)
      NativeRustcVmArm.keccak256WordsStack (m0.regs.X3.toBitVec + BitVec.ofNat 64 i) := by
  have hst := g.stk
  refine not_inRange_of_apart g.nw ?_ (g.ap (by omega)) hi
  have := hst.2.1
  have := @sp_lt m0
  have hs := stack_toNat hst
  unfold NoWrap
  rw [hs]
  simp only [NativeRustcVmArm.keccak256WordsStack, NativeRustcVmArm.keccakFStack] at *
  omega

/-- **The bytecode's words**, in any state of the body. -/
theorem wordsAt_bcw {m0 m : MachineData} (g : Geo m0) (hc : Ctx m0 m) :
    NativeRustcVm.WordsAt m.dmem m0.regs.X3.toBitVec (bcw m0) :=
  bytesAt_of_same hc.same (NativeRustcVm.wordsAt_of_mapped g.map) fun i hi => bc_same g (by
    rw [NativeRustcVm.length_wordsBytes, bcw, NativeRustcVm.length_wordsOf] at hi
    exact hi)

/-- The words of the bytecode at entry are `bcw`. -/
theorem eq_bcw {m0 : MachineData} (g : Geo m0) {w : List UInt64}
    (hlen : w.length = m0.regs.X4.toNat)
    (hw : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec w) : w = bcw m0 := by
  have hb := NativeRustcVm.wordsAt_of_mapped g.map
  refine List.ext_getElem (by rw [hlen, bcw, NativeRustcVm.length_wordsOf]) fun i h1 h2 => ?_
  exact (NativeRustcVm.WordsAt.getElem hw h1).unique (NativeRustcVm.WordsAt.getElem hb h2)

variable [Labels] {env : Env} {S S₀ : SState} {m m₀ : MachineData}

/-- **`Ctx` after a block** that writes only below the saved slots of the frame and keeps SP and
X19 to X24, X26 to X28. -/
theorem ctx_step {m0 m m' : MachineData}
    (hstk : StackOk m0 NativeRustcVmArm.keccak256WordsStack)
    (hc : Ctx m0 m) {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m rs vars) S m') (hwf : (Env.ofMachine m rs vars).WF)
    (hb : rs[0]? = some (frame m0, 288)) (hsp : S.sp = .ptr 0 0)
    (hregs : AllOf (fun r => S.reg r = some (.reg r)) ctxRegs)
    (hall : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 208) : Ctx m0 m' := by
  have hreg : ∀ r ∈ ctxRegs, (m'.regs.getXReg r).toBitVec = (m.regs.getXReg r).toBitVec :=
    fun r hr => (hm.regs r _ (mem_of_allOf (P := fun r => S.reg r = some (.reg r)) hregs hr)).trans
      rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm.sp, hsp]
    simp [Sym.eval, Env.base_ofMachine_eq, hb]
  · rw [hreg .X19 (by simp [ctxRegs])]; exact hc.x19
  · rw [hreg .X20 (by simp [ctxRegs])]; exact hc.x20
  · rw [hreg .X21 (by simp [ctxRegs])]; exact hc.x21
  · rw [hreg .X22 (by simp [ctxRegs])]; exact hc.x22
  · rw [hreg .X23 (by simp [ctxRegs])]; exact hc.x23
  · rw [hreg .X24 (by simp [ctxRegs])]; exact hc.x24
  · exact (UInt64.toBitVec_inj.mp (hreg .X26 (by simp [ctxRegs]))).trans hc.x26
  · exact (UInt64.toBitVec_inj.mp (hreg .X27 (by simp [ctxRegs]))).trans hc.x27
  · exact (UInt64.toBitVec_inj.mp (hreg .X28 (by simp [ctxRegs]))).trans hc.x28
  · have hsv := hc.saved
    have hb' : (Env.ofMachine m rs vars).regions[0]? = some (frame m0, 288) := hb
    have hk : ∀ o, 208 ≤ o → firstOverlap 0 o 8 S.mem = none := fun o ho =>
      firstOverlap_none_of_below (fun w hw _ => (hall w hw).2) ho
    simp only [AllOf, savedSlots] at hsv ⊢
    obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, -⟩ := hsv
    exact ⟨wordAt_keep hm hb' (by decide) (hk _ (by decide)) s0,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s1,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s2,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s3,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s4,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s5,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s6,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s7,
      wordAt_keep hm hb' (by decide) (hk _ (by decide)) s8, trivial⟩
  · intro p hp
    refine (NativeRustcArm.KeccakF.same_region hm hwf hb
      (fun w hw => ⟨(hall w hw).1, by have := (hall w hw).2; omega⟩) p
      fun h => hp (inStack_of_frame hstk h)).trans (hc.same p hp)
  · exact fun p h => hm.kept hwf p (hc.kept p h)

omit [Labels] in
/-- `Ctx` across a call that keeps memory, SP and the callee-saved registers. -/
theorem ctx_call {m0 m m' : MachineData} (hc : Ctx m0 m) (hd : m'.dmem = m.dmem)
    (hs : Saved m m') : Ctx m0 m' := by
  have r := hs.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs.2.1]; exact hc.sp
  · rw [r .X19 rfl]; exact hc.x19
  · rw [r .X20 rfl]; exact hc.x20
  · rw [r .X21 rfl]; exact hc.x21
  · rw [r .X22 rfl]; exact hc.x22
  · rw [r .X23 rfl]; exact hc.x23
  · rw [r .X24 rfl]; exact hc.x24
  · rw [r .X26 rfl]; exact hc.x26
  · rw [r .X27 rfl]; exact hc.x27
  · rw [r .X28 rfl]; exact hc.x28
  · rw [hd]; exact hc.saved
  · rw [hd]; exact hc.same
  · rw [hd]; exact hc.kept

end

end NativeRustcVmArm.WordsIv
