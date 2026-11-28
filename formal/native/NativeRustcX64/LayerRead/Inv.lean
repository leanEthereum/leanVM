module

public import NativeRustcX64.LayerRead.Glue
public import NativeRustcX64.Spec.LayerRead
public import NativeRustcX64.Code.Xmss.LayerRead
public import NativeRustcX64.Got

/-!
# Slice parser invariants

Region 0 starts at the deepest call's return address. The frame starts at 8, the saved input
pointer is at 16, the output pointer at 24, the temporary chain/path buffer at 32, and the
copied chain values at 960. Six saved registers occupy 1888 through 1935.
-/

namespace NativeRustcX64.Xmss.LayerRead

open NativeRustcX64.Sym

@[expose] public section

def base (m : MachineData) : BitVec 64 := stackBelow m layerReadStack
def out (m : MachineData) : BitVec 64 := reg m .rdi
def cur (m : MachineData) : BitVec 64 := reg m .rsi
def sig (m : MachineData) : BitVec 64 := LayerReadPre.input m
def remaining (m : MachineData) : Nat := LayerReadPre.remaining m
def saveRegs : List Reg64 := [.rbx, .r12, .r13, .r14, .r15, .rbp]
def rand (m : MachineData) : List UInt8 := NativeRustc.slice (LayerReadPre.bytes m) 0 16
def chainSlot (m : MachineData) (j : Nat) : List UInt8 :=
  NativeRustc.slice (LayerReadPre.bytes m) (16 + 16 * j) 16
def pathSlot (m : MachineData) (j : Nat) : List UInt8 :=
  NativeRustc.slice (LayerReadPre.bytes m) (944 + 16 * j) 16
def chainBytes (m : MachineData) : List UInt8 := ((List.range 58).map (chainSlot m)).flatten
def pathBytes (m : MachineData) : List UInt8 := ((List.range 16).map (pathSlot m)).flatten
def Scratch (m : MachineData) (p : BitVec 64) : Prop :=
  InRange (base m) layerReadStack p ∨ InRange (cur m) 16 p
abbrev ParserGot [Labels] (m : MachineData) : Prop :=
  GotAt m layerReadStack [(out m, 1200), (cur m, 16), (sig m, 1200)] ["memcpy"]

structure CommonAt (m₀ m : MachineData) (o : Nat) : Prop where
  rsp : reg m .rsp = base m₀ + BitVec.ofNat 64 o
  same : SameOutside m₀.dmem m.dmem (Scratch m₀)
  kept : Kept m₀.dmem m.dmem
  save : ∀ j < 6, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (1888 + 8 * j))
    (regBytes (reg m₀ (saveRegs.getD j .rax)))
  output : BytesAt m.dmem (base m₀ + 24#64) (regBytes (out m₀))

abbrev Common (m₀ m : MachineData) : Prop := CommonAt m₀ m 8

/-- Each turn reads two chain values. The length register excludes the preceding turns, but
not the randomizer; the slice descriptor already excludes the randomizer after the first turn. -/
structure LoopAt (m₀ m : MachineData) (i : Nat) : Prop where
  common : Common m₀ m
  lt : i < 29
  r14 : reg m .r14 = cur m₀
  r11 : reg m .r11 = sig m₀
  r12 : reg m .r12 = BitVec.ofNat 64 (remaining m₀ - 32 * i)
  rax : reg m .rax = BitVec.ofNat 64 ((remaining m₀ - 16) / 16)
  rdx : reg m .rdx = BitVec.ofNat 64 ((remaining m₀ - 16) / 16 - 2 * i)
  rdi : reg m .rdi = BitVec.ofNat 64 (2 * i)
  rcx : reg m .rcx = BitVec.ofNat 64 (32 * i)
  rsi : reg m .rsi = base m₀ + 32#64
  chain : ∀ j < 2 * i, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (32 + 16 * j))
    (chainSlot m₀ j)

structure LoopDone (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  r14 : reg m .r14 = cur m₀
  r11 : reg m .r11 = sig m₀
  r12 : reg m .r12 = BitVec.ofNat 64 (remaining m₀ - 928)
  r13 : reg m .r13 = sig m₀ + 912#64
  r15 : reg m .r15 = sig m₀ + 944#64
  rbx : reg m .rbx = BitVec.ofNat 64 (remaining m₀ - 896)
  rbp : reg m .rbp = BitVec.ofNat 64 (remaining m₀ - 944)
  rsi : reg m .rsi = base m₀ + 32#64
  chain : ∀ j < 58, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (32 + 16 * j))
    (chainSlot m₀ j)

structure MidAt (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  r14 : reg m .r14 = cur m₀
  r12 : reg m .r12 = BitVec.ofNat 64 (remaining m₀ - 928)
  r13 : reg m .r13 = sig m₀ + 912#64
  r15 : reg m .r15 = sig m₀ + 944#64
  rbx : reg m .rbx = BitVec.ofNat 64 (remaining m₀ - 896)
  rbp : reg m .rbp = BitVec.ofNat 64 (remaining m₀ - 944)
  input : BytesAt m.dmem (base m₀ + 16#64) (regBytes (sig m₀))
  chain : BytesAt m.dmem (base m₀ + 960#64) (chainBytes m₀)

structure PathCall [Labels] (m₀ m : MachineData) : Prop where
  common : CommonAt m₀ m 0
  r14 : reg m .r14 = out m₀
  rdi : reg m .rdi = out m₀
  rsi : reg m .rsi = base m₀ + 32#64
  rdx : reg m .rdx = 256#64
  cursor : BytesAt m.dmem (cur m₀) (regBytes (sig m₀ + 1200#64))
  length : BytesAt m.dmem (cur m₀ + 8#64) (regBytes (BitVec.ofNat 64 (remaining m₀ - 1200)))
  input : BytesAt m.dmem (base m₀ + 16#64) (regBytes (sig m₀))
  chain : BytesAt m.dmem (base m₀ + 960#64) (chainBytes m₀)
  path : BytesAt m.dmem (base m₀ + 32#64) (pathBytes m₀)
  rbx : reg m .rbx = (Labels.label "memcpy").toBitVec

structure Pre (m : MachineData) : Prop where
  rspLe : layerReadStack ≤ (rspOf m).toNat
  rspNW : (rspOf m).toNat + 8 ≤ 2 ^ 64
  baseNat : (base m).toNat = (rspOf m).toNat - layerReadStack
  stackMapped : Mapped m.dmem (base m) 1944
  enough : 1200 ≤ remaining m
  lengthLt : remaining m < 2 ^ 64
  outMapped : Mapped m.dmem (out m) 1200
  curMapped : Mapped m.dmem (cur m) 16
  sigMapped : Mapped m.dmem (sig m) 1200
  outNW : NoWrap (out m) 1200
  curNW : NoWrap (cur m) 16
  sigNW : NoWrap (sig m) 1200
  outF : Apart (out m) 1200 (base m) 1944
  curF : Apart (cur m) 16 (base m) 1944
  sigF : Apart (sig m) 1200 (base m) 1944
  outCur : Apart (out m) 1200 (cur m) 16
  outSig : Apart (out m) 1200 (sig m) 1200
  curSig : Apart (cur m) 16 (sig m) 1200

theorem pre_of [Labels] {m : MachineData} (h : LayerReadPre m) : Pre m := by
  obtain ⟨⟨hle, hnw, hmap⟩, henough, hlt, ⟨ho1, ho2, ho3⟩, ⟨hc1, hc2, hc3⟩,
    ⟨hs1, hs2, hs3⟩, hoc, hos, hcs, _⟩ := h
  have hF : (base m).toNat = (rspOf m).toNat - layerReadStack := by
    unfold base stackBelow
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (rspOf m).isLt
    unfold layerReadStack at *
    omega
  exact ⟨hle, hnw, hF, hmap, henough, hlt, ho1, hc1, hs1, ho2, hc2, hs2,
    ho3, hc3, hs3, hoc, hos, hcs⟩

theorem Pre.baseNW {m : MachineData} (P : Pre m) : NoWrap (base m) 1944 := by
  have := P.baseNat
  have := P.rspLe
  have := P.rspNW
  unfold NoWrap
  unfold layerReadStack at *
  omega

theorem Pre.rsp_eq {m : MachineData} (P : Pre m) :
    rspOf m = base m + 1936#64 := by
  apply BitVec.eq_of_toNat_eq
  have := P.baseNat
  have := P.rspLe
  have := P.baseNW
  unfold NoWrap layerReadStack at *
  rw [toNat_add_ofNat _ _ (by omega)]
  omega

theorem Pre.baseNW' {m : MachineData} (P : Pre m) : NoWrap (base m) layerReadStack := by
  have := P.baseNW
  unfold NoWrap layerReadStack at *
  omega

theorem Pre.got_not_changed [Labels] {m : MachineData} (P : Pre m) (G : ParserGot m)
    {i : Nat} (hi : i < 8) :
    ¬(Scratch m (gotAddr "memcpy" + BitVec.ofNat 64 i) ∨
      InRange (out m) 1200 (gotAddr "memcpy" + BitVec.ofNat 64 i)) := by
  have hg := G.1 "memcpy" (by simp)
  rintro ((h | h) | h)
  · have hs : Apart (gotAddr "memcpy") 8 (base m) layerReadStack := by
      have hs := hg.2.2.1
      change Apart (gotAddr "memcpy") 8 (base m) (layerReadStack + 8) at hs
      unfold Apart at hs ⊢
      omega
    exact hs.not_inRange hg.2.1 P.baseNW' hi h
  · exact (hg.2.2.2 (cur m, 16) (by simp)).not_inRange hg.2.1 P.curNW hi h
  · exact (hg.2.2.2 (out m, 1200) (by simp)).not_inRange hg.2.1 P.outNW hi h

theorem Pre.got_byte [Labels] {m₀ m : MachineData} (P : Pre m₀) (G : ParserGot m₀)
    (hs : SameOutside m₀.dmem m.dmem (fun p => Scratch m₀ p ∨ InRange (out m₀) 1200 p))
    {i : Nat} (hi : i < 8) :
    m.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) =
      some (byteOf (Labels.label "memcpy").toBitVec i) := by
  rw [hs _ (P.got_not_changed G hi)]
  exact G.byte (by simp) hi

theorem Pre.sig_not_scratch {m : MachineData} (P : Pre m) {x : Nat} (hx : x < 1200) :
    ¬Scratch m (sig m + BitVec.ofNat 64 x) := by
  rintro (h | h)
  · refine not_inRange_of_apart P.baseNW' ?_ h
    have := P.sigF.symm.sub_right P.sigNW (i' := x) (k' := 1) (by omega) (by omega)
    unfold Apart at this ⊢
    unfold layerReadStack
    omega
  · exact not_inRange_of_apart P.curNW (P.curSig.sub_right P.sigNW (by omega) (by omega)) h

theorem Pre.slice_length {m : MachineData} (_P : Pre m) {x : Nat} (hx : x + 16 ≤ 1200) :
    (NativeRustc.slice (LayerReadPre.bytes m) x 16).length = 16 := by
  simp [NativeRustc.slice, LayerReadPre.bytes, length_bytesOf]
  omega

theorem Pre.rand_length {m : MachineData} (P : Pre m) : (rand m).length = 16 :=
  P.slice_length (by omega)
theorem Pre.chainSlot_length {m : MachineData} (P : Pre m) {j : Nat} (hj : j < 58) :
    (chainSlot m j).length = 16 := P.slice_length (by omega)
theorem Pre.pathSlot_length {m : MachineData} (P : Pre m) {j : Nat} (hj : j < 16) :
    (pathSlot m j).length = 16 := P.slice_length (by omega)

theorem Pre.stack_toNat {m : MachineData} (P : Pre m) {x : Nat} (hx : x < 1944) :
    (base m + BitVec.ofNat 64 x).toNat = (base m).toNat + x :=
  toNat_addr P.baseNW hx

theorem Pre.stack_scratch {m : MachineData} (P : Pre m) {o s : Nat} (hs : o + s ≤ 1936)
    {p : BitVec 64} (h : InRange (base m + BitVec.ofNat 64 o) s p) : Scratch m p :=
  Or.inl (inRange_sub P.baseNW' (by unfold layerReadStack; omega) h)

theorem CommonAt.transfer {m₀ m m' : MachineData} {o o' : Nat}
    (C : CommonAt m₀ m o) (hk : Kept m.dmem m'.dmem)
    (hrsp : reg m' .rsp = base m₀ + BitVec.ofNat 64 o')
    {R : BitVec 64 → Prop} (hsame : SameOutside m.dmem m'.dmem R)
    (hR : ∀ p, R p → Scratch m₀ p)
    (hsave : ∀ j < 6, ∀ t < 8, ¬R (base m₀ + BitVec.ofNat 64 (1888 + 8 * j) + BitVec.ofNat 64 t))
    (hout : ∀ t < 8, ¬R (base m₀ + 24#64 + BitVec.ofNat 64 t)) :
    CommonAt m₀ m' o' where
  rsp := hrsp
  same := (C.same.trans hsame).mono fun p hp => hp.elim id (hR p)
  kept := C.kept.trans hk
  save j hj := (C.save j hj).sameOutside hsame fun t ht =>
    hsave j hj t (by rw [length_regBytes] at ht; exact ht)
  output := C.output.sameOutside hsame fun t ht => hout t (by rw [length_regBytes] at ht; exact ht)

end

end NativeRustcX64.Xmss.LayerRead
