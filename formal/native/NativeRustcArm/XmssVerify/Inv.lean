module

public import NativeRustcArm.LayerRead.Glue
public import NativeRustcArm.Spec.XmssVerify
public import NativeRustcArm.Code.Xmss.XmssVerify

/-!
# `xmss_verify`: the addresses and the facts of its proof

For an entry state `m₀`: the stack `xmss_verify` may use, `xmssVerifyStack` bytes from
`lo m₀` (its frame of 5872 bytes at its top, from `ad m₀ fb`, and below it the deepest callee's
stack); an address `ad m₀ o`, `o` bytes from `lo m₀`. `Pre`: the facts of the precondition.
`Common`: what holds after the prologue at every step of the body: SP the frame's base, X29 its
save area, the entry's callee-saved registers in the save area, memory as at entry but in the
stack. Frame offsets (`fb + o`): the message at `8`, the signature's bytes at `44`, the key at
`2448`, the layers at `2492` and `3692`, `wots_leaf`'s output and the hasher at `5408`, the save
area at `5776`.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The lowest byte of the stack `xmss_verify` may use. -/
def lo (m₀ : MachineData) : BitVec 64 := stackBelow m₀ xmssVerifyStack

/-- The address `o` bytes from `lo`. -/
def ad (m₀ : MachineData) (o : Nat) : BitVec 64 := lo m₀ + BitVec.ofNat 64 o

/-- The frame's base, from `lo`: the deepest callee's stack is below it. -/
def fb : Nat := wotsLeafStack

theorem fb_eq : fb = 3328 := rfl

theorem stack_eq : xmssVerifyStack = 9200 := rfl

/-- Arithmetic on frame offsets: `omega` with `fb`'s value. -/
macro "fbo" : tactic =>
  `(tactic| first | (rw [fb_eq] <;> omega) | ((try simp only [fb_eq, stack_eq] at *) <;> omega))

/-- The callee-saved registers the prologue saves, in the order of their slots from `5776`. -/
def saveRegs : List XReg :=
  [.X29, .X30, .X28, .X27, .X26, .X25, .X24, .X23, .X22, .X21, .X20, .X19]

/-- The input words' address. -/
def inp (m₀ : MachineData) : BitVec 64 := xmssInput m₀

/-- The facts of the precondition the proof uses. -/
structure Pre [Labels] (w : Nat → UInt64) (m₀ : MachineData) : Prop where
  sp16 : m₀.regs.SP.toNat % 16 = 0
  spLe : 9200 ≤ m₀.regs.SP.toNat
  loNat : (lo m₀).toNat = m₀.regs.SP.toNat - 9200
  mapped : Mapped m₀.dmem (lo m₀) 9200
  rc : BytesAt m₀.dmem rcAddr rcBytes
  rcNW : NoWrap rcAddr 192
  rcApart : Apart rcAddr 192 (lo m₀) 9200
  words : ∀ i < 309, BytesAt m₀.dmem (inp m₀ + BitVec.ofNat 64 (8 * i)) (wordBytes (w i))
  inpNW : NoWrap (inp m₀) 2472
  inpApart : Apart (inp m₀) 2472 (lo m₀) 9200

theorem pre_of [Labels] {w : Nat → UInt64} {m₀ : MachineData} (h : XmssVerifyPre w m₀) : Pre w m₀ := by
  obtain ⟨⟨h16, hle, hmap⟩, ⟨hrc, hrcw, hrca⟩, hw, hnw, hap⟩ := h
  have hlo : (lo m₀).toNat = m₀.regs.SP.toNat - 9200 := by
    unfold lo stackBelow
    rw [BitVec.toNat_sub]
    have := m₀.regs.SP.toBitVec.isLt
    simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat] at *
    rw [stack_eq] at *
    omega
  exact ⟨h16, hle, hlo, hmap, hrc, hrcw, hrca, hw, hnw, hap⟩

section
variable [Labels] {w : Nat → UInt64} {m₀ : MachineData}

theorem Pre.loNW (P : Pre w m₀) : NoWrap (lo m₀) 9200 := by
  have := m₀.regs.SP.toBitVec.isLt
  have := P.loNat
  have := P.spLe
  unfold NoWrap
  simp only [UInt64.toNat_toBitVec] at *
  omega

omit [Labels] in
theorem ad_add (m₀ : MachineData) (o t : Nat) : ad m₀ o + BitVec.ofNat 64 t = ad m₀ (o + t) :=
  addr_add_addr _ _ _

theorem Pre.ad_toNat (P : Pre w m₀) {o : Nat} (ho : o < 9200) : (ad m₀ o).toNat = (lo m₀).toNat + o :=
  toNat_addr P.loNW ho

theorem Pre.ad_nw (P : Pre w m₀) {o s : Nat} (h : o + s ≤ 9200) : NoWrap (ad m₀ o) s :=
  NoWrap.sub P.loNW h

/-- Two ranges of the stack that do not overlap are apart. -/
theorem Pre.apart_ad (P : Pre w m₀) {o s o' s' : Nat} (h : o + s ≤ o' ∨ o' + s' ≤ o)
    (ho : o + s ≤ 9200) (ho' : o' + s' ≤ 9200) (hs : 0 < s) (hs' : 0 < s') :
    Apart (ad m₀ o) s (ad m₀ o') s' :=
  apart_offsets P.loNW h ho ho' hs hs'

/-- An address of the stack outside a range of it. -/
theorem Pre.not_inRange_ad (P : Pre w m₀) {o s x : Nat} (ho : o + s ≤ 9200) (hx : x < 9200)
    (h : x < o ∨ o + s ≤ x) : ¬InRange (ad m₀ o) s (ad m₀ x) := by
  unfold ad
  rw [inRange_offsets P.loNW ho hx]
  omega

theorem Pre.inRange_lo (P : Pre w m₀) {o s : Nat} (ho : o + s ≤ 9200) {p : BitVec 64}
    (h : InRange (ad m₀ o) s p) : InRange (lo m₀) 9200 p :=
  inRange_sub P.loNW ho h

/-- The input words are apart from a range of the stack. -/
theorem Pre.inp_apart (P : Pre w m₀) {i n o s : Nat} (hi : i + n ≤ 2472) (ho : o + s ≤ 9200)
    (hn : 0 < n) (hs : 0 < s) :
    Apart (inp m₀ + BitVec.ofNat 64 i) n (ad m₀ o) s :=
  (P.inpApart.sub_left P.inpNW hi hn).sub_right P.loNW ho hs

theorem Pre.rc_apart (P : Pre w m₀) {o s : Nat} (ho : o + s ≤ 9200) (hs : 0 < s) :
    Apart rcAddr 192 (ad m₀ o) s :=
  P.rcApart.sub_right P.loNW ho hs

/-- An input byte is outside the stack. -/
theorem Pre.inp_not_lo (P : Pre w m₀) {i : Nat} (hi : i < 2472) :
    ¬InRange (lo m₀) 9200 (inp m₀ + BitVec.ofNat 64 i) :=
  not_inRange_of_apart P.loNW (by
    have := (P.inpApart.sub_left (i := i) (k := 1) P.inpNW (by omega) (by omega)).symm
    exact this)

theorem Pre.rc_not_lo (P : Pre w m₀) {i : Nat} (hi : i < 192) :
    ¬InRange (lo m₀) 9200 (rcAddr + BitVec.ofNat 64 i) :=
  not_inRange_of_apart P.loNW (P.rcApart.sub_left (i := i) (k := 1) P.rcNW (by omega) (by omega)).symm

/-- The input bytes are data memory. -/
theorem Pre.inpMapped (P : Pre w m₀) : Mapped m₀.dmem (inp m₀) 2472 := fun i hi => by
  have := (P.words (i / 8) (by omega)).mapped (i % 8) (by rw [NativeRustc.length_wordBytes]; omega)
  rwa [addr_add_addr, show 8 * (i / 8) + i % 8 = i by omega] at this

/-- The words' bytes at an input word's address, after any state with `Common`. -/
theorem Pre.words_at (P : Pre w m₀) {d : DataMem} (hs : SameOutside m₀.dmem d (InRange (lo m₀) 9200))
    {i : Nat} (hi : i < 309) : BytesAt d (inp m₀ + BitVec.ofNat 64 (8 * i)) (wordBytes (w i)) :=
  (P.words i hi).sameOutside hs fun t ht => by
    rw [addr_add_addr]
    rw [NativeRustc.length_wordBytes] at ht
    exact P.inp_not_lo (by omega)

end

/-- **What holds after the prologue**: SP the frame's base, X29 the save area, the entry's
callee-saved registers in their slots, memory as at entry but in the stack, every mapped byte
kept. -/
structure Common (m₀ m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = ad m₀ fb
  x29 : (m.regs.getXReg .X29).toBitVec = ad m₀ (fb + 5776)
  save : ∀ j < 12, BytesAt m.dmem (ad m₀ (fb + 5776 + 8 * j))
    (regBytes (m₀.regs.getXReg (saveRegs.getD j .X0)).toBitVec)
  same : SameOutside m₀.dmem m.dmem (InRange (lo m₀) 9200)
  kept : Kept m₀.dmem m.dmem

section
variable {w : Nat → UInt64} {m₀ m : MachineData}

/-- The stack below SP is `at` of the frame's base less its size. -/
theorem Common.stackBelow (C : Common m₀ m) {n : Nat} (hn : n ≤ fb) :
    stackBelow m n = ad m₀ (fb - n) := by
  have h : BitVec.ofNat 64 fb = BitVec.ofNat 64 (fb - n) + BitVec.ofNat 64 n := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hn]
  unfold NativeRustcArm.stackBelow
  rw [C.sp, ad, ad, h, ← BitVec.add_assoc, BitVec.add_sub_cancel]

end

end

end NativeRustcArm.Xmss.XmssVerify
