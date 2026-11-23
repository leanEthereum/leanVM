module

public import NativeRustcX64.Spec.XmssVerify
public import NativeRustcX64.LayerRead.Glue

/-!
# `xmss_verify`: the addresses and the facts of its proof (x86-64)

For an entry state `m₀` (RSP `S`): the stack `xmss_verify` may use, `xmssVerifyStack` bytes
from `lo m₀`, and the return address at `S`; an address `ad m₀ o`, `o` bytes from
`lo m₀`. The frame region, the 5816 bytes from `ad m₀ fr` (`fr = wotsLeafStack`): at its offset
`0` to `24` `wots_leaf`'s stack arguments and the return addresses of the calls, at `24` the frame
(RSP after the prologue), at `5760` the pushed registers (`saveRegs`), at `5808` the return
address. Below it `wots_leaf`'s stack, the deepest callee's. Region offsets `q` of the frame:
the hasher's address at `24`, the public key at `40`, the message at `152`, the cursor and
`wots_leaf`'s output and the hasher at `184`, the signature's bytes at `952`, the layers at
`3356` and `4556`.

`Pre`: the facts of the precondition. `Common`: what holds after the prologue at every step of
the body: the entry's callee-saved registers in their slots, memory as at entry but in the stack,
every mapped byte kept.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The lowest byte of the stack `xmss_verify` may use. -/
def lo (m₀ : MachineData) : BitVec 64 := stackBelow m₀ xmssVerifyStack

/-- The address `o` bytes from `lo`. -/
def ad (m₀ : MachineData) (o : Nat) : BitVec 64 := lo m₀ + BitVec.ofNat 64 o

/-- The frame region's base, from `lo`: the deepest callee's stack is below it. -/
def fr : Nat := wotsLeafStack

theorem fr_eq : fr = 3440 := rfl

theorem stack_eq : xmssVerifyStack = 9248 := rfl

/-- Arithmetic on frame offsets: `omega` with `fr`'s value. -/
macro "fro" : tactic =>
  `(tactic| first | (rw [fr_eq] <;> omega) | ((try simp only [fr_eq, stack_eq] at *) <;> omega))

/-- The callee-saved registers the prologue pushes, in the order of their slots from `5760`. -/
def saveRegs : List Reg64 := [.rbx, .r12, .r13, .r14, .r15, .rbp]

/-- The input words' address. -/
def inp (m₀ : MachineData) : BitVec 64 := xmssInput m₀

/-- The facts of the precondition the proof uses. -/
structure Pre [Labels] (w : Nat → UInt64) (m₀ : MachineData) : Prop where
  spLe : 9248 ≤ (rspOf m₀).toNat
  spNW : (rspOf m₀).toNat + 8 ≤ 2 ^ 64
  loNat : (lo m₀).toNat = (rspOf m₀).toNat - 9248
  mapped : Mapped m₀.dmem (lo m₀) 9256
  rc : BytesAt m₀.dmem rcAddr rcBytes
  rcNW : NoWrap rcAddr 192
  rcApart : Apart rcAddr 192 (lo m₀) 9256
  words : ∀ i < 309, BytesAt m₀.dmem (inp m₀ + BitVec.ofNat 64 (8 * i)) (wordBytes (w i))
  inpNW : NoWrap (inp m₀) 2472
  inpApart : Apart (inp m₀) 2472 (lo m₀) 9256
  got : GotAt m₀ xmssVerifyStack [(inp m₀, 2472)] ["memcpy", "memset"]

theorem pre_of [Labels] {w : Nat → UInt64} {m₀ : MachineData} (h : XmssVerifyPre w m₀) :
    Pre w m₀ := by
  obtain ⟨⟨hle, hnw, hmap⟩, ⟨hrc, hrcw, hrca⟩, hw, hinw, hap, hgot⟩ := h
  have hlo : (lo m₀).toNat = (rspOf m₀).toNat - 9248 := by
    unfold lo stackBelow
    rw [BitVec.toNat_sub]
    have := (rspOf m₀).isLt
    simp only [BitVec.toNat_ofNat] at *
    rw [stack_eq] at *
    omega
  exact ⟨hle, hnw, hlo, hmap, hrc, hrcw, hrca, hw, hinw, hap, hgot⟩

section
variable [Labels] {w : Nat → UInt64} {m₀ : MachineData}

theorem Pre.loNW (P : Pre w m₀) : NoWrap (lo m₀) 9256 := by
  have := P.loNat
  have := P.spLe
  have := P.spNW
  unfold NoWrap
  omega

omit [Labels] in
theorem ad_add (m₀ : MachineData) (o t : Nat) : ad m₀ o + BitVec.ofNat 64 t = ad m₀ (o + t) :=
  addr_add_addr _ _ _

theorem Pre.ad_toNat (P : Pre w m₀) {o : Nat} (ho : o < 9256) :
    (ad m₀ o).toNat = (lo m₀).toNat + o :=
  toNat_addr P.loNW ho

theorem Pre.ad_nw (P : Pre w m₀) {o s : Nat} (h : o + s ≤ 9256) : NoWrap (ad m₀ o) s :=
  NoWrap.sub P.loNW h

/-- Two ranges of the stack that do not overlap are apart. -/
theorem Pre.apart_ad (P : Pre w m₀) {o s o' s' : Nat} (h : o + s ≤ o' ∨ o' + s' ≤ o)
    (ho : o + s ≤ 9256) (ho' : o' + s' ≤ 9256) (hs : 0 < s) (hs' : 0 < s') :
    Apart (ad m₀ o) s (ad m₀ o') s' :=
  apart_offsets P.loNW h ho ho' hs hs'

/-- An address of the stack outside a range of it. -/
theorem Pre.not_inRange_ad (P : Pre w m₀) {o s x : Nat} (ho : o + s ≤ 9256) (hx : x < 9256)
    (h : x < o ∨ o + s ≤ x) : ¬InRange (ad m₀ o) s (ad m₀ x) := by
  unfold ad
  rw [inRange_offsets P.loNW ho hx]
  omega

theorem Pre.inRange_lo (P : Pre w m₀) {o s : Nat} (ho : o + s ≤ 9248) {p : BitVec 64}
    (h : InRange (ad m₀ o) s p) : InRange (lo m₀) 9248 p :=
  inRange_sub (NoWrap.sub (i := 0) (k := 9248) P.loNW (by omega) |> fun h' => by
    simpa using h') ho h

/-- The input words are apart from a range of the stack. -/
theorem Pre.inp_apart (P : Pre w m₀) {i n o s : Nat} (hi : i + n ≤ 2472) (ho : o + s ≤ 9256)
    (hn : 0 < n) (hs : 0 < s) :
    Apart (inp m₀ + BitVec.ofNat 64 i) n (ad m₀ o) s :=
  (P.inpApart.sub_left P.inpNW hi hn).sub_right P.loNW ho hs

theorem Pre.rc_apart (P : Pre w m₀) {o s : Nat} (ho : o + s ≤ 9256) (hs : 0 < s) :
    Apart rcAddr 192 (ad m₀ o) s :=
  P.rcApart.sub_right P.loNW ho hs

/-- An input byte is outside the stack and the return address. -/
theorem Pre.inp_not_lo (P : Pre w m₀) {i : Nat} (hi : i < 2472) :
    ¬InRange (lo m₀) 9256 (inp m₀ + BitVec.ofNat 64 i) :=
  not_inRange_of_apart P.loNW (P.inpApart.sub_left (i := i) (k := 1) P.inpNW (by omega)
    (by omega)).symm

theorem Pre.rc_not_lo (P : Pre w m₀) {i : Nat} (hi : i < 192) :
    ¬InRange (lo m₀) 9256 (rcAddr + BitVec.ofNat 64 i) :=
  not_inRange_of_apart P.loNW (P.rcApart.sub_left (i := i) (k := 1) P.rcNW (by omega)
    (by omega)).symm

/-- The stack proper is in the stack and the return address. -/
theorem Pre.lo_mono (P : Pre w m₀) {p : BitVec 64} (h : InRange (lo m₀) 9248 p) :
    InRange (lo m₀) 9256 p := by
  have h1 : (lo m₀).toNat + 9248 ≤ 2 ^ 64 := by have := P.loNW; unfold NoWrap at this; omega
  rw [inRange_iff h1] at h
  rw [inRange_iff P.loNW]
  omega

/-- The input bytes are data memory. -/
theorem Pre.inpMapped (P : Pre w m₀) : Mapped m₀.dmem (inp m₀) 2472 := fun i hi => by
  have := (P.words (i / 8) (by omega)).mapped (i % 8)
    (by rw [NativeRustc.length_wordBytes]; omega)
  rwa [addr_add_addr, show 8 * (i / 8) + i % 8 = i by omega] at this

/-- The words' bytes at an input word's address, after any state with `Common`. -/
theorem Pre.words_at (P : Pre w m₀) {d : DataMem}
    (hs : SameOutside m₀.dmem d (InRange (lo m₀) 9248)) {i : Nat} (hi : i < 309) :
    BytesAt d (inp m₀ + BitVec.ofNat 64 (8 * i)) (wordBytes (w i)) :=
  (P.words i hi).sameOutside hs fun t ht => by
    rw [addr_add_addr]
    rw [NativeRustc.length_wordBytes] at ht
    exact fun h => P.inp_not_lo (by omega) (P.lo_mono h)

end

/-- **What holds after the prologue**: the entry's callee-saved registers in their slots, memory
as at entry but in the stack, every mapped byte kept. -/
structure Common (m₀ m : MachineData) : Prop where
  save : ∀ j < 6, BytesAt m.dmem (ad m₀ (fr + 5760 + 8 * j))
    (regBytes (reg m₀ (saveRegs.getD j .rax)))
  same : SameOutside m₀.dmem m.dmem (InRange (lo m₀) 9248)
  kept : Kept m₀.dmem m.dmem

end

end NativeRustcX64.Xmss.XmssVerify
