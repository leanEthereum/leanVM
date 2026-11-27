module

public import NativeRustcArm.Code.Common.Finalize.Names

public import NativeRustcArm.Hasher.Bytes
public import NativeRustcArm.Hasher.FinalizeExec

/-!
# `Hasher::finalize`: where things are, what its states keep

From the entry state `m0` (output at `oAt m0`, hasher at `hAt m0`, SP `spAt m0`; the frame of 384
bytes at `frAt m0`): `FinalizePre`'s addresses as numbers (`Geo`, `geo_of`); what every state
after the prologue `m1` keeps (`Fr`: the output pointer, SP, X29, X22–X27, memory as `m1`'s but in
the frame's first 336 bytes and `keccak_f`'s stack (`ChgF`), every mapped byte); the hasher and
the round constants stay as at the entry (`hasher_same`, `rc_same`). The byte facts of the final
block (`getD_finalBlock`) and of the values the executor computes (`byteOf_eorW32`,
`byteOf_ofNat_ofBytes`). The blocks' places and labels (`hb<k>`, `lbl_*`).
-/

namespace NativeRustcArm.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Finalize NativeRustcArm

@[expose] public section

/-- The output's address at the entry. -/
def oAt (m : MachineData) : BitVec 64 := m.regs.X0.toBitVec
/-- The hasher's address at the entry. -/
def hAt (m : MachineData) : BitVec 64 := m.regs.X1.toBitVec
/-- SP at the entry. -/
def spAt (m : MachineData) : BitVec 64 := m.regs.SP.toBitVec
/-- The frame's address. -/
def frAt (m : MachineData) : BitVec 64 := spAt m - 384#64

/-- The hasher's bytes at the entry. -/
def hbytes (m0 : MachineData) : List UInt8 := bytesOf m0.dmem (hAt m0) 344

/-- What the states after the prologue change: the frame's first 336 bytes and `keccak_f`'s
stack. -/
def ChgF (m0 : MachineData) (p : BitVec 64) : Prop :=
  InRange (frAt m0) 336 p ∨ InRange (frAt m0 - 192#64) 192 p

/-- What every state after the prologue keeps. -/
structure Fr (m0 m1 m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = frAt m0
  x19 : (m.regs.getXReg .X19).toBitVec = oAt m0
  x29 : (m.regs.getXReg .X29).toBitVec = frAt m0 + 336#64
  saved : ∀ r ∈ [XReg.X22, .X23, .X24, .X25, .X26, .X27], m.regs.getXReg r = m0.regs.getXReg r
  same : SameOutside m1.dmem m.dmem (ChgF m0)
  kept : Kept m0.dmem m.dmem

/-- `FinalizePre`'s addresses as numbers. -/
structure Geo (m0 : MachineData) : Prop where
  o : (oAt m0).toNat + 32 ≤ 2 ^ 64
  h : (hAt m0).toNat + 344 ≤ 2 ^ 64
  s : 576 ≤ (spAt m0).toNat
  al : (spAt m0).toNat % 16 = 0
  oh : (oAt m0).toNat + 32 ≤ (hAt m0).toNat ∨ (hAt m0).toNat + 344 ≤ (oAt m0).toNat
  hs : (hAt m0).toNat + 344 ≤ (spAt m0).toNat - 576 ∨ (spAt m0).toNat ≤ (hAt m0).toNat
  os : (oAt m0).toNat + 32 ≤ (spAt m0).toNat - 576 ∨ (spAt m0).toNat ≤ (oAt m0).toNat

/-- The round constants' place as numbers. -/
structure GeoRc [Labels] (m0 : MachineData) : Prop where
  nw : rcAddr.toNat + 192 ≤ 2 ^ 64
  rs : rcAddr.toNat + 192 ≤ (spAt m0).toNat - 576 ∨ (spAt m0).toNat ≤ rcAddr.toNat
  ro : (oAt m0).toNat + 32 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (oAt m0).toNat

end

public section

theorem toNat_sub_ofNat' {a : BitVec 64} {j : Nat} (h : j ≤ a.toNat) :
    (a - BitVec.ofNat 64 j).toNat = a.toNat - j := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem geo_of {m0 : MachineData} [Labels] (hpre : FinalizePre m0) : Geo m0 := by
  obtain ⟨⟨hal, hs, -⟩, -, -, -, hh, -, ho, hoh, hhs, hos, -⟩ := hpre
  have hs' : 576 ≤ m0.regs.SP.toNat := hs
  have hb : (stackBelow m0 finalizeStack).toNat = m0.regs.SP.toNat - 576 :=
    toNat_sub_ofNat' hs'
  have e1 : (spAt m0).toNat = m0.regs.SP.toNat := rfl
  have hu : finalizeStack = 576 := rfl
  unfold Apart at hoh hhs hos
  rw [hb] at hhs hos
  refine ⟨ho, hh, hs', hal, hoh, ?_, ?_⟩
  · rw [e1]
    exact hhs.imp id fun h => by unfold hAt; omega
  · rw [e1]
    exact hos.imp id fun h => by unfold oAt; omega

theorem geoRc_of {m0 : MachineData} [Labels] (hpre : FinalizePre m0) : GeoRc m0 := by
  obtain ⟨⟨-, hs, -⟩, ⟨-, hnw, hrs⟩, -, -, -, -, -, -, -, -, hor⟩ := hpre
  have hs' : 576 ≤ m0.regs.SP.toNat := hs
  have hb : (stackBelow m0 finalizeStack).toNat = m0.regs.SP.toNat - 576 :=
    toNat_sub_ofNat' hs'
  have e1 : (spAt m0).toNat = m0.regs.SP.toNat := rfl
  have hu : finalizeStack = 576 := rfl
  unfold Apart at hrs hor
  rw [hb] at hrs
  refine ⟨hnw, ?_, hor⟩
  rw [e1]
  exact hrs.imp id fun h => by omega

theorem frAt_toNat {m0 : MachineData} (g : Geo m0) : (frAt m0).toNat = (spAt m0).toNat - 384 :=
  toNat_sub_ofNat' (by have := g.s; omega)

/-- What the states change, as numbers. -/
theorem chgF_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    ChgF m0 p ↔ (spAt m0).toNat - 576 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat - 48 := by
  have hf := frAt_toNat g
  have h192 : (frAt m0 - 192#64).toNat = (spAt m0).toNat - 576 := by
    rw [toNat_sub_ofNat' (by rw [hf]; have := g.s; omega), hf]
    omega
  unfold ChgF
  rw [inRange_iff (by rw [hf]; have := (spAt m0).isLt; omega),
    inRange_iff (by rw [h192]; have := (spAt m0).isLt; omega), hf, h192]
  have := g.s
  omega

/-- The frame, as numbers. -/
theorem frame_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    InRange (frAt m0) 384 p ↔ (spAt m0).toNat - 384 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat := by
  have hf := frAt_toNat g
  rw [inRange_iff (by rw [hf]; have := (spAt m0).isLt; omega), hf]
  have := g.s
  omega

/-- **The hasher is as at the entry** in any state after the prologue. -/
theorem hasher_same {m0 m1 m : MachineData} (g : Geo m0) (hfr : Fr m0 m1 m)
    (h01 : SameOutside m0.dmem m1.dmem (InRange (frAt m0) 384)) {i : Nat} (hi : i < 344) :
    m.dmem.get? (hAt m0 + BitVec.ofNat 64 i) = m0.dmem.get? (hAt m0 + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := hAt m0) (i := i) (by have := g.h; omega)
  rw [hfr.same _ (by rw [chgF_iff g, ht]; have := g.hs; omega),
    h01 _ (by rw [frame_iff g, ht]; have := g.hs; omega)]

/-- **The round constants are as at the entry** in any state after the prologue. -/
theorem rc_same {m0 m1 m : MachineData} [Labels] (g : Geo m0) (gr : GeoRc m0)
    (hfr : Fr m0 m1 m) (h01 : SameOutside m0.dmem m1.dmem (InRange (frAt m0) 384)) {i : Nat}
    (hi : i < 192) :
    m.dmem.get? (rcAddr + BitVec.ofNat 64 i) = m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := rcAddr) (i := i) (by have := gr.nw; omega)
  rw [hfr.same _ (by rw [chgF_iff g, ht]; have := gr.rs; omega),
    h01 _ (by rw [frame_iff g, ht]; have := gr.rs; omega)]

/-- `Fr` after a step that keeps the registers it names and SP, changes memory only in `ChgF`
and unmaps nothing. -/
theorem Fr.update {m0 m1 m m' : MachineData} (hf : Fr m0 m1 m)
    (hr : ∀ r ∈ [XReg.X19, .X29, .X22, .X23, .X24, .X25, .X26, .X27],
      m'.regs.getXReg r = m.regs.getXReg r)
    (hsp : m'.regs.SP = m.regs.SP) (hs : SameOutside m.dmem m'.dmem (ChgF m0))
    (hk : Kept m.dmem m'.dmem) : Fr m0 m1 m' where
  sp := by rw [hsp]; exact hf.sp
  x19 := by rw [hr .X19 (by simp)]; exact hf.x19
  x29 := by rw [hr .X29 (by simp)]; exact hf.x29
  saved r h := by
    rw [hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)), hf.saved r h]
  same p hp := by rw [hs p hp]; exact hf.same p hp
  kept p hp := hk p (hf.kept p hp)

/-! ## Bytes -/

theorem getD_modify (l : List UInt8) (i j : Nat) (f : UInt8 → UInt8) :
    (l.modify i f).getD j 0 = if j = i ∧ j < l.length then f (l.getD j 0) else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases h : j < l.length
  · rw [List.getElem?_eq_getElem h]
    by_cases hij : j = i
    · subst hij
      simp [h]
    · simp [hij, Ne.symm hij]
  · rw [List.getElem?_eq_none (by omega)]
    simp [h]

/-- **A byte of the final block**: the remaining byte, or `0`, XOR `PAD_FIRST` after them, XOR
`PAD_LAST` at the end. -/
theorem getD_finalBlock {T : List UInt8} (hT : T.length < 136) {j : Nat} (hj : j < 136) :
    (finalBlock T).getD j 0 =
      ((if j < T.length then T.getD j 0 else 0) ^^^ (if j = T.length then 1 else 0)) ^^^
        (if j = 135 then 0x80 else 0) := by
  have hl : (T ++ List.replicate (136 - T.length) 0).length = 136 := by simp; omega
  have hpad : (T ++ List.replicate (136 - T.length) 0).getD j 0 = if j < T.length then T.getD j 0
      else 0 := by
    simp only [List.getD_eq_getElem?_getD]
    by_cases h : j < T.length
    · rw [List.getElem?_append_left h, ite_pos' h]
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, ite_neg' h]
      split <;> rfl
  rw [finalBlock, getD_modify, List.length_modify, hl, getD_modify, hl, hpad]
  by_cases h2 : j = 135
  · rw [ite_pos' ⟨h2, hj⟩, ite_pos' h2]
    by_cases h1 : j = T.length
    · rw [ite_pos' ⟨h1, hj⟩, ite_pos' h1]
    · rw [ite_neg' (fun h => h1 h.1), ite_neg' h1, UInt8.xor_zero]
  · rw [ite_neg' (fun h => h2 h.1), ite_neg' h2, UInt8.xor_zero]
    by_cases h1 : j = T.length
    · rw [ite_pos' ⟨h1, hj⟩, ite_pos' h1]
    · rw [ite_neg' (fun h => h1 h.1), ite_neg' h1, UInt8.xor_zero]

/-- Byte 0 of a 32-bit XOR. -/
theorem byteOf_eorW32 (x y : BitVec 64) :
    byteOf (BinOp.apply .eor .W32 x y) 0 = byteOf x 0 ^^^ byteOf y 0 := by
  apply UInt8.toNat_inj.mp
  simp only [BinOp.apply, ext, low, byteOf, UInt8.toNat_ofNat', UInt8.toNat_xor, Nat.mul_zero,
    Nat.pow_zero, Nat.div_one]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, BitVec.toNat_setWidth, BitVec.toNat_xor, Nat.testBit_xor,
    BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  by_cases hj : j < 8
  · simp [hj, show j < 32 by omega, show j < 64 by omega]
  · simp [hj]

/-- The byte `t` of the value of bytes `bs`. -/
theorem byteOf_ofNat_ofBytes (bs : List UInt8) (hn : bs.length ≤ 8) (t : Nat) :
    byteOf (BitVec.ofNat 64 (Nat.ofBytes bs)) t = bs.getD t 0 := by
  have := byteOf_ofBytes_of_le bs hn t
  rwa [ofBytes_natCast, BitVec.ofInt_natCast] at this

/-! ## Places -/

variable [ElfHost] {sec k : Nat}

theorem hb0 (hp : PlacedIn code sec k) : b0.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Finalize.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : PlacedIn code sec k) : b1.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Finalize.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : PlacedIn code sec k) : b2.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Finalize.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : PlacedIn code sec k) : b3.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Finalize.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : PlacedIn code sec k) : b4.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Finalize.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb4ab (hp : PlacedIn code sec k) : (b4a ++ b4b).IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Finalize.b4Offset) := by
  rw [b4a, b4b, List.take_append_drop]
  exact hb4 hp
theorem hb4a (hp : PlacedIn code sec k) : b4a.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Finalize.b4Offset) :=
  (List.IsInfixAt.append (hb4ab hp)).1
theorem hb4b (hp : PlacedIn code sec k) : b4b.IsInfixAt (ElfHost.sectionProg sec) (k + (NativeRustcArm.Common.Finalize.b4Offset + b4a.length)) :=
  (List.IsInfixAt.append (hb4ab hp)).2
theorem hb5 (hp : PlacedIn code sec k) : b5.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Finalize.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])

theorem lbl_entry (hp : PlacedIn code sec k) :
    Labels.label NativeRustcArm.Common.Finalize.entryLabel = ElfHost.addrOf sec (k + NativeRustcArm.Common.Finalize.b0Offset) :=
  hp.label NativeRustcArm.Common.Finalize.entry_at

end

end NativeRustcArm.Hasher.Finalize
