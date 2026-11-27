module

public import NativeRustcArm.Code.Common.Update.Names

public import NativeRustcArm.Hasher.Bytes
public import NativeRustcArm.Hasher.UpdateExec

/-!
# `Hasher::update`'s loop: its states

From the entry state `m0` (hasher at `hAt m0`, input `input m0` of `nOf m0` bytes, SP `spAt m0`)
and the state `m1` after the prologue (the callee-saved registers in the frame): what every state
of the loop keeps (`Frame`: the hasher and buffer pointers, `136`, SP, X25–X28, memory as `m1`'s
but in the hasher and `keccak_f`'s stack (`Chg`), every mapped byte); the state at the loop head
`.LUpdate_2` having absorbed the input's first `c` bytes (`Inv`); the state at `.LUpdate_1` after a
turn that took `t` bytes (`Mid`). The blocks' places and labels in the program (`hb<k>`, `lbl_*`).
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Update NativeRustcArm

@[expose] public section

/-- The hasher's address at the entry. -/
def hAt (m : MachineData) : BitVec 64 := m.regs.X0.toBitVec
/-- The input's address at the entry. -/
def dAt (m : MachineData) : BitVec 64 := m.regs.X1.toBitVec
/-- The input's length at the entry. -/
def nOf (m : MachineData) : Nat := m.regs.X2.toNat
/-- SP at the entry. -/
def spAt (m : MachineData) : BitVec 64 := m.regs.SP.toBitVec

/-- The input. -/
def input (m0 : MachineData) : List UInt8 := bytesOf m0.dmem (dAt m0) (nOf m0)

/-- The hasher's bytes in `m`. -/
def hasher (m0 m : MachineData) : List UInt8 := bytesOf m.dmem (hAt m0) 344

/-- What the loop changes: the hasher and `keccak_f`'s stack, below the frame. -/
def Chg (m0 : MachineData) (p : BitVec 64) : Prop :=
  InRange (hAt m0) 344 p ∨ InRange (spAt m0 - 256#64) 192 p

/-- The bytes `H` have absorbed the input's first `c` bytes after whatever the entry's had. -/
def Holds (m0 : MachineData) (H : List UInt8) (c : Nat) : Prop :=
  ∀ a, HasherHolds (hasher m0 m0) a → HasherHolds H (a ++ (input m0).take c)

/-- What every state of the loop keeps. -/
structure Frame (m0 m1 m : MachineData) : Prop where
  x20 : (m.regs.getXReg .X20).toBitVec = hAt m0
  x23 : (m.regs.getXReg .X23).toBitVec = hAt m0 + 200#64
  x24 : (m.regs.getXReg .X24).toBitVec = 136#64
  sp : m.regs.SP.toBitVec = spAt m0 - 64#64
  saved : ∀ r ∈ [XReg.X25, .X26, .X27, .X28], m.regs.getXReg r = m0.regs.getXReg r
  same : SameOutside m1.dmem m.dmem (Chg m0)
  kept : Kept m0.dmem m.dmem

/-- **The loop head** `.LUpdate_2`, the input's first `c` bytes absorbed. -/
structure Inv (m0 m1 : MachineData) (c : Nat) (m : MachineData) : Prop where
  frame : Frame m0 m1 m
  le : c ≤ nOf m0
  x19 : (m.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 (nOf m0 - c)
  x21 : (m.regs.getXReg .X21).toBitVec = dAt m0 + BitVec.ofNat 64 c
  x0 : (m.regs.getXReg .X0).toNat = bufLen (hasher m0 m)
  holds : Holds m0 (hasher m0 m) c

/-- **`.LUpdate_1`**, after a turn from `c` absorbed bytes that took `t` more. -/
structure Mid (m0 m1 : MachineData) (c t : Nat) (m : MachineData) : Prop where
  frame : Frame m0 m1 m
  le : c + t ≤ nOf m0
  pos : 0 < t ∨ c = nOf m0
  x19 : (m.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 (nOf m0 - c)
  x21 : (m.regs.getXReg .X21).toBitVec = dAt m0 + BitVec.ofNat 64 c
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 t
  x0 : (m.regs.getXReg .X0).toNat = bufLen (hasher m0 m)
  holds : Holds m0 (hasher m0 m) (c + t)

end

public section

/-! ## Moving the facts -/

theorem hasher_congr {m0 m m' : MachineData} (h : ∀ p, m'.dmem.get? p = m.dmem.get? p) :
    hasher m0 m' = hasher m0 m :=
  bytesOf_congr fun _ _ => h _

/-- `Frame` after a step that keeps its registers and SP, changes memory only in `Chg` and unmaps
nothing. -/
theorem Frame.update {m0 m1 m m' : MachineData} (hf : Frame m0 m1 m)
    (hr : ∀ r ∈ [XReg.X20, .X23, .X24, .X25, .X26, .X27, .X28],
      m'.regs.getXReg r = m.regs.getXReg r)
    (hsp : m'.regs.SP = m.regs.SP) (hs : SameOutside m.dmem m'.dmem (Chg m0))
    (hk : Kept m.dmem m'.dmem) : Frame m0 m1 m' where
  x20 := by rw [hr .X20 (by simp)]; exact hf.x20
  x23 := by rw [hr .X23 (by simp)]; exact hf.x23
  x24 := by rw [hr .X24 (by simp)]; exact hf.x24
  sp := by rw [hsp]; exact hf.sp
  saved r h := by
    rw [hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))),
      hf.saved r h]
  same p hp := by rw [hs p hp]; exact hf.same p hp
  kept p hp := hk p (hf.kept p hp)

theorem Frame.congr {m0 m1 m m' : MachineData} (hf : Frame m0 m1 m)
    (hr : ∀ r ∈ [XReg.X20, .X23, .X24, .X25, .X26, .X27, .X28],
      m'.regs.getXReg r = m.regs.getXReg r)
    (hsp : m'.regs.SP = m.regs.SP) (hd : ∀ p, m'.dmem.get? p = m.dmem.get? p) :
    Frame m0 m1 m' where
  x20 := by rw [hr .X20 (by simp)]; exact hf.x20
  x23 := by rw [hr .X23 (by simp)]; exact hf.x23
  x24 := by rw [hr .X24 (by simp)]; exact hf.x24
  sp := by rw [hsp]; exact hf.sp
  saved r h := by
    rw [hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))),
      hf.saved r h]
  same p hp := by rw [hd p]; exact hf.same p hp
  kept p hp := by rw [hd p]; exact hf.kept p hp

/-! ## Places -/

variable [ElfHost] {sec k : Nat}

theorem hb0 (hp : PlacedIn code sec k) : b0.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Update.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : PlacedIn code sec k) : b1.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Update.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : PlacedIn code sec k) : b2.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Update.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : PlacedIn code sec k) : b3.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Update.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : PlacedIn code sec k) : b4.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Update.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : PlacedIn code sec k) : b5.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Update.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : PlacedIn code sec k) : b6.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Update.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : PlacedIn code sec k) : b7.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Update.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : PlacedIn code sec k) : b8.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.Update.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])

theorem lbl_entry (hp : PlacedIn code sec k) :
    Labels.label NativeRustcArm.Common.Update.entryLabel = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b0Offset) :=
  hp.label NativeRustcArm.Common.Update.entry_at
theorem lbl_1 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Common.Update.label_1 = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b1Offset) :=
  hp.label NativeRustcArm.Common.Update.label_1_at
theorem lbl_2 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Common.Update.label_2 = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b2Offset) :=
  hp.label NativeRustcArm.Common.Update.label_2_at
theorem lbl_6 (hp : PlacedIn code sec k) : Labels.label NativeRustcArm.Common.Update.label_6 = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b8Offset) :=
  hp.label NativeRustcArm.Common.Update.label_6_at

end

end NativeRustcArm.Hasher.Update
