module

public import NativeRustcVmArm.KeccakGkr.Common
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Model
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.States

/-!
# `keccak_open`: the context

The entry's regions (`fbA` the 2224-byte frame, `slA` the slot point, `rwA` the rows, the regions
written `wsOf` and read `rsOf`), the body (`Body`), the regions as numbers (`Nums`, `nums_of`),
and the bytes a step of the fold may change (`Safe`: the stack below the frame's words, the
frame's buffers, the rows).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (DecArea tstateBytes TStateAt)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

@[expose] public section

/-- The frame's base. -/
abbrev fbA (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 2224
/-- The slot point. -/
abbrev slA (m0 : MachineData) : BitVec 64 := openSlot m0
/-- The rows. -/
abbrev rwA (m0 : MachineData) : BitVec 64 := openRows m0
/-- The slot point's address, a word. -/
abbrev slW (m0 : MachineData) : UInt64 := UInt64.ofBitVec (slA m0)
/-- The rows' address, a word. -/
abbrev rwW (m0 : MachineData) : UInt64 := UInt64.ofBitVec (rwA m0)
/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- The result. -/
abbrev oA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- SP at the entry, a number. -/
abbrev spN (m0 : MachineData) : Nat := m0.regs.SP.toBitVec.toNat

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(2216, .X19), (2208, .X20), (2200, .X21), (2192, .X22), (2184, .X23), (2176, .X24),
    (2168, .X25), (2160, .X26), (2152, .X27), (2144, .X28), (2128, .X29), (2136, .X30)]

/-- The regions `keccak_open` writes. -/
abbrev wsOf (m0 : MachineData) : List Region :=
  [⟨oA m0, 24⟩, ⟨tA m0, tstateBytes⟩, ewsRegion (openSlot m0) qkeccakSlotBits,
    ⟨openRows m0, rowsBytes⟩]

/-- The regions `keccak_open` reads. -/
abbrev rsOf [Labels] (a : DecArea) (c : KeccakClaimW) (m0 : MachineData) : List Region :=
  [a.region, ewsRegion m0.regs.X3.toBitVec c.point.size, ⟨m0.regs.X5.toBitVec, weightsBytes⟩,
    rcRegion, ⟨m0.regs.SP.toBitVec, 32⟩]

/-- The body: the 2224-byte frame, the outputs written. -/
abbrev Body [Labels] (m0 st : MachineData) : Prop :=
  Frame m0 2224 keccakOpenStack slots (wsOf m0) st

/-- **The regions as numbers**: none wraps; the stack, the outputs and the regions read apart. -/
structure Nums (a : DecArea) (m0 : MachineData) : Prop where
  hN : 3104 ≤ spN m0
  al : spN m0 % 16 = 0
  argW : spN m0 + 32 ≤ 2 ^ 64
  oW : (oA m0).toNat + 24 ≤ 2 ^ 64
  oS : (oA m0).toNat + 24 ≤ spN m0 - 3104 ∨ spN m0 ≤ (oA m0).toNat
  tW : (tA m0).toNat + 760 ≤ 2 ^ 64
  tS : (tA m0).toNat + 760 ≤ spN m0 - 3104 ∨ spN m0 ≤ (tA m0).toNat
  sW : (slA m0).toNat + 96 ≤ 2 ^ 64
  sS : (slA m0).toNat + 96 ≤ spN m0 - 3104 ∨ spN m0 ≤ (slA m0).toNat
  rW : (rwA m0).toNat + 65536 ≤ 2 ^ 64
  rS : (rwA m0).toNat + 65536 ≤ spN m0 - 3104 ∨ spN m0 ≤ (rwA m0).toNat
  wW : a.words.toNat + 8 * a.len ≤ 2 ^ 64
  wS : a.words.toNat + 8 * a.len ≤ spN m0 - 3104 ∨ spN m0 ≤ a.words.toNat
  o_t : (oA m0).toNat + 24 ≤ (tA m0).toNat ∨ (tA m0).toNat + 760 ≤ (oA m0).toNat
  o_s : (oA m0).toNat + 24 ≤ (slA m0).toNat ∨ (slA m0).toNat + 96 ≤ (oA m0).toNat
  o_r : (oA m0).toNat + 24 ≤ (rwA m0).toNat ∨ (rwA m0).toNat + 65536 ≤ (oA m0).toNat
  t_s : (tA m0).toNat + 760 ≤ (slA m0).toNat ∨ (slA m0).toNat + 96 ≤ (tA m0).toNat
  t_r : (tA m0).toNat + 760 ≤ (rwA m0).toNat ∨ (rwA m0).toNat + 65536 ≤ (tA m0).toNat
  s_r : (slA m0).toNat + 96 ≤ (rwA m0).toNat ∨ (rwA m0).toNat + 65536 ≤ (slA m0).toNat
  o_w : (oA m0).toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (oA m0).toNat
  s_w : (slA m0).toNat + 96 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (slA m0).toNat
  r_w : (rwA m0).toNat + 65536 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (rwA m0).toNat
  t_a : (tA m0).toNat + 760 ≤ spN m0 ∨ spN m0 + 32 ≤ (tA m0).toNat
  s_a : (slA m0).toNat + 96 ≤ spN m0 ∨ spN m0 + 32 ≤ (slA m0).toNat

/-- The bytes a step of the fold may change: the stack below the frame's words, the frame's
buffers, the rows. -/
def Safe (m0 : MachineData) (q : BitVec 64) : Prop :=
  (spN m0 - 3104 ≤ q.toNat ∧ q.toNat < spN m0 - 2208) ∨
    (spN m0 - 2168 ≤ q.toNat ∧ q.toNat < spN m0 - 96) ∨
    ((rwA m0).toNat ≤ q.toNat ∧ q.toNat < (rwA m0).toNat + 65536)

end

public section

theorem stack_eq : keccakOpenStack = 3104 := by decide

theorem slotBits_eq : qkeccakSlotBits = 6 := by decide

theorem slots_le : ∀ p ∈ slots, 2128 ≤ p.1 ∧ p.1 + 8 ≤ 2224 := by decide

theorem slots_le' : ∀ p ∈ slots, p.1 + 8 ≤ 2224 := fun p hp ↦ (slots_le p hp).2

theorem all_slots : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → r ∈ ([] : List XReg) := by
  intro r hr hn
  exfalso
  apply hn
  cases r <;> simp_all [calleeSaved, slots]

/-- An address as a number in a range from a base: inside, without wrapping. -/
theorem inRange_nat {x p : BitVec 64} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) :
    InRange x n p ↔ x.toNat ≤ p.toNat ∧ p.toNat < x.toNat + n :=
  Sym.inRange_iff hx

theorem apart_nat {x y : BitVec 64} {n m : Nat} :
    Apart x n y m ↔ x.toNat + n ≤ y.toNat ∨ y.toNat + m ≤ x.toNat := Iff.rfl

theorem fb_toNat {m0 : MachineData} (h : 2224 ≤ spN m0) : (fbA m0).toNat = spN m0 - 2224 :=
  toNat_sub_ofNat h

theorem fb_add {m0 : MachineData} (h : 2224 ≤ spN m0) {o : Nat} (ho : o ≤ 2224) :
    (fbA m0 + BitVec.ofNat 64 o).toNat = spN m0 - 2224 + o := by
  have h2 : spN m0 < 2 ^ 64 := (m0.regs.SP.toBitVec).isLt
  rw [toNat_add_ofNat' (by rw [fb_toNat h]; omega), fb_toNat h]

theorem stackBelow_nat {m0 : MachineData} (h : 3104 ≤ spN m0) :
    (stackBelow m0 keccakOpenStack).toNat = spN m0 - 3104 := by
  rw [stack_eq]; exact toNat_sub_ofNat h

section
variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem pre_areas (h : KeccakOpenPre a s c m0) :
    Areas m0 keccakOpenStack (wsOf m0) (rsOf a c m0) :=
  h.2.2.2.2.2.2.2.2.2

theorem wsOff (h : KeccakOpenPre a s c m0) : WsOff m0 keccakOpenStack (wsOf m0) :=
  wsOff_of_areas (pre_areas h) h.1

/-- **The regions as numbers** from the precondition. -/
theorem nums_of (h : KeccakOpenPre a s c m0) : Nums a m0 := by
  have hA := pre_areas h
  have hS := h.1
  have hN : 3104 ≤ spN m0 := by have := hS.2.1; rw [stack_eq] at this; exact this
  have hsb := stackBelow_nat hN
  have er : rowsBytes = 65536 := rfl
  have et : tstateBytes = 760 := rfl
  have es : 16 * qkeccakSlotBits = 96 := by rw [slotBits_eq]
  have ok : ∀ w ∈ wsOf m0, w.addr.toNat + w.size ≤ 2 ^ 64 := fun w hw ↦ (Areas.ok hA (.inl hw)).2
  have okr : ∀ r ∈ rsOf a c m0, r.addr.toNat + r.size ≤ 2 ^ 64 :=
    fun r hr ↦ (Areas.ok hA (.inr hr)).2
  have st : ∀ w ∈ wsOf m0, w.addr.toNat + w.size ≤ spN m0 - 3104 ∨
      spN m0 ≤ w.addr.toNat := fun w hw ↦ by
    have := Areas.apart_stack hA hw
    rw [apart_nat, hsb, stack_eq] at this
    omega
  have str : ∀ r ∈ rsOf a c m0, r.addr.toNat + r.size ≤ spN m0 - 3104 ∨
      spN m0 ≤ r.addr.toNat := fun r hr ↦ by
    have := Areas.stack_rs hA hr
    rw [apart_nat, hsb, stack_eq] at this
    omega
  have wr : ∀ w ∈ wsOf m0, ∀ r ∈ rsOf a c m0, w.addr.toNat + w.size ≤ r.addr.toNat ∨
      r.addr.toNat + r.size ≤ w.addr.toNat := fun w hw r hr ↦ Areas.apart_rs hA hw hr
  have m0' : (⟨oA m0, 24⟩ : Region) ∈ wsOf m0 := List.mem_cons_self
  have m1 : (⟨tA m0, tstateBytes⟩ : Region) ∈ wsOf m0 :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : ewsRegion (openSlot m0) qkeccakSlotBits ∈ wsOf m0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have m3 : (⟨openRows m0, rowsBytes⟩ : Region) ∈ wsOf m0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have ra : a.region ∈ rsOf a c m0 := List.mem_cons_self
  have rg : (⟨m0.regs.SP.toBitVec, 32⟩ : Region) ∈ rsOf a c m0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have p01 : Apart (oA m0) 24 (tA m0) tstateBytes :=
    Areas.apart_ws hA (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have p02 : Apart (oA m0) 24 (openSlot m0) (16 * qkeccakSlotBits) :=
    Areas.apart_ws hA (i := 0) (j := 2) (by simp) (by simp) (by decide)
  have p03 : Apart (oA m0) 24 (openRows m0) rowsBytes :=
    Areas.apart_ws hA (i := 0) (j := 3) (by simp) (by simp) (by decide)
  have p12 : Apart (tA m0) tstateBytes (openSlot m0) (16 * qkeccakSlotBits) :=
    Areas.apart_ws hA (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have p13 : Apart (tA m0) tstateBytes (openRows m0) rowsBytes :=
    Areas.apart_ws hA (i := 1) (j := 3) (by simp) (by simp) (by decide)
  have p23 : Apart (openSlot m0) (16 * qkeccakSlotBits) (openRows m0) rowsBytes :=
    Areas.apart_ws hA (i := 2) (j := 3) (by simp) (by simp) (by decide)
  have o0 : (oA m0).toNat + 24 ≤ 2 ^ 64 := ok _ m0'
  have s0 : (oA m0).toNat + 24 ≤ spN m0 - 3104 ∨ spN m0 ≤ (oA m0).toNat := st _ m0'
  have o1 : (tA m0).toNat + tstateBytes ≤ 2 ^ 64 := ok _ m1
  have s1 : (tA m0).toNat + tstateBytes ≤ spN m0 - 3104 ∨ spN m0 ≤ (tA m0).toNat := st _ m1
  have o2 : (openSlot m0).toNat + 16 * qkeccakSlotBits ≤ 2 ^ 64 :=
    ok (ewsRegion (openSlot m0) qkeccakSlotBits) m2
  have s2 : (openSlot m0).toNat + 16 * qkeccakSlotBits ≤ spN m0 - 3104 ∨
      spN m0 ≤ (openSlot m0).toNat := st (ewsRegion (openSlot m0) qkeccakSlotBits) m2
  have o3 : (openRows m0).toNat + rowsBytes ≤ 2 ^ 64 := ok ⟨openRows m0, rowsBytes⟩ m3
  have s3 : (openRows m0).toNat + rowsBytes ≤ spN m0 - 3104 ∨ spN m0 ≤ (openRows m0).toNat :=
    st ⟨openRows m0, rowsBytes⟩ m3
  have ow : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := okr _ ra
  have sw : a.words.toNat + 8 * a.len ≤ spN m0 - 3104 ∨ spN m0 ≤ a.words.toNat := str _ ra
  have og : spN m0 + 32 ≤ 2 ^ 64 := okr _ rg
  have a0 : (oA m0).toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (oA m0).toNat :=
    wr _ m0' _ ra
  have a2 : (openSlot m0).toNat + 16 * qkeccakSlotBits ≤ a.words.toNat ∨
      a.words.toNat + 8 * a.len ≤ (openSlot m0).toNat :=
    wr (ewsRegion (openSlot m0) qkeccakSlotBits) m2 _ ra
  have a3 : (openRows m0).toNat + rowsBytes ≤ a.words.toNat ∨
      a.words.toNat + 8 * a.len ≤ (openRows m0).toNat := wr ⟨openRows m0, rowsBytes⟩ m3 _ ra
  have g1 : (tA m0).toNat + tstateBytes ≤ spN m0 ∨ spN m0 + 32 ≤ (tA m0).toNat := wr _ m1 _ rg
  have g2 : (openSlot m0).toNat + 16 * qkeccakSlotBits ≤ spN m0 ∨
      spN m0 + 32 ≤ (openSlot m0).toNat := wr (ewsRegion (openSlot m0) qkeccakSlotBits) m2 _ rg
  rw [apart_nat] at p01 p02 p03 p12 p13 p23
  rw [er, et, es] at *
  exact ⟨hN, hS.1, og, o0, s0, o1, s1, o2, s2, o3, s3, ow, sw, p01, p02, p03, p12, p13, p23,
    a0, a2, a3, g1, g2⟩

end

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
