module

public import NativeRustcArm.KeccakF.Bytes

/-!
# `keccak_f`'s loop invariant

At the head of the round loop `.LKeccakF_1` (after `i` rounds, from the machine state `m0` at
`keccak_f`'s entry): SP is the frame's base (`frame`, 192 bytes below the entry's SP), the
counter X17 is `8 i`; the lanes of the state after `i` rounds (`stAfter`) are in
registers (`laneRegs`) and frame slots (`laneSlots`), its column parities in registers
(`parRegs`); the frame slots `savedSlots` hold the entry's state pointer X0, its return address
X30 and its callee-saved X19 to X28; X29 is the entry's; memory outside the frame is the entry's,
and every byte mapped at entry is mapped (`At`).

A write the executor leaves as the newest over 8 bytes is a word there (`wordAt_write`); 8
bytes no write covers keep their word (`wordAt_keep`).
-/

namespace NativeRustcArm.KeccakF

open NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics

@[expose] public section

/-- The frame's base: SP in the loop. -/
def frame (m0 : MachineData) : BitVec 64 := stackBelow m0 keccakFStack

/-- The state after `i` rounds, from the 200 bytes at the entry's X0. -/
def stAfter (m0 : MachineData) (i : Nat) : KeccakState :=
  roundsTo (stateOf (bytesOf m0.dmem m0.regs.X0.toBitVec 200)) i

/-- The registers that hold lanes at the loop head, with the lanes' indices. -/
def laneRegs : List (XReg × Nat) :=
  [(.X22, 4), (.X4, 6), (.X12, 8), (.X6, 9), (.X2, 11), (.X1, 12), (.X7, 13), (.X5, 14),
    (.X18, 15), (.X19, 16), (.X3, 17), (.X25, 18), (.X20, 19), (.X23, 20), (.X21, 21),
    (.X16, 22), (.X24, 23), (.X27, 24)]

/-- The frame slots that hold lanes at the loop head, with the lanes' indices. -/
def laneSlots : List (Nat × Nat) :=
  [(48, 0), (88, 1), (80, 2), (56, 3), (72, 5), (64, 7), (40, 10)]

/-- The registers that hold the column parities at the loop head, with the columns. -/
def parRegs : List (XReg × Nat) := [(.X28, 0), (.X30, 1), (.X8, 2), (.X15, 3), (.X0, 4)]

/-- The frame slots that hold the entry's registers. -/
def savedSlots : List (Nat × XReg) :=
  [(8, .X0), (96, .X30), (112, .X28), (120, .X27), (128, .X26), (136, .X25), (144, .X24),
    (152, .X23), (160, .X22), (168, .X21), (176, .X20), (184, .X19)]

/-- **The loop invariant** after `i` rounds, from the entry's state `m0`. -/
structure At (m0 : MachineData) (i : Nat) (m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = frame m0
  ctr : (m.regs.getXReg .X17).toBitVec = BitVec.ofNat 64 (8 * i)
  regs : AllOf (fun p : XReg × Nat =>
    (m.regs.getXReg p.1).toBitVec = (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneRegs
  slots : AllOf (fun p : Nat × Nat => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneSlots
  par : AllOf (fun p : XReg × Nat =>
    (m.regs.getXReg p.1).toBitVec = (par (stAfter m0 i) p.2).toBitVec) parRegs
  saved : AllOf (fun p : Nat × XReg => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (m0.regs.getXReg p.2).toBitVec) savedSlots
  x29 : m.regs.getXReg .X29 = m0.regs.getXReg .X29
  same : SameOutside m0.dmem m.dmem (InRange (frame m0) keccakFStack)
  kept : Kept m0.dmem m.dmem

end

public section

theorem wordAt_of_eq {d : DataMem} {p v w : BitVec 64} (h : WordAt d p v) (hv : v = w) :
    WordAt d p w := hv ▸ h

theorem allOf_imp {α : Type} {P Q : α → Prop} {l : List α} (h : ∀ a ∈ l, P a → Q a)
    (hl : AllOf P l) : AllOf Q l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    exact ⟨h a List.mem_cons_self hl.1, ih (fun b hb => h b (List.mem_cons_of_mem a hb)) hl.2⟩

theorem frame_toNat {m0 : MachineData} (h : StackOk m0 keccakFStack) :
    (frame m0).toNat = m0.regs.SP.toNat - 192 := by
  have := h.2.1
  simp only [frame, stackBelow, keccakFStack] at this ⊢
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

theorem frame_noWrap {m0 : MachineData} (h : StackOk m0 keccakFStack) :
    NoWrap (frame m0) keccakFStack := by
  have := m0.regs.SP.toBitVec.isLt
  simp only [NoWrap, frame_toNat h, keccakFStack]
  simp only [UInt64.toNat_toBitVec] at this
  have := h.2.1
  simp only [keccakFStack] at this
  omega

theorem frame_aligned {m0 : MachineData} (h : StackOk m0 keccakFStack) :
    (frame m0).toNat % 16 = 0 := by
  rw [frame_toNat h]
  have := h.1
  have := h.2.1
  simp only [keccakFStack] at this
  omega

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- Where every write of a block is in region `r`, memory changes only there. -/
theorem same_region (hm : Match env S m) (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hall : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ sz) :
    SameOutside env.mem0 m.dmem (InRange b sz) := by
  refine fun p hp => hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ => hp ?_
  obtain ⟨hr, hle⟩ := hall w hw
  rw [hr, hb] at hb'
  cases hb'
  rw [inRange_iff (hwf.noWrap r b sz hb)]
  omega

/-- Where every write of a block is in region `r` or `r'`, memory changes only there. -/
theorem same_region2 (hm : Match env S m) (hwf : env.WF) {r r' : Nat} {b b' : BitVec 64}
    {sz sz' : Nat} (hb : env.regions[r]? = some (b, sz)) (hb' : env.regions[r']? = some (b', sz'))
    (hall : ∀ w ∈ S.mem, (w.r = r ∧ w.off + w.n ≤ sz) ∨ (w.r = r' ∧ w.off + w.n ≤ sz')) :
    SameOutside env.mem0 m.dmem (fun p => InRange b sz p ∨ InRange b' sz' p) := by
  refine fun p hp => hm.get?_mem0 hwf fun ⟨w, hw, c, n, hc, h1, h2⟩ => hp ?_
  rcases hall w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · rw [hr, hb] at hc
    cases hc
    left
    rw [inRange_iff (hwf.noWrap r b sz hb)]
    omega
  · rw [hr, hb'] at hc
    cases hc
    right
    rw [inRange_iff (hwf.noWrap r' b' sz' hb')]
    omega

/-- **A word written**: where the newest write over the 8 bytes at `o` in region `r` is one
write of `v` there, they are `v`'s word. -/
theorem wordAt_write (hm : Match env S m) {r o sz : Nat} {b : BitVec 64}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {v : Sym}
    (h : firstOverlap r o 8 S.mem = some ⟨r, o, 8, v⟩) :
    WordAt m.dmem (b + BitVec.ofNat 64 o) (v.eval env) :=
  hm.bytesAt_write hb hle fun i hi => by
    rw [findWrite_some h ⟨Nat.le_refl _, Nat.le_refl _⟩ (Nat.le_add_right o i) (by omega),
      Nat.add_sub_cancel_left]

/-- **A word kept**: 8 bytes in region `r` that no write covers keep their word. -/
theorem wordAt_keep (hm : Match env S m) {r o sz : Nat} {b : BitVec 64}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {w : BitVec 64}
    (h : firstOverlap r o 8 S.mem = none) (h0 : WordAt env.mem0 (b + BitVec.ofNat 64 o) w) :
    WordAt m.dmem (b + BitVec.ofNat 64 o) w := by
  intro i hi
  rw [List.length_map, List.length_range] at hi
  rw [addr_add, hm.mem r b sz hb (o + i) (by omega)]
  unfold memByte
  rw [findWrite_none h (Nat.le_add_right o i) (by omega), ← addr_add]
  exact h0 i (by simp [hi])

end

end NativeRustcArm.KeccakF
