module

public import NativeRustcX64.KeccakF.Bytes

/-!
# `keccak_f`'s loop invariant (x86-64)

The frame contains the 288 bytes below the entry's RSP and its return address. The loop's RSP
is `frame + 128`; six saved registers occupy offsets 240 through 280.

At the loop head after `i` rounds (`At m0 i m`), frame slot 176 holds `8 * i + 8`, the state pointer is at
offset 216, and the lanes and column parities occupy `laneRegs`, `laneSlots` and `parRegs`.
Each turn computes two rounds. Memory outside the frame's first 288 bytes is unchanged, and
every byte mapped at entry remains mapped.

A write the executor leaves as the newest over 8 bytes is a word there (`wordAt_write`); 8 bytes
no write covers keep their word (`wordAt_keep`).
-/

namespace NativeRustcX64.KeccakF

open NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics

@[expose] public section

/-- The frame's base: 288 bytes below the entry's RSP. -/
def frame (m0 : MachineData) : BitVec 64 := stackBelow m0 keccakFStack

/-- The state after `i` rounds, from the 200 bytes at the entry's RDI. -/
def stAfter (m0 : MachineData) (i : Nat) : KeccakState :=
  roundsTo (stateOf (bytesOf m0.dmem (m0.regs.get64 .rdi) 200)) i

/-- The registers that hold lanes at the loop head, with the lanes' indices. -/
def laneRegs : List (Reg64 × Nat) :=
  [(.r13, 0), (.r10, 1), (.r8, 3), (.rbx, 12), (.rdx, 16), (.r12, 18), (.r11, 22), (.r9, 24)]

/-- The frame slots that hold lanes at the loop head, with the lanes' indices. -/
def laneSlots : List (Nat × Nat) :=
  [(64, 2), (160, 4), (80, 5), (16, 6), (32, 7), (168, 8), (24, 9), (48, 10), (56, 11),
    (40, 13), (112, 14), (72, 15), (8, 17), (0, 19), (88, 20), (104, 21), (96, 23)]

/-- The registers that hold the column parities at the loop head, with the columns. -/
def parRegs : List (Reg64 × Nat) := [(.rax, 0), (.r14, 1), (.r15, 2), (.rbp, 3), (.rcx, 4)]

/-- The frame slots of the pushed registers. -/
def savedSlots : List (Nat × Reg64) :=
  [(240, .rbx), (248, .r12), (256, .r13), (264, .r14), (272, .r15), (280, .rbp)]

/-- **The loop invariant** after `i` rounds, from the entry's state `m0`. -/
structure At (m0 : MachineData) (i : Nat) (m : MachineData) : Prop where
  rsp : rspOf m = frame m0 + 128#64
  ctr : WordAt m.dmem (frame m0 + BitVec.ofNat 64 176) (BitVec.ofNat 64 (8 * i + 8))
  ptr : WordAt m.dmem (frame m0 + BitVec.ofNat 64 216) (m0.regs.get64 .rdi)
  regs : AllOf (fun p : Reg64 × Nat =>
    m.regs.get64 p.1 = (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneRegs
  slots : AllOf (fun p : Nat × Nat => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneSlots
  par : AllOf (fun p : Reg64 × Nat =>
    m.regs.get64 p.1 = (par (stAfter m0 i) p.2).toBitVec) parRegs
  saved : AllOf (fun p : Nat × Reg64 => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (m0.regs.get64 p.2)) savedSlots
  same : SameOutside m0.dmem m.dmem (InRange (frame m0) keccakFStack)
  kept : Kept m0.dmem m.dmem

/-- Lanes at the cut between the two unrolled rounds. -/
def midLaneRegs : List (Reg64 × Nat) :=
  [(.rsi, 15), (.rdx, 16), (.r12, 18), (.r14, 20), (.r13, 22), (.rbp, 23), (.rdi, 24), (.rcx, 0)]

def midLaneSlots : List (Nat × Nat) :=
  [(232, 0), (184, 1), (208, 2), (16, 3), (128, 4), (48, 5), (24, 6), (192, 7), (200, 8),
    (152, 9), (32, 10), (0, 11), (120, 12), (40, 13), (88, 14), (96, 15), (80, 16),
    (56, 17), (8, 19), (136, 20), (144, 21), (72, 23)]

def midParRegs : List (Reg64 × Nat) :=
  [(.rax, 0), (.r10, 1), (.rbx, 2), (.r8, 3), (.r11, 4)]

/-- The first round is complete; R9 already holds column 3's parity rotated by one. -/
structure MidAt (m0 : MachineData) (i : Nat) (m : MachineData) : Prop where
  rsp : rspOf m = frame m0 + 128#64
  ctr : WordAt m.dmem (frame m0 + BitVec.ofNat 64 176) (BitVec.ofNat 64 (8 * i))
  ptr : WordAt m.dmem (frame m0 + BitVec.ofNat 64 216) (m0.regs.get64 .rdi)
  regs : AllOf (fun p : Reg64 × Nat =>
    m.regs.get64 p.1 = (Keccak.lane (stAfter m0 i) p.2).toBitVec) midLaneRegs
  slots : AllOf (fun p : Nat × Nat => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (Keccak.lane (stAfter m0 i) p.2).toBitVec) midLaneSlots
  par : AllOf (fun p : Reg64 × Nat =>
    m.regs.get64 p.1 = (par (stAfter m0 i) p.2).toBitVec) midParRegs
  rot : m.regs.get64 .r9 = (NativeRustc.Keccak.par (stAfter m0 i) 3).toBitVec.rotateLeft 1
  saved : AllOf (fun p : Nat × Reg64 => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (m0.regs.get64 p.2)) savedSlots
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
    (frame m0).toNat = (rspOf m0).toNat - 288 := by
  have := h.1
  simp only [frame, stackBelow, keccakFStack] at this ⊢
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

/-- The frame and the return address do not wrap around. -/
theorem frame_noWrap {m0 : MachineData} (h : StackOk m0 keccakFStack) :
    NoWrap (frame m0) (keccakFStack + 8) := by
  have h1 := h.1
  have h2 := h.2.1
  simp only [NoWrap, frame_toNat h, keccakFStack] at h1 ⊢
  omega

theorem frame_add (m0 : MachineData) :
    frame m0 + BitVec.ofNat 64 288 = rspOf m0 := by
  simp only [frame, stackBelow, keccakFStack]
  exact BitVec.sub_add_cancel _ _

variable [Labels] {env : Env} {S : SState} {m : MachineData}

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

/-- Where every write of a block is in the first `lim` bytes of region `r`, memory changes only
there. -/
theorem same_region (hm : Match env S m) (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz lim : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hall : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ lim)
    (hlim : lim ≤ sz) : SameOutside env.mem0 m.dmem (InRange b lim) := by
  refine fun p hp => hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ => hp ?_
  obtain ⟨hr, hle⟩ := hall w hw
  rw [hr, hb] at hb'
  cases hb'
  have := hwf.noWrap r b sz hb
  rw [inRange_iff (by omega)]
  omega

/-- Where every write of a block is in the first `lim` bytes of region `r` or in region `r'`,
memory changes only there. -/
theorem same_region2 (hm : Match env S m) (hwf : env.WF) {r r' : Nat} {b b' : BitVec 64}
    {sz sz' lim : Nat} (hb : env.regions[r]? = some (b, sz))
    (hb' : env.regions[r']? = some (b', sz')) (hlim : lim ≤ sz)
    (hall : ∀ w ∈ S.mem, (w.r = r ∧ w.off + w.n ≤ lim) ∨ (w.r = r' ∧ w.off + w.n ≤ sz')) :
    SameOutside env.mem0 m.dmem (fun p => InRange b lim p ∨ InRange b' sz' p) := by
  refine fun p hp => hm.get?_mem0 hwf fun ⟨w, hw, c, n, hc, h1, h2⟩ => hp ?_
  rcases hall w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · rw [hr, hb] at hc
    cases hc
    left
    have := hwf.noWrap r b sz hb
    rw [inRange_iff (by omega)]
    omega
  · rw [hr, hb'] at hc
    cases hc
    right
    rw [inRange_iff (hwf.noWrap r' b' sz' hb')]
    omega

end

end NativeRustcX64.KeccakF
