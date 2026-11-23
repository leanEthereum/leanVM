module

public import NativeRustcVmArm.Wire.WriteOpenings.Copy
public import NativeRustcVmArm.Wire.WriteOpenings.A.Defs

/-!
# `write_openings` without levels (`h = 0`), a leaf: the states

Opening `j` from the queries' loop head (`HeadB`, `b25`): the query's word stored, the positions
scanned (`ScanB`, `b26`) to the query's (`FoundB`, `b29`), the leaf copied four words (`ChunkB`,
`b32`) then one (`RemB`, `b35`) at a time, the next query (`AtB36`, `b36`). The registers the
loop keeps after its head: `RB`.
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

@[expose] public section

/-- The registers of the queries' loop without levels, after query `j`'s head. -/
structure RB (R : Run) (j : Nat) (m : MachineData) : Prop where
  x1 : rv m .X1 = BitVec.ofNat 64 (8 * R.np)
  x2 : rv m .X2 = R.qa + BitVec.ofNat 64 (8 * (j + 1))
  x3 : rv m .X3 = R.oa 24
  x4 : rv m .X4 = R.lv
  x5 : rv m .X5 = R.qa + BitVec.ofNat 64 (8 * R.nq)
  x8 : rv m .X8 = BitVec.ofNat 64 (q4 R.lw)
  x9 : rv m .X9 = R.oa (ob j + 32)
  x10 : rv m .X10 = R.oa (ob j + 8)
  x11 : rv m .X11 = BitVec.ofNat 64 (j + 1)
  x12 : rv m .X12 = BitVec.ofNat 64 1544
  x19 : rv m .X19 = R.pa
  x21 : rv m .X21 = BitVec.ofNat 64 R.lw

/-- `RB`'s registers. -/
abbrev rbRegs : List XReg := [.X1, .X2, .X3, .X4, .X5, .X8, .X9, .X10, .X11, .X12, .X19, .X21]

section
variable [Host]

/-- **The queries' loop head** without levels (`b25`) at query `j`. -/
structure HeadB (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b25Offset
  fr : Frm R st.data
  x1 : rv st.data .X1 = BitVec.ofNat 64 (8 * R.np)
  x2 : rv st.data .X2 = R.qa + BitVec.ofNat 64 (8 * j)
  x3 : rv st.data .X3 = R.oa 24
  x4 : rv st.data .X4 = R.lv
  x5 : rv st.data .X5 = R.qa + BitVec.ofNat 64 (8 * R.nq)
  x8 : rv st.data .X8 = BitVec.ofNat 64 (q4 R.lw)
  x9 : rv st.data .X9 = R.oa (ob j + 32)
  x10 : rv st.data .X10 = R.oa (ob j + 8)
  x11 : rv st.data .X11 = BitVec.ofNat 64 j
  x12 : rv st.data .X12 = BitVec.ofNat 64 1544
  x19 : rv st.data .X19 = R.pa
  x21 : rv st.data .X21 = BitVec.ofNat 64 R.lw
  lt : j < R.nq
  hz : R.h = 0
  lw0 : 0 < R.lw
  done : R.Done st.data.dmem j

/-- **The positions' scan** (`b26`) of query `j` at position `i`. -/
structure ScanB (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b26Offset
  fr : Frm R st.data
  rb : RB R j st.data
  x13 : rv st.data .X13 = R.lv + BitVec.ofNat 64 (512 * i)
  x14 : rv st.data .X14 = R.lv + BitVec.ofNat 64 (512 * i + 16)
  x15 : rv st.data .X15 = BitVec.ofNat 64 i
  x16 : rv st.data .X16 = (R.qw j).toBitVec
  x17 : rv st.data .X17 = BitVec.ofNat 64 (8 * (R.np - i))
  lt : j < R.nq
  ilt : i < R.np
  hz : R.h = 0
  lw0 : 0 < R.lw
  miss : ∀ i' < i, R.pw i' ≠ R.qw j
  mem : Begun R j st.data.dmem

/-- **Query `j` found at position `i`** (`b29`). -/
structure FoundB (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b29Offset
  fr : Frm R st.data
  rb : RB R j st.data
  x13 : rv st.data .X13 = R.lv + BitVec.ofNat 64 (512 * i)
  x14 : rv st.data .X14 = R.lv + BitVec.ofNat 64 (512 * i + 16)
  lt : j < R.nq
  ilt : i < R.np
  hz : R.h = 0
  lw0 : 0 < R.lw
  pos : R.pos (R.qw j) = some i
  mem : Begun R j st.data.dmem

/-- **Opening `j`'s leaf** (leaf `i`) copied up to word `t`: what the copy loops keep. -/
structure CopyB (R : Run) (j i t : Nat) (m : MachineData) : Prop where
  fr : Frm R m
  rb : RB R j m
  lt : j < R.nq
  ilt : i < R.np
  hz : R.h = 0
  pos : R.pos (R.qw j) = some i
  mem : Begun R j m.dmem
  leaf : R.LeafPart m.dmem j i t
  tle : t ≤ R.lw

/-- **Four words at a time** (`b32`), `t` copied. -/
structure ChunkB (R : Run) (j i t : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b32Offset
  c : CopyB R j i t st.data
  x13 : rv st.data .X13 = R.lv + BitVec.ofNat 64 (512 * i)
  x14 : rv st.data .X14 = R.lv + BitVec.ofNat 64 (512 * i + 8 * t + 16)
  x15 : rv st.data .X15 = R.oa (ob j + 8 * t + 32)
  x16 : rv st.data .X16 = BitVec.ofNat 64 (q4 R.lw - t)
  t4 : t % 4 = 0
  tq : t + 4 ≤ q4 R.lw

/-- The last words, one at a time (`b34`), `t` copied. -/
structure AtB34 (R : Run) (j i t : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b34Offset
  c : CopyB R j i t st.data
  x13 : rv st.data .X13 = R.lv + BitVec.ofNat 64 (512 * i)
  x15 : rv st.data .X15 = BitVec.ofNat 64 t
  tlt : t < R.lw

/-- **One word at a time** (`b35`), `t` copied. -/
structure RemB (R : Run) (j i t : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b35Offset
  c : CopyB R j i t st.data
  x13 : rv st.data .X13 = R.lv + BitVec.ofNat 64 (512 * i + 8 * t)
  x14 : rv st.data .X14 = R.oa (ob j + 8 + 8 * t)
  x15 : rv st.data .X15 = BitVec.ofNat 64 (R.lw - t)
  tlt : t < R.lw

/-- The leaf copied (`b36`). -/
structure AtB36 (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b36Offset
  c : CopyB R j i R.lw st.data

end

end

public section

variable {R : Run} {j i : Nat} {m m' : MachineData}

theorem RB.keep (h : RB R j m)
    (hk : ∀ r ∈ rbRegs, m'.regs.getXReg r = m.regs.getXReg r) : RB R j m' :=
  ⟨by rw [hk .X1 (by simp)]; exact h.x1, by rw [hk .X2 (by simp)]; exact h.x2,
    by rw [hk .X3 (by simp)]; exact h.x3, by rw [hk .X4 (by simp)]; exact h.x4,
    by rw [hk .X5 (by simp)]; exact h.x5, by rw [hk .X8 (by simp)]; exact h.x8,
    by rw [hk .X9 (by simp)]; exact h.x9, by rw [hk .X10 (by simp)]; exact h.x10,
    by rw [hk .X11 (by simp)]; exact h.x11, by rw [hk .X12 (by simp)]; exact h.x12,
    by rw [hk .X19 (by simp)]; exact h.x19, by rw [hk .X21 (by simp)]; exact h.x21⟩

theorem CopyB.keep {t : Nat} (h : CopyB R j i t m) (hfr : Frm R m') (hd : m'.dmem = m.dmem)
    (hk : ∀ r ∈ rbRegs, m'.regs.getXReg r = m.regs.getXReg r) : CopyB R j i t m' :=
  ⟨hfr, h.rb.keep hk, h.lt, h.ilt, h.hz, h.pos, hd ▸ h.mem, hd ▸ h.leaf, h.tle⟩

/-- Query `j + 1`'s address is the queries' end exactly after the last. -/
theorem qa_cmp (G : Geo R) (hj : j < R.nq) :
    decide ((R.qa + BitVec.ofNat 64 (8 * (j + 1))).toNat =
      (R.qa + BitVec.ofNat 64 (8 * R.nq)).toNat) = decide (j + 1 = R.nq) := by
  have hnq := G.nq256
  by_cases h : j + 1 = R.nq
  · rw [h, decide_eq_true rfl, decide_eq_true rfl]
  · rw [decide_eq_false h, decide_eq_false]
    intro he
    apply h
    have e : BitVec.ofNat 64 (8 * (j + 1)) = BitVec.ofNat 64 (8 * R.nq) := by
      have := congrArg (· - R.qa) (BitVec.eq_of_toNat_eq he)
      simpa [BitVec.add_comm R.qa, BitVec.add_sub_cancel] using this
    have := congrArg BitVec.toNat e
    rw [ofNat_toNat (by omega), ofNat_toNat (by omega)] at this
    omega

/-- Opening `j` done: begun, its leaf, no levels. -/
theorem done_succ (hz : R.h = 0) {d : Mem 64} (hb : Begun R j d) (hp : R.pos (R.qw j) = some i)
    (hl : R.LeafPart d j i R.lw) : R.Done d (j + 1) := by
  refine ⟨hb.1.1, fun j' hj' ↦ ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h' | rfl
  · exact hb.1.2 j' h'
  · exact ⟨i, hp, hb.2, hl, by rw [hz]; exact path_zero⟩

end

end NativeRustcVmArm.Wire.WriteOpenings
