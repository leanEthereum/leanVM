module

public import NativeRustcVmArm.Wire.WriteOpenings.Keep

/-!
# `write_openings` with levels (`h > 0`): the states

Opening `j` from the queries' loop head (`HeadA`, `b2`): the query's word stored, the positions
scanned (`ScanA`, `b3`) to the query's (`b6`), the leaf copied four words (`ChunkA`, `b9`) then
one word (`RemA`, `b12`) at a time, the levels (`LevA`, `b16`), the next query (`b21`).

The registers: `Cs` (callee-saved, constant), `Cr j` (the leaf's and the path's addresses of
opening `j`), `Args` (the arguments, until `b6` saves them in the frame: `FrW1`); `b13` saves the
opening's addresses (`FrW2`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

@[expose] public section

/-- Register `x`'s value: `(m.regs.getXReg x).toBitVec`, spelled out. -/
syntax "rv " term:max term:max : term
macro_rules | `(rv $m $x) => `((($m).regs.getXReg $x).toBitVec)

/-- `x` rounded down to a multiple of four. -/
abbrev q4 (x : Nat) : Nat := x / 4 * 4

/-- The callee-saved registers `write_openings` keeps throughout. -/
structure Cs (R : Run) (m : MachineData) : Prop where
  x19 : rv m .X19 = R.pa
  x21 : rv m .X21 = BitVec.ofNat 64 R.lw
  x22 : rv m .X22 = BitVec.ofNat 64 10240
  x23 : rv m .X23 = R.sb
  x26 : rv m .X26 = BitVec.ofNat 64 (10240 * R.h)
  x29 : rv m .X29 = R.cnt

/-- Opening `j`'s addresses. -/
structure Cr (R : Run) (j : Nat) (m : MachineData) : Prop where
  x15 : rv m .X15 = BitVec.ofNat 64 (q4 R.lw)
  x16 : rv m .X16 = R.oa (ob j + 32)
  x17 : rv m .X17 = R.oa (ob j + 8)
  x20 : rv m .X20 = R.oa (ob j + 544)

/-- The arguments' registers. -/
structure Args (R : Run) (m : MachineData) : Prop where
  x1 : rv m .X1 = BitVec.ofNat 64 (8 * R.np)
  x3 : rv m .X3 = R.oa 24
  x4 : rv m .X4 = R.lv
  x5 : rv m .X5 = R.qa + BitVec.ofNat 64 (8 * R.nq)

/-- Frame word at offset `o`. -/
abbrev FW (R : Run) (d : Mem 64) (o : Nat) (v : BitVec 64) : Prop :=
  WordAt d (base R.m0 176 + BitVec.ofNat 64 o) (UInt64.ofBitVec v)

/-- The arguments and the next query's number and address, saved by `b6`. -/
structure FrW1 (R : Run) (j : Nat) (d : Mem 64) : Prop where
  w32 : FW R d 32 (BitVec.ofNat 64 (j + 1))
  w40 : FW R d 40 R.lv
  w48 : FW R d 48 (R.oa 24)
  w56 : FW R d 56 (BitVec.ofNat 64 (8 * R.np))
  w64 : FW R d 64 (R.qa + BitVec.ofNat 64 (8 * R.nq))
  w72 : FW R d 72 (R.qa + BitVec.ofNat 64 (8 * (j + 1)))

/-- Opening `j`'s addresses, saved by `b13`. -/
structure FrW2 (R : Run) (j : Nat) (d : Mem 64) : Prop where
  w8 : FW R d 8 (R.oa (ob j + 544))
  w16 : FW R d 16 (R.oa (ob j + 8))
  w24 : FW R d 24 (R.oa (ob j + 32))

section
variable [Host]

/-- **The queries' loop head** (`b2`) at query `j`. -/
structure HeadA (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b2Offset
  fr : Frm R st.data
  cs : Cs R st.data
  cr : Cr R j st.data
  args : Args R st.data
  x2 : rv st.data .X2 = R.qa + BitVec.ofNat 64 (8 * j)
  x9 : rv st.data .X9 = BitVec.ofNat 64 j
  x11 : rv st.data .X11 = BitVec.ofNat 64 1544
  lt : j < R.nq
  h0 : 0 < R.h
  done : R.Done st.data.dmem j

/-- **The positions' scan** (`b3`) of query `j` at position `i`. -/
structure ScanA (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b3Offset
  fr : Frm R st.data
  cs : Cs R st.data
  cr : Cr R j st.data
  args : Args R st.data
  x2 : rv st.data .X2 = R.qa + BitVec.ofNat 64 (8 * (j + 1))
  x8 : rv st.data .X8 = R.lv + BitVec.ofNat 64 (512 * i)
  x9 : rv st.data .X9 = R.lv + BitVec.ofNat 64 (512 * i + 16)
  x10 : rv st.data .X10 = BitVec.ofNat 64 i
  x11 : rv st.data .X11 = BitVec.ofNat 64 (8 * (R.np - i))
  x13 : rv st.data .X13 = BitVec.ofNat 64 (j + 1)
  x25 : rv st.data .X25 = (R.qw j).toBitVec
  lt : j < R.nq
  ilt : i < R.np
  h0 : 0 < R.h
  miss : ∀ i' < i, R.pw i' ≠ R.qw j
  mem : Begun R j st.data.dmem

/-- **Opening `j`'s leaf** (leaf `i`) copied up to word `t`: what the copy loops keep. -/
structure CopyA (R : Run) (j i t : Nat) (m : MachineData) : Prop where
  fr : Frm R m
  cs : Cs R m
  cr : Cr R j m
  x25 : rv m .X25 = (R.qw j).toBitVec
  lt : j < R.nq
  ilt : i < R.np
  h0 : 0 < R.h
  pos : R.pos (R.qw j) = some i
  w1 : FrW1 R j m.dmem
  mem : Begun R j m.dmem
  leaf : R.LeafPart m.dmem j i t
  tle : t ≤ R.lw

/-- **Four words at a time** (`b9`), `t` copied. -/
structure ChunkA (R : Run) (j i t : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b9Offset
  c : CopyA R j i t st.data
  x8 : rv st.data .X8 = R.lv + BitVec.ofNat 64 (512 * i)
  x9 : rv st.data .X9 = R.lv + BitVec.ofNat 64 (512 * i + 8 * t + 16)
  x10 : rv st.data .X10 = R.oa (ob j + 8 * t + 32)
  x11 : rv st.data .X11 = BitVec.ofNat 64 (q4 R.lw - t)
  t4 : t % 4 = 0
  tq : t + 4 ≤ q4 R.lw

/-- **One word at a time** (`b12`), `t` copied. -/
structure RemA (R : Run) (j i t : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b12Offset
  c : CopyA R j i t st.data
  x8 : rv st.data .X8 = R.lv + BitVec.ofNat 64 (512 * i + 8 * t)
  x9 : rv st.data .X9 = R.oa (ob j + 8 + 8 * t)
  x10 : rv st.data .X10 = BitVec.ofNat 64 (R.lw - t)
  tlt : t < R.lw

/-- At level `l` of opening `j`: what the levels' loop keeps. -/
structure LevS (R : Run) (j l : Nat) (m : MachineData) : Prop where
  fr : Frm R m
  cs : Cs R m
  x20 : rv m .X20 = R.oa (ob j + 544 + 32 * l)
  x25 : rv m .X25 = (R.qw j).toBitVec
  x27 : rv m .X27 = BitVec.ofNat 64 l
  x28 : rv m .X28 = BitVec.ofNat 64 (10240 * l)
  lt : j < R.nq
  llt : l < R.h
  w1 : FrW1 R j m.dmem
  w2 : FrW2 R j m.dmem
  mem : Begun R j m.dmem
  leaf : ∃ i, R.pos (R.qw j) = some i ∧ R.LeafPart m.dmem j i R.lw
  path : R.PathPart m.dmem j l

/-- **The levels' loop head** (`b16`) of opening `j` at level `l`. -/
structure LevA (R : Run) (j l : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b16Offset
  s : LevS R j l st.data

end

end

public section

variable {R : Run} {m m' : MachineData}

theorem Cs.keep (h : Cs R m)
    (hk : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X26, .X29], m'.regs.getXReg r = m.regs.getXReg r) :
    Cs R m' :=
  ⟨by rw [hk .X19 (by simp)]; exact h.x19, by rw [hk .X21 (by simp)]; exact h.x21,
    by rw [hk .X22 (by simp)]; exact h.x22, by rw [hk .X23 (by simp)]; exact h.x23,
    by rw [hk .X26 (by simp)]; exact h.x26, by rw [hk .X29 (by simp)]; exact h.x29⟩

theorem Cr.keep {j : Nat} (h : Cr R j m)
    (hk : ∀ r ∈ [XReg.X15, .X16, .X17, .X20], m'.regs.getXReg r = m.regs.getXReg r) :
    Cr R j m' :=
  ⟨by rw [hk .X15 (by simp)]; exact h.x15, by rw [hk .X16 (by simp)]; exact h.x16,
    by rw [hk .X17 (by simp)]; exact h.x17, by rw [hk .X20 (by simp)]; exact h.x20⟩

theorem Args.keep (h : Args R m)
    (hk : ∀ r ∈ [XReg.X1, .X3, .X4, .X5], m'.regs.getXReg r = m.regs.getXReg r) : Args R m' :=
  ⟨by rw [hk .X1 (by simp)]; exact h.x1, by rw [hk .X3 (by simp)]; exact h.x3,
    by rw [hk .X4 (by simp)]; exact h.x4, by rw [hk .X5 (by simp)]; exact h.x5⟩

/-- A frame word survives a write into the phase. -/
theorem Geo.fw_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (InRange (R.oa o) n)) (hon : o + n ≤ phaseBytes) {f : Nat}
    (hf : f + 8 ≤ 176) {v : BitVec 64} (h : FW R d f v) : FW R d' f v :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hq ↦ by
    rw [NativeRustcVm.length_wordBytes] at hi
    have hin : Inside (R.oa o) n (R.big 7) :=
      inside_off (A := R.big 7) G.outNw hon (by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; unfold InRange at hq; omega
        · exact h0)
    refine G.not_in (i := 7) (j := 0) (by omega) (by omega) (by omega) hin hq ?_
    show InRange (base R.m0 176) 176 _
    rw [NativeRustcVm.addr_add_add]
    exact NativeRustcVm.inRange_add (by omega) (by omega)

theorem Geo.w1_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (InRange (R.oa o) n)) (hon : o + n ≤ phaseBytes) {j : Nat}
    (h : FrW1 R j d) : FrW1 R j d' :=
  ⟨G.fw_keep hs hon (by omega) h.w32, G.fw_keep hs hon (by omega) h.w40,
    G.fw_keep hs hon (by omega) h.w48, G.fw_keep hs hon (by omega) h.w56,
    G.fw_keep hs hon (by omega) h.w64, G.fw_keep hs hon (by omega) h.w72⟩

theorem Geo.w2_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (InRange (R.oa o) n)) (hon : o + n ≤ phaseBytes) {j : Nat}
    (h : FrW2 R j d) : FrW2 R j d' :=
  ⟨G.fw_keep hs hon (by omega) h.w8, G.fw_keep hs hon (by omega) h.w16,
    G.fw_keep hs hon (by omega) h.w24⟩

end


end NativeRustcVmArm.Wire.WriteOpenings
