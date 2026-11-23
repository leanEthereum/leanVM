module

public import NativeRustcVmX64.Wire.WriteOpenings.Step

/-!
# `write_openings` with levels (`h > 0`): the states (x86-64)

Opening `j` from the queries' loop head (`HeadA`, `b2`): the query's word stored, the positions
scanned (`ScanA`, `b3`) to the query's (`FoundA`, `b7`), the leaf copied four words (`ChunkA`,
`b10`) then one word (`RemA`, `b13`) at a time (`LeafA`, `b14`), the levels (`LevA`, `b18`), the
next query (`NextA`, `b23`).

The frame words: `wA` (`b1`'s; the leaf's and the path's addresses of opening `j` advance in
`b23`), `wB` (with the next query's number, `b2`'s, and `b7`'s: the queries' end and next
address, `8 np`), `wC` (with `b14`'s: the leaves, `lw % 4`, the positions). The registers: `hA` at
the head, `sA` through the scan, `kA` through the leaf's copy, `lA` through the levels.
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

@[expose] public section

/-- `b1`'s frame words. -/
abbrev wA (R : Run) (j : Nat) : List (Nat × BitVec 64) :=
  [(32, BitVec.ofNat 64 R.lw), (88, BitVec.ofNat 64 (q4 R.lw)), (96, R.lv + BitVec.ofNat 64 24),
    (40, R.oa (ob j + 8)), (16, R.oa (ob j + 544))]

/-- `wA`, the next query's number, and `b7`'s frame words. -/
abbrev wB (R : Run) (j : Nat) : List (Nat × BitVec 64) :=
  wA R j ++ [(104, BitVec.ofNat 64 (j + 1)), (56, R.qe),
    (64, R.qa + BitVec.ofNat 64 (8 * (j + 1))), (80, BitVec.ofNat 64 (8 * R.np))]

/-- `wB` and `b14`'s frame words. -/
abbrev wC (R : Run) (j : Nat) : List (Nat × BitVec 64) :=
  wB R j ++ [(24, R.lv), (48, BitVec.ofNat 64 (R.lw % 4)), (72, R.pa)]

/-- The registers at the queries' loop head. -/
abbrev hA (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  [(.rdi, R.qa + BitVec.ofNat 64 (8 * j)), (.rsi, BitVec.ofNat 64 j), (.rbp, R.out),
    (.rcx, BitVec.ofNat 64 (8 * R.np)), (.rdx, R.pa), (.r9, R.lv + BitVec.ofNat 64 24),
    (.r11, R.lv), (.r12, R.oa (ob j + 32)), (.r13, BitVec.ofNat 64 (R.lw % 4)), (.rbx, R.sb),
    (.r14, R.qe)]

/-- The registers the scan keeps. -/
abbrev sA (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  [(.rdi, R.qa + BitVec.ofNat 64 (8 * (j + 1))), (.rbp, R.out),
    (.rcx, BitVec.ofNat 64 (8 * R.np)), (.rdx, R.pa), (.r10, BitVec.ofNat 64 R.lw), (.r11, R.lv),
    (.r12, R.oa (ob j + 32)), (.r13, BitVec.ofNat 64 (R.lw % 4)), (.rbx, R.sb), (.r14, R.qe),
    (.r15, (R.qw j).toBitVec)]

/-- The registers the leaf's copy keeps. -/
abbrev kA (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  [(.rdx, R.pa), (.r11, R.lv), (.r12, R.oa (ob j + 32)), (.r13, BitVec.ofNat 64 (R.lw % 4)),
    (.rbx, R.sb), (.r15, (R.qw j).toBitVec)]

/-- The registers the levels keep. -/
abbrev lA (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  [(.r12, R.oa (ob j + 32)), (.r15, (R.qw j).toBitVec)]

/-- What the leaf's copy keeps (query `j` at position `i`). -/
structure KA (R : Run) (j i : Nat) (m : MachineData) : Prop where
  F : Fr R 8 m
  lt : j < R.nq
  h0 : 0 < R.h
  ilt : i < R.np
  pos : R.pos (R.qw j) = some i
  mem : R.Begun j m.dmem
  w : FWs R m.dmem (wB R j)
  rg : Regs m (kA R j)

/-- `find`'s outcome in RAX, RDX. -/
def FindOut (o : Option Nat) (m : MachineData) : Prop :=
  match o with
  | some n => reg m .rax = 1 ∧ (reg m .rdx).toNat = n
  | none => reg m .rax = 0

/-- At level `l` of opening `j`: what the levels' loop keeps. -/
structure LevS (R : Run) (j l : Nat) (m : MachineData) : Prop where
  F : Fr R 8 m
  lt : j < R.nq
  llt : l < R.h
  mem : R.Begun j m.dmem
  leaf : ∃ i, R.pos (R.qw j) = some i ∧ R.LeafPart m.dmem j i R.lw
  path : R.PathPart m.dmem j l
  w : FWs R m.dmem (wC R j)
  rg : Regs m (lA R j)
  rbp : reg m .rbp = R.sb + BitVec.ofNat 64 (10240 * l)
  r13 : reg m .r13 = BitVec.ofNat 64 l
  r14 : reg m .r14 = R.oa (ob j + 544 + 32 * l)

/-- Decides a fact about the offsets or registers of the lists above. -/
macro "kdecA" : tactic => `(tactic| (simp only [wA, wB, wC, hA, sA, kA, lA, List.map_append,
  List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide +kernel))

variable [Host]

/-- **The queries' loop head** (`b2`) at query `j`. -/
structure HeadA (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 32
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : 0 < R.h
  done : R.Done st.data.dmem j
  w : FWs R st.data.dmem (wA R j)
  rg : Regs st.data (hA R j)

/-- **The positions' scan** (`b3`) of query `j` at position `i`. -/
structure ScanA (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 44
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : 0 < R.h
  ilt : i < R.np
  miss : ∀ i' < i, R.pw i' ≠ R.qw j
  mem : R.Begun j st.data.dmem
  w : FWs R st.data.dmem (wA R j)
  w104 : R.FW st.data.dmem 104 (BitVec.ofNat 64 (j + 1))
  rg : Regs st.data (sA R j)
  rsi : reg st.data .rsi = BitVec.ofNat 64 i
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i)
  r8 : reg st.data .r8 = BitVec.ofNat 64 (8 * (R.np - i))
  r9 : reg st.data .r9 = R.lv + BitVec.ofNat 64 (512 * i + 24)

/-- **Query `j` found at position `i`** (`b7`). -/
structure FoundA (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 54
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : 0 < R.h
  ilt : i < R.np
  pos : R.pos (R.qw j) = some i
  mem : R.Begun j st.data.dmem
  w : FWs R st.data.dmem (wA R j)
  w104 : R.FW st.data.dmem 104 (BitVec.ofNat 64 (j + 1))
  rg : Regs st.data (sA R j)
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i)
  r9 : reg st.data .r9 = R.lv + BitVec.ofNat 64 (512 * i + 24)

/-- **Four words at a time** (`b10`), `t` copied. -/
structure ChunkA (R : Run) (j i t : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 65
  k : KA R j i st.data
  leaf : R.LeafPart st.data.dmem j i t
  t4 : t % 4 = 0
  tq : t + 4 ≤ q4 R.lw
  rcx : reg st.data .rcx = BitVec.ofNat 64 t
  rdi : reg st.data .rdi = BitVec.ofNat 64 (q4 R.lw)
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i)
  r9 : reg st.data .r9 = R.lv + BitVec.ofNat 64 (512 * i + 8 * t + 24)

/-- **Before the remaining words** (`b12`), `q4 lw` copied. -/
structure PreRemA (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 80
  k : KA R j i st.data
  leaf : R.LeafPart st.data.dmem j i (q4 R.lw)
  pos : 0 < R.lw % 4
  rcx : reg st.data .rcx = BitVec.ofNat 64 (q4 R.lw)
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i)

/-- **One word at a time** (`b13`), `q4 lw + u` copied. -/
structure RemA (R : Run) (j i u : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 86
  k : KA R j i st.data
  leaf : R.LeafPart st.data.dmem j i (q4 R.lw + u)
  ult : u < R.lw % 4
  rdi : reg st.data .rdi = BitVec.ofNat 64 u
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i + 8 * q4 R.lw)
  rcx : reg st.data .rcx = R.oa (ob j + 8 + 8 * q4 R.lw)

/-- **The leaf copied** (`b14`). -/
structure LeafA (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 92
  k : KA R j i st.data
  leaf : R.LeafPart st.data.dmem j i R.lw

/-- **The levels' loop** (`b18`) of opening `j` at level `l`. -/
structure LevA (R : Run) (j l : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 117
  s : LevS R j l st.data

/-- **Level `l`'s count read** (`b19`): in RBX, at most `256`. -/
structure CntA (R : Run) (j l : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 122
  s : LevS R j l st.data
  rbx : reg st.data .rbx = (R.cw l).toBitVec
  cw256 : (R.cw l).toNat ≤ 256

/-- **Back from `find`** (`b20`) at level `l`: the count in RBX, `find`'s outcome. -/
structure RetA (R : Run) (j l : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 128
  s : LevS R j l st.data
  rbx : reg st.data .rbx = (R.cw l).toBitVec
  cw256 : (R.cw l).toNat ≤ 256
  res : FindOut (R.fidx l (R.qw j)) st.data

/-- **Level `l`'s digest in RSI, RDX, RCX, RAX** (`b17`). -/
structure DigA (R : Run) (j l : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 107
  s : LevS R j l st.data
  dg : [UInt64.ofBitVec (reg st.data .rsi), UInt64.ofBitVec (reg st.data .rdx),
    UInt64.ofBitVec (reg st.data .rcx), UInt64.ofBitVec (reg st.data .rax)] = R.digest l (R.qw j)

/-- **Opening `j` written** (`b23`). -/
structure NextA (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 139
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : 0 < R.h
  done : R.Done st.data.dmem (j + 1)
  w : FWs R st.data.dmem (wC R j)
  r12 : reg st.data .r12 = R.oa (ob j + 32)

end

public section

variable {R : Run} {j i : Nat} {m m' : MachineData}

/-- `KA` across a block without writes. -/
theorem KA.next (h : KA R j i m) (F : Fr R 8 m') (hd : m'.dmem = m.dmem)
    (hr : Regs m' (kA R j)) : KA R j i m' :=
  ⟨F, h.lt, h.h0, h.ilt, h.pos, hd ▸ h.mem, h.w.keep (FwK.of_eq hd _), hr⟩

/-- `KA` across a block writing the phase from opening `j`'s leaf on. -/
theorem KA.write (G : Geo R) (h : KA R j i m) (F : Fr R 8 m') {o n : Nat}
    (hs : SameOutside m.dmem m'.dmem (R.FO o n)) (hon : o + n ≤ phaseBytes) (ho : ob j + 8 ≤ o)
    (hk : FwK R m.dmem m'.dmem ((wB R j).map Prod.fst)) (hr : Regs m' (kA R j)) :
    KA R j i m' :=
  ⟨F, h.lt, h.h0, h.ilt, h.pos, G.begun_keep hs hon h.lt h.mem ho, h.w.keep hk, hr⟩

end

end NativeRustcVmX64.Wire.WriteOpenings
