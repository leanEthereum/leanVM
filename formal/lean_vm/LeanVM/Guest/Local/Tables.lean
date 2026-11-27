/-
  LeanVM.Guest.Local.Tables

  The records a compiled function's local certificates share beside its layout: a lane per
  offset, the segments, the atoms and the control statements, and how a fact names the
  instruction that made it.
-/

module

public import LeanVM.Guest.Local.Layout
public import LeanVM.Guest.Packed.Chunks

/-!
# The shared tables

Beside the layout (`Layout.lean`: blocks and runs), the soundness and completeness checks of a
compiled function read four tables, each record a few fields of one number (`fld`), in the
layout's conventions: offsets and positions in 20 bits (21 for a justification's references),
blocks and frame cells in 16.

* **Offsets** (`PcLane`, 64 bits, a chunked vector in code order, `Packed.Chunks`): the offset's
  block `bid` (its run's `b`, which a check streaming offsets compares with the current run), and
  the completeness walk's justification of the instruction: a rule `tag` and two references `r1`,
  `r2` (`scripts/cplc`'s 23 rules; their meaning is the completeness check's).
* **Segments** (`SegRec`, a `PTree` by index in code order): offsets `[start, stop)` without a
  jump, the exit at `stop` (`exitKind`: `exFall`, …), its target, the segment's block, and its
  counts of each of the six opcodes, the exit's `JUMP` included.
* **Atoms** (`AtomRec`, a `PTree` by position, `Pos.lean`): the atom's kind, its values' frame
  cells (up to five; a `keccak` or frame address's in a side list from `aux`), `aux` (a `load`'s
  offset, a constant's index), its block, and up to three witness offsets: the instructions its
  soundness rests on, each of whose run's block an ancestor of the atom's (dominance, `Layout.visits`).
* **Control statements** (`CtlRec`, a `PTree` by position): the kind, the block, the anchor (the
  `JUMP` implementing it), the callee frame cell `q` and return offset `r`, the target (a callee's
  entry, a branch's offset), a dispatch's selector cell and table base, its first arm's block,
  and the defining offsets of the cells its anchor reads (`od`, `of`, `oc`).

A **fact** (a known cell value, a `SET`'s constant, a frame pointer's bounce, a product by a
power of `g`) is named by the one instruction that made it: on the guest every value a jump or a
gadget relies on has a single defining instruction dominating its use, so no fact is a join of
several.
-/

namespace LeanVM.Guest.Local

@[expose] public section

/-- An offset's lane. -/
structure PcLane where
  bid : ℕ
  tag : ℕ
  r1 : ℕ
  r2 : ℕ

/-- Lanes of 64 bits: `bid` 16, `tag` 6, `r1` 21, `r2` 21. -/
def pcW : ℕ := 64

def PcLane.ofNat (x : ℕ) : PcLane := ⟨fld x 0 16, fld x 16 6, fld x 22 21, fld x 43 21⟩

/-- A segment's exit. -/
def exFall : ℕ := 0
def exGoto : ℕ := 1
def exBr : ℕ := 2
def exCall : ℕ := 3
def exTCall : ℕ := 4
def exTbl : ℕ := 5
def exRet : ℕ := 6
def exFinal : ℕ := 7
def exTail : ℕ := 8

/-- A segment. -/
structure SegRec where
  start : ℕ
  stop : ℕ
  exitKind : ℕ
  target : ℕ
  blk : ℕ
  /-- The count of opcode `k < 6`. -/
  count : ℕ → ℕ

/-- Slots of 201 bits: `start` 20, `stop` 20, `exitKind` 4, `target` 20, `blk` 16, six counts of
20. -/
def segW : ℕ := 201

def SegRec.ofNat (x : ℕ) : SegRec :=
  ⟨fld x 0 20, fld x 20 20, fld x 40 4, fld x 44 20, fld x 64 16, fun k ↦ fld x (80 + 20 * k) 20⟩

/-- An atom. -/
structure AtomRec where
  kind : ℕ
  /-- Cell `k < 5` of its values. -/
  cell : ℕ → ℕ
  aux : ℕ
  blk : ℕ
  /-- Witness `k < 3`, an offset plus one (`0`: none). -/
  wit : ℕ → ℕ

/-- Slots of 181 bits: `kind` 4, five cells of 16, `aux` 20, `blk` 16, three witnesses of 20. -/
def atomW : ℕ := 181

def AtomRec.ofNat (x : ℕ) : AtomRec :=
  ⟨fld x 0 4, fun k ↦ fld x (4 + 16 * k) 16, fld x 84 20, fld x 104 16, fun k ↦ fld x (120 + 20 * k) 20⟩

/-- A control statement. -/
structure CtlRec where
  kind : ℕ
  blk : ℕ
  anchor : ℕ
  q : ℕ
  r : ℕ
  target : ℕ
  sel : ℕ
  base : ℕ
  arm0 : ℕ
  /-- The defining offset (plus one, `0`: none) of the anchor's `od`, `of`, `oc` (`k < 3`). -/
  def_ : ℕ → ℕ

/-- Slots of 229 bits: `kind` 4, `blk` 16, `anchor` 20, `q` 16, `r` 20, `target` 20, `sel` 16,
`base` 20, `arm0` 16, three defining offsets of 20. -/
def ctlW : ℕ := 229

def CtlRec.ofNat (x : ℕ) : CtlRec :=
  ⟨fld x 0 4, fld x 4 16, fld x 20 20, fld x 40 16, fld x 56 20, fld x 76 20, fld x 96 16,
    fld x 112 20, fld x 132 16, fun k ↦ fld x (148 + 20 * k) 20⟩

/-- A function's tables. -/
structure Tables where
  pcs : List ℕ
  nseg : ℕ
  segs : Packed.PTree
  atoms : Packed.PTree
  ctls : Packed.PTree

namespace Tables

variable (T : Tables)

/-- Offset `pc`'s lane (chunks of 64 lanes). -/
def pc (o : ℕ) : PcLane := PcLane.ofNat (Packed.Chunks.lane T.pcs pcW 64 o)

noncomputable def seg (k : ℕ) : SegRec := SegRec.ofNat ((Packed.PTree.get segW T.segs k).getD 0)

noncomputable def atom (q : ℕ) : AtomRec := AtomRec.ofNat ((Packed.PTree.get atomW T.atoms q).getD 0)

noncomputable def ctl (q : ℕ) : CtlRec := CtlRec.ofNat ((Packed.PTree.get ctlW T.ctls q).getD 0)

end Tables

end

end LeanVM.Guest.Local
