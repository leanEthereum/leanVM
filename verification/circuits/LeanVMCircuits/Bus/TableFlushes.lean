module

@[expose] public section

/-!
# The instruction tables' flushes

The source of the eleven instruction tables' local layouts and ordered bus flushes, exported to `crates/leanvm_core/src/tables/clean.rs`. Native `ClassSpec` still selects the circuits and clock slots; `checkflushes` checks its slot lists and native word-to-column clock-port projection against this source. Each tuple is a list of symbolic coordinates over the row's local columns (`Coord`, Rust's `bus::Coord`).

A row pulls its state `⟨ST, pc, ts, 0⟩` and pushes `⟨ST, npc, ts + step, exit⟩`, pulls its decoded bytecode entry
`⟨BC, pc, …⟩`, then makes its accesses in clock-slot order: access `i` in slot `k` pulls `⟨sep, addr, prev_i, old⟩`
and pushes `⟨sep, addr, at, new⟩`, where `prev_i` is the column `prev + i` and `at` the column `ts` for slot 0, the
sum `ts + ⟨k⟩` otherwise.

`dump` renders the source together with its slot lists and clock-port columns in the format the feature-gated `circuits` CLI writes; `lake exe checkflushes` checks the remaining native bindings.
-/

namespace LeanVMCircuits.Bus.ClassTable

/-- A tuple coordinate as a function of a row's local columns. -/
inductive Coord where
  /-- The column `i`. -/
  | col (i : Nat)
  /-- The field element with coefficient word `w`. -/
  | const (w : Nat)
  /-- A sum of two coordinates. -/
  | sum (a b : Coord)
  /-- The column `i` times the constant with coefficient word `w`. -/
  | scaled (w i : Nat)
  deriving DecidableEq

/-- How a class uses RAM (`Ram`). -/
inductive Ram where
  | none
  | read
  | write
  | block
  | limbs
  deriving DecidableEq

/-- The words of a clock circuit's ports past the timestamps and the step (`Word`). -/
inductive Word where
  | v1
  | v2
  | dest
  | flags
  | flagBit (k : Nat)
  | limbAddress (k : Nat)
  deriving DecidableEq

/-- What fixes a class table's columns and flushes (`ClassSpec`): its accesses and memory shape, and which words its
circuits have (`ClassSpec::words`), the flags, the immediate, the flag bits and the verdict. -/
structure Spec where
  name : String
  /-- The table's index in protocol order. -/
  index : Nat
  control : Bool
  readsRs2 : Bool
  writesRd : Bool
  readsRd : Bool
  ram : Ram
  copies : Bool
  hasFlags : Bool
  hasImm : Bool
  nFlagBits : Nat
  hasBad : Bool
  clockInputs : List Word
  clockOutputs : List Word

/-- The `rs2` read's columns. -/
structure SourceColumns where
  a2 : Nat
  v2 : Nat

/-- The destination read's columns. -/
structure PointerColumns where
  ad : Nat
  vd : Nat

/-- The destination write's columns. -/
structure DestinationColumns where
  ad : Nat
  vdOld : Nat
  out : Nat

/-- The control-flow columns. -/
structure ControlColumns where
  dt : Nat
  jump : Nat
  exit : Nat

/-- The single cell's columns. -/
structure MemoryColumns where
  address : Nat
  cell : Nat
  new : Nat

/-- The hash block's columns. -/
structure BlockColumns where
  words : Nat
  out : Nat

/-- The extension-field limbs' columns. -/
structure LimbColumns where
  limbs : Nat
  new : Nat
  addresses : Nat

/-- A table's local column layout (`Columns`). -/
structure Layout where
  pc : Nat
  ts : Nat
  a1 : Nat
  pc4 : Nat
  v1 : Nat
  flags : Option Nat
  rs2 : Option SourceColumns
  rd : Option DestinationColumns
  pointer : Option PointerColumns
  control : Option ControlColumns
  imm : Option Nat
  ram : Option MemoryColumns
  block : Option BlockColumns
  limbs : Option LimbColumns
  flagBits : Option Nat
  bad : Option Nat
  prev : Nat
  step : Nat

/-! ### Slots -/

/-- The register accesses' slots, `rs1`, `rs2`, `rd` (`Clock::REG_SLOTS`). -/
def regSlots : List Nat := [0, 1, 3]

/-- The slots of a memory shape (`Ram::slots`). -/
def Ram.slots : Ram → List Nat
  | .none => []
  | .read | .write => [2]
  | .block => List.range' 2 16
  | .limbs => List.range' 4 9

namespace Spec

variable (s : Spec)

/-- The registers accessed, as indices into `regSlots` (`ClassSpec::registers`). -/
def registers : List Nat :=
  match s.readsRs2, s.writesRd || s.readsRd with
  | true, true => [0, 1, 2]
  | true, false => [0, 1]
  | false, true => [0, 2]
  | false, false => [0]

/-- The accesses per row (`ClassSpec::n_accesses`). -/
def nAccesses : Nat := s.registers.length + s.ram.slots.length

/-- The accesses' clock slots in column order (`ClassSpec::slots`). -/
def slots : List Nat := s.registers.map (regSlots.getD · 0) ++ s.ram.slots

/-! ### Columns -/

/-- Reserve `k` contiguous local columns. -/
def alloc (k : Nat) : StateM Nat Nat := modifyGet fun n => (n, n + k)

/-- Reserve one column when `b`. -/
def allocIf (b : Bool) : StateM Nat (Option Nat) := if b then some <$> alloc 1 else pure none

/-- Allocate the exported local layout, retaining aliases for unchanged doubleword moves. -/
def allocate : StateM Nat Layout := do
  let pc ← alloc 1
  let ts ← alloc 1
  let a1 ← alloc 1
  let pc4 ← alloc 1
  let v1 ← alloc 1
  let flags ← allocIf s.hasFlags
  let rs2 ← if s.readsRs2 then
      (do let a2 ← alloc 1; let v2 ← alloc 1; pure (some (SourceColumns.mk a2 v2)))
    else pure none
  let rd ← if s.writesRd then
      (do
        let ad ← alloc 1
        let vdOld ← alloc 1
        let out ← allocIf !s.copies
        pure (some (ad, vdOld, out)))
    else pure none
  let pointer ← if s.readsRd then
      (do let ad ← alloc 1; let vd ← alloc 1; pure (some (PointerColumns.mk ad vd)))
    else pure none
  let control ← if s.control then
      (do let dt ← alloc 1; let jump ← alloc 1; let exit ← alloc 1; pure (some (ControlColumns.mk dt jump exit)))
    else pure none
  let imm ← allocIf s.hasImm
  let (ram, block) ← match s.ram with
    | .none | .limbs => pure (none, none)
    | .read | .write => do
      let address ← alloc 1
      let cell ← alloc 1
      let new ← match s.ram, rs2 with
        | .read, _ => pure cell
        | .write, some r => if s.copies then pure r.v2 else alloc 1
        | _, _ => alloc 1
      pure (some (MemoryColumns.mk address cell new), none)
    | .block => do
      let words ← alloc 16
      let out ← alloc 4
      pure (none, some (BlockColumns.mk words out))
  let rd := rd.map fun (ad, vdOld, out) =>
    DestinationColumns.mk ad vdOld (out.getD ((ram.map MemoryColumns.cell).getD 0))
  let limbs ← if s.ram = .limbs then
      (do
        let limbs ← alloc 9
        let new ← alloc 3
        let addresses ← alloc 6
        pure (some (LimbColumns.mk limbs new addresses)))
    else pure none
  let flagBits ← if 0 < s.nFlagBits then some <$> alloc s.nFlagBits else pure none
  let bad ← allocIf s.hasBad
  let prev ← alloc s.nAccesses
  let step ← alloc 1
  pure ⟨ pc, ts, a1, pc4, v1, flags, rs2, rd, pointer, control, imm, ram, block, limbs, flagBits, bad, prev, step ⟩

/-- The table's columns. -/
def layout : Layout := (s.allocate.run' 0 : Id Layout)

end Spec

/-! ### Flushes -/

/-- The state's separator word (`Separator::value`). -/
def stWord : Nat := 1
/-- Memory's separator word. -/
def memWord : Nat := 2
/-- The bytecode's separator word. -/
def bcWord : Nat := 4
/-- The registers' separator word. -/
def regWord : Nat := 8

namespace Layout

variable (L : Layout)

/-- The number of local columns (`Columns::len`). -/
def len : Nat := L.step + 1

/-- The limbs whose address the clock circuit computes (`Ext::OFFSET_LIMBS`). -/
def offsetLimbs : List Nat := [1, 2, 4, 5, 7, 8]

/-- The column of a clock circuit word (`Columns::column`). -/
def column : Word → Option Nat
  | .v1 => some L.v1
  | .v2 => L.rs2.map SourceColumns.v2
  | .dest => L.pointer.map PointerColumns.vd
  | .flags => L.flags
  | .flagBit k => L.flagBits.map (· + k)
  | .limbAddress k => L.limbs.bind fun l => (offsetLimbs.findIdx? (· == k)).map (l.addresses + ·)

/-- The successor `pc + 4`, plus the jump for a class with control flow (`ControlColumns::next_pc`). -/
def npc : Coord := match L.control with
  | some c => .sum (.col L.pc4) (.col c.jump)
  | none => .col L.pc4

/-- The exit selector, zero for a class without control flow. -/
def exit : Coord := match L.control with
  | some c => .col c.exit
  | none => .const 0

/-- The state the row pulls, `⟨ST, pc, ts, 0⟩`. -/
def statePull : List Coord := [.const stWord, .col L.pc, .col L.ts, .const 0]

/-- The state the row pushes, `⟨ST, npc, ts + step, exit⟩`. -/
def statePush : List Coord := [.const stWord, L.npc, .sum (.col L.ts) (.col L.step), L.exit]

end Layout

/-- `Vec::resize` with zero constants. -/
def resize (n : Nat) (l : List Coord) : List Coord := l.take n ++ List.replicate (n - l.length) (.const 0)

/-- An access as the row makes it: separator, address, the value pulled and the value pushed. -/
structure Access where
  sep : Coord
  addr : Coord
  old : Coord
  new : Coord

/-- A read pushes back the value it pulls. -/
def Access.read (sep addr value : Coord) : Access := ⟨ sep, addr, value, value ⟩

/-- What a hash row leaves in word `k` of its block (`BlockColumns::left`). -/
def BlockColumns.left (b : BlockColumns) (k : Nat) : Nat := if 4 ≤ k ∧ k < 8 then b.out + (k - 4) else b.words + k

/-- What an extension-field row leaves in limb `k`. -/
def LimbColumns.left (l : LimbColumns) (k : Nat) : Nat := if 6 ≤ k then l.new + (k - 6) else l.limbs + k

namespace Spec

variable (s : Spec)

/-- The twelve-coordinate decoded entry the row reads. -/
def bytecode : List Coord :=
  let L := s.layout
  let entry := [.const bcWord, .col L.pc, .const (2 ^ s.index), (L.flags.map .col).getD (.const 0), .col L.a1,
    (L.rs2.map fun r => .col r.a2).getD (.const 0),
    match L.rd, L.pointer with
    | some rd, _ => .col rd.ad
    | none, some p => .col p.ad
    | none, none => .const 32,
    (L.imm.map .col).getD (.const 0), .col L.pc4] ++ (L.control.map fun c => Coord.col c.dt).toList
  let entry := match L.bad with
    | some b => resize 10 entry ++ [.col b]
    | none => entry
  resize 11 entry ++ [L.exit]

/-- The source accesses in their clock-slot order. -/
def accesses : List Access :=
  let L := s.layout
  let reg := Coord.const regWord
  let mem := Coord.const memWord
  [Access.read reg (.col L.a1) (.col L.v1)] ++
    (L.rs2.map fun r => Access.read reg (.col r.a2) (.col r.v2)).toList ++
    (L.rd.map fun rd => Access.mk reg (.col rd.ad) (.col rd.vdOld) (.col rd.out)).toList ++
    (L.pointer.map fun p => Access.read reg (.col p.ad) (.col p.vd)).toList ++
    (L.ram.map fun m => Access.mk mem (.col m.address) (.col m.cell) (.col m.new)).toList ++
    (match L.block with
      | some b => (List.range 16).map fun k =>
          Access.mk mem (.sum (.col L.v1) (.const (8 * k))) (.col (b.words + k)) (.col (b.left k))
      | none => []) ++
    (match L.limbs, L.rs2, L.pointer, L.flagBits with
      | some l, some r, some p, some bits =>
        (List.range 9).map fun k =>
          let sep := if k / 3 = 1 ∧ 0 < k % 3 then .sum mem (.scaled (memWord + regWord) (bits + 1)) else mem
          let addr := ((Layout.offsetLimbs.findIdx? (· == k)).map (l.addresses + ·)).getD
            ([L.v1, r.v2, p.vd].getD (k / 3) 0)
          Access.mk sep (.col addr) (.col (l.limbs + k)) (.col (l.left k))
      | _, _, _, _ => [])

/-- The timestamp coordinate of an access in slot `k`: the clock column, plus the slot for a nonzero one. -/
def timeAt (ts k : Nat) : Coord := if k = 0 then .col ts else .sum (.col ts) (.const k)

/-- Each access with its slot and its index, which numbers its previous timestamp's column. -/
def indexed : List (Access × Nat × Nat) := s.accesses.zip (s.slots.zip (List.range s.slots.length))

/-- The tuples the row pushes: its state, then each access's. -/
def pushes : List (List Coord) :=
  s.layout.statePush :: s.indexed.map fun x => [x.1.sep, x.1.addr, timeAt s.layout.ts x.2.1, x.1.new]

/-- The tuples the row pulls: its state, its bytecode entry, then each access's. -/
def pulls : List (List Coord) :=
  s.layout.statePull :: s.bytecode ::
    s.indexed.map fun x => [x.1.sep, x.1.addr, .col (s.layout.prev + x.2.2), x.1.old]

/-- The columns of the clock circuit's ports (`ClassSpec::clock_ports`): the clock, each previous timestamp, the
inputs, the step, the outputs. -/
def clockPorts : List (Option Nat) :=
  some s.layout.ts :: (List.range s.nAccesses).map (fun i => some (s.layout.prev + i)) ++
    s.clockInputs.map s.layout.column ++ [some s.layout.step] ++ s.clockOutputs.map s.layout.column

/-! ### The checks a class table's proofs rest on, decided for every table -/

/-- An access separator is the registers', memory's, or `memory + (memory + registers)·base` over the flag bit
`base`. -/
def SepOk (sep : Coord) : Prop :=
  sep = .const regWord ∨ sep = .const memWord ∨
    s.layout.flagBits.map (fun b => Coord.sum (.const memWord) (.scaled (memWord + regWord) (b + 1))) = some sep

instance (sep : Coord) : Decidable (s.SepOk sep) := by unfold SepOk; infer_instance

/-- The facts the row theorem needs of a table's construction: distinct slots below `2^5`, one access per slot, the
entry `⟨BC, pc, …⟩` of twelve coordinates, and the separators. -/
def WellFormed : Prop :=
  s.slots.Nodup ∧ (∀ k ∈ s.slots, k < 2 ^ 5) ∧ s.accesses.length = s.slots.length ∧
    s.bytecode = .const bcWord :: .col s.layout.pc :: s.bytecode.drop 2 ∧ (s.bytecode.drop 2).length = 10 ∧
    ∀ a ∈ s.accesses, s.SepOk a.sep

instance : Decidable s.WellFormed := by unfold WellFormed; infer_instance

end Spec

/-! ### The tables -/

/-- The tables in protocol order (`ClassSpec::ALU` to `ClassSpec::EXT`). -/
def all : List Spec := [
  ⟨ "ALU", 0, true, true, true, false, .none, false, true, true, 0, false, [], [] ⟩,
  ⟨ "LOAD", 1, false, false, true, false, .read, false, true, true, 0, false, [], [] ⟩,
  ⟨ "STORE", 2, false, true, false, false, .write, false, true, true, 0, false, [], [] ⟩,
  ⟨ "LD", 3, false, false, true, false, .read, true, false, true, 0, false, [], [] ⟩,
  ⟨ "SD", 4, false, true, false, false, .write, true, false, true, 0, false, [], [] ⟩,
  ⟨ "SHIFT", 5, false, true, true, false, .none, false, true, true, 0, false, [], [] ⟩,
  ⟨ "MUL", 6, false, true, true, false, .none, false, true, false, 0, false, [], [] ⟩,
  ⟨ "MULH", 7, false, true, true, false, .none, false, true, false, 0, false, [], [] ⟩,
  ⟨ "DIV", 8, false, true, true, false, .none, false, true, false, 0, true, [], [] ⟩,
  ⟨ "HASH", 9, false, true, false, false, .block, false, true, false, 0, false, [], [] ⟩,
  ⟨ "EXT", 10, false, true, false, true, .limbs, false, true, false, 2, false, [.v1, .v2, .dest, .flags],
    [.flagBit 0, .flagBit 1, .limbAddress 1, .limbAddress 2, .limbAddress 4, .limbAddress 5, .limbAddress 7,
      .limbAddress 8] ⟩]

/-- Every table's construction has the facts the row theorem needs. -/
theorem all_wellFormed : ∀ s ∈ all, s.WellFormed := by decide

/-- The tables' slot lists. -/
theorem all_slots : all.map Spec.slots = [[0, 1, 3], [0, 3, 2], [0, 1, 2], [0, 3, 2], [0, 1, 2], [0, 1, 3],
    [0, 1, 3], [0, 1, 3], [0, 1, 3], List.range 18, [0, 1, 3] ++ List.range' 4 9] := by decide

/-! ### The dump -/

/-- A coordinate as the dump writes it. -/
def Coord.render : Coord → String
  | .col i => s!"c{i}"
  | .const w => s!"k{w}"
  | .sum a b => s!"(+ {a.render} {b.render})"
  | .scaled w i => s!"(* {w} c{i})"

/-- A list, after its length. -/
def counted (l : List String) : String := " ".intercalate (toString l.length :: l)

/-- A table's lines: its name, its number of columns, its slots, its clock ports' columns (`-` for a port without
one), then its pushes and pulls. -/
def Spec.render (s : Spec) : List String :=
  [s!"table {s.name}", s!"columns {s.layout.len}", s!"slots {counted (s.slots.map toString)}",
    s!"clock {counted (s.clockPorts.map fun c => (c.map toString).getD "-")}"] ++
    s.pushes.map (fun t => s!"push {counted (t.map Coord.render)}") ++
    s.pulls.map (fun t => s!"pull {counted (t.map Coord.render)}")

/-- Every table's lines. -/
def dump : List String := all.flatMap Spec.render

end LeanVMCircuits.Bus.ClassTable
