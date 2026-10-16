module

public import LeanVMCircuits.Bus.TableClock
public import LeanVMCircuits.ExtensionEmit

@[expose] public section

/-! Generate the eleven production column layouts and ordered bus plans from the proved table source. -/

namespace LeanVMCircuits.Bus.ClassTable.Emit

/-- Rust indices fit every supported consumer, including a 32-bit target. -/
def index (n : Nat) : Except String String :=
  if n < 2 ^ 32 then .ok (toString n) else .error s!"unsupported table index {n}"

/-- A coefficient word, not an integer cast into the characteristic-two field. -/
def word (w : Nat) : Except String String :=
  if w < 2 ^ 64 then .ok s!"F64({w})" else .error s!"unsupported table coefficient word {w}"

/-- This exporter supports only the four source coordinate constructors, with bounded columns. -/
def coord (n : Nat) : Coord → Except String String
  | .col i => if i < n then return s!"Coord::Col({← index i})"
      else .error s!"unsupported table column {i}, width {n}"
  | .const w => return s!"Coord::Const({← word w})"
  | .sum a b => return s!"Coord::Sum(vec![{← coord n a}, {← coord n b}])"
  | .scaled w i => if i < n then return s!"Coord::Scaled({← word w}, {← index i})"
      else .error s!"unsupported scaled table column {i}, width {n}"

/-- No coordinate may be silently discarded by the bus's sixteen-coordinate padding. -/
def tuple (n : Nat) (cs : List Coord) : Except String String := do
  unless cs.length ≤ 16 do throw "unsupported table tuple wider than the bus"
  return "vec![" ++ String.intercalate ", " (← cs.mapM (coord n)) ++ "]"

def option {α : Type} (render : α → Except String String) : Option α → Except String String
  | none => return "None"
  | some value => return s!"Some({← render value})"

/-- The same aliases that the row source uses, without a second native allocator. -/
def columns (L : Layout) : Except String String := do
  let rs2 ← option (fun r : SourceColumns => do
    return "SourceColumns { " ++ s!"a2: {← index r.a2}, v2: {← index r.v2}" ++ " }") L.rs2
  let rd ← option (fun r : DestinationColumns => do
    return "DestinationColumns { " ++ s!"ad: {← index r.ad}, vd_old: {← index r.vdOld}, out: {← index r.out}" ++ " }") L.rd
  let pointer ← option (fun p : PointerColumns => do
    return "PointerColumns { " ++ s!"ad: {← index p.ad}, vd: {← index p.vd}" ++ " }") L.pointer
  let control ← option (fun c : ControlColumns => do
    return "ControlColumns { " ++ s!"dt: {← index c.dt}, jump: {← index c.jump}, exit: {← index c.exit}" ++ " }") L.control
  let ram ← option (fun m : MemoryColumns => do
    return "MemoryColumns { " ++ s!"address: {← index m.address}, cell: {← index m.cell}, new: {← index m.new}" ++ " }") L.ram
  let block ← option (fun b : BlockColumns => do
    return "BlockColumns { " ++ s!"words: {← index b.words}, out: {← index b.out}" ++ " }") L.block
  let limbs ← option (fun l : LimbColumns => do
    return "LimbColumns { " ++ s!"limbs: {← index l.limbs}, new: {← index l.new}, addresses: {← index l.addresses}" ++ " }") L.limbs
  return "Columns {\n" ++
    s!"pc: {← index L.pc}, ts: {← index L.ts}, a1: {← index L.a1}, pc4: {← index L.pc4}, v1: {← index L.v1},\n" ++
    s!"flags: {← option index L.flags}, rs2: {rs2}, rd: {rd}, pointer: {pointer}, control: {control},\n" ++
    s!"imm: {← option index L.imm}, ram: {ram}, block: {block}, limbs: {limbs},\n" ++
    s!"flag_bits: {← option index L.flagBits}, bad: {← option index L.bad}, prev: {← index L.prev}, step: {← index L.step},\n" ++
    "}"

def flushes (s : Spec) : Except String String := do
  unless s.WellFormed do throw s!"unsupported table access/bytecode shape {s.index}"
  let pushes ← s.pushes.mapM (tuple s.layout.len)
  let pulls ← s.pulls.mapM (tuple s.layout.len)
  return "FlushBuilder {\n" ++
    "push: vec![" ++ String.intercalate ",\n" pushes ++ "],\n" ++
    "pull: vec![" ++ String.intercalate ",\n" pulls ++ "],\n}"

/-- Only the shipped protocol-order family is exported; no fallback table or ignored interaction is allowed. -/
def emit : Except String String := do
  unless all.map Spec.index = List.range 11 do throw "unsupported table protocol order"
  let layouts ← all.mapM fun s => do
    unless s.nFlagBits = 0 ∨ s.nFlagBits = 2 do throw "unsupported table flag-bit width"
    return s!"{s.index} => {← columns s.layout},\n"
  let plans ← all.mapM fun s => return s!"{s.index} => {← flushes s},\n"
  let extension ← LeanVMCircuits.ExtensionProduct.Emit.emit
  return "// Generated from LeanVMCircuits.Bus.ClassTable.all and ExtensionProduct.rows by GenerateTables.lean. Do not edit.\n" ++
    "// These exact plans and identities are the source of the Clean row and bus theorems.\n\n" ++
    "use super::columns::{BlockColumns, Columns, ControlColumns, DestinationColumns, LimbColumns, MemoryColumns, PointerColumns, SourceColumns};\n" ++
    "use super::bus::FlushBuilder;\nuse crate::bus::{BusForm, Coord};\nuse primitives::field::{F64, F192};\n\n" ++
    "/// The eleven local layouts, including shared load/store value columns.\n" ++
    "pub(super) fn table_columns(index: usize) -> Columns {\nmatch index {\n" ++ String.join layouts ++
    "_ => panic!(\"unsupported instruction table index {index}\"),\n}\n}\n\n" ++
    "/// Ordered state, bytecode and access tuples of the proved integer-multiplicity Clean source.\n" ++
    "pub(super) fn table_flushes(index: usize) -> FlushBuilder {\nmatch index {\n" ++ String.join plans ++
    "_ => panic!(\"unsupported instruction table index {index}\"),\n}\n}\n\n" ++ extension

end LeanVMCircuits.Bus.ClassTable.Emit
