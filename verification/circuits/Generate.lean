import LeanVMCircuits.AdderFamily
import LeanVMCircuits.ShiftExport
import LeanVMCircuits.Blake2s.Emit
import LeanVMCircuits.MemoryExport
import LeanVMCircuits.AluExport

open LeanVMCircuits.Flock

structure Codegen where
  bindings : List (Nat × String)
  cache : List (Affine × String) := []
  lines : Array String := #[]
  next : Nat := 0

def fresh (state : Codegen) (operation : String) : String × Codegen :=
  let name := s!"w{state.next}"
  (name, { state with next := state.next + 1, lines := state.lines.push s!"    let {name} = {operation};" })

def emitAffine (affine : Affine) (state : Codegen) : Except String (String × Codegen) :=
  if let some name := state.cache.findSome? (fun (key, name) => if key = affine then some name else none) then
    .ok (name, state)
  else
    match affine with
    | .zero => .ok ("Wire::ZERO", state)
    | .one => .ok ("Wire::ONE", state)
    | .var index =>
      match state.bindings.findSome? (fun (key, name) => if key = index then some name else none) with
      | some name => .ok (name, state)
      | none => .error s!"unbound or forward variable {index}"
    | .xor left right => do
      let (leftName, state) ← emitAffine left state
      let (rightName, state) ← emitAffine right state
      let (name, state) := fresh state s!"c.xor({leftName}, {rightName})"
      return (name, { state with cache := (affine, name) :: state.cache })

private def referenced (affine : Affine) (used : Std.HashSet Nat) : Std.HashSet Nat :=
  match affine with
  | .zero | .one => used
  | .var index => used.insert index
  | .xor left right => referenced right (referenced left used)

def emit (name : String) (width : Nat) (withCarry : Bool) (bindings : List (Nat × String))
    (parameters : String) (artifact : Artifact)
    (outputProducts : List (Nat × Nat × Nat) := [])
    (returnedOutputs : Option (List Nat) := none) : Except String String := do
  if (outputProducts.map Prod.fst).eraseDups.length != outputProducts.length then
    throw "duplicate committed product variable"
  if (outputProducts.map Prod.snd).eraseDups.length != outputProducts.length then
    throw "duplicate committed product output"
  if !outputProducts.all (fun placement => artifact.rows.any (fun row => row.output == placement.1)) then
    throw "committed product variable is absent from the artifact"
  let returnedOutputs := returnedOutputs.getD (List.range artifact.outputs.length)
  let mut used := if outputProducts.isEmpty then {} else artifact.rows.foldl
    (fun used row => referenced row.right (referenced row.left used)) {}
  if !outputProducts.isEmpty then
    for index in returnedOutputs do
      let some affine := artifact.outputs[index]? | throw s!"exported output {index} is absent"
      used := referenced affine used
  let mut seen := bindings.foldl (fun seen binding => seen.insert binding.1) ({} : Std.HashSet Nat)
  let mut state : Codegen := { bindings }
  for row in artifact.rows do
    if seen.contains row.output then throw s!"duplicate product variable {row.output}"
    seen := seen.insert row.output
    let (left, afterLeft) ← emitAffine row.left state
    let (right, afterRight) ← emitAffine row.right afterLeft
    let placement := outputProducts.find? (fun placement => placement.1 == row.output)
    let operation := match placement with
      | some (_, port, bit) => s!"c.and_output({port}, {bit}, {left}, {right})"
      | none => s!"c.and({left}, {right})"
    if placement.isSome && !used.contains row.output then
      state := { afterRight with lines := afterRight.lines.push s!"    {operation};" }
    else
      let (name, afterProduct) := fresh afterRight operation
      state := { afterProduct with bindings := (row.output, name) :: afterProduct.bindings }
  let mut outputs : Array String := #[]
  for index in returnedOutputs do
    let some affine := artifact.outputs[index]? | throw s!"exported output {index} is absent"
    let (name, afterOutput) ← emitAffine affine state
    state := afterOutput
    outputs := outputs.push name
  if outputs.size != width + (if withCarry then 1 else 0) then throw "unexpected exported output width"
  let result := if withCarry then s!"([Wire; {width}], Wire)" else s!"[Wire; {width}]"
  let header := s!"/// The checked {name} artifact, products in source order.\n\
    pub fn {name}(c: &mut Builder{parameters}) -> {result} \{\n"
  let outputLines := (List.range ((width + 3) / 4)).map fun line =>
    "        " ++ String.intercalate ", " ((List.range 4).filterMap fun i =>
      if line * 4 + i < width then outputs[line * 4 + i]? else none) ++ ","
  let opening := if withCarry then "\n    (\n    [\n" else "\n    [\n"
  let closing := if withCarry then s!"\n    ],\n    {outputs[width]!},\n    )\n}\n" else "\n    ]\n}\n"
  return header ++ String.intercalate "\n" state.lines.toList ++ opening ++
    String.intercalate "\n" outputLines ++ closing

def emitAdder (name : String) (width : Nat) (withCarry : Bool) (artifact : Artifact) : Except String String :=
  let bindings := (List.range width).flatMap fun i => [(i, s!"x[{i}]"), (width + i, s!"y[{i}]")]
  let bindings := if withCarry then (2 * width, "carry_in") :: bindings else bindings
  let carry := if withCarry then ", carry_in: Wire" else ""
  emit name width withCarry bindings s!", x: &[Wire; {width}], y: &[Wire; {width}]{carry}" artifact

def emitProduction : Except String String := do
  let wrapping64 ← emitAdder "wrapping_add64" 64 false adder64
  let wrapping32 ← emitAdder "wrapping_add32" 32 false adder32
  let wrapping31 ← emitAdder "wrapping_add31" 31 false LeanVMCircuits.Blake2s.Export.adder31
  let blake2s ← LeanVMCircuits.Blake2s.Emit.emit
  let carry64 ← emitAdder "add_with_carry64" 64 true carryAdder64
  let shiftBindings := (List.range 64).flatMap fun i =>
    [(i, s!"v1[{i}]"), (64 + i, s!"v2[{i}]"), (128 + i, s!"imm[{i}]")]
  let shiftBindings := [(192, "flags[0]"), (193, "flags[1]"), (194, "flags[2]")] ++ shiftBindings
  let shift64 ← emit "shift64" 64 false shiftBindings
    ", v1: &[Wire; 64], v2: &[Wire; 64], imm: &[Wire; 64], flags: &[Wire; 3]" Shift.artifact
  let loadBindings := (List.range 64).flatMap fun i =>
    [(i, s!"v1[{i}]"), (64 + i, s!"imm[{i}]"), (131 + i, s!"cell[{i}]")]
  let loadBindings := [(128, "flags[0]"), (129, "flags[1]"), (130, "flags[2]")] ++ loadBindings
  let load64 ← emit "load64" 128 false loadBindings
    ", v1: &[Wire; 64], imm: &[Wire; 64], flags: &[Wire; 3], cell: &[Wire; 64]" Load.artifact
  let storeBindings := (List.range 64).flatMap fun i =>
    [(i, s!"v1[{i}]"), (64 + i, s!"v2[{i}]"), (128 + i, s!"imm[{i}]"), (194 + i, s!"cell[{i}]")]
  let storeBindings := [(192, "flags[0]"), (193, "flags[1]")] ++ storeBindings
  let store64 ← emit "store64" 128 false storeBindings
    ", v1: &[Wire; 64], v2: &[Wire; 64], imm: &[Wire; 64], flags: &[Wire; 2], cell: &[Wire; 64]" Store.artifact
  let aluBindings := (List.range 64).flatMap fun i =>
    [(i, s!"v1[{i}]"), (64 + i, s!"v2[{i}]"), (128 + i, s!"imm[{i}]"),
      (207 + i, s!"dt[{i}]"), (271 + i, s!"pc4[{i}]")]
  let aluBindings := (List.range 15).map (fun i => (192 + i, s!"flags[{i}]")) ++ aluBindings
  let alu64 ← emit "alu64" 64 false aluBindings
    ", v1: &[Wire; 64], v2: &[Wire; 64], imm: &[Wire; 64], flags: &[Wire; 15], dt: &[Wire; 64], pc4: &[Wire; 64]"
    Alu.artifact Alu.outputProducts (some (List.range 64))
  return "// Generated by verification/circuits/Generate.lean from checked Flock artifacts. Do not edit.\n\
    //! Clean-authored GF(2) circuits consumed by production instruction classes.\n\n\
    use crate::circuit::{Builder, Wire};\n\n" ++ wrapping64 ++ "\n" ++ wrapping32 ++ "\n" ++ wrapping31 ++ "\n" ++ carry64 ++ "\n" ++ shift64 ++ "\n" ++ load64 ++ "\n" ++ store64 ++ "\n" ++ alu64 ++ "\n" ++ blake2s

def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "usage: lake env lean --run Generate.lean <destination.rs>")
  match emitProduction with
  | .error message => throw (IO.userError message)
  | .ok code =>
    IO.FS.writeFile destination code
    let format ← IO.Process.output {
      cmd := "rustfmt", args := #["--config-path", "../../rustfmt.toml", destination] }
    if format.exitCode != 0 then throw (IO.userError format.stderr)
