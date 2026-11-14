import LeanVM.Guest.Data.Source
import Statement.Data.Bytecode
import LeanVM.Guest.Backend.Invariants
import LeanVM.Guest.Interp
import LeanVMTests.Guest.Programs

/-!
# `guest-backend`: the guest compiled by the Lean back end

Run from `lean_vm`.

* `lake exe guest-backend check` compiles the guest's source (`Data.guest`) with `Backend.compile`
  and compares the result with the statement's program, `assemble Data.functions Data.logSize`
  (`Statement/Data/`, `LeanVM.Guest.guestProgram`): the compiled functions against
  `Data.functions`, value for value (`Assembled.toFunctions`), and every slot of the program, the
  padding included (`instructionAtPc`). It fails on any difference and names the first. It
  also evaluates the back end's invariants (`Backend.invariants`) and compares the traced
  expansion's core functions with `Expand.expandProgram`'s.
* `lake exe guest-backend functions [N]` is the comparison with every function resolved at the
  statement's layout, so that each function is compared on its own: the count of identical
  functions and instructions when the programs differ, and the first `N` that differ.
* `lake exe guest-backend export guest FILE` and `export programs DIR [--check]` write the guest,
  and the compiler's test programs (`LeanVMTests.Guest.Programs`), in the line format of
  `crates/leanvm_core/src/cpu/text.rs`, which the Rust tests compare with the Rust compiler's
  output (`crates/lean_compiler/tests/suite/lean_backend.rs`, `rec_aggregation`'s
  `lean_backend_guest`).
* `lake exe guest-backend time` prints the time of each pass on the guest.
* `lake exe guest-backend core NAME` prints a function's core IR, and `show NAME` its code beside
  the statement's.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend

namespace GuestBackend

/-! ## The statement's bytecode -/

/-- The statement's program (`Statement/Data/`): its functions `(name, entry, length)`, each
function's instructions, and its log size. -/
structure Reference where
  fns : Array (String × Nat × Nat)
  code : Array OffsetInstruction
  logSize : Nat

/-- The functions of `Data.functions`, one after another. -/
def reference : Reference :=
  { fns := (Data.functions.map fun f => (f.name, f.entryPc, f.instructionCount)).toArray,
    code := Data.functions.foldl (init := #[]) fun acc f =>
      acc ++ ((List.range f.instructionCount).map f.instructionAt).toArray,
    logSize := Data.logSize }

/-! ## Rendering -/

def showOp : OffsetInstruction → String
  | .xor a b c => s!"X {a} {b} {c}"
  | .mul a b c => s!"M {a} {b} {c}"
  | .set o k0 k1 => s!"S {o} {k0} {k1}"
  | .deref o1 o2 o3 mode =>
      let m := match mode with
        | .cell => 0
        | .pc => 1
        | .fp => 2
      s!"D {o1} {o2} {o3} {m}"
  | .jump oc od of => s!"J {oc} {od} {of}"
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
      s!"K {m0} {m1} {m2} {m3} {tail} {b8} {cap} {out} {inOdd.toNat} {outOdd.toNat} {outCells.cellCount}"

def showBits : BitsDest → String
  | .stack b => s!"stack {b}"
  | .heap p => s!"heap {p}"

/-- A hint's line. -/
def showHint (pc : Nat) : RHint → String
  | .frameAddress offset => s!"H {pc} frame {offset}"
  | .allocFrames ptr size bound inv tail => s!"H {pc} frames {ptr} {size} {bound} {inv} {tail}"
  | .alloc ptr size => s!"H {pc} alloc {ptr} {size}"
  | .allocDyn ptr size => s!"H {pc} allocdyn {ptr} {size}"
  | .witnessStack s base len => s!"H {pc} wstack {s} {base} {len}"
  | .witnessHeap s ptr lo len => s!"H {pc} wheap {s} {ptr} {lo} {len}"
  | .log2Ceil bits dst nbits floor => s!"H {pc} log2 {showBits bits} {dst} {nbits} {floor}"
  | .bitDecompose v bits nbits => s!"H {pc} bits {v} {showBits bits} {nbits}"
  | .bitDecomposeExp v bits nbits => s!"H {pc} bitsexp {v} {showBits bits} {nbits}"
  | .digitDecomposeExp v dst nbits ndigits digitBits start sc =>
      let sc := match sc with
        | some c => s!"{c}"
        | none => "-"
      s!"H {pc} digits {v} {showBits dst} {nbits} {ndigits} {digitBits} {start} {sc}"
  | .windowsExp v dest skip start width count =>
      s!"H {pc} windows {v} {showBits dest} {skip} {start} {width} {count}"
  | .fieldLimbs v base len => s!"H {pc} limbs {v} {base} {len}"
  | .inverse v dst => s!"H {pc} inverse {v} {dst}"

/-- A program in the line format of `crates/leanvm_core/src/cpu/text.rs` (`Program::__to_text`):
its padded size, `main`'s frame, a line a function, a line an instruction before the padding, a
line a hint in pc order. -/
def render (c : Assembled) : String :=
  let head := #[s!"size {c.size}", s!"main_frame {c.mainFrame}"]
  let fns := c.fns.map fun (name, entry, len) => s!"F {name} {entry} {len}"
  let hints := c.hints.flatMap fun (pc, hs) => (hs.map (showHint pc)).toArray
  "\n".intercalate (head ++ fns ++ c.code.map showOp ++ hints).toList ++ "\n"

/-! ## The comparison -/

def guestCore : IO (List TracedFn) :=
  match ExpandTrace.expandProgram Data.guest with
  | .ok P => pure P
  | .error e => throw (IO.userError s!"expansion failed: {e}")

def orThrow {α : Type} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- The guest compiled, each function resolved at the statement's layout. -/
def atReference (ref : Reference) (P : List TracedFn) : IO Assembled := do
  let (fns, slots) ← orThrow (lowerProgram P)
  let (fns, _) := withTables fns slots
  let size := 2 ^ ref.logSize
  let entry : Std.HashMap String Nat := ref.fns.foldl (init := {}) fun m (name, e, _) => m.insert name e
  let frame : Std.HashMap String Nat := fns.foldl (init := {}) fun m f => m.insert f.name f.frameSize
  let tablesBase := match (ref.code[0]? : Option OffsetInstruction) with
    | some (.set o _ _) => o
    | _ => 0
  let l : Layout := { entry, frame, tablesBase, sentinel := size - 1, gpow := gpowTable size }
  return assembleAt l size fns

/-- Compare `ours` with the statement's program function by function; the number of identical
functions and the differing ones `(name, our length, its length, first differing offset)`. -/
def compareFns (ref : Reference) (ours : Assembled) :
    Nat × Nat × Array (String × Nat × Nat × Nat) := Id.run do
  let mut same := 0
  let mut sameIns := 0
  let mut bad := #[]
  for i in List.range (max ref.fns.size ours.fns.size) do
    let (rn, re, rl) := ref.fns.getD i ("-", 0, 0)
    let (on, oe, ol) := ours.fns.getD i ("-", 0, 0)
    let n := min rl ol
    let mut first := n
    let mut eq := 0
    for k in List.range n do
      if ref.code[re + k]? == ours.code[oe + k]? then eq := eq + 1
      else if first == n then first := k
    sameIns := sameIns + eq
    if rn == on && rl == ol && first == n then same := same + 1
    else bad := bad.push (if rn == on then rn else s!"{on}/{rn}", ol, rl, first)
  return (same, sameIns, bad)

def report (ref : Reference) (ours : Assembled) (limit : Nat) : IO Bool := do
  let (same, sameIns, bad) := compareFns ref ours
  IO.println s!"functions: {same} of {ref.fns.size} identical ({ours.fns.size} compiled)"
  IO.println s!"instructions: {sameIns} of {ref.code.size} equal at their offset ({ours.code.size} compiled)"
  for (name, ol, rl, first) in bad.toList.take limit do
    IO.println s!"  {name}: {ol} instructions for {rl}, first difference at offset {first}"
  if bad.size > limit then IO.println s!"  … and {bad.size - limit} more"
  return bad.isEmpty && ours.code.size == ref.code.size && ours.size == 2 ^ ref.logSize

/-- The checks that need no reference: the traced expansion against `Expand`, and the back
end's invariants. -/
def selfChecks (name : String) (p : Source.Program) : IO Bool := do
  let traced ← orThrow (ExpandTrace.expandProgram p)
  let core ← orThrow (Expand.expandProgram p)
  let checks ← orThrow (invariants traced)
  let checks := ("the traced expansion's core functions are Expand's", sameCore traced core) :: checks
  for (what, ok) in checks do
    unless ok do IO.println s!"{name}: FAILED: {what}"
  return checks.all (·.2)

/-- Whether the compiled functions are the statement's, value for value: names, entries, lengths
and chunks. -/
def sameFunctions (ours : Assembled) : Bool :=
  let fs := ours.toFunctions
  fs.length == Data.functions.length && (fs.zip Data.functions).all fun (a, b) =>
    a.name == b.name && a.entryPc == b.entryPc && a.instructionCount == b.instructionCount &&
      a.chunks == b.chunks

/-- The first slot at which the statement's program, `assemble Data.functions Data.logSize`, and
the compiled one differ, the padding included. -/
def firstDifference (ours : Assembled) : Option Nat :=
  (List.range (2 ^ Data.logSize)).find? fun pc =>
    instructionAtPc Data.functions pc != ours.code.getD pc .padding

def check : IO UInt32 := do
  let ref := reference
  let sound ← selfChecks "guest" Data.guest
  if sound then IO.println "the traced expansion is Expand's, and the back end's invariants hold"
  let ours ← orThrow (Backend.compile Data.guest)
  let same ← report ref ours 20
  let sized := ours.size == 2 ^ Data.logSize && ours.code.size == Data.codeLen && sameFunctions ours
  match firstDifference ours with
  | none =>
      if same && sized then
        IO.println s!"identical: `Data.functions` value for value, and the {2 ^ Data.logSize} slots of \
          `assemble Data.functions {Data.logSize}`, {ours.code.size} instructions in {ours.fns.size} \
          functions and the padding"
        return if sound then 0 else 1
      else
        IO.println "the slots agree, the function tables or the sizes do not"
        return 1
  | some pc =>
      IO.println s!"first difference at pc {pc}: {showOp (ours.code.getD pc .padding)} for \
        {showOp (instructionAtPc Data.functions pc)}"
      return 1

def functions (args : List String) : IO UInt32 := do
  let limit := match args with
    | [n] => n.toNat!
    | _ => 40
  let ours ← atReference reference (← guestCore)
  let ok ← report reference ours limit
  return if ok then 0 else 1

/-- A function's code beside the statement's, up to its thirtieth difference. -/
def «show» (name : String) : IO UInt32 := do
  let P ← guestCore
  let ref := reference
  let ours ← atReference ref P
  let some (_, re, rl) := ref.fns.find? (·.1 == name) | return 0
  let some (_, oe, ol) := ours.fns.find? (·.1 == name) | return 0
  IO.println s!"-- {ol} instructions for {rl}"
  let mut shown := 0
  for k in List.range (max rl ol) do
    let a := if k < ol then (ours.code[oe + k]?.map showOp).getD "-" else "-"
    let b := if k < rl then (ref.code[re + k]?.map showOp).getD "-" else "-"
    if a != b then shown := shown + 1
    if shown ≤ 30 then
      IO.println s!"{k}: {a}{if a == b then "" else s!"    <<<< {b}"}"
  return 0

/-- A function's core IR. -/
def core (name : String) : IO UInt32 := do
  let P ← guestCore
  let some f := P.find? (·.core.name == name) | do IO.eprintln s!"no function {name}"; return 1
  IO.println (Interp.showFn f.core)
  return 0

def exportGuest (file : String) : IO UInt32 := do
  let ours ← orThrow (Backend.compile Data.guest)
  IO.FS.writeFile file (render ours)
  IO.println s!"{file}: {ours.code.size} instructions, size {ours.size}, main frame {ours.mainFrame}"
  return 0

def exportPrograms (dir : String) (checkOnly : Bool) : IO UInt32 := do
  let mut failed := false
  for t in LeanVMTests.Guest.Programs.all do
    let path := s!"{dir}/{t.name}.txt"
    unless ← selfChecks t.name t.program do failed := true
    match Backend.compile t.program with
    | .error e =>
        IO.eprintln s!"{t.name}: {e}"
        failed := true
    | .ok c =>
        if checkOnly then
          if !(← System.FilePath.pathExists path) || (← IO.FS.readFile path) != render c then
            IO.eprintln s!"{path} is stale: run `lake exe guest-backend export programs {dir}`"
            failed := true
        else
          IO.FS.createDirAll dir
          IO.FS.writeFile path (render c)
          IO.println s!"{path}: {c.code.size} instructions, size {c.size}, main frame {c.mainFrame}"
  return if failed then 1 else 0

def time : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let P ← guestCore
  let t1 ← IO.monoMsNow
  IO.println s!"expand: {t1 - t0} ms, {P.length} functions"
  let (pfns, tables) ← orThrow (placeProgram P)
  let t2 ← IO.monoMsNow
  IO.println s!"place: {t2 - t1} ms, {tables.len} jump table slots"
  let (lowered, fills) := pfns.foldl (init := (#[], #[])) fun (ls, fills) pf =>
    let (l, f) := emitFn pf.fn
    (ls.push l, fills ++ f)
  let n := lowered.foldl (fun n (l : Lowered) => n + l.code.size) 0
  let t3 ← IO.monoMsNow
  IO.println s!"emit: {t3 - t2} ms, {n} instructions"
  let a := assemble lowered.toList (tableSlots tables.len fills tables.entries)
  let t4 ← IO.monoMsNow
  IO.println s!"assemble: {t4 - t3} ms, {a.code.size} instructions, size {a.size}, {a.hints.size} hinted pcs"
  IO.println s!"total: {t4 - t0} ms"
  return 0

end GuestBackend

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check"] => GuestBackend.check
  | "functions" :: rest => GuestBackend.functions rest
  | ["show", name] => GuestBackend.show name
  | ["core", name] => GuestBackend.core name
  | ["export", "guest", file] => GuestBackend.exportGuest file
  | ["export", "programs", dir] => GuestBackend.exportPrograms dir false
  | ["export", "programs", dir, "--check"] => GuestBackend.exportPrograms dir true
  | ["time"] => GuestBackend.time
  | _ =>
      IO.eprintln "usage: guest-backend check | functions [N] | show NAME | core NAME | export guest FILE | export programs DIR [--check] | time"
      return 2
