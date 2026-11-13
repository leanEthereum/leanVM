import Statement.Prover.Execute
import LeanVM.Protocol.Verifier
import LeanVM.Cli.Common

/-!
# `leanvm-execute`: the statement's executor against the Rust's

`lake exe leanvm-execute <case dir>...` reads, from each case directory
(`scripts/export-prover-traces-rust.sh` writes them), `bytecode.bin`, `public_input.bin` and
`advice.txt` (`Program::advice_text`), runs `LeanVM.Prover.Exec.execute`, and compares its
execution with the Rust interpreter's, `memory.bin` and `trace.txt`: the memory's size, every cell
and the step count. It prints each case's time and exits with `1` if a case differs or fails.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec LeanVM.Protocol.Verifier LeanVM.Cli

namespace LeanvmExecute

/-- A parser over the advice's whitespace-separated tokens. -/
abbrev P := StateT ℕ (ReaderT (Array String) (Except String))

def tok : P String := do
  let i ← get
  let some t := (← read)[i]? | throw "advice: unexpected end"
  set (i + 1)
  pure t

def expect (t : String) : P Unit := do
  let u ← tok
  unless u = t do throw s!"advice: expected `{t}`, found `{u}`"

def nat : P ℕ := do
  let t ← tok
  let some n := t.toNat? | throw s!"advice: not a number: `{t}`"
  pure n

def hex : P ℕ := do
  let t ← tok
  t.toList.foldlM (fun n c ↦ match hexDigit? c with
    | some d => pure (16 * n + d)
    | none => throw s!"advice: not hexadecimal: `{t}`") 0

def word : P E := do
  let c0 ← hex
  let c1 ← hex
  pure (E.ofLimbs (K.ofBits c0) (K.ofBits c1))

def dest : P BitsDest := do
  match ← tok with
  | "s" => .stack <$> nat
  | "h" => .heap <$> nat
  | t => throw s!"advice: not a destination: `{t}`"

def hint : P Hint := do
  match ← tok with
  | "fa" => .frameAddress <$> nat
  | "af" => return .allocFrames (← nat) (← nat) (← nat) (K.ofBits (← hex)) (← nat)
  | "al" => return .alloc (← nat) (← nat)
  | "ad" => return .allocDyn (← nat) (← nat)
  | "ws" => return .witnessStack (← tok) (← nat) (← nat)
  | "wh" => return .witnessHeap (← tok) (← nat) (← nat) (← nat)
  | "lc" => return .log2Ceil (← dest) (← nat) (← nat) (← nat)
  | "bd" => return .bitDecompose (← nat) (← dest) (← nat)
  | "be" => return .bitDecomposeExp (← nat) (← dest) (← nat)
  | "dd" =>
    return .digitDecomposeExp (← nat) (← dest) (← nat) (← nat) (← nat) (← nat)
      (match ← tok with | "-" => none | t => t.toNat?)
  | "we" => return .windowsExp (← nat) (← dest) (← nat) (← nat) (← nat) (← nat)
  | "fl" => return .fieldLimbs (← nat) (← nat) (← nat)
  | "iv" => return .inverse (← nat) (← nat)
  | t => throw s!"advice: not a hint: `{t}`"

def many {α : Type} (n : ℕ) (p : P α) : P (List α) := (List.range n).mapM fun _ ↦ p

def advice : P Advice := do
  expect "leanvm-advice"; expect "1"; expect "main_frame"
  let mainFrame ← nat
  expect "hints"
  let hints ← many (← nat) do
    let pc ← nat
    return (pc, ← many (← nat) hint)
  expect "streams"
  let streams ← many (← nat) do
    let name ← tok
    return (name, ← many (← nat) do many (← nat) word)
  pure ⟨mainFrame, hints, streams⟩

/-- A word as `limb 1:limb 0` in hex. -/
def hexWord (v : E) : String :=
  s!"{String.ofList (Nat.toDigits 16 (v.limb 1).lane.toNat)}:{String.ofList (Nat.toDigits 16 (v.limb 0).lane.toNat)}"

def describe : Fault → String
  | .conflict c had new => s!"write-once conflict at cell {c}: had {hexWord had}, new {hexWord new}"
  | .unwrittenRead c => s!"read of unwritten cell {c}"
  | .wildPointer _ => "wild pointer"
  | .notInK what _ => s!"{what} is not in K"
  | .notAGPower what _ => s!"{what} is not a g-power in range"
  | .backSolveThroughZero => "back-solve through zero"
  | .witness p => p
  | .outOfMemory => "out of memory"
  | .haltOutsideMain fp => s!"halt outside main (fp {fp})"
  | .stepLimit => "step limit"
  | .badInstruction => "instruction does not decode"
  | .linkMismatch a b => s!"linked cells {a}, {b} differ"

/-- One case: `true` when the executions agree. -/
def runCase (dir : String) : IO Bool := do
  let read := fun (p : String) => do return (← IO.FS.readBinFile (dir ++ "/" ++ p)).toList
  let some words := decodeWords (← read "bytecode.bin") | throw (IO.userError "bad bytecode")
  let some digest := decodeDigest (← read "public_input.bin")
    | throw (IO.userError "bad public input")
  let prog ← IO.ofExcept (decodeProgram words.toArray)
  let input : PublicInput := ⟨fun i ↦ K.ofLane digest[i]⟩
  let tokens := (((← IO.FS.readFile (dir ++ "/advice.txt")).splitToList Char.isWhitespace).filter
    (· ≠ "")).toArray
  let adv ← IO.ofExcept ((advice.run' 0).run tokens)
  let some mem := decodeScalars (← read "memory.bin") | throw (IO.userError "bad memory")
  let mem := mem.toArray
  let nums := ((← IO.FS.readFile (dir ++ "/trace.txt")).trimAscii.toString.splitOn " ").filterMap
    String.toNat?
  let [κ, steps, _] := nums | throw (IO.userError "bad trace.txt")
  let start ← IO.monoMsNow
  match execute prog input adv with
  | .error (pc, f) =>
    IO.println s!"{dir}: FAIL at pc {pc}: {describe f}"
    return false
  | .ok t =>
    let stop ← IO.monoMsNow
    let mut diff : Option ℕ := none
    if h : t.logMemorySize = κ then
      for h' : i in [0:2 ^ κ] do
        if t.memory ⟨i, h ▸ h'.upper⟩ ≠ mem.getD i 0 then
          diff := some i
          break
    let ok := t.logMemorySize = κ ∧ t.stepCount = steps ∧ diff.isNone
    IO.println s!"{dir}: {if ok then "OK" else "DIFFERS"}: {t.stepCount} steps (Rust {steps}), \
      2^{t.logMemorySize} cells (Rust 2^{κ}){(diff.map (s!", first differing cell {·}")).getD ""}, \
      {(stop - start).toFloat / 1000} s"
    return ok

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: leanvm-execute <case dir>..."
    return 2
  let mut ok := true
  for dir in args do
    ok := (← runCase dir) && ok
  return if ok then 0 else 1

end LeanvmExecute

def main (args : List String) : IO UInt32 := LeanvmExecute.main args
