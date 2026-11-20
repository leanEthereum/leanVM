/-
  RunImage: the end statement's own machine, run on a real image and input.

    lake exe rv64mc-run ELF WORDS [--verify] [--fuel N]

  `ELF` is the guest image, `WORDS` the input as little-endian 64-bit words (`scripts/input-words.py`). The image is
  read into the statement's `Image` by `Rv64mc.readImage`, the reader the end theorem's `image` is defined with
  (`Rv64mc/ImageOfElf.lean`), the loaded state is built and checked against `Loaded`, and the statement's `step` is
  run until it stops.
  It prints whether `AllDecode` holds, `decodeInput`'s result, the statement's `verify` on it with `--verify`, and
  where the run stopped: at the halting `ECALL` with its `a0`, or trapped.

  The memory, registers and code are held in hash maps and arrays, and each step builds the `MachineState` they
  stand for (riscv-zkvm's `ExecState.toMachineState`), applies the statement's `step` to it, and copies back the
  registers and the doublewords the instruction can write (`ExecState.writtenAddrs`). The code map is checked equal
  to `Image.codeAt` on every code address. Not proved: that this loop computes `steps` (`notes/non-vacuity.md`).
-/

import Rv64mc.ImageOfElf
import RiscvZkvm.Interpreter.State

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Rv64mc

/-- The 32 registers of a machine state. -/
def regsArray (m : MachineState) : Array Word :=
  (Array.range 32).map fun i => m.getReg (regOfBits (BitVec.ofNat 5 i))

/-- One step of the statement's machine on the hash-map state, or the state itself and `true` where the machine
    stops. What the step wrote is read off the machine state first, so that the hash map is no longer shared with it
    when it is updated in place. -/
def stepFast (e : ExecState) : ExecState × Bool :=
  let m := e.toMachineState
  match Rv64mc.step m with
  | none => (e, true)
  | some m' =>
    let writes := (ExecState.writtenAddrs .zisk m).map fun a => (a, m'.getMem a)
    let regs := regsArray m'
    let pc := m'.pc
    match e with
    | ⟨_, _, mem, code, committed, publicValues, privateInput, inputBufBase⟩ =>
      let mem := writes.foldl (fun acc (a, v) => acc.insert a v) mem
      (⟨regs, pc, mem, code, committed, publicValues, privateInput, inputBufBase⟩, false)

/-- Run until the machine stops or `fuel` steps: the steps taken, the last state, whether it stopped. -/
def runFast (e : ExecState) (n fuel : Nat) : Nat × ExecState × Bool := Id.run do
  let mut e := e
  let mut n := n
  while n < fuel do
    let (e', stop) := stepFast e
    e := e'
    if stop then return (n, e, true)
    n := n + 1
  return (n, e, false)

def readWords (bs : ByteArray) : List Word :=
  (List.range (bs.size / 8)).map fun k =>
    BitVec.ofNat 64 ((List.range 8).foldl (fun acc j => acc + (bs.get! (8 * k + j)).toNat * 256 ^ j) 0)

def main (args : List String) : IO UInt32 := do
  let (elfPath, wordsPath) ← match args with
    | e :: w :: _ => pure (e, w)
    | _ => IO.eprintln "usage: rv64mc-run ELF WORDS [--verify] [--fuel N]"; return 2
  let doVerify := args.contains "--verify"
  let fuel := match args.dropWhile (· != "--fuel") with
    | _ :: n :: _ => n.toNat!
    | _ => 10 ^ 11
  let img ← try readImage elfPath catch err => IO.eprintln s!"{err}"; return 2
  let words := readWords (← IO.FS.readBinFile wordsPath)
  IO.println s!"image: entry {img.entry.toHex}, {img.code.length} code words, {img.data.length} data words"
  IO.println s!"AllDecode: {img.code.all fun w => Runnable (RiscvZkvm.Interpreter.decode w)}"
  IO.println s!"input: {words.length} words (capacity {inputCapacity})"
  -- the loaded state: data, then input; registers zero but `a0`
  let mem0 : Std.HashMap Word Word := img.data.foldl (fun acc (a, v) => acc.insert a v) {}
  let mem0 := (List.range words.length).zip words |>.foldl
    (fun acc (i, w) => acc.insert (inputBase + BitVec.ofNat 64 (8 * i)) w) mem0
  let code : Std.HashMap Word Instr := (List.range img.code.length).foldl (fun acc k =>
    let pc := img.codeBase + BitVec.ofNat 64 (4 * k)
    match img.codeAt pc with
    | some i => acc.insert pc i
    | none => acc) {}
  let regs := (Array.replicate 32 (0 : Word)).set! 10 (BitVec.ofNat 64 words.length)
  let e0 : ExecState := { regs, pc := img.entry, mem := mem0, code }
  let s0 := e0.toMachineState
  -- `Loaded img words s0`, clause by clause (the code map on every code address and one past it)
  let codeOk := (List.range (img.code.length + 1)).all fun k =>
    let pc := img.codeBase + BitVec.ofNat 64 (4 * k)
    s0.code pc == img.codeAt pc
  let dataOk := img.data.all fun (a, v) => s0.getMem a == v
  let inputOk := (List.range words.length).zip words |>.all fun (i, w) =>
    s0.getMem (inputBase + BitVec.ofNat 64 (8 * i)) == w
  let loaded := s0.pc == img.entry && codeOk && dataOk && inputOk &&
    s0.getReg .x10 == BitVec.ofNat 64 words.length && decide (words.length ≤ inputCapacity)
  IO.println s!"Loaded: {loaded} (code {codeOk}, data {dataOk}, input {inputOk})"
  (← IO.getStdout).flush
  match decodeInput words with
  | none => IO.println "decodeInput: none"
  | some (bc, pi, proof) =>
    IO.println s!"decodeInput: some (bytecode {bc.length} words, stream {proof.stream.length} scalars, \
      {proof.openings.length} phases)"
    if doVerify then IO.println s!"verify: {verify bc pi proof}"
  let mut (n, e, stopped) := (0, e0, false)
  while !stopped && n < fuel do
    (n, e, stopped) := runFast e n (min fuel (n + 10 ^ 7))
    if !stopped then IO.println s!"  {n} steps"; (← IO.getStdout).flush
  let t := e.toMachineState
  if !stopped then
    IO.println s!"run: out of fuel after {n} steps at pc {t.pc.toHex}"
    return 1
  let halting := t.code t.pc == some .ECALL && t.getReg .x5 == 0
  if halting then
    IO.println s!"run: halted after {n} steps, a0 = {t.getReg .x10}"
  else
    IO.println s!"run: trapped after {n} steps at pc {t.pc.toHex} ({repr (t.code t.pc)})"
  return 0
