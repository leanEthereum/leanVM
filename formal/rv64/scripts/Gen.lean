import Rv64Verifier.Sym.Api
import Rv64Verifier.Image

/-!
# Block specifications of a function of the image, generated

  lake exe rv64-gen NAME OUT.lean      (NAME: a part of the function's name, or its index in `Image.functions`)

Splits the function of the image whose name contains `NAME` into basic blocks (leaders: its entry,
the targets of its branches and jumps that land inside it, and every instruction after a branch, a
jump or a call), runs the symbolic executor over each, and writes a module with, per block, its
`Expect` (the final pc, every register, every doubleword written with its value, every side
condition) and its `BlockSpec`, both checked by the kernel when the module builds. The output is
generated: regenerate it, never edit it. Nothing here is trusted: a wrong expectation fails the
module's build.
-/

open Rv64Verifier Rv64Verifier.Sym RiscvZkvm.Rv64

deriving instance Repr for Expect

def cfg : Config := { noAlias := true }

def maxBlock : Nat := 128

def allRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- The successors a control-flow instruction at `pc` names inside `[lo, hi)`, and whether the next
instruction starts a block. -/
def successors (pc : Word) (i : Instruction) : List Word × Bool :=
  match classify i with
  | some (.branch _ _ _ off) => ([pc + off, pc + 4], true)
  | some (.jal _ off) => ([pc + off], true)
  | some (.jalr ..) => ([], true)
  | _ => match i with
    | .base .ECALL | .base .EBREAK => ([], true)
    | _ => ([], false)

def leaders (code : Code) (lo hi : Word) : List Word := Id.run do
  let n := (hi.toNat - lo.toNat) / 4
  let mut ls : List Word := [lo]
  for k in List.range n do
    let pc := lo + BitVec.ofNat 64 (4 * k)
    match code.fetch pc with
    | none => ls := (pc + 4) :: ls
    | some i =>
      let (ts, next) := successors pc i
      for t in ts do
        if lo.toNat ≤ t.toNat ∧ t.toNat < hi.toNat then ls := t :: ls
      if next then ls := (pc + 4) :: ls
  return (ls.filter (fun a ↦ a.toNat < hi.toNat)).mergeSort (fun a b ↦ a.toNat ≤ b.toNat) |>.eraseDups

def fmt {α : Type} [Repr α] (a : α) : String :=
  "\n    ".intercalate ((repr a).pretty 100 |>.splitOn "\n")

def hex (w : Word) : String := String.ofList (Nat.toDigits 16 w.toNat)

def block (code : Code) (pc : Word) (n : Nat) : Except String String := do
  let i := (pc.toNat - code.base.toNat) / 4
  let words := (code.words.drop i).take n
  let some r := symRun cfg words pc n | throw s!"symbolic execution failed in the block at 0x{hex pc}"
  let mut obl := r.st.obl
  let mut mem : List (Addr × E) := []
  for (k, _) in r.st.mem do
    match readMem cfg k r.st.mem with
    | some (v, os) => mem := mem ++ [(k, v)]; obl := obl ++ os
    | none => throw s!"unreadable write in the block at 0x{hex pc}"
  let x : Expect := {
    steps := r.steps, pc := r.pc, regs := allRegs.map (fun reg ↦ (reg, r.st.regs.get reg)),
    mem := mem, writes := r.st.mem.map Prod.fst, obl := Oblig.dedup obl }
  let name := s!"b{hex pc}"
  return s!"def {name} : Expect :=\n  {fmt x}\n\n" ++
    s!"theorem {name}_spec : BlockSpec Image.code {fmt pc} {r.steps}\n" ++
    s!"    (fun s ↦ Oblig.all s {name}.obl) {name}.Holds :=\n" ++
    s!"  BlockSpec.of_expect (cfg := cfg) (fuel := {n}) (x := {name})\n" ++
    s!"    (words := (Image.code.words.drop {i}).take {n}) (by decide +kernel)\n" ++
    s!"    (CodeAt.slice Image.code {i} {n} {fmt pc} (by decide +kernel) (by decide +kernel)\n" ++
    s!"      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)\n\n"

def main (args : List String) : IO UInt32 := do
  let [pat, out] := args | IO.eprintln "usage: rv64-gen NAME OUT.lean"; return 2
  let found := match pat.toNat? with
    | some i => (Image.functions[i]?).toList
    | none => Image.functions.filter (fun f ↦ (f.1.splitOn pat).length > 1)
  let [(name, lo, size)] := found
    | IO.eprintln s!"{found.length} functions match {pat}: {found.map (·.1)}"; return 2
  let hi := lo + BitVec.ofNat 64 size
  -- Long straight-line runs split every `maxBlock` instructions: a block's kernel check grows
  -- faster than its length.
  let ls0 := leaders Image.code lo hi
  let ls := (ls0.zip (ls0.drop 1 ++ [hi])).flatMap fun (a, b) ↦
    (List.range ((b.toNat - a.toNat - 1) / 4 / maxBlock + 1)).map fun j ↦
      a + BitVec.ofNat 64 (4 * maxBlock * j)
  let mut body := ""
  for (a, b) in ls.zip (ls.drop 1 ++ [hi]) do
    -- A block runs up to its first word that does not decode (`unimp`, the panic paths' trap):
    -- the machine traps there, and a trap is not a step.
    let n := ((List.range ((b.toNat - a.toNat) / 4)).takeWhile fun k ↦
      (Image.code.fetch (a + BitVec.ofNat 64 (4 * k))).isSome).length
    if n == 0 then
      body := body ++ s!"-- 0x{hex a}: a word that does not decode; the machine traps here.\n\n"
      continue
    match block Image.code a n with
    | .ok s => body := body ++ s
    | .error e => IO.eprintln e; return 1
  let ns := s!"Rv64Verifier.Blocks.{((out.splitOn "/").getLast!.dropEnd 5).toString}"
  let header := s!"-- Generated by `lake exe rv64-gen` from `{name}` ({size} bytes at 0x{hex lo}, " ++
    s!"{ls.length} blocks). Do not edit.\n\nimport Rv64Verifier.Sym.Api\nimport Rv64Verifier.Image\n\n" ++
    s!"namespace {ns}\n\nopen Rv64Verifier Rv64Verifier.Sym RiscvZkvm.Rv64\n\n" ++
    "def cfg : Config := { noAlias := true }\n\n"
  IO.FS.writeFile out (header ++ body ++ s!"end {ns}\n")
  IO.println s!"{name}: {ls.length} blocks -> {out}"
  return 0
