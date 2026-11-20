/-
  Rv64mc.ImageOfElf

  The one reader of an ELF into the statement's `Image` (`imageOfElf`): the executable segment's 32-bit words from
  its address, and every other loadable segment's 8-byte words, zero past its file size. The runner
  (`RunImage.lean`) runs it on the ELF it is given; `elf_image NAME "PATH"` runs it on the ELF at `PATH` when the
  module is built and defines `NAME : Image` as what it gives, a literal for the kernel (`Rv64mc/Gen/Image.lean`,
  written by `scripts/gen.py`). Trusted as the ELF reader: no theorem says the literal is the file's.
-/

import Lean
import Rv64mc.EndStatement
import RiscvZkvm.Interpreter.Elf

namespace Rv64mc

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

/-- Little-endian bytes `i .. i + n - 1` of `bs`, zero past its end. -/
def leBytes (bs : ByteArray) (i n : Nat) : Nat :=
  (List.range n).foldl (fun acc j => acc + (if i + j < bs.size then (bs.get! (i + j)).toNat else 0) * 256 ^ j) 0

/-- The statement's `Image` of an ELF: one executable segment, all in the file, as 32-bit words; every other
    segment as 8-byte words from an 8-aligned address, zero past its file size. -/
def imageOfElf (e : Elf64Image) : Except String Image := do
  let texts := e.segments.filter (·.executable)
  let some text := texts[0]? | throw "no executable segment"
  if texts.size != 1 then throw "more than one executable segment"
  if text.data.size % 4 != 0 then throw "the executable segment's size is not a multiple of 4"
  if text.memsz != text.data.size then throw "the executable segment is not all in the file"
  let code := (List.range (text.data.size / 4)).map fun k => BitVec.ofNat 32 (leBytes text.data (4 * k) 4)
  let mut data : Array (Word × Word) := #[]
  for seg in e.segments do
    if seg.executable then continue
    if seg.vaddr % 8 != 0 then throw s!"data segment at {seg.vaddr} not 8-aligned"
    for k in List.range ((seg.memsz + 7) / 8) do
      data := data.push (BitVec.ofNat 64 (seg.vaddr + 8 * k), BitVec.ofNat 64 (leBytes seg.data (8 * k) 8))
  return { entry := BitVec.ofNat 64 e.entry, codeBase := BitVec.ofNat 64 text.vaddr, code, data := data.toList }

/-- The ELF at `path`, read. -/
def readImage (path : System.FilePath) : IO Image := do
  match parseElf64 (← IO.FS.readBinFile path) >>= imageOfElf with
  | .ok img => pure img
  | .error err => throw (IO.userError s!"{path}: {err}")

open Lean Elab Command Meta

/-- A list literal. -/
private def listLit (ty : Expr) (ys : List Expr) : Expr :=
  ys.foldr (fun y acc => mkApp3 (mkConst ``List.cons [0]) ty y acc) (mkApp (mkConst ``List.nil [0]) ty)

/-- A list as `List.flatten` of literals of at most 256, so that no term nests deeper than that. -/
private def chunkedList (ty : Expr) (xs : List Expr) : Expr :=
  let chunks := (List.range ((xs.length + 255) / 256)).map fun k => listLit ty ((xs.drop (256 * k)).take 256)
  mkApp2 (mkConst ``List.flatten [0]) ty (listLit (mkApp (mkConst ``List [0]) ty) chunks)

private def bv (w n : Nat) : Expr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit n)

/-- `elf_image NAME "PATH"`: `def NAME : Image` as `imageOfElf` reads the ELF at `PATH`, when the module is built. -/
syntax (name := elfImage) "elf_image " ident str : command

@[command_elab elfImage]
def elabElfImage : CommandElab := fun stx => do
  let some path := stx[2].isStrLit? | throwUnsupportedSyntax
  let name := stx[1].getId
  let img ← match ← (readImage path).toBaseIO with
    | .ok i => pure i
    | .error e => throwError "elf_image: {e}"
  let w32 := mkApp (mkConst ``BitVec) (mkNatLit 32)
  let w64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) w64 w64
  let code := chunkedList w32 (img.code.map fun w => bv 32 w.toNat)
  let data := chunkedList pairTy (img.data.map fun (a, v) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) w64 w64 (bv 64 a.toNat) (bv 64 v.toNat))
  let value := mkApp4 (mkConst ``Image.mk) (bv 64 img.entry.toNat) (bv 64 img.codeBase.toNat) code data
  let declName := (← getCurrNamespace) ++ name
  liftCoreM <| addDecl <| .defnDecl {
    name := declName, levelParams := [], type := mkConst ``Image, value
    hints := .abbrev, safety := .safe }

end Rv64mc
