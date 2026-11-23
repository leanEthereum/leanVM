module

import Kraken.AArch64.Print
import NativeRustcArm.Code.Xmss
import NativeRustcArm.Code.Sphincs
import NativeRustcArm.Code.XmssAlign
import NativeRustcArm.Code.SphincsAlign
import NativeRustcVmArm.Code.Vm
import NativeRustcVmArm.Code.VmAlign

/-!
# `print-rustc-code-arm`

`lake exe print-rustc-code-arm xmss|sphincs|vm FILE.s` writes an ingested rustc program
as an assembly file, each directive printed by Kraken's printer
(`Kraken.AArch64.Print.directive`). Sections and alignment are added: each function (a label
not starting with `.L`) opens a section `.text.<name>`, as rustc's do, and each data label of `rodata`
a section `.rodata.<label>` with rustc's alignment from its separate `Align` module. `rustc/ingest/faithful.sh`
assembles the file and compares it with rustc's object file.
-/

/-- The directives printed, each label for which `opens` gives a section directive opening it. -/
def printWithSections (ds : Program) (opens : String → Option String) : Except String String := do
  let mut out := ""
  let mut opened := false
  for d in ds do
    if let .label l := d then
      if let some s := opens l then
        out := out ++ s
        opened := true
    unless opened do throw "a directive before the first section"
    let indent := match d with | .label _ => "" | _ => "\t"
    out := out ++ indent ++ Kraken.AArch64.Print.directive d ++ "\n"
  return out

/-- The assembly of `code`, whose last directives are `rodata`: a section `.text.<f>` at each label `f`
not starting with `.L` before `rodata`, a section `.rodata.<l>` at each label `l` of `rodata`. -/
def asmFile (code rodata : Program) (dataAlign : String → Nat) : Except String String := do
  let n := code.length - rodata.length
  unless code.drop n == rodata do throw "the program does not end with its data"
  let text ← printWithSections (code.take n) fun l =>
    if l.startsWith ".L" then none else some s!"\t.section .text.{l},\"ax\",@progbits\n\t.p2align 2\n"
  let data ← printWithSections rodata fun l =>
    some s!"\t.section .rodata.{l},\"a\",@progbits\n\t.p2align {dataAlign l}\n"
  return text ++ data

public def main (args : List String) : IO UInt32 := do
  let prog? : Option (Program × Program × (String → Nat)) := match args with
    | ["xmss", _] => some (NativeRustcArm.Xmss.code, NativeRustcArm.Xmss.rodata, NativeRustcArm.Xmss.dataAlign)
    | ["sphincs", _] => some (NativeRustcArm.Sphincs.code, NativeRustcArm.Sphincs.rodata, NativeRustcArm.Sphincs.dataAlign)
    | ["vm", _] => some (NativeRustcVmArm.Vm.code, NativeRustcVmArm.Vm.rodata, NativeRustcVmArm.Vm.dataAlign)
    | _ => none
  match prog?, args with
  | some (code, rodata, dataAlign), [_, path] =>
    match asmFile code rodata dataAlign with
    | .ok s => IO.FS.writeFile path s; return 0
    | .error e => IO.eprintln e; return 1
  | _, _ =>
    IO.eprintln "usage: print-rustc-code-arm xmss|sphincs|vm FILE.s"
    return 2
