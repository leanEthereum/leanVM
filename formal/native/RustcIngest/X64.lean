module

public meta import RustcIngest.Command
public meta import Kraken.X64.Parser

/-!
# x86-64 assembly ingestion during elaboration

Loop alignment is retained as Kraken's `.align` directives; panic entries become `ud2`.
-/

open Ingest

/-- x86-64. -/
public meta def x64 : Arch Instr ConstExpr where
  ns := "NativeRustcX64"
  syntaxModule := "Kraken.X64.Syntax"
  infixModule := "NativeRustcArm.Code.Infix"
  parse := Kraken.X64.Parser.parse
  labelConst := .label
  endsBlock
    | .regular _ _ (.jcc _ _) | .regular _ _ (.jmp _) | .regular _ _ (.call _) | .regular _ _ .ret => true
    | _ => false
  comment := "#"
  bodyDirective l :=
    if l.startsWith ".cfi_" then pure none
    else match l.splitOn " " with
      | [".p2align", n] => match n.toNat? with
        | some k => pure (some s!".align {2 ^ k}")
        | none => throw s!"unexpected directive {l}"
      | _ => throw s!"unexpected directive {l}"
  trap := #[0x0f, 0x0b]
  trapAsm := "ud2"
  dataSize d := match d with
    | ".byte" => some 1 | ".short" | ".value" | ".word" => some 2 | ".long" => some 4 | ".quad" => some 8
    | _ => none
  wordDirective n := match n with | 1 => ".byte" | 2 => ".short" | 4 => ".long" | _ => ".quad"

elab "ingest_x64 " ns:str path:str : command =>
  Ingest.elaborateModule x64 "x86_64" ns.getString path.getString
