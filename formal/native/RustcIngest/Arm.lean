module

public meta import RustcIngest.Command
public meta import Kraken.AArch64.Parser

/-!
# AArch64 assembly ingestion during elaboration
-/

open Ingest

/-- AArch64. -/
public meta def arm : Arch Instr ConstExpr where
  ns := "NativeRustcArm"
  syntaxModule := "Kraken.AArch64.Syntax"
  infixModule := "NativeRustcArm.Code.Infix"
  parse := Kraken.AArch64.Parser.parse
  labelConst := .label
  endsBlock i := match i.operation_size, i.operation with
    | _, .B _ | _, .B_cond _ _ | _, .BL _ | _, .BLR _ | _, .BR _ | _, .RET _
    | _, .CBZ _ _ | _, .CBNZ _ _ | _, .TBZ _ _ _ | _, .TBNZ _ _ _ => true
    | _, _ => false
  comment := "//"
  bodyDirective l :=
    if l.startsWith ".cfi_" then pure none else throw s!"unexpected directive {l}"
  addend i c := match i with
    | ⟨.W64, .ADRP dst (.label l)⟩ => pure ⟨.W64, .ADRP dst (.add (.label l) (.int64 (Int64.ofInt c)))⟩
    | ⟨.W64, .ADD_e dst src (.imm ⟨.lo12 (.label l), .S0⟩)⟩ =>
      pure ⟨.W64, .ADD_e dst src (.imm ⟨.lo12 (.add (.label l) (.int64 (Int64.ofInt c))), .S0⟩)⟩
    | _ => throw "an addend outside `adrp` and `add :lo12:`"
  trap := #[0, 0, 0, 0]
  trapAsm := "udf #0"
  dataSize d := match d with
    | ".byte" => some 1 | ".hword" => some 2 | ".word" => some 4 | ".xword" => some 8 | _ => none
  wordDirective n := match n with | 1 => ".byte" | 2 => ".hword" | 4 => ".word" | _ => ".xword"

elab "ingest_arm " ns:str path:str : command =>
  Ingest.elaborateModule arm "aarch64" ns.getString path.getString
