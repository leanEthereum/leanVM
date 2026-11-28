module

public import NativeRustcVmArm.Code.Vm.Names

public import NativeRustcArm.Sym
public meta import NativeRustcVmArm.Code.Vm.Kmul
public meta import NativeRustcVmArm.Code.Vm.TableTerms
public meta import NativeRustcVmArm.Code.Vm.Keccak256WordsOfFiatShamirIv.Part0

/-!
# The symbolic executor on blocks of the leanVM verifier

Blocks of `leanvm_verify` using the instruction forms the signature verifiers do not: `rbit`
(`kmul`), `umull` (`keccak256_words`), and `adrp`/`add :lo12:` of a label plus a constant
(`table_terms`), whose pair is the label plus the constant.
-/

namespace NativeRustcArm.Sym.Test.Vm

set_option Elab.async false

open NativeRustcVmArm.Vm

/-- `kmul`: SP at the top of its 112-byte frame. -/
def kmulS : SState := init [(112, true)] (.ptr 0 112)

sym_block kmul_exec := exec Kmul.b0 kmulS

/-- `kmul` runs to its `ret`, SP back at the frame's top. -/
example : (exec Kmul.b0 kmulS).map (fun r => (r.1.sp, r.2)) = some (.ptr 0 112, .ret) := by
  rw [kmul_exec]
  rfl

sym_block keccak_b1_exec := exec Keccak256WordsOfFiatShamirIv.b1 (init [])

/-- `umull x8, w20, w8` with `w8 = 0xF0F0F0F1`, then `lsr x8, x8, #39`. -/
example : (exec Keccak256WordsOfFiatShamirIv.b1 (init [])).map (·.1.reg .X8) =
    some (some (.un (.ubfm 39 63) .W64
      (.bin .mul .W64 (.un .trunc .W32 (.reg .X20)) (.lit 0xF0F0F0F1)))) := by
  rw [keccak_b1_exec]
  rfl

/-- `table_terms`: SP at the top of its 288-byte frame, below its two stack arguments. -/
def tableTermsS : SState := init [(304, true)] (.ptr 0 288)

sym_block table_terms_exec := exec TableTerms.b0 tableTermsS

/-- `adrp x19, l+8`, `add x19, x19, :lo12:l+8`: X19 (and X21, its copy) is `l + 8`. -/
example : (exec TableTerms.b0 tableTermsS).map (fun r => (r.1.reg .X19, r.1.reg .X21)) =
    some (some (.bin .add .W64 (.label NativeRustcVmArm.Vm.Symbols.rodata4Label) (.lit 8)),
      some (.bin .add .W64 (.label NativeRustcVmArm.Vm.Symbols.rodata4Label) (.lit 8))) := by
  rw [table_terms_exec]
  rfl

end NativeRustcArm.Sym.Test.Vm
