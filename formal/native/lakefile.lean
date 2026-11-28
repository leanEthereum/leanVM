import Lake

open Lake DSL System

package native where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`warningAsError, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    -- Kraken's `[Labels]` has no parameters; the loaded program supplies its instance.
    ⟨`weak.linter.concreteInstances, false⟩]

require statement from "../Statement"

require fast_fields from "../fast_fields"

require «lean-vm» from "../lean_vm"

require Kraken from git "https://github.com/kevaundray/kraken" @ "6930e39c710ac5e5307612e985f97520858023ab"

require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly" @ "afb9b1363984a70f10e24bd597f6ff40ebc8afbb"

require "leanprover-community" / mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"

require VCVio from git "https://github.com/Verified-zkEVM/VCVio.git" @ "f1e63c780de398fb62206dd5890f27e1ad64e0e6"

require PolyFun from git "https://github.com/Verified-zkEVM/PolyFun" @ "528b3b1fda285487e55704409bd1b058dc18fcad"

def rustcAssemblyInputs (pkg : Package) (paths : Array FilePath) : FetchM (Job Unit) := do
  let jobs ← paths.mapM fun path => inputBinFile (pkg.dir / path)
  return Job.mixArray jobs

target rustcArmInputs pkg : Unit :=
  rustcAssemblyInputs pkg #["rustc/asm/signatures-aarch64.s"]

target rustcX64Inputs pkg : Unit :=
  rustcAssemblyInputs pkg #["rustc/asm/signatures-x86_64.s"]


lean_lib RustcIngest where
  globs := #[.submodules `RustcIngest]

-- Model facts shared by the rustc proofs, without a compiler or intermediate machine.
@[default_target]
lean_lib Native where
  globs := #[.submodules `Native]

@[default_target]
lean_lib NativeRustc where
  globs := #[.submodules `NativeRustc]

-- Each architecture uses its own Kraken semantics and symbolic executor.
-- Proof globs exclude Code, whose libraries attach the assembly dependencies.
@[default_target]
lean_lib NativeRustcArm where
  globs := #[
    .one `NativeRustcArm, .one `NativeRustcArm.Basic, .one `NativeRustcArm.Data, .one `NativeRustcArm.Host,
    .one `NativeRustcArm.Restrict,
    .submodules `NativeRustcArm.Hasher, .submodules `NativeRustcArm.KeccakF,
    .one `NativeRustcArm.LayerRead.Glue, .submodules `NativeRustcArm.Mem,
    .one `NativeRustcArm.Rodata, .submodules `NativeRustcArm.Spec, .one `NativeRustcArm.Sphincs,
    .submodules `NativeRustcArm.SphincsVerify, .submodules `NativeRustcArm.Sym, .one `NativeRustcArm.Sym]

@[default_target]
lean_lib NativeRustcX64 where
  globs := #[
    .one `NativeRustcX64, .one `NativeRustcX64.Basic, .one `NativeRustcX64.Data,
    .one `NativeRustcX64.Got, .one `NativeRustcX64.Restrict, .submodules `NativeRustcX64.Hasher,
    .submodules `NativeRustcX64.KeccakF, .one `NativeRustcX64.LayerRead.Glue,
    .submodules `NativeRustcX64.Mem, .one `NativeRustcX64.Mem, .one `NativeRustcX64.Rodata,
    .submodules `NativeRustcX64.Spec, .one `NativeRustcX64.Sphincs, .submodules `NativeRustcX64.SphincsVerify,
    .submodules `NativeRustcX64.Sym, .one `NativeRustcX64.Sym]

@[default_target]
lean_lib NativeRustcArmCode where
  roots := #[`NativeRustcArm.Code]
  globs := #[.andSubmodules `NativeRustcArm.Code]
  needs := #[`@/rustcArmInputs]

@[default_target]
lean_lib NativeRustcX64Code where
  roots := #[`NativeRustcX64.Code]
  globs := #[.andSubmodules `NativeRustcX64.Code]
  needs := #[`@/rustcX64Inputs]


lean_exe «print-rustc-code-arm» where
  root := `PrintRustcCodeArm
  srcDir := "cli"

lean_exe «print-rustc-code-x64» where
  root := `PrintRustcCodeX64
  srcDir := "cli"

