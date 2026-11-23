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

target rustcVmArmInputs pkg : Unit :=
  rustcAssemblyInputs pkg #["rustc/vm/asm/vm-aarch64.s", "rustc/ingest/vm-names.txt"]

target rustcVmX64Inputs pkg : Unit :=
  rustcAssemblyInputs pkg #["rustc/vm/asm/vm-x86_64.s", "rustc/ingest/vm-names.txt"]


lean_lib RustcIngest where
  globs := #[.submodules `RustcIngest]

-- Model facts shared by the rustc proofs, without a compiler or intermediate machine.
@[default_target]
lean_lib Native where
  globs := #[.submodules `Native]

@[default_target]
lean_lib NativeVm where
  globs := #[.submodules `NativeVm]

@[default_target]
lean_lib NativeRustc where
  globs := #[.submodules `NativeRustc]

-- Each architecture uses its own Kraken semantics and symbolic executor.
-- Proof globs exclude Code, whose libraries attach the assembly dependencies.
@[default_target]
lean_lib NativeRustcArm where
  globs := #[
    .one `NativeRustcArm, .one `NativeRustcArm.Basic, .one `NativeRustcArm.Data, .one `NativeRustcArm.Host,
    .submodules `NativeRustcArm.Hasher, .submodules `NativeRustcArm.KeccakF,
    .submodules `NativeRustcArm.LayerRead, .one `NativeRustcArm.LayerRead, .submodules `NativeRustcArm.Mem,
    .one `NativeRustcArm.Rodata, .submodules `NativeRustcArm.Spec, .one `NativeRustcArm.Sphincs,
    .submodules `NativeRustcArm.SphincsVerify, .submodules `NativeRustcArm.Sym, .one `NativeRustcArm.Sym,
    .submodules `NativeRustcArm.WotsLeaf, .one `NativeRustcArm.WotsLeaf, .one `NativeRustcArm.Xmss,
    .submodules `NativeRustcArm.XmssVerify, .one `NativeRustcArm.XmssVerify]

@[default_target]
lean_lib NativeRustcX64 where
  globs := #[
    .one `NativeRustcX64, .one `NativeRustcX64.Basic, .one `NativeRustcX64.Data,
    .one `NativeRustcX64.Got, .submodules `NativeRustcX64.Hasher,
    .submodules `NativeRustcX64.KeccakF, .submodules `NativeRustcX64.LayerRead, .one `NativeRustcX64.LayerRead,
    .submodules `NativeRustcX64.Mem, .one `NativeRustcX64.Mem, .one `NativeRustcX64.Rodata,
    .submodules `NativeRustcX64.Spec, .one `NativeRustcX64.Sphincs, .submodules `NativeRustcX64.SphincsVerify,
    .submodules `NativeRustcX64.Sym, .one `NativeRustcX64.Sym, .submodules `NativeRustcX64.WotsLeaf,
    .one `NativeRustcX64.WotsLeaf, .one `NativeRustcX64.Xmss, .submodules `NativeRustcX64.XmssVerify,
    .one `NativeRustcX64.XmssVerify]

@[default_target]
lean_lib NativeRustcVm where
  globs := #[.submodules `NativeRustcVm]

@[default_target]
lean_lib NativeRustcVmArm where
  globs := #[
    .one `NativeRustcVmArm, .submodules `NativeRustcVmArm.Arrays, .one `NativeRustcVmArm.Arrays,
    .one `NativeRustcVmArm.Basic, .submodules `NativeRustcVmArm.Bus, .one `NativeRustcVmArm.Bus,
    .submodules `NativeRustcVmArm.Field, .one `NativeRustcVmArm.Field, .submodules `NativeRustcVmArm.Keccak,
    .one `NativeRustcVmArm.Keccak, .submodules `NativeRustcVmArm.KeccakGkr, .one `NativeRustcVmArm.KeccakGkr,
    .submodules `NativeRustcVmArm.Layout, .one `NativeRustcVmArm.Layout, .one `NativeRustcVmArm.Mem,
    .submodules `NativeRustcVmArm.Placed, .one `NativeRustcVmArm.Placed, .submodules `NativeRustcVmArm.Ring,
    .one `NativeRustcVmArm.Ring, .submodules `NativeRustcVmArm.Rodata, .one `NativeRustcVmArm.Rodata,
    .submodules `NativeRustcVmArm.Spec, .submodules `NativeRustcVmArm.Sumcheck, .one `NativeRustcVmArm.Sumcheck,
    .submodules `NativeRustcVmArm.Tables, .one `NativeRustcVmArm.Tables, .submodules `NativeRustcVmArm.Top,
    .submodules `NativeRustcVmArm.Transcript, .one `NativeRustcVmArm.Transcript, .submodules `NativeRustcVmArm.Whir,
    .one `NativeRustcVmArm.Whir, .submodules `NativeRustcVmArm.Wire, .one `NativeRustcVmArm.Wire]

@[default_target]
lean_lib NativeRustcVmX64 where
  globs := #[
    .one `NativeRustcVmX64, .submodules `NativeRustcVmX64.Arrays, .one `NativeRustcVmX64.Arrays,
    .one `NativeRustcVmX64.Basic, .submodules `NativeRustcVmX64.Bus, .one `NativeRustcVmX64.Bus,
    .submodules `NativeRustcVmX64.Field, .one `NativeRustcVmX64.Field, .one `NativeRustcVmX64.Got,
    .submodules `NativeRustcVmX64.Keccak, .one `NativeRustcVmX64.Keccak, .submodules `NativeRustcVmX64.KeccakGkr,
    .one `NativeRustcVmX64.KeccakGkr, .submodules `NativeRustcVmX64.Layout, .one `NativeRustcVmX64.Layout,
    .one `NativeRustcVmX64.Mem, .submodules `NativeRustcVmX64.Placed, .one `NativeRustcVmX64.Placed,
    .submodules `NativeRustcVmX64.Ring, .one `NativeRustcVmX64.Ring, .submodules `NativeRustcVmX64.Rodata,
    .one `NativeRustcVmX64.Rodata, .submodules `NativeRustcVmX64.Spec, .submodules `NativeRustcVmX64.Sumcheck,
    .one `NativeRustcVmX64.Sumcheck, .submodules `NativeRustcVmX64.Tables, .one `NativeRustcVmX64.Tables,
    .submodules `NativeRustcVmX64.Top, .one `NativeRustcVmX64.Top, .submodules `NativeRustcVmX64.Transcript,
    .one `NativeRustcVmX64.Transcript, .submodules `NativeRustcVmX64.Whir, .one `NativeRustcVmX64.Whir,
    .submodules `NativeRustcVmX64.Wire, .one `NativeRustcVmX64.Wire]

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

@[default_target]
lean_lib NativeRustcVmArmCode where
  roots := #[`NativeRustcVmArm.Code]
  globs := #[.andSubmodules `NativeRustcVmArm.Code]
  needs := #[`@/rustcVmArmInputs]

@[default_target]
lean_lib NativeRustcVmX64Code where
  roots := #[`NativeRustcVmX64.Code]
  globs := #[.andSubmodules `NativeRustcVmX64.Code]
  needs := #[`@/rustcVmX64Inputs]


lean_exe «print-rustc-code-arm» where
  root := `PrintRustcCodeArm
  srcDir := "cli"

lean_exe «print-rustc-code-x64» where
  root := `PrintRustcCodeX64
  srcDir := "cli"

