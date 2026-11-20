/-
  Rv64mc.Spec.Whir.DeriveConfig

  The contract of `verifier::whir::derive_config(log_n, log_inv_rate) -> Result<WhirConfig, VerifierError>`: `sret`
  in `a0`, `log_n` in `a1`, `log_inv_rate` in `a2`; at `sret` `Model.deriveConfigRust`'s answer (`ConfigResultAt`):
  `Ok` with the ladder's rates and folds as fresh `Vec<usize>`s and the tabulated counts as a constant slice of the
  image, or an `Err` (`WhirShape`, `QueryCountLadder`).
-/

import Rv64mc.Spec.Whir.WhirQueries

namespace Rv64mc.Spec.Whir.DeriveConfig

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **The `WhirConfig` `c` at `a`**: its rates and folds fresh, its counts a constant slice. -/
def ConfigAt (env : Env) (m m' : MachineState) (a : Word) (c : Model.WhirConfigRust) : Prop :=
  FreshVecW env m m' (a + BitVec.ofNat 64 Layouts.WhirConfig.log_inv_rates) (c.logInvRates.map (BitVec.ofNat 64)) ∧
    FreshVecW env m m' (a + BitVec.ofNat 64 Layouts.WhirConfig.folds) (c.folds.map (BitVec.ofNat 64)) ∧
    m'.getMem (a + BitVec.ofNat 64 (Layouts.WhirConfig.queries + Layouts.SliceE.len)) =
      BitVec.ofNat 64 c.queries.length ∧
    DataWords env (m'.getMem (a + BitVec.ofNat 64 (Layouts.WhirConfig.queries + Layouts.SliceE.ptr)))
      (c.queries.map (BitVec.ofNat 64))

/-- **The `Result<WhirConfig, VerifierError>` at `a`.** -/
def ConfigResultAt (env : Env) (m m' : MachineState) (a : Word) : Option Model.WhirConfigRust → Prop
  | some c => ConfigAt env m m' (a + BitVec.ofNat 64 Layouts.ResultWhirConfig.Ok.f0) c
  | none => m'.getMem (a + BitVec.ofNat 64 Layouts.ResultWhirConfig.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultWhirConfig.Err.tag

def Pre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.ResultWhirConfig.byteSize

def Post (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  ConfigResultAt env m m' (regs .x10) (Model.deriveConfigRust (regs .x11).toNat (regs .x12).toNat)

/-- **The contract of `derive_config`**, function `i` of `p` with `need` bytes of stack. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (Pre env) (Post env) (SretOut Layouts.ResultWhirConfig.byteSize)

end Rv64mc.Spec.Whir.DeriveConfig
