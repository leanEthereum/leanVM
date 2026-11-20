/-
  Rv64mc.Spec.Whir.StackedOpening

  The contracts of the stacked opening (`lib.rs`) and of the WHIR opening it ends in (`whir.rs`), as the image has
  them: `verify_whir` is generic over its basis closure, and the image has one instance, at
  `verify_stacked_opening`'s `evaluate_basis` (`verify_whir::<verify_stacked_opening::{closure#1}>`).

  * The claims (`&[(StackWeight, E)]`): `ClaimsAt`, claim `k` at `a + 80 k`, its weight at `StackClaim.f0`
    (`StackWeightAt`) and its value at `StackClaim.f1`, the array live.
  * `evaluate_basis`'s captured environment, which rustc lays out without a printable type: read off the code of
    `verify_stacked_opening` (it stores them at `sp + 0x18`) and of the closure (it loads them from `a0`), the
    claims' pointer at offset `0`, their count at `8`, and the address of the `scales` `Vec` header at `16`
    (`BasisEnvAt`, offsets `basisClaims`, `basisCount`, `basisScales`).
  * `evaluate_basis(&env, point: &[E]) -> E` (`env` in `a0`, the point in `a1`, `a2`): `basisRust`, the closure of
    `Model.verifyStackedOpeningRust` (the weights by `StackWeight::evaluate`, dotted with the scales).
  * `verify_whir(transcript, log_n, log_inv_rate, target, root, evaluate_basis) -> Result<(), VerifierError>`
    (the transcript in `a0`, `log_n` in `a1`, `log_inv_rate` in `a2`, `target`'s limbs in `a3`, `a4`, the root's
    32 bytes at `a5`, the closure's environment at `a6`; the result's tag in `a0`): the mirror's step
    `Model.verifyWhirRust` with that basis.
  * `verify_stacked_opening(transcript, root, stack_log, log_inv_rate, claims) -> Result<(), VerifierError>` (the
    transcript in `a0`, the root at `a1`, `stack_log` in `a2`, `log_inv_rate` in `a3`, the claims in `a4`, `a5`):
    the mirror's step `Model.verifyStackedOpeningRust`.

  Each returns `Ok` (the niche tag, `Layouts.ResultUnit.Ok.tag`) exactly where the mirror succeeds, the transcript
  then the mirror's, and writes the transcript besides its stack and its allocations (`Out`).
-/

import Rv64mc.Spec.Whir.StackWeight
import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Spec.Whir.StackedOpening

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.RingWeight Rv64mc.Spec.Whir.StackWeight
  Rv64mc.Spec.Transcript

/-! ## The claims and the basis closure -/

/-- **The claims `cs` from `a`**, claim `k` at `a + 80 k`: its weight and its value, the array live. -/
def ClaimsAt (env : Env) (m : MachineState) (a : Word) (cs : List (Model.StackWeightRust × E)) : Prop :=
  env.Live m a (Layouts.StackClaim.byteSize * cs.length) ∧ ∀ k (h : k < cs.length),
    StackWeightAt env m (a + BitVec.ofNat 64 (Layouts.StackClaim.byteSize * k + Layouts.StackClaim.f0)) cs[k].1 ∧
      EAt m (a + BitVec.ofNat 64 (Layouts.StackClaim.byteSize * k + Layouts.StackClaim.f1)) (Model.limbs cs[k].2)

/-- The offsets of `evaluate_basis`'s captured environment, read off the code (no printable type). -/
abbrev basisClaims : Nat := 0
abbrev basisCount : Nat := 8
abbrev basisScales : Nat := 16
abbrev basisBytes : Nat := 24

/-- **`evaluate_basis`'s environment at `e`**: the claims `cs` (pointer and count) and the `scales` `Vec`. -/
def BasisEnvAt (env : Env) (m : MachineState) (top e : Word) (cs : List (Model.StackWeightRust × E))
    (scales : List E) : Prop :=
  InFrame top e basisBytes ∧
    ClaimsAt env m (m.getMem (e + BitVec.ofNat 64 basisClaims)) cs ∧
    m.getMem (e + BitVec.ofNat 64 basisCount) = BitVec.ofNat 64 cs.length ∧
    InFrame top (m.getMem (e + BitVec.ofNat 64 basisScales)) Layouts.Vec.byteSize ∧
    EVecAt env m (m.getMem (e + BitVec.ofNat 64 basisScales)) scales

/-- `evaluate_basis`, the closure of `Model.verifyStackedOpeningRust`. -/
def basisRust (cs : List (Model.StackWeightRust × E)) (scales : List E) (point : List E) : Option E := do
  let weights ← cs.mapM fun c ↦ c.1.evaluate point
  Model.dotRust scales weights

def BasisPre (env : Env) (cs : List (Model.StackWeightRust × E)) (scales point : List E) (regs : Reg → Word)
    (m : MachineState) : Prop :=
  BasisEnvAt env m (regs .x2) (regs .x10) cs scales ∧ ESlice env m (regs .x11) (regs .x12) point

def BasisPost (cs : List (Model.StackWeightRust × E)) (scales point : List E) (_regs : Reg → Word)
    (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  ∀ v, basisRust cs scales point = some v → r' .x10 = (Model.limbs v).1 ∧ r' .x11 = (Model.limbs v).2

/-- **The contract of `evaluate_basis`** (`verify_stacked_opening::{closure#1}`), function `i` of `p` with `need`
    bytes of stack, for every claims, scales and point. -/
def basisSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ cs scales point, Holds env p i need (BasisPre env cs scales point) (BasisPost cs scales point)

/-! ## `verify_whir` -/

/-- `Result<(), VerifierError>` returned in registers: `Ok` exactly where the mirror's step succeeds. -/
def UnitRet (r' : Reg → Word) (ok : Bool) : Prop :=
  if ok then r' .x10 = BitVec.ofNat 64 Layouts.ResultUnit.Ok.tag
  else r' .x10 ≠ BitVec.ofNat 64 Layouts.ResultUnit.Ok.tag

/-- What the transcript methods write besides their stack and allocations: the transcript. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.Transcript.byteSize b

/-- The mirror's step's outcome: `Ok` and the next transcript, or failure. -/
def StepPost (env : Env) (step : Model.TM Unit) (t : Model.TState) (regs : Reg → Word) (r' : Reg → Word)
    (m' : MachineState) : Prop :=
  match step.run t with
  | some ((), t') => UnitRet r' true ∧ TranscriptAt env m' (regs .x10) t'
  | none => UnitRet r' false

def WhirPre (env : Env) (t : Model.TState) (target : E) (root : List (BitVec 8))
    (cs : List (Model.StackWeightRust × E)) (scales : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x10) t ∧ InFrame (regs .x2) (regs .x10) Layouts.Transcript.byteSize ∧
    ProofSafe env m (regs .x2) (regs .x10) ∧
    regs .x13 = (Model.limbs target).1 ∧ regs .x14 = (Model.limbs target).2 ∧
    DigestAt m (regs .x15) root ∧ InFrame (regs .x2) (regs .x15) Layouts.Digest.byteSize ∧
    BasisEnvAt env m (regs .x2) (regs .x16) cs scales

def WhirPost (env : Env) (t : Model.TState) (target : E) (root : List (BitVec 8))
    (cs : List (Model.StackWeightRust × E)) (scales : List E) (regs : Reg → Word) (_m : MachineState)
    (r' : Reg → Word) (m' : MachineState) : Prop :=
  StepPost env (Model.verifyWhirRust (regs .x11).toNat (regs .x12).toNat target root (basisRust cs scales)) t regs r'
    m'

/-- **The contract of `verify_whir::<verify_stacked_opening::{closure#1}>`**, function `i` of `p` with `need`
    bytes of stack, for every transcript state, target, root, claims and scales. -/
def whirSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t target root cs scales,
    Holds env p i need (WhirPre env t target root cs scales) (WhirPost env t target root cs scales) Out

/-! ## `verify_stacked_opening` -/

def Pre (env : Env) (t : Model.TState) (root : List (BitVec 8)) (cs : List (Model.StackWeightRust × E))
    (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x10) t ∧ InFrame (regs .x2) (regs .x10) Layouts.Transcript.byteSize ∧
    ProofSafe env m (regs .x2) (regs .x10) ∧
    DigestAt m (regs .x11) root ∧ InFrame (regs .x2) (regs .x11) Layouts.Digest.byteSize ∧
    regs .x15 = BitVec.ofNat 64 cs.length ∧ ClaimsAt env m (regs .x14) cs

def Post (env : Env) (t : Model.TState) (root : List (BitVec 8)) (cs : List (Model.StackWeightRust × E))
    (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  StepPost env (Model.verifyStackedOpeningRust root (regs .x12).toNat (regs .x13).toNat cs) t regs r' m'

/-- **The contract of `verify_stacked_opening`**, function `i` of `p` with `need` bytes of stack, for every
    transcript state, root and claims. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t root cs, Holds env p i need (Pre env t root cs) (Post env t root cs) Out

end Rv64mc.Spec.Whir.StackedOpening
